/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.SystemT.Reduction

/-!
# Tests for System T reduction

* T1: Girard's addition reduces `2 + 3` to `5`.
* T2: the Ackermann term at `m = 0` and `m = 1`, reduced step by step.
* T3: the Ackermann term at `(2, 1)` and `(3, 0)` through `ackT_steps`, against Mathlib's `ack`.
* T4: a step of an open term, transported by a closing substitution.
* T5: numerals are normal.
* T6: with a normal base and step function, the recursor on a variable is normal: a variable
  argument blocks both recursor conversions, which fire only on `zero` and `succ`, though
  reduction inside the base or the step function still applies when they are not normal.
* T7: reduction under a λ-abstraction, so the relation is full reduction.
* T8: argument order of the recursor: the reduct passes the recursive result first; the reduct
  with the arguments swapped is not a step.
* T9: a step of a closed term, transported by weakening.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.SystemT.Tests

open scoped CslibStlc
open Tm

/-- **Girard's addition.** The term $\lambda x.\,\lambda y.\,\mathsf{R}\,x\,
(\lambda z.\,\lambda z'.\,\mathsf{succ}\,z)\,y$ (Girard-Lafont-Taylor §7.3.2). -/
def addT {Γ : List Ty} : Tm Γ (Ty.nat ⇒ Ty.nat ⇒ Ty.nat) :=
  .lam (.lam (.natRec (.var (.succ .zero)) (.lam (.lam (.succ (.var (.succ .zero))))) (.var .zero)))

/-- **Step function returning the recursive result.** The term $\lambda r.\,\lambda p.\,r$. -/
def vFst {Γ : List Ty} : Tm Γ (Ty.nat ⇒ Ty.nat ⇒ Ty.nat) := .lam (.lam (.var (.succ .zero)))

/-- **T1: addition.** Girard's addition applied to the numerals of $2$ and $3$ reduces to the
numeral of $5$. -/
theorem addT_two_three :
    Steps (.app (.app addT (numeral 2)) (numeral 3) : Tm [] .nat) (numeral 5) :=
  .head (.appFun .beta) <| .head .beta <| .head .natRecSucc <| .head (.appFun .beta) <|
  .head .beta <| .head (.succ .natRecSucc) <| .head (.succ (.appFun .beta)) <|
  .head (.succ .beta) <| .head (.succ (.succ .natRecSucc)) <|
  .head (.succ (.succ (.appFun .beta))) <| .head (.succ (.succ .beta)) <|
  .head (.succ (.succ (.succ .natRecZero))) .refl

/-- **T2: Ackermann at zero.** The Ackermann term applied to the numerals of $0$ and $2$ reduces
to the numeral of $3 = \mathrm{ack}(0, 2)$. -/
theorem ackT_zero_two :
    Steps (.app (.app ackT (numeral 0)) (numeral 2) : Tm [] .nat) (numeral 3) :=
  .head (.appFun .beta) <| .head (.appFun .natRecZero) <| .head .beta .refl

/-- **T2: Ackermann at one.** The Ackermann term applied to the numerals of $1$ and $0$ reduces
to the numeral of $2 = \mathrm{ack}(1, 0)$, through the outer recursion at type
$\mathsf{nat} \Rightarrow \mathsf{nat}$. -/
theorem ackT_one_zero :
    Steps (.app (.app ackT (numeral 1)) (numeral 0) : Tm [] .nat) (numeral 2) :=
  .head (.appFun .beta) <| .head (.appFun .natRecSucc) <| .head (.appFun (.appFun .beta)) <|
  .head (.appFun .beta) <| .head .beta <| .head .natRecZero <| .head (.appFun .natRecZero) <|
  .head .beta .refl

/-- **T3: Ackermann against Mathlib.** By `ackT_steps`, the Ackermann term reduces on $(2, 1)$
and on $(3, 0)$ to the numeral of $5$, the value Mathlib's `ack` takes there. -/
theorem ackT_two_one_three_zero :
    ack 2 1 = 5 ∧ ack 3 0 = 5 ∧
    Steps (.app (.app ackT (numeral 2)) (numeral 1) : Tm [] .nat) (numeral 5) ∧
    Steps (.app (.app ackT (numeral 3)) (numeral 0) : Tm [] .nat) (numeral 5) := by
  have h21 : ack 2 1 = 5 := by rw [ack_two]
  have h30 : ack 3 0 = 5 := by rw [ack_succ_zero, h21]
  refine ⟨h21, h30, ?_, ?_⟩
  · simpa only [h21] using ackT_steps (Γ := []) 2 1
  · simpa only [h30] using ackT_steps (Γ := []) 3 0

/-- **T4: transport by a closing substitution.** In the context with one variable $x$ of type
$\mathsf{nat}$, $\mathsf{R}\,0\,v\,(\mathsf{succ}\,x)$ steps to $v\,(\mathsf{R}\,0\,v\,x)\,x$;
substituting the numeral of $2$ for $x$ gives the corresponding step of closed terms. -/
theorem natRec_open_subst :
    Step ((.natRec .zero vFst (.succ (.var .zero)) : Tm [Ty.nat] .nat).subst
        (Sub.single (numeral 2)))
      ((.app (.app vFst (.natRec .zero vFst (.var .zero))) (.var .zero) : Tm [Ty.nat] .nat).subst
        (Sub.single (numeral 2))) ∧
    (.natRec .zero vFst (.succ (.var .zero)) : Tm [Ty.nat] .nat).subst (Sub.single (numeral 2)) =
      .natRec .zero vFst (numeral 3) :=
  ⟨Step.subst _ .natRecSucc, rfl⟩

/-- **T5: numerals are normal.** The numeral of $3$ does not step. -/
theorem numeral_three_normal {t' : Tm [] .nat} : ¬ Step (numeral 3) t' := by
  intro h
  cases h with
  | succ h => cases h with
    | succ h => cases h with
      | succ h => cases h

/-- **T6: the recursor fires only on constructors.** In the context with one variable $x$ of type
$\mathsf{nat}$, $\mathsf{R}\,0\,(\lambda r.\,\lambda p.\,r)\,x$ does not step. -/
theorem natRec_var_normal {t' : Tm [Ty.nat] .nat} :
    ¬ Step (.natRec .zero vFst (.var .zero)) t' := by
  intro h
  cases h with
  | natRecBase h => cases h
  | natRecStep h => cases h with
    | lam h => cases h with
      | lam h => cases h
  | natRecArg h => cases h

/-- **T7: reduction under an abstraction.** $\lambda x.\,(\lambda y.\,y)\,x$ steps to
$\lambda x.\,x$, a step that a weak call-by-value relation does not take. -/
theorem step_under_lam :
    Step (.lam (.app (.lam (.var .zero)) (.var .zero)) : Tm [] (Ty.nat ⇒ Ty.nat))
      (.lam (.var .zero)) :=
  .lam .beta

/-- **T8: argument order of the recursor.** With $v = \lambda r.\,\lambda p.\,r$,
$\mathsf{R}\,0\,v\,(\mathsf{succ}\,0)$ steps to $v\,(\mathsf{R}\,0\,v\,0)\,0$, the recursive
result first and the predecessor second, and does not step to $v\,0\,(\mathsf{R}\,0\,v\,0)$. -/
theorem natRec_argument_order :
    Step (.natRec .zero vFst (.succ .zero) : Tm [] .nat)
      (.app (.app vFst (.natRec .zero vFst .zero)) .zero) ∧
    ¬ Step (.natRec .zero vFst (.succ .zero) : Tm [] .nat)
      (.app (.app vFst .zero) (.natRec .zero vFst .zero)) := by
  refine ⟨.natRecSucc, ?_⟩
  intro h
  cases h

/-- **T9: transport by weakening.** The closed step
$\mathsf{R}\,0\,v\,(\mathsf{succ}\,0) \to v\,(\mathsf{R}\,0\,v\,0)\,0$ holds after weakening both
sides into the context with one variable of type $\mathsf{nat}$. -/
theorem natRec_step_weaken :
    Step ((.natRec .zero vFst (.succ .zero) : Tm [] .nat).rename (Δ := [Ty.nat]) .succ)
      ((.app (.app vFst (.natRec .zero vFst .zero)) .zero : Tm [] .nat).rename (Δ := [Ty.nat])
        .succ) ∧
    (.natRec .zero vFst (.succ .zero) : Tm [] .nat).rename (Δ := [Ty.nat]) .succ =
      .natRec .zero vFst (.succ .zero) :=
  ⟨Step.rename _ .natRecSucc, rfl⟩

end Cslib.Languages.LambdaCalculus.SystemT.Tests
