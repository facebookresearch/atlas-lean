/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.SystemT.Syntax
public import Mathlib.Computability.Ackermann
public import Mathlib.Logic.Relation

/-!
# System T: full reduction

`Step t t'` is one-step full reduction of System T: the compatible closure, over open contexts,
of β-reduction and the two conversions of the recursor (Girard, Lafont and Taylor, *Proofs and
Types*, §7.1.4):

* `natRec u v zero` reduces to `u`;
* `natRec u v (succ t)` reduces to `v (natRec u v t) t`: the step function receives the value
  of the recursion at the predecessor first and the predecessor second.

Reduction applies in every position, under λ-abstractions and inside every argument of the
recursor, so the relation is full reduction rather than a call-by-value strategy. `Steps` is its
reflexive transitive closure.

The file states the congruence rules of `Steps`, stability of reduction under renaming and
substitution, that numerals are normal forms, and the Ackermann function: the term `ackT`
recurses at type `nat ⇒ nat`, as Girard suggests in §7.3.2, and reduces on numerals `m` and `n`
to the numeral of Mathlib's `ack m n`.

## References

* J.-Y. Girard, Y. Lafont, P. Taylor, *Proofs and Types*, Cambridge University Press, 1989,
  Chapter 7: §7.1.4 (conversions), §7.3.2 (numerals, iteration and Ackermann's function).
* M. H. Sørensen, P. Urzyczyn, *Lectures on the Curry-Howard Isomorphism*, 1998,
  Definition 11.6.1.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.SystemT

open scoped CslibStlc
open Tm

/-- **Full reduction of System T.** Write $b[a]$ for the instantiation of the newest variable of
an abstraction body $b$ with $a$, and $\mathsf{R}\,u\,v\,t$ for the recursor. One-step reduction
$t \to t'$ between terms of the same type in the same context is the least relation closed under
these rules: $(\lambda b)\,a \to b[a]$; $\mathsf{R}\,u\,v\,\mathsf{zero} \to u$;
$\mathsf{R}\,u\,v\,(\mathsf{succ}\,t) \to v\,(\mathsf{R}\,u\,v\,t)\,t$; and reduction of any
immediate subterm: the function or the argument of an application, the body of an abstraction,
the argument of a successor, and each of the three arguments of the recursor
(Girard-Lafont-Taylor §7.1.4, Sørensen-Urzyczyn Definition 11.6.1). -/
inductive Step : {Γ : List Ty} → {A : Ty} → Tm Γ A → Tm Γ A → Prop where
  | beta {Γ : List Ty} {A B : Ty} {body : Tm (A :: Γ) B} {a : Tm Γ A} :
      Step (.app (.lam body) a) (body.instantiate a)
  | natRecZero {Γ : List Ty} {A : Ty} {u : Tm Γ A} {v : Tm Γ (A ⇒ Ty.nat ⇒ A)} :
      Step (.natRec u v .zero) u
  | natRecSucc {Γ : List Ty} {A : Ty} {u : Tm Γ A} {v : Tm Γ (A ⇒ Ty.nat ⇒ A)}
      {t : Tm Γ .nat} :
      Step (.natRec u v (.succ t)) (.app (.app v (.natRec u v t)) t)
  | appFun {Γ : List Ty} {A B : Ty} {f f' : Tm Γ (A ⇒ B)} {a : Tm Γ A} (h : Step f f') :
      Step (.app f a) (.app f' a)
  | appArg {Γ : List Ty} {A B : Ty} {f : Tm Γ (A ⇒ B)} {a a' : Tm Γ A} (h : Step a a') :
      Step (.app f a) (.app f a')
  | lam {Γ : List Ty} {A B : Ty} {body body' : Tm (A :: Γ) B} (h : Step body body') :
      Step (.lam body) (.lam body')
  | succ {Γ : List Ty} {t t' : Tm Γ .nat} (h : Step t t') : Step (.succ t) (.succ t')
  | natRecBase {Γ : List Ty} {A : Ty} {u u' : Tm Γ A} {v : Tm Γ (A ⇒ Ty.nat ⇒ A)}
      {t : Tm Γ .nat} (h : Step u u') :
      Step (.natRec u v t) (.natRec u' v t)
  | natRecStep {Γ : List Ty} {A : Ty} {u : Tm Γ A} {v v' : Tm Γ (A ⇒ Ty.nat ⇒ A)}
      {t : Tm Γ .nat} (h : Step v v') :
      Step (.natRec u v t) (.natRec u v' t)
  | natRecArg {Γ : List Ty} {A : Ty} {u : Tm Γ A} {v : Tm Γ (A ⇒ Ty.nat ⇒ A)}
      {t t' : Tm Γ .nat} (h : Step t t') :
      Step (.natRec u v t) (.natRec u v t')

/-- **Multi-step reduction of System T.** For terms $t$ and $t'$ of the same type in the same
context, $t \to^* t'$ holds when $t$ reduces to $t'$ in finitely many, possibly zero, steps of
full reduction. -/
abbrev Steps {Γ : List Ty} {A : Ty} : Tm Γ A → Tm Γ A → Prop := Relation.ReflTransGen Step

namespace Steps

/-- **Reduction in the function of an application.** If $f \to^* f'$, then
$f\,a \to^* f'\,a$. -/
theorem appFun {Γ : List Ty} {A B : Ty} {f f' : Tm Γ (A ⇒ B)} {a : Tm Γ A} (h : Steps f f') :
    Steps (.app f a) (.app f' a) :=
  Relation.ReflTransGen.lift (fun f => Tm.app f a) (fun _ _ h => Step.appFun h) _ _ h

/-- **Reduction in the argument of an application.** If $a \to^* a'$, then
$f\,a \to^* f\,a'$. -/
theorem appArg {Γ : List Ty} {A B : Ty} {f : Tm Γ (A ⇒ B)} {a a' : Tm Γ A} (h : Steps a a') :
    Steps (.app f a) (.app f a') :=
  Relation.ReflTransGen.lift (fun a => Tm.app f a) (fun _ _ h => Step.appArg h) _ _ h

/-- **Reduction under an abstraction.** If $b \to^* b'$, then $\lambda b \to^* \lambda b'$. -/
theorem lam {Γ : List Ty} {A B : Ty} {body body' : Tm (A :: Γ) B} (h : Steps body body') :
    Steps (.lam body) (.lam body') :=
  Relation.ReflTransGen.lift Tm.lam (fun _ _ h => Step.lam h) _ _ h

/-- **Reduction under a successor.** If $t \to^* t'$, then
$\mathsf{succ}\,t \to^* \mathsf{succ}\,t'$. -/
theorem succ {Γ : List Ty} {t t' : Tm Γ .nat} (h : Steps t t') : Steps (.succ t) (.succ t') :=
  Relation.ReflTransGen.lift Tm.succ (fun _ _ h => Step.succ h) _ _ h

/-- **Reduction in the base case of a recursor.** If $u \to^* u'$, then
$\mathsf{R}\,u\,v\,t \to^* \mathsf{R}\,u'\,v\,t$. -/
theorem natRecBase {Γ : List Ty} {A : Ty} {u u' : Tm Γ A} {v : Tm Γ (A ⇒ Ty.nat ⇒ A)}
    {t : Tm Γ .nat} (h : Steps u u') : Steps (.natRec u v t) (.natRec u' v t) :=
  Relation.ReflTransGen.lift (fun u => Tm.natRec u v t) (fun _ _ h => Step.natRecBase h) _ _ h

/-- **Reduction in the step function of a recursor.** If $v \to^* v'$, then
$\mathsf{R}\,u\,v\,t \to^* \mathsf{R}\,u\,v'\,t$. -/
theorem natRecStep {Γ : List Ty} {A : Ty} {u : Tm Γ A} {v v' : Tm Γ (A ⇒ Ty.nat ⇒ A)}
    {t : Tm Γ .nat} (h : Steps v v') : Steps (.natRec u v t) (.natRec u v' t) :=
  Relation.ReflTransGen.lift (fun v => Tm.natRec u v t) (fun _ _ h => Step.natRecStep h) _ _ h

/-- **Reduction in the argument of a recursor.** If $t \to^* t'$, then
$\mathsf{R}\,u\,v\,t \to^* \mathsf{R}\,u\,v\,t'$. -/
theorem natRecArg {Γ : List Ty} {A : Ty} {u : Tm Γ A} {v : Tm Γ (A ⇒ Ty.nat ⇒ A)}
    {t t' : Tm Γ .nat} (h : Steps t t') : Steps (.natRec u v t) (.natRec u v t') :=
  Relation.ReflTransGen.lift (fun t => Tm.natRec u v t) (fun _ _ h => Step.natRecArg h) _ _ h

end Steps

/-- **Reduction is stable under renaming.** If $t \to t'$ in context $\Gamma$, then for every
renaming $\rho$ from $\Gamma$ to $\Delta$ the renamings of $t$ and $t'$ along $\rho$ satisfy the
same step in $\Delta$. -/
theorem Step.rename {Γ Δ : List Ty} {A : Ty} (ρ : Ren Γ Δ) {t t' : Tm Γ A} (h : Step t t') :
    Step (t.rename ρ) (t'.rename ρ) :=
  by
    induction h generalizing Δ with
    | beta =>
        rw [rename_instantiate]
        exact .beta
    | natRecZero => exact .natRecZero
    | natRecSucc => exact .natRecSucc
    | appFun _ ih => exact .appFun (ih ρ)
    | appArg _ ih => exact .appArg (ih ρ)
    | lam _ ih => exact .lam (ih (Stlc.Var.lift ρ))
    | succ _ ih => exact .succ (ih ρ)
    | natRecBase _ ih => exact .natRecBase (ih ρ)
    | natRecStep _ ih => exact .natRecStep (ih ρ)
    | natRecArg _ ih => exact .natRecArg (ih ρ)

/-- **Reduction is stable under substitution.** If $t \to t'$ in context $\Gamma$, then for every
substitution $\sigma$ from $\Gamma$ to $\Delta$ the results of applying $\sigma$ to $t$ and to
$t'$ satisfy the same step in $\Delta$. -/
theorem Step.subst {Γ Δ : List Ty} {A : Ty} (σ : Sub Γ Δ) {t t' : Tm Γ A} (h : Step t t') :
    Step (t.subst σ) (t'.subst σ) :=
  by
    induction h generalizing Δ with
    | @beta _ _ _ body a =>
        have e : (body.instantiate a).subst σ =
            (body.subst (Sub.lift σ)).instantiate (a.subst σ) := by
          rw [instantiate_subst_lift, instantiate, subst_subst]
          apply subst_congr
          intro C x
          cases x <;> rfl
        rw [e]
        exact .beta
    | natRecZero => exact .natRecZero
    | natRecSucc => exact .natRecSucc
    | appFun _ ih => exact .appFun (ih σ)
    | appArg _ ih => exact .appArg (ih σ)
    | lam _ ih => exact .lam (ih (Sub.lift σ))
    | succ _ ih => exact .succ (ih σ)
    | natRecBase _ ih => exact .natRecBase (ih σ)
    | natRecStep _ ih => exact .natRecStep (ih σ)
    | natRecArg _ ih => exact .natRecArg (ih σ)

/-- **Multi-step reduction is stable under renaming.** If $t \to^* t'$ in context $\Gamma$, then
for every renaming $\rho$ from $\Gamma$ to $\Delta$ the renamings satisfy $\to^*$ in $\Delta$. -/
theorem Steps.rename {Γ Δ : List Ty} {A : Ty} (ρ : Ren Γ Δ) {t t' : Tm Γ A} (h : Steps t t') :
    Steps (t.rename ρ) (t'.rename ρ) :=
  Relation.ReflTransGen.lift (Tm.rename ρ) (fun _ _ h => Step.rename ρ h) _ _ h

/-- **Multi-step reduction is stable under substitution.** If $t \to^* t'$ in context $\Gamma$,
then for every substitution $\sigma$ from $\Gamma$ to $\Delta$ the substituted terms satisfy
$\to^*$ in $\Delta$. -/
theorem Steps.subst {Γ Δ : List Ty} {A : Ty} (σ : Sub Γ Δ) {t t' : Tm Γ A} (h : Steps t t') :
    Steps (t.subst σ) (t'.subst σ) :=
  Relation.ReflTransGen.lift (Tm.subst σ) (fun _ _ h => Step.subst σ h) _ _ h

/-- **Numerals are normal forms.** In every context, no step of full reduction applies to the
numeral $\mathsf{succ}^n(\mathsf{zero})$. -/
theorem numeral_normal {Γ : List Ty} (n : Nat) {t' : Tm Γ .nat} : ¬ Step (numeral n) t' :=
  by
    induction n generalizing t' with
    | zero =>
        intro h
        rw [numeral_zero] at h
        cases h
    | succ n ih =>
        intro h
        rw [numeral_succ] at h
        cases h with
        | succ h => exact ih h

/-- **The recursor on a successor numeral.** For every natural number $n$, the recursor applied
to the numeral of $n + 1$ steps to the step function applied to the recursor at the numeral of
$n$ and then to the numeral of $n$ (Girard-Lafont-Taylor §7.3.2). -/
theorem Step.natRec_numeral_succ {Γ : List Ty} {A : Ty} (u : Tm Γ A)
    (v : Tm Γ (A ⇒ Ty.nat ⇒ A)) (n : Nat) :
    Step (.natRec u v (numeral (n + 1))) (.app (.app v (.natRec u v (numeral n))) (numeral n)) :=
  .natRecSucc

/-- **Ackermann's function in System T.** The term
$\lambda m.\,\mathsf{R}\,(\lambda n.\,\mathsf{succ}\,n)\,
(\lambda f.\,\lambda \_.\,\lambda n.\,\mathsf{R}\,(f\,\underline{1})\,
(\lambda r.\,\lambda \_.\,f\,r)\,n)\,m$ of type
$\mathsf{nat} \Rightarrow \mathsf{nat} \Rightarrow \mathsf{nat}$, where $\underline{1}$ is the
numeral of $1$. The outer recursor works at type $\mathsf{nat} \Rightarrow \mathsf{nat}$: from
the function $f$ for $m$ it builds the function for $m + 1$, sending $n$ to $f^{n+1}(1)$. This
adapts the iteration at higher type of Girard-Lafont-Taylor §7.3.2, whose iterator
$\mathrm{it}(f)$ sends $n$ to $f^n(1)$, with $\mathrm{it}(f)(0) = 1$: here the inner recursion
starts at $f(1)$, so the function for $m + 1$ sends $0$ to $f(1)$, matching
$\mathrm{ack}(m + 1, 0) = \mathrm{ack}(m, 1)$ for Mathlib's `ack`. -/
def ackT {Γ : List Ty} : Tm Γ (Ty.nat ⇒ Ty.nat ⇒ Ty.nat) :=
  .lam (.natRec (.lam (.succ (.var .zero)))
    (.lam (.lam (.lam
      (.natRec (.app (.var (.succ (.succ .zero))) (numeral 1))
        (.lam (.lam (.app (.var (.succ (.succ (.succ (.succ .zero))))) (.var (.succ .zero)))))
        (.var .zero)))))
    (.var .zero))

/-- **A β-step up to equality of the reduct.** If the instantiation of `body` with `a` equals
`t`, then `(λ body) a` steps to `t` (helper for `ackT_steps`). -/
private theorem step_beta_of_eq {Γ : List Ty} {A B : Ty} {body : Tm (A :: Γ) B} {a : Tm Γ A}
    {t : Tm Γ B} (h : body.instantiate a = t) : Step (.app (.lam body) a) t :=
  h ▸ .beta

/-- **Base function of `ackT`.** The successor function `λn. succ n` (helper for
`ackT_steps`). -/
private def ackBase {Γ : List Ty} : Tm Γ (Ty.nat ⇒ Ty.nat) := .lam (.succ (.var .zero))

/-- **Step function of `ackT`.** The term `λf. λ_. λn. R (f 1) (λr. λ_. f r) n` (helper for
`ackT_steps`). -/
private def ackStep {Γ : List Ty} : Tm Γ ((Ty.nat ⇒ Ty.nat) ⇒ Ty.nat ⇒ Ty.nat ⇒ Ty.nat) :=
  .lam (.lam (.lam
    (.natRec (.app (.var (.succ (.succ .zero))) (numeral 1))
      (.lam (.lam (.app (.var (.succ (.succ (.succ (.succ .zero))))) (.var (.succ .zero)))))
      (.var .zero))))

/-- **Inner step function of `ackT`.** For a function `f`, the term `λr. λ_. f r` (helper for
`ackT_steps`). -/
private def ackInner {Γ : List Ty} (f : Tm Γ (Ty.nat ⇒ Ty.nat)) :
    Tm Γ (Ty.nat ⇒ Ty.nat ⇒ Ty.nat) :=
  .lam (.lam (.app (Tm.weaken (Tm.weaken f)) (.var (.succ .zero))))

/-- **Unfolding the step function of `ackT`.** For every function `f` and numerals `k`, `n`,
`ackStep f k n` reduces to `R (f 1) (ackInner f) n`: three β-steps on an open term with
variables for `f`, `k`, `n`, then a closing substitution (helper for `ackT_steps`). -/
private theorem ackStep_steps {Γ : List Ty} (f : Tm Γ (Ty.nat ⇒ Ty.nat)) (k n : Nat) :
    Steps (.app (.app (.app ackStep f) (numeral k)) (numeral n))
      (.natRec (.app f (numeral 1)) (ackInner f) (numeral n)) := by
  have h : Steps (Γ := Ty.nat :: Ty.nat :: (Ty.nat ⇒ Ty.nat) :: Γ)
      (.app (.app (.app ackStep (.var (.succ (.succ .zero)))) (.var (.succ .zero))) (.var .zero))
      (.natRec (.app (.var (.succ (.succ .zero))) (numeral 1))
        (ackInner (.var (.succ (.succ .zero)))) (.var .zero)) :=
    .head (.appFun (.appFun .beta)) (.head (.appFun .beta) (.single (step_beta_of_eq rfl)))
  exact Steps.subst (Sub.cons (numeral n) (Sub.cons (numeral k) (Sub.cons f Sub.id))) h

/-- **One round of the inner recursion of `ackT`.** For every function `f` and number `n`,
`R (f 1) (ackInner f) (n + 1)` reduces to `f (R (f 1) (ackInner f) n)` (helper for
`ackT_steps`). -/
private theorem ackInner_unfold {Γ : List Ty} (f : Tm Γ (Ty.nat ⇒ Ty.nat)) (n : Nat) :
    Steps (.natRec (.app f (numeral 1)) (ackInner f) (numeral (n + 1)))
      (.app f (.natRec (.app f (numeral 1)) (ackInner f) (numeral n))) := by
  have h : Steps (Γ := Ty.nat :: (Ty.nat ⇒ Ty.nat) :: Γ)
      (.natRec (.app (.var (.succ .zero)) (numeral 1)) (ackInner (.var (.succ .zero)))
        (.succ (.var .zero)))
      (.app (.var (.succ .zero))
        (.natRec (.app (.var (.succ .zero)) (numeral 1)) (ackInner (.var (.succ .zero)))
          (.var .zero))) :=
    .head .natRecSucc (.head (.appFun .beta) (.single (step_beta_of_eq rfl)))
  exact Steps.subst (Sub.cons (numeral n) (Sub.cons f Sub.id)) h

/-- **The inner recursion of `ackT` iterates `f`.** If `f` reduces on every numeral `j` to the
numeral of `ack k j`, then `R (f 1) (ackInner f) n` reduces to the numeral of `ack (k + 1) n`
(helper for `ackT_steps`). -/
private theorem ackInner_steps {Γ : List Ty} (f : Tm Γ (Ty.nat ⇒ Ty.nat)) (k : Nat)
    (hf : ∀ j, Steps (.app f (numeral j)) (numeral (ack k j))) (n : Nat) :
    Steps (.natRec (.app f (numeral 1)) (ackInner f) (numeral n)) (numeral (ack (k + 1) n)) := by
  induction n with
  | zero =>
      rw [ack_succ_zero]
      exact .head .natRecZero (hf 1)
  | succ n ih =>
      rw [ack_succ_succ]
      exact (ackInner_unfold f n).trans ((Steps.appArg ih).trans (hf _))

/-- **The outer recursion of `ackT` computes Ackermann's function.** For all numbers `m` and `n`,
`R ackBase ackStep m` applied to the numeral of `n` reduces to the numeral of `ack m n` (helper
for `ackT_steps`). -/
private theorem ackFun_steps {Γ : List Ty} (m n : Nat) :
    Steps (.app (.natRec ackBase ackStep (numeral m)) (numeral n) : Tm Γ .nat)
      (numeral (ack m n)) := by
  induction m generalizing n with
  | zero =>
      rw [ack_zero]
      exact .head (.appFun .natRecZero) (.single (step_beta_of_eq rfl))
  | succ k ih =>
      exact .head (.appFun .natRecSucc) ((ackStep_steps _ k n).trans (ackInner_steps _ k ih n))
/-- **The System T Ackermann term computes Ackermann's function.** In every context and for all
natural numbers $m$ and $n$, the term `ackT` applied to the numerals of $m$ and $n$ reduces in
finitely many steps to the numeral of `ack m n`, Mathlib's Ackermann function. -/
theorem ackT_steps {Γ : List Ty} (m n : Nat) :
    Steps (.app (.app ackT (numeral m)) (numeral n) : Tm Γ .nat) (numeral (ack m n)) :=
  .head (.appFun (step_beta_of_eq rfl)) (ackFun_steps m n)

end Cslib.Languages.LambdaCalculus.SystemT
