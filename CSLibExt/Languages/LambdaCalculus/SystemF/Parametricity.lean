/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.SystemF.Erasure
public import CSLibExt.Languages.LambdaCalculus.SystemF.Interpretation
public import CSLibExt.Languages.LambdaCalculus.SystemF.Typing

/-!
# Relational parametricity for pure System F

The fundamental theorem covers all five typing rules, arbitrary relation
environments, and two independently chosen related closing substitutions.
Universal types range over all beta-invariant binary relations in the existing
syntactic term model. This is not an equality-only or typing-defined relation.
The computational conclusion is about full-beta conversion of erasures, not
CBV termination or a set-valued interpretation of all universes.

## Provenance and adaptation

The abstraction-theorem pattern is due to Reynolds (1983, Section 3), with
polymorphic relations in Section 8. The related-environment formulation and
derivation of free theorems follow Wadler (1989, Section 6 and Figure 1).

This is a project-authored syntactic-model adaptation, not a formalization of
Reynolds' proposed set-theoretic interpretation. Relations are beta-invariant
binary predicates on the fixed model of erased untyped terms, using CSLib's
full-beta conversion. Arrows use model application; universal types range over
all such relations. The theorem proves related erased closing instances, and
the identity consumer proves full-beta conversion of erasures, not CBV
termination or normalization. No full set-valued model is assumed; Reynolds
(1984) proves the obstruction to extending the standard set-theoretic model.

## References

* John C. Reynolds, *Types, Abstraction and Parametric Polymorphism*,
  *Information Processing 83*, R. E. A. Mason (ed.), North-Holland, 1983,
  pp. 513-523, Sections 3 and 8.
* Philip Wadler, *Theorems for free!*, *FPCA '89*, ACM Press, 1989,
  pp. 347-359, Section 6 and Figure 1.
  <https://doi.org/10.1145/99370.99404>
* John C. Reynolds, *Polymorphism is not set-theoretic*,
  *Semantics of Data Types*, LNCS 173, 1984, pp. 145-156.
  <https://doi.org/10.1007/3-540-13346-1_7>
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.SystemF

/-- **Fundamental theorem of relational parametricity for System F.**
The fundamental binary relational-parametricity theorem of pure System F.

A syntactic-model adaptation of Reynolds' abstraction theorem (1983,
Sections 3 and 8), following Wadler's related-environment formulation (1989,
Section 6); see the module's provenance and model qualifications.
-/
theorem fundamental {n m : Nat} {Γ : Ctx n m} {t : Tm n m} {A : Ty n}
    (ht : Typing Γ t A) (ρ : Fin n → Rel) (σ τ : Fin m → Model)
    (hστ : ∀ i, ((Γ i).interpret ρ).holds (σ i) (τ i)) :
    (A.interpret ρ).holds (Tm.close σ t) (Tm.close τ t) := by
  induction ht with
  | var i => exact hστ i
  | app hf ha ihf iha => exact (ihf ρ σ τ hστ) _ _ (iha ρ σ τ hστ)
  | @lam n m Γ A B b hb ih =>
    intro x y hxy
    apply ((B.interpret ρ).congr
      (Tm.close_beta σ A b x) (Tm.close_beta τ A b y)).mpr
    apply ih ρ (Fin.cases x σ) (Fin.cases y τ)
    intro i
    induction i using Fin.cases with
    | zero => exact hxy
    | succ i => exact hστ i
  | tabs hb ih =>
    intro R
    apply ih (Fin.cases R ρ) σ τ
    intro i
    simpa only [Ty.interpret_weaken] using hστ i
  | @tapp n m Γ f A C hf ih =>
    rw [Ty.interpret_instantiate]
    exact ih ρ σ τ hστ (A.interpret ρ)

/-- **Closed typed System F terms are related to themselves.**
Every closed typed term is related to itself under arbitrary relations. -/
theorem fundamental_closed {n : Nat} {Γ : Ctx n 0} {t : Tm n 0} {A : Ty n}
    (ht : Typing Γ t A) (ρ : Fin n → Rel) :
    (A.interpret ρ).holds (Tm.eraseModel t) (Tm.eraseModel t) :=
  fundamental ht ρ Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i)

/-- **Polymorphic identity type.**
The polymorphic identity type, universally quantified at any type depth. -/
def polyIdType {n : Nat} : Ty n := .all (.arr (.var 0) (.var 0))

/-- **Polymorphic identity term.** The pure polymorphic identity term. -/
def polyId {n m : Nat} : Tm n m := .tabs (.lam (.var 0) (.var 0))

/-- **Typing of the polymorphic identity.**
The polymorphic identity is well typed in any existing term context. -/
theorem polyId_typed {n m : Nat} (Γ : Ctx n m) :
    Typing Γ polyId polyIdType := .tabs (.lam (.var 0))

/-- **Closed inhabitants of the polymorphic identity type are identities.**
Every closed inhabitant acts as identity after every type instantiation.

The conclusion is full-beta conversion in the existing erased term model,
for an arbitrary locally closed input. It makes no CBV termination claim.
This consumer specializes the free-theorem method of Wadler (1989, Figure 1)
to the declared syntactic model; it applies to every typed inhabitant.
-/
theorem polymorphic_identity {t : Tm 0 0}
    (ht : Typing Fin.elim0 t polyIdType) (A : Ty 0) (x : Model) :
    BetaEq (Model.app (Tm.eraseModel (.tapp t A)) x) x := by
  have h := fundamental_closed ht Fin.elim0
  have hx := h (Rel.betaClass x) x x ⟨BetaEq.refl x, BetaEq.refl x⟩
  exact hx.1

/-- **Polymorphic identity inhabitants preserve admissible relations.**
Type instantiations preserve every admissible binary input relation. -/
theorem polymorphic_related {t : Tm 0 0}
    (ht : Typing Fin.elim0 t polyIdType) (A B : Ty 0) (R : Rel)
    {x y : Model} (hxy : R.holds x y) :
    R.holds (Model.app (Tm.eraseModel (.tapp t A)) x)
      (Model.app (Tm.eraseModel (.tapp t B)) y) := by
  exact fundamental_closed ht Fin.elim0 R x y hxy

/-- **No closed System F term inhabits $\forall X, X$.**
The empty relation rules out every closed inhabitant of `forall X, X`. -/
theorem forall_var_uninhabited (t : Tm 0 0) :
    ¬ Typing Fin.elim0 t (.all (.var 0)) := by
  intro ht
  exact fundamental_closed ht Fin.elim0 Rel.empty

end Cslib.Languages.LambdaCalculus.SystemF
