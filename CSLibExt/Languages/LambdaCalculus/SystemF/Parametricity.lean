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
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.SystemF

/-- The fundamental binary relational-parametricity theorem of pure System F. -/
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

/-- Every closed typed term is related to itself under arbitrary relations. -/
theorem fundamental_closed {n : Nat} {Γ : Ctx n 0} {t : Tm n 0} {A : Ty n}
    (ht : Typing Γ t A) (ρ : Fin n → Rel) :
    (A.interpret ρ).holds (Tm.eraseModel t) (Tm.eraseModel t) :=
  fundamental ht ρ Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i)

/-- The polymorphic identity type, universally quantified at any type depth. -/
def polyIdType {n : Nat} : Ty n := .all (.arr (.var 0) (.var 0))

/-- The pure polymorphic identity term. -/
def polyId {n m : Nat} : Tm n m := .tabs (.lam (.var 0) (.var 0))

/-- The polymorphic identity is well typed in any existing term context. -/
theorem polyId_typed {n m : Nat} (Γ : Ctx n m) :
    Typing Γ polyId polyIdType := .tabs (.lam (.var 0))

/-- Every closed inhabitant acts as identity after every type instantiation.

The conclusion is full-beta conversion in the existing erased term model,
for an arbitrary locally closed input. It makes no CBV termination claim.
-/
theorem polymorphic_identity {t : Tm 0 0}
    (ht : Typing Fin.elim0 t polyIdType) (A : Ty 0) (x : Model) :
    BetaEq (Model.app (Tm.eraseModel (.tapp t A)) x) x := by
  have h := fundamental_closed ht Fin.elim0
  have hx := h (Rel.betaClass x) x x ⟨BetaEq.refl x, BetaEq.refl x⟩
  exact hx.1

/-- Type instantiations preserve every admissible binary input relation. -/
theorem polymorphic_related {t : Tm 0 0}
    (ht : Typing Fin.elim0 t polyIdType) (A B : Ty 0) (R : Rel)
    {x y : Model} (hxy : R.holds x y) :
    R.holds (Model.app (Tm.eraseModel (.tapp t A)) x)
      (Model.app (Tm.eraseModel (.tapp t B)) y) := by
  exact fundamental_closed ht Fin.elim0 R x y hxy

/-- The empty relation rules out every closed inhabitant of `forall X, X`. -/
theorem forall_var_uninhabited (t : Tm 0 0) :
    ¬ Typing Fin.elim0 t (.all (.var 0)) := by
  intro ht
  exact fundamental_closed ht Fin.elim0 Rel.empty

end Cslib.Languages.LambdaCalculus.SystemF
