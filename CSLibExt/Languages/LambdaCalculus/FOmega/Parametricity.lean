/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.FOmega.Typing
public import CSLibExt.Languages.LambdaCalculus.FOmega.Closing
public import CSLibExt.Languages.LambdaCalculus.FOmega.RelationalTypes

/-! # Higher-kinded relational parametricity of pure Fω

The fundamental theorem covers all six typing rules, arbitrary values at every
kind, and two independently chosen related term environments. Type conversion
uses proved operator-beta soundness; it is not a semantic or typing assumption.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.FOmega

/-- The full binary higher-kinded fundamental theorem of pure Fω. -/
theorem fundamental {Δ : List Kind} {m : Nat} {Γ : Ctx Δ m}
    {t : Tm Δ m} {A : Ty Δ .star} (ht : Typing Γ t A)
    (ρ : KEnv SystemF.Rel Δ) (σ τ : Fin m → SystemF.Model)
    (hστ : ∀ i, ((Γ i).interpret ρ).holds (σ i) (τ i)) :
    (A.interpret ρ).holds (Tm.close σ t) (Tm.close τ t) := by
  induction ht with
  | var i => exact hστ i
  | app hf ha ihf iha => exact (ihf ρ σ τ hστ) _ _ (iha ρ σ τ hστ)
  | @lam Δ m Γ A B b hb ih =>
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
    apply ih (KEnv.extend ρ R) σ τ
    intro i
    simpa only [Ty.interpret_weaken] using hστ i
  | @tapp Δ m κ Γ f A C hf ih =>
    rw [Ty.interpret_instantiate]
    exact ih ρ σ τ hστ (A.interpret ρ)
  | conv ht hc ih =>
    rw [← hc.interpret ρ]
    exact ih ρ σ τ hστ

/-- Every closed-term typed expression is related to itself at every kind environment. -/
theorem fundamental_closed {Δ : List Kind} {Γ : Ctx Δ 0}
    {t : Tm Δ 0} {A : Ty Δ .star} (ht : Typing Γ t A)
    (ρ : KEnv SystemF.Rel Δ) :
    (A.interpret ρ).holds (Tm.eraseModel t) (Tm.eraseModel t) :=
  fundamental ht ρ Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i)

/-- A genuine higher-kind identity type: `∀ F : * → *, ∀ X : *, F X → F X`. -/
def higherIdType {Δ : List Kind} : Ty Δ .star :=
  .all (κ := .arrow .star .star) (.all (κ := .star)
    (.arr (.app (.var (.succ .zero)) (.var .zero))
      (.app (.var (.succ .zero)) (.var .zero))))

/-- The pure higher-kinded polymorphic identity term. -/
def higherId {Δ : List Kind} {m : Nat} : Tm Δ m :=
  .tabs (κ := .arrow .star .star) (.tabs (κ := .star)
    (.lam (.app (.var (.succ .zero)) (.var .zero)) (.var 0)))

/-- The higher-kinded identity is typed in every existing term context. -/
theorem higherId_typed {Δ : List Kind} {m : Nat} (Γ : Ctx Δ m) :
    Typing Γ higherId higherIdType := .tabs (.tabs (.lam (.var 0)))

private def totalAtKind : (κ : Kind) → Kind.Sem SystemF.Rel κ
  | .star => SystemF.Rel.total
  | .arrow _ μ => fun _ => totalAtKind μ

private def totalEnv {Δ : List Kind} : KEnv SystemF.Rel Δ :=
  fun {κ} _ => totalAtKind κ

/-- Every closed-term inhabitant is beta-identity at every kind-correct instantiation.

The inhabitant is arbitrary, not the manually defined `higherId`. The input
is any locally closed model term; no CBV termination or normalization is claimed.
-/
theorem higher_kinded_identity {Δ : List Kind} {t : Tm Δ 0}
    (ht : Typing Fin.elim0 t higherIdType)
    (F : Ty Δ (.arrow .star .star)) (A : Ty Δ .star) (x : SystemF.Model) :
    SystemF.BetaEq
      (SystemF.Model.app (Tm.eraseModel (.tapp (.tapp t F) A)) x) x := by
  have h := fundamental_closed ht totalEnv
  have hx := h (fun _ => SystemF.Rel.betaClass x) SystemF.Rel.total x x
    ⟨SystemF.BetaEq.refl x, SystemF.BetaEq.refl x⟩
  exact hx.1

/-- Different higher-kind type instantiations preserve every admissible binary relation. -/
theorem higher_kinded_related {Δ : List Kind} {t : Tm Δ 0}
    (ht : Typing Fin.elim0 t higherIdType)
    (F G : Ty Δ (.arrow .star .star)) (A B : Ty Δ .star)
    (Φ : SystemF.Rel → SystemF.Rel) (R : SystemF.Rel)
    {x y : SystemF.Model} (hxy : (Φ R).holds x y) :
    (Φ R).holds
      (SystemF.Model.app (Tm.eraseModel (.tapp (.tapp t F) A)) x)
      (SystemF.Model.app (Tm.eraseModel (.tapp (.tapp t G) B)) y) :=
  fundamental_closed ht totalEnv Φ R x y hxy

/-- The empty relation excludes all closed-term inhabitants of `∀ X : *, X`. -/
theorem forall_var_uninhabited {Δ : List Kind} (t : Tm Δ 0) :
    ¬ Typing Fin.elim0 t (.all (κ := .star) (.var .zero)) := by
  intro ht
  exact fundamental_closed ht totalEnv SystemF.Rel.empty

/-- A constant empty operator excludes `∀ F : * → *, ∀ X : *, F X`. -/
theorem higher_result_uninhabited {Δ : List Kind} (t : Tm Δ 0) :
    ¬ Typing Fin.elim0 t (.all (κ := .arrow .star .star)
      (.all (κ := .star) (.app (.var (.succ .zero)) (.var .zero)))) := by
  intro ht
  exact fundamental_closed ht totalEnv (fun _ => SystemF.Rel.empty)
    SystemF.Rel.total

end Cslib.Languages.LambdaCalculus.FOmega
