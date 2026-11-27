/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RepresentationTheory.AdmissibleRepresentation.Descent
import Mathlib.FieldTheory.Galois.Basic

/-! Tests for Galois descent of admissibility along a normal subgroup `H'` of finite index of `H`:
linear independence, spanning, bases and dimensions of `D_S(V)`, the base change isomorphism, the
three forms of admissibility, and the Galois group of a finite Galois extension acting on the
larger field, where every hypothesis holds for `H = ⊤` and `H' = ⊥`. -/

open scoped TensorProduct

open Representation

variable {F G S V : Type*} [Field F] [Group G] [CommRing S] [Algebra F S] [AddCommGroup V]
  [Module F V]

-- `S^H ⊆ S^{H'}` and `D_{S,H}(V) ⊆ D_{S,H'}(V)` for `H' ≤ H`, and `S^H` is a field with
-- `S^{H'}`.
example (act : G →* (S →ₐ[F] S)) (ρ : Representation F G V) {H H' : Subgroup G} (h : H' ≤ H)
    (hL : IsField (fixedSubalgebra S act H')) :
    fixedSubalgebra S act H ≤ fixedSubalgebra S act H' ∧
      (ρ.periods act H : Set (S ⊗[F] V)) ⊆ ρ.periods act H' ∧
      IsField (fixedSubalgebra S act H) :=
  ⟨fixedSubalgebra_antitone act h, periods_subset_periods ρ act h,
    isField_fixedSubalgebra_of_le h hL⟩

section Descent

variable {act : G →* (S →ₐ[F] S)} {H H' : Subgroup G} (ρ : Representation F G V)
  (hle : H' ≤ H) (hN : (H'.subgroupOf H).Normal) [(H'.subgroupOf H).FiniteIndex]
  (hL : IsField (fixedSubalgebra S act H'))
  (hfaithful : ∀ h ∈ H, (∀ x ∈ fixedSubalgebra S act H', act h x = x) → h ∈ H')
include hle hN hL hfaithful

-- `D_{S,H}(V)` spans `D_{S,H'}(V)` over `S^{H'}`, and the dimensions agree.
example :
    Submodule.span (fixedSubalgebra S act H') (ρ.periods act H : Set (S ⊗[F] V)) =
        ρ.periods act H' ∧
      Module.finrank (fixedSubalgebra S act H) (ρ.periods act H) =
        Module.finrank (fixedSubalgebra S act H') (ρ.periods act H') :=
  ⟨span_periods_of_normal ρ hle hN hL hfaithful, finrank_periods_eq_of_normal ρ hle hN hL hfaithful⟩

-- An `S^H`-basis of `D_{S,H}(V)` is an `S^{H'}`-basis of `D_{S,H'}(V)`.
example {ι : Type*} (b : Module.Basis ι (fixedSubalgebra S act H) (ρ.periods act H)) (i : ι) :
    (periodsBasisOfNormal ρ hle hN hL hfaithful b i : S ⊗[F] V) = b i := by
  simp

-- `S^{H'} ⊗_{S^H} D_{S,H}(V) ≃ D_{S,H'}(V)`, `a ⊗ x ↦ a • x`.
example (a : fixedSubalgebra S act H') (x : ρ.periods act H) :
    letI := fixedSubalgebraAlgebra act hle
    (periodsBaseChangeEquiv ρ hle hN hL hfaithful (a ⊗ₜ x) : S ⊗[F] V) = (a : S) • (x : S ⊗[F] V) :=
  coe_periodsBaseChangeEquiv_tmul ρ hle hN hL hfaithful a x

-- Admissibility in the dimension form descends.
example : ρ.IsAdmissible act H ↔ ρ.IsAdmissible act H' :=
  isAdmissible_iff_of_normal ρ hle hN hL hfaithful

end Descent

-- `E`-linearly independent vectors of `D_{S,H}(V)` are `S^{H'}`-linearly independent, using only
-- the normality of `H'` and the field `S^{H'}`.
example {act : G →* (S →ₐ[F] S)} {H H' : Subgroup G} (ρ : Representation F G V) (hle : H' ≤ H)
    (hN : (H'.subgroupOf H).Normal) (hL : IsField (fixedSubalgebra S act H')) {ι : Type*}
    {v : ι → ρ.periods act H} (hv : LinearIndependent (fixedSubalgebra S act H) v) :
    LinearIndependent (fixedSubalgebra S act H') fun i => (v i : S ⊗[F] V) :=
  linearIndependent_periods_of_normal ρ hle hN hL hv

-- For a regular ring, the basis and comparison forms descend too.
example [IsDomain S] {act : G →* (S →ₐ[F] S)} {H H' : Subgroup G}
    (hS : IsRegularPeriodRing act H') (ρ : Representation F G V) [FiniteDimensional F V]
    (hle : H' ≤ H) (hN : (H'.subgroupOf H).Normal) [(H'.subgroupOf H).FiniteIndex]
    (hfaithful : ∀ h ∈ H, (∀ x ∈ fixedSubalgebra S act H', act h x = x) → h ∈ H') :
    IsRegularPeriodRing act H ∧ (ρ.HasFixedBasis act H ↔ ρ.HasFixedBasis act H') ∧
      (Function.Bijective (ρ.comparison act H) ↔ Function.Bijective (ρ.comparison act H')) :=
  ⟨hS.mono hle, hS.hasFixedBasis_iff_of_normal ρ hle hN hfaithful,
    hS.comparison_bijective_iff_of_normal ρ hle hN hfaithful⟩

-- The Galois group of a finite Galois extension `L/K` acting on `L`: for `H = ⊤` and `H' = ⊥`,
-- every hypothesis holds, so admissibility for `Gal(L/K)` is admissibility for the trivial
-- subgroup.
example {K L W : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [AddCommGroup W] [Module K W] (ρ : Representation K (L ≃ₐ[K] L) W) :
    let act : (L ≃ₐ[K] L) →* (L →ₐ[K] L) :=
      (Units.coeHom _).comp ((AlgEquiv.algHomUnitsEquiv K L).symm.toMonoidHom)
    ρ.IsAdmissible act ⊤ ↔ ρ.IsAdmissible act ⊥ := by
  intro act
  have hN : ((⊥ : Subgroup (L ≃ₐ[K] L)).subgroupOf ⊤).Normal := by
    rw [Subgroup.bot_subgroupOf]
    infer_instance
  have : ((⊥ : Subgroup (L ≃ₐ[K] L)).subgroupOf ⊤).FiniteIndex := Subgroup.finiteIndex_of_finite
  have hmem (x : L) : x ∈ fixedSubalgebra L act ⊥ := fun g hg => by
    rw [Subgroup.mem_bot.1 hg, map_one, AlgHom.one_apply]
  have hL : IsField (fixedSubalgebra L act ⊥) :=
    { exists_pair_ne := ⟨0, 1, zero_ne_one⟩
      mul_comm := mul_comm
      mul_inv_cancel := fun {a} ha =>
        ⟨⟨(a : L)⁻¹, hmem _⟩, Subtype.ext (mul_inv_cancel₀ fun h => ha (Subtype.ext h))⟩ }
  refine isAdmissible_iff_of_normal ρ bot_le hN hL fun g _ hg => Subgroup.mem_bot.2 ?_
  exact AlgEquiv.ext fun x => hg x (hmem x)
