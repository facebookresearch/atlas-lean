/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RepresentationTheory.AdmissibleRepresentation.Regular

/-! Tests for admissible representations over a regular ring of periods: every field is regular,
the action on the fraction field extends the action on the ring, condition (ii) as an equality of
invariants, the ring of invariants is a field, `D_S(V)` is free and finite-dimensional, Fontaine's
theorem (`α_V` injective, `dim_E D_S(V) ≤ dim_F V`, and the three forms of admissibility agree),
and the trivial representation and the Galois action on a field as examples. -/

open scoped TensorProduct

open Representation

variable {F G S V : Type*} [Field F] [Group G] [CommRing S] [IsDomain S] [Algebra F S]
  [AddCommGroup V] [Module F V]

-- Every field is regular, for every action and every subgroup.
example {L : Type*} [Field L] [Algebra F L] (act : G →* (L →ₐ[F] L)) (H : Subgroup G) :
    IsRegularPeriodRing act H :=
  isRegularPeriodRing_of_isField (Field.toIsField L) act H

-- The action on the fraction field extends `act`, and condition (ii) says that the invariants
-- of `S` are those of its fraction field.
example (act : G →* (S →ₐ[F] S)) (g : G) (s : S) :
    fractionRingAction act g (algebraMap S (FractionRing S) s) =
      algebraMap S (FractionRing S) (act g s) := by
  simp

example {act : G →* (S →ₐ[F] S)} {H : Subgroup G} (hS : IsRegularPeriodRing act H)
    (x : FractionRing S) (hx : ∀ g ∈ H, fractionRingAction act g x = x) :
    ∃ s ∈ fixedSubalgebra S act H, algebraMap S (FractionRing S) s = x := by
  have : x ∈ {x | ∀ g ∈ H, fractionRingAction act g x = x} := hx
  rw [← hS.image_fixedSubalgebra] at this
  exact this

-- The ring of invariants is a field, and `D_S(V)` is free and finite-dimensional over it.
example {act : G →* (S →ₐ[F] S)} {H : Subgroup G} (hS : IsRegularPeriodRing act H)
    (b : fixedSubalgebra S act H) (hb : b ≠ 0) : ∃ c, b * c = 1 :=
  hS.isField.mul_inv_cancel hb

example {act : G →* (S →ₐ[F] S)} {H : Subgroup G} (hS : IsRegularPeriodRing act H)
    (ρ : Representation F G V) [FiniteDimensional F V] :
    Module.Free (fixedSubalgebra S act H) (ρ.periods act H) ∧
      Module.Finite (fixedSubalgebra S act H) (ρ.periods act H) :=
  ⟨hS.free_periods ρ, hS.finite_periods ρ⟩

-- Condition (ii) without fractions.
example {act : G →* (S →ₐ[F] S)} {H : Subgroup G} (hS : IsRegularPeriodRing act H) {a s : S}
    (hs : s ≠ 0) (h : ∀ g ∈ H, act g a * s = a * act g s) :
    ∃ e ∈ fixedSubalgebra S act H, a = e * s :=
  hS.exists_mem_fixedSubalgebra_eq_mul hs h

-- Fontaine's theorem: `α_V` is injective and `dim_E D_S(V) ≤ dim_F V`, with equality exactly when
-- `α_V` is an isomorphism, and exactly when `S ⊗_F V` has a basis of fixed vectors.
example {act : G →* (S →ₐ[F] S)} {H : Subgroup G} (hS : IsRegularPeriodRing act H)
    (ρ : Representation F G V) [FiniteDimensional F V] :
    Function.Injective (ρ.comparison act H) ∧
      Module.finrank (fixedSubalgebra S act H) (ρ.periods act H) ≤ Module.finrank F V ∧
      (ρ.IsAdmissible act H ↔ Function.Bijective (ρ.comparison act H)) ∧
      (ρ.IsAdmissible act H ↔ ρ.HasFixedBasis act H) :=
  ⟨hS.comparison_injective ρ, hS.finrank_periods_le ρ,
    hS.isAdmissible_iff_comparison_bijective ρ, hS.isAdmissible_iff_hasFixedBasis ρ⟩

-- Equality in `dim_E D_S(V) ≤ dim_F V` holds exactly when `α_V` is an isomorphism.
example {act : G →* (S →ₐ[F] S)} {H : Subgroup G} (hS : IsRegularPeriodRing act H)
    (ρ : Representation F G V) [FiniteDimensional F V] :
    Module.finrank (fixedSubalgebra S act H) (ρ.periods act H) = Module.finrank F V ↔
      Function.Bijective (ρ.comparison act H) :=
  hS.finrank_periods_eq_iff ρ

-- `E`-linearly independent vectors of `D_S(V)` are `S`-linearly independent.
example {act : G →* (S →ₐ[F] S)} {H : Subgroup G} (hS : IsRegularPeriodRing act H)
    (ρ : Representation F G V) {ι : Type*} {v : ι → ρ.periods act H}
    (hv : LinearIndependent (fixedSubalgebra S act H) v) :
    LinearIndependent S fun i => (v i : S ⊗[F] V) :=
  hS.linearIndependent ρ hv

-- The trivial representation is admissible for every regular ring, so `α_V` is an isomorphism
-- for it.
example {act : G →* (S →ₐ[F] S)} {H : Subgroup G} (hS : IsRegularPeriodRing act H)
    [FiniteDimensional F V] : Function.Bijective ((trivial F G V).comparison act H) :=
  (hS.isAdmissible_iff_comparison_bijective _).1 (HasFixedBasis.isAdmissible
    ⟨_, Algebra.TensorProduct.basis S (Module.finBasis F V), fun i g _ => by
      rw [Algebra.TensorProduct.basis_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        map_one, trivial_apply]⟩)

-- The Galois group of a field extension acting on the larger field: a regular ring, so for every
-- representation the comparison map is injective.
example {K L W : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup W] [Module K W]
    (H : Subgroup (L ≃ₐ[K] L)) (ρ : Representation K (L ≃ₐ[K] L) W) :
    Function.Injective (ρ.comparison
      ((Units.coeHom _).comp ((AlgEquiv.algHomUnitsEquiv K L).symm.toMonoidHom)) H) :=
  (isRegularPeriodRing_of_isField (Field.toIsField L) _ H).comparison_injective ρ
