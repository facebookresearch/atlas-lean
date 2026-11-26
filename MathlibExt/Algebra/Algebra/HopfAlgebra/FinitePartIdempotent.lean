/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_HopfAlgebra_antipode_finitePartIdempotent.lean`
and
`P2M/Sol/S_HopfAlgebra_antipode_finitePartIdempotent.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.Nakayama
import MathlibExt.Algebra.Algebra.HopfAlgebra.Antipode

@[expose] public section

open scoped TensorProduct

namespace HopfFinitePartAux

section Away

variable {H : Type*} [CommRing H]

private theorem eq_zero_of_subsingleton_away {g : H} (hg : IsIdempotentElem g)
    (L : Type*) [CommRing L] [Algebra H L] [IsLocalization.Away g L] [Subsingleton L] :
    g = 0 := by
  have h : algebraMap H L 1 = algebraMap H L 0 := Subsingleton.elim _ _
  obtain ⟨⟨c, n, rfl⟩, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers g) L).1 h
  simp only [mul_one, mul_zero] at hc
  rcases n with _ | n
  · rw [pow_zero] at hc
    rw [← mul_one g, hc, mul_zero]
  · rw [← hg.pow_succ_eq n, hc]

end Away

section Local

variable {R : Type*} [CommRing R] [IsLocalRing R] {H : Type*} [CommRing H] [Algebra R H]

private theorem mul_eq_zero_of_finite_away_of_map_maximalIdeal_eq_top {e f : H}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hfin : Module.Finite R (Localization.Away e))
    (hgen : Ideal.map (algebraMap R (Localization.Away f)) (IsLocalRing.maximalIdeal R) = ⊤) :
    e * f = 0 := by
  have hg : IsIdempotentElem (e * f) := he.mul hf
  let L := Localization.Away (e * f)
  have hue : IsUnit (algebraMap H L e) := by
    have h := IsLocalization.Away.algebraMap_isUnit (S := L) (e * f)
    rw [map_mul] at h
    exact isUnit_of_mul_isUnit_left h
  have huf : IsUnit (algebraMap H L f) := by
    have h := IsLocalization.Away.algebraMap_isUnit (S := L) (e * f)
    rw [map_mul] at h
    exact isUnit_of_mul_isUnit_right h
  let φe : Localization.Away e →+* L := IsLocalization.Away.lift e hue
  let φf : Localization.Away f →+* L := IsLocalization.Away.lift f huf
  have hφe : ∀ h : H, φe (algebraMap H _ h) = algebraMap H L h :=
    fun h => IsLocalization.Away.lift_eq e hue h
  have hφf : ∀ h : H, φf (algebraMap H _ h) = algebraMap H L h :=
    fun h => IsLocalization.Away.lift_eq f huf h
  have hφeR : ∀ r : R, φe (algebraMap R _ r) = algebraMap R L r := fun r => by
    rw [IsScalarTower.algebraMap_apply R H (Localization.Away e), hφe,
      ← IsScalarTower.algebraMap_apply]
  have hφfR : ∀ r : R, φf (algebraMap R _ r) = algebraMap R L r := fun r => by
    rw [IsScalarTower.algebraMap_apply R H (Localization.Away f), hφf,
      ← IsScalarTower.algebraMap_apply]
  let ψ : Localization.Away e →ₗ[R] L :=
    { toFun := φe
      map_add' := fun x y => map_add φe x y
      map_smul' := fun r x => by
        simp only [Algebra.smul_def, map_mul, hφeR, RingHom.id_apply] }
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨h, rfl⟩ :=
      IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem (S := L) (e * f) hg x
    exact ⟨algebraMap H _ h, hφe h⟩
  have : Module.Finite R L := Module.Finite.of_surjective ψ hψ
  have hgenL : Ideal.map (algebraMap R L) (IsLocalRing.maximalIdeal R) = ⊤ := by
    have h1 : Ideal.map φf (Ideal.map (algebraMap R (Localization.Away f))
        (IsLocalRing.maximalIdeal R)) = ⊤ := by
      rw [hgen, Ideal.map_top]
    rw [Ideal.map_map] at h1
    have h2 : φf.comp (algebraMap R (Localization.Away f)) = algebraMap R L :=
      RingHom.ext hφfR
    rwa [h2] at h1
  have htop : (⊤ : Submodule R L) ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R L) := by
    rw [Ideal.smul_top_eq_map, hgenL]
    intro x _
    trivial
  have hbot : (⊤ : Submodule R L) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson (IsLocalRing.maximalIdeal R) ⊤
      Module.Finite.fg_top htop (IsLocalRing.ringJacobson_eq_maximalIdeal R).ge
  have : Subsingleton L := by
    refine ⟨fun x y => ?_⟩
    have hx : x ∈ (⊤ : Submodule R L) := trivial
    have hy : y ∈ (⊤ : Submodule R L) := trivial
    rw [hbot, Submodule.mem_bot] at hx hy
    rw [hx, hy]
  exact eq_zero_of_subsingleton_away hg L

private theorem finitePartIdempotent_unique (e e' : H) (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e')
    (hfin : Module.Finite R (Localization.Away e))
    (hfin' : Module.Finite R (Localization.Away e'))
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e)))
      (IsLocalRing.maximalIdeal R) = ⊤)
    (hgen' : Ideal.map (algebraMap R (Localization.Away (1 - e')))
      (IsLocalRing.maximalIdeal R) = ⊤) :
    e = e' := by
  have h1 : e * (1 - e') = 0 :=
    mul_eq_zero_of_finite_away_of_map_maximalIdeal_eq_top he he'.one_sub hfin hgen'
  have h2 : e' * (1 - e) = 0 :=
    mul_eq_zero_of_finite_away_of_map_maximalIdeal_eq_top he' he.one_sub hfin' hgen
  have h1' : e = e * e' := by
    have h := h1
    rw [mul_sub, mul_one, sub_eq_zero] at h
    exact h
  have h2' : e' = e' * e := by
    have h := h2
    rw [mul_sub, mul_one, sub_eq_zero] at h
    exact h
  rw [h1', mul_comm, ← h2']

end Local

section MapAlong

variable {R : Type*} [CommRing R] {H H' : Type*} [CommRing H] [CommRing H']
  [Algebra R H] [Algebra R H']

private theorem finite_away_map (φ : H →ₐ[R] H') (hφ : Function.Surjective φ) {g : H}
    (hfin : Module.Finite R (Localization.Away g)) :
    Module.Finite R (Localization.Away (φ g)) :=
  Module.Finite.of_surjective (Localization.awayMapₐ φ g).toLinearMap
    (IsLocalization.Away.mapₐ_surjective_of_surjective g hφ)

private theorem map_maximalIdeal_away_map [IsLocalRing R] (φ : H →ₐ[R] H') (g : H)
    (hgen : Ideal.map (algebraMap R (Localization.Away g)) (IsLocalRing.maximalIdeal R) = ⊤) :
    Ideal.map (algebraMap R (Localization.Away (φ g))) (IsLocalRing.maximalIdeal R) = ⊤ := by
  have h := congrArg
    (Ideal.map (Localization.awayMapₐ φ g : Localization.Away g →+* Localization.Away (φ g))) hgen
  rwa [Ideal.map_top, Ideal.map_map, AlgHom.comp_algebraMap] at h

end MapAlong

end HopfFinitePartAux

/-- **The antipode fixes the finite-part idempotent.** Let `R` be a commutative local ring and
`H` a commutative Hopf algebra over `R`. An idempotent `e : H` is fixed by the antipode when
`Localization.Away e` is a finite `R`-module and the maximal ideal of `R` extends to the unit
ideal of `Localization.Away (1 - e)`: the ideal there generated by its image under `algebraMap`
is `⊤`. -/
theorem HopfAlgebra.antipode_finitePartIdempotent
    (R : Type*) [CommRing R] [IsLocalRing R] (H : Type*) [CommRing H] [HopfAlgebra R H]
    (e : H) (he : IsIdempotentElem e)
    (hfin : Module.Finite R (Localization.Away e))
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e)))
      (IsLocalRing.maximalIdeal R) = ⊤) :
    HopfAlgebra.antipode R e = e := by
  let S : H →ₐ[R] H := HopfAlgebra.antipodeAlgHom R H
  have hS : Function.Surjective S :=
    fun a => ⟨HopfAlgebra.antipode R a, HopfAlgebra.antipode_antipode a⟩
  have h1 : Module.Finite R (Localization.Away (S e)) :=
    HopfFinitePartAux.finite_away_map S hS hfin
  have h2 : Ideal.map (algebraMap R (Localization.Away (1 - S e)))
      (IsLocalRing.maximalIdeal R) = ⊤ := by
    have h := HopfFinitePartAux.map_maximalIdeal_away_map S (1 - e) hgen
    rwa [map_sub, map_one] at h
  have h3 : S e = e :=
    HopfFinitePartAux.finitePartIdempotent_unique _ _ (he.map S) he h1 hfin h2 hgen
  exact h3
