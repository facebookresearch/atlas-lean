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

private theorem algebraMap_eq_one_of_isIdempotentElem {e : H} (he : IsIdempotentElem e)
    (L : Type*) [CommRing L] [Algebra H L] [IsLocalization.Away e L] :
    algebraMap H L e = 1 := by
  have hu : IsUnit (algebraMap H L e) := IsLocalization.Away.algebraMap_isUnit e
  apply hu.mul_left_cancel
  rw [← map_mul, he.eq, mul_one]

private theorem algebraMap_surjective_of_isIdempotentElem {e : H} (he : IsIdempotentElem e)
    (L : Type*) [CommRing L] [Algebra H L] [IsLocalization.Away e L] :
    Function.Surjective (algebraMap H L) := by
  intro x
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers e) x
  refine ⟨r, ?_⟩
  obtain ⟨n, hn⟩ := s.2
  symm
  rw [IsLocalization.mk'_eq_iff_eq_mul, ← hn, map_pow,
    algebraMap_eq_one_of_isIdempotentElem he L, one_pow, mul_one]

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
    obtain ⟨h, rfl⟩ := algebraMap_surjective_of_isIdempotentElem hg L x
    exact ⟨algebraMap H _ h, hφe h⟩
  haveI : Module.Finite R L := Module.Finite.of_surjective ψ hψ
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
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) ⊤
      Module.Finite.fg_top htop (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  haveI : Subsingleton L := by
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

private noncomputable def awayMapAlong (φ : H →ₐ[R] H') (g : H) :
    Localization.Away g →+* Localization.Away (φ g) :=
  IsLocalization.Away.lift g
    (g := ((algebraMap H' (Localization.Away (φ g))).comp (φ : H →+* H')))
    (by
      rw [RingHom.comp_apply]
      exact IsLocalization.Away.algebraMap_isUnit (φ g))

private theorem awayMapAlong_algebraMap (φ : H →ₐ[R] H') (g : H) (h : H) :
    awayMapAlong φ g (algebraMap H _ h) = algebraMap H' _ (φ h) :=
  IsLocalization.Away.lift_eq g _ h

private theorem awayMapAlong_algebraMap_base (φ : H →ₐ[R] H') (g : H) (r : R) :
    awayMapAlong φ g (algebraMap R _ r) = algebraMap R _ r := by
  rw [IsScalarTower.algebraMap_apply R H (Localization.Away g), awayMapAlong_algebraMap,
    AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

private theorem finite_away_map (φ : H →ₐ[R] H') (hφ : Function.Surjective φ) {g : H}
    (hg : IsIdempotentElem g) (hfin : Module.Finite R (Localization.Away g)) :
    Module.Finite R (Localization.Away (φ g)) := by
  let ψ : Localization.Away g →ₗ[R] Localization.Away (φ g) :=
    { toFun := awayMapAlong φ g
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => by
        simp only [Algebra.smul_def, map_mul, awayMapAlong_algebraMap_base, RingHom.id_apply] }
  refine Module.Finite.of_surjective ψ fun x => ?_
  obtain ⟨h', rfl⟩ :=
    algebraMap_surjective_of_isIdempotentElem (hg.map φ) (Localization.Away (φ g)) x
  obtain ⟨h, rfl⟩ := hφ h'
  exact ⟨algebraMap H _ h, awayMapAlong_algebraMap φ g h⟩

private theorem map_maximalIdeal_away_map [IsLocalRing R] (φ : H →ₐ[R] H') (g : H)
    (hgen : Ideal.map (algebraMap R (Localization.Away g)) (IsLocalRing.maximalIdeal R) = ⊤) :
    Ideal.map (algebraMap R (Localization.Away (φ g))) (IsLocalRing.maximalIdeal R) = ⊤ := by
  have h1 : Ideal.map (awayMapAlong φ g) (Ideal.map (algebraMap R (Localization.Away g))
      (IsLocalRing.maximalIdeal R)) = ⊤ := by
    rw [hgen, Ideal.map_top]
  rwa [Ideal.map_map, show (awayMapAlong φ g).comp (algebraMap R (Localization.Away g))
      = algebraMap R (Localization.Away (φ g)) from
    RingHom.ext (awayMapAlong_algebraMap_base φ g)] at h1

end MapAlong

end HopfFinitePartAux

/-- An idempotent of a commutative Hopf algebra over a local ring is fixed by
the antipode when localizing away from it is finite over the base and
localizing away from its complement kills the maximal ideal. -/
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
    HopfFinitePartAux.finite_away_map S hS he hfin
  have h2 : Ideal.map (algebraMap R (Localization.Away (1 - S e)))
      (IsLocalRing.maximalIdeal R) = ⊤ := by
    have h := HopfFinitePartAux.map_maximalIdeal_away_map S (1 - e) hgen
    rwa [map_sub, map_one] at h
  have h3 : S e = e :=
    HopfFinitePartAux.finitePartIdempotent_unique _ _ (he.map S) he h1 hfin h2 hgen
  exact h3
