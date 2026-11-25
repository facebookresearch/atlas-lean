/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from the following files
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
the theorem files `Theorems/Thm_<Y>.lean` and solution files `P2M/Sol/S_<Y>.lean`
for `<Y>` in the list below, where `CF_` abbreviates `CerednikDrinfeld_FormalOmega_`:
`CF_DeligneDatum_exists_latticeMap_scalarGL_eq_or_of_vertexNondegAt_of_edgeNondegAt`
`CF_DeligneDatum_exists_latticeMap_scalarGL_eq_of_edgeNondegAt_of_edgeNondegAt`
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.AlgebraicGeometry.FormalOmega.LatticeStd

/-!
# Homothety helpers for edge nondegeneracy uniqueness

Lattice scaling lemmas (powers of a uniformizer acting on full lattices of `K²`) used in
`MathlibExt.AlgebraicGeometry.FormalOmega.EdgeNondegUnique`.
-/

@[expose] public section

noncomputable section

open scoped Matrix
open LT.LatticeTree

namespace CerednikDrinfeld.FormalOmega.EdgeNondegUnique

section Scaling

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]

/-- A homothety image `c • L` lies in `L'` iff every `c • w` with `w ∈ L` does. -/
theorem sc_le_iff (c : Kˣ) (L L' : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL c) L ≤ L' ↔ ∀ w ∈ L, (c : K) • w ∈ L' := by
  constructor
  · intro h w hw
    exact h (mem_latticeMap_scalarGL.mpr ⟨w, hw, rfl⟩)
  · intro h v hv
    obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.mp hv
    exact h w hw

/-- Lattices are stable under scaling by elements of the base ring. -/
theorem algebraMap_smul_mem (L : Submodule R (Fin 2 → K)) (r : R) {w : Fin 2 → K}
    (hw : w ∈ L) : algebraMap R K r • w ∈ L := by
  rw [algebraMap_smul]
  exact L.smul_mem r hw

/-- Composing two homotheties multiplies their scalars. -/
theorem sc_sc (c d : Kˣ) (L : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL c) (latticeMap (scalarGL d) L) = latticeMap (scalarGL (c * d)) L := by
  rw [scalarGL_mul, latticeMap_mul]

variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] {ϖ : R}

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The image in the fraction field of a nonzero element is nonzero. -/
theorem alg_ne_zero {x : R} (hx : x ≠ 0) : algebraMap R K x ≠ 0 :=
  fun h => hx (IsFractionRing.injective R K (by rw [h, map_zero]))

/-- The uniformizer `ϖ` viewed as a unit of the fraction field. -/
abbrev piU (hϖ : Irreducible ϖ) : Kˣ := unitOfNeZero (K := K) hϖ.ne_zero

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The value of `piU` is the image of the uniformizer. -/
theorem piU_coe (hϖ : Irreducible ϖ) :
    ((piU (K := K) hϖ : Kˣ) : K) = algebraMap R K ϖ := rfl

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The value of a power of `piU` is the image of the power of the uniformizer. -/
theorem piU_pow_coe (hϖ : Irreducible ϖ) (n : ℕ) :
    ((piU (K := K) hϖ ^ n : Kˣ) : K) = algebraMap R K (ϖ ^ n) := by
  rw [Units.val_pow_eq_pow_val, piU_coe, map_pow]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- Lattices are stable under scaling by powers of the uniformizer. -/
theorem pow_smul_mem (hϖ : Irreducible ϖ) (L : Submodule R (Fin 2 → K)) (n : ℕ)
    {w : Fin 2 → K} (hw : w ∈ L) : ((piU (K := K) hϖ ^ n : Kˣ) : K) • w ∈ L := by
  rw [piU_pow_coe]
  exact algebraMap_smul_mem L _ hw

/-- Some power of the uniformizer scales a given vector into a full lattice. -/
theorem exists_pow_smul_mem (hϖ : Irreducible ϖ) {L : Submodule R (Fin 2 → K)}
    (hL : Submodule.IsFullLattice K L) (v : Fin 2 → K) :
    ∃ n : ℕ, ((piU (K := K) hϖ ^ n : Kˣ) : K) • v ∈ L := by
  have hv : v ∈ Submodule.span K (L : Set (Fin 2 → K)) := by
    rw [hL.span_eq_top]
    exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by rwa [pow_zero, Units.val_one, one_smul]⟩
  | zero => exact ⟨0, by rw [smul_zero]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
      obtain ⟨m, hm⟩ := hx
      obtain ⟨n, hn⟩ := hy
      refine ⟨m + n, ?_⟩
      rw [smul_add]
      refine L.add_mem ?_ ?_
      · rw [add_comm, pow_add, Units.val_mul, mul_smul]
        exact pow_smul_mem hϖ L n hm
      · rw [pow_add, Units.val_mul, mul_smul]
        exact pow_smul_mem hϖ L m hn
  | smul c x _ hx =>
      obtain ⟨n, hn⟩ := hx
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) c
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      obtain ⟨e, u, hbu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
      refine ⟨e + n, ?_⟩
      have hπ : algebraMap R K ϖ ≠ 0 := alg_ne_zero hϖ.ne_zero
      have hu : algebraMap R K u ≠ 0 := alg_ne_zero u.ne_zero
      have key : ((piU (K := K) hϖ ^ (e + n) : Kˣ) : K) *
          (algebraMap R K a / algebraMap R K b) =
          algebraMap R K (a * ↑u⁻¹) * ((piU (K := K) hϖ ^ n : Kˣ) : K) := by
        rw [hbu, piU_pow_coe, piU_pow_coe, map_mul, map_mul, map_pow, map_pow, map_pow,
          map_units_inv, pow_add]
        field_simp
      rw [smul_smul, key, mul_smul, algebraMap_smul]
      exact L.smul_mem _ hn

/-- Some power of the uniformizer scales a full lattice `M` into a full lattice `L`. -/
theorem exists_sc_pow_le (hϖ : Irreducible ϖ) {L M : Submodule R (Fin 2 → K)}
    (hL : Submodule.IsFullLattice K L) (hM : Submodule.IsFullLattice K M) :
    ∃ n : ℕ, latticeMap (scalarGL (piU (K := K) hϖ ^ n)) M ≤ L := by
  obtain ⟨s, hs⟩ := Submodule.IsLattice.fg K M
  choose f hf using fun v : Fin 2 → K => exists_pow_smul_mem hϖ hL v
  refine ⟨s.sup f, (sc_le_iff _ _ _).2 ?_⟩
  rw [← hs]
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
      have hle : f x ≤ s.sup f := Finset.le_sup (Finset.mem_coe.mp hx)
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      rw [hk, add_comm, pow_add, Units.val_mul, mul_smul]
      exact pow_smul_mem hϖ L k (hf x)
  | zero =>
      rw [smul_zero]
      exact L.zero_mem
  | add x y _ _ hx hy =>
      rw [smul_add]
      exact L.add_mem hx hy
  | smul r x _ hx =>
      rw [smul_comm]
      exact L.smul_mem r hx

/-- An element divisible by every power of the uniformizer is zero. -/
theorem eq_zero_of_forall_pow_dvd (hϖ : Irreducible ϖ) {r : R}
    (h : ∀ n : ℕ, ϖ ^ n ∣ r) : r = 0 := by
  by_contra hr
  obtain ⟨m, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  obtain ⟨s, hs⟩ := h (m + 1)
  have h1 : (w : R) * ϖ ^ m = (ϖ * s) * ϖ ^ m := by
    rw [← hw, hs]; ring
  have h2 : (w : R) = ϖ * s := mul_right_cancel₀ (pow_ne_zero m hϖ.ne_zero) h1
  exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left (h2 ▸ w.isUnit))

/-- A nonzero vector lies outside `ϖ ^ n • M` for some `n`. -/
theorem exists_not_mem_sc_pow (hϖ : Irreducible ϖ) {M : Submodule R (Fin 2 → K)}
    (hM : Submodule.IsFullLattice K M) {v : Fin 2 → K} (hv : v ≠ 0) :
    ∃ n : ℕ, v ∉ latticeMap (scalarGL (piU (K := K) hϖ ^ n)) M := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha⟩ := exists_sc_pow_le hϖ (isFullLattice_stdLattice (R := R) (K := K)) hM
  apply hv
  have hcoord : ∀ (n : ℕ) (i : Fin 2), ∃ r : R, algebraMap R K (ϖ ^ n * r) =
      (((piU (K := K) hϖ ^ a : Kˣ) : K) • v) i := by
    intro n i
    obtain ⟨w, hw, hwv⟩ := mem_latticeMap_scalarGL.mp (hcon n)
    have hw' : ((piU (K := K) hϖ ^ a : Kˣ) : K) • w ∈ stdLattice R K :=
      ha (mem_latticeMap_scalarGL.mpr ⟨w, hw, rfl⟩)
    obtain ⟨r, hr⟩ : IsLocalization.IsInteger R
        ((((piU (K := K) hϖ ^ a : Kˣ) : K) • w) i) := hw' i
    refine ⟨r, ?_⟩
    rw [map_mul, ← piU_pow_coe hϖ, hr, ← hwv]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hzero : ((piU (K := K) hϖ ^ a : Kˣ) : K) • v = 0 := by
    funext i
    obtain ⟨r₀, hr₀⟩ := hcoord 0 i
    rw [pow_zero, one_mul] at hr₀
    have hr : r₀ = 0 := by
      apply eq_zero_of_forall_pow_dvd hϖ
      intro n
      obtain ⟨r, hr⟩ := hcoord n i
      rw [← hr₀] at hr
      exact ⟨r, (IsFractionRing.injective R K hr).symm⟩
    rw [Pi.zero_apply, ← hr₀, hr, map_zero]
  have hu : ((piU (K := K) hϖ ^ a : Kˣ) : K) ≠ 0 := Units.ne_zero _
  exact (smul_eq_zero.mp hzero).resolve_left hu

/-- Some homothety carries `L` into `M` but not into `ϖ • M`. -/
theorem exists_sc_le_not_le (hϖ : Irreducible ϖ) {L M : Submodule R (Fin 2 → K)}
    (hL : Submodule.IsFullLattice K L) (hM : Submodule.IsFullLattice K M) :
    ∃ c : Kˣ, latticeMap (scalarGL c) L ≤ M ∧
      ¬ latticeMap (scalarGL c) L ≤ latticeMap (scalarGL (piU (K := K) hϖ)) M := by
  obtain ⟨a, ha⟩ := exists_sc_pow_le hϖ hM hL
  have hne : ∃ v ∈ latticeMap (scalarGL (piU (K := K) hϖ ^ a)) L, v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hbot : latticeMap (scalarGL (piU (K := K) hϖ ^ a)) L = ⊥ := by
      rw [eq_bot_iff]; intro v hv; rw [Submodule.mem_bot]; exact hcon v hv
    have hfull := IsFullLattice.map hL (scalarGL (piU (K := K) hϖ ^ a))
    have htop := hfull.span_eq_top
    rw [hbot] at htop
    have hbt : (⊤ : Submodule K (Fin 2 → K)) = ⊥ := by
      rw [← htop, Submodule.span_eq_bot]
      intro x hx
      rw [SetLike.mem_coe, Submodule.mem_bot] at hx
      exact hx
    exact top_ne_bot hbt
  obtain ⟨v, hv, hv0⟩ := hne
  obtain ⟨b, hb⟩ := exists_not_mem_sc_pow hϖ hM hv0
  classical
  have hex : ∃ j : ℕ, ¬ latticeMap (scalarGL (piU (K := K) hϖ ^ a)) L ≤
      latticeMap (scalarGL (piU (K := K) hϖ ^ j)) M := ⟨b, fun h => hb (h hv)⟩
  set j := Nat.find hex with hj_def
  have hj : ¬ latticeMap (scalarGL (piU (K := K) hϖ ^ a)) L ≤
      latticeMap (scalarGL (piU (K := K) hϖ ^ j)) M :=
    Nat.find_spec hex
  have hj0 : j ≠ 0 := by
    intro h0
    apply hj
    rw [h0, pow_zero, scalarGL_one, latticeMap_one]
    exact ha
  obtain ⟨i, hi'⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hi : j = i + 1 := hi'
  clear hi'
  have hi' : latticeMap (scalarGL (piU (K := K) hϖ ^ a)) L ≤
      latticeMap (scalarGL (piU (K := K) hϖ ^ i)) M := by
    have := Nat.find_min hex
      (show i < Nat.find hex by rw [← hj_def, hi]; exact Nat.lt_succ_self i)
    push Not at this
    exact this
  refine ⟨(piU (K := K) hϖ ^ i)⁻¹ * piU (K := K) hϖ ^ a, ?_, ?_⟩
  · have h1 := latticeMap_mono (R := R) (scalarGL (piU (K := K) hϖ ^ i)⁻¹) hi'
    rw [sc_sc, sc_sc, inv_mul_cancel, scalarGL_one, latticeMap_one] at h1
    exact h1
  · intro hcon
    apply hj
    have h1 := latticeMap_mono (R := R) (scalarGL (piU (K := K) hϖ ^ i)) hcon
    rw [sc_sc, sc_sc, ← mul_assoc, mul_inv_cancel, one_mul, ← pow_succ, ← hi] at h1
    exact h1

/-- For full lattices `L < M`, some vector of `L` is `ϖ` times a vector of `M` but not `ϖ` times a
vector of `L`. -/
theorem exists_mem_smul_not_mem_smul (hϖ : Irreducible ϖ)
    {L M : Submodule R (Fin 2 → K)} (hL : Submodule.IsFullLattice K L) (hLM : L ≤ M) (hne : L ≠ M) :
    ∃ v ∈ L, (∃ w ∈ M, v = algebraMap R K ϖ • w) ∧
      ¬ ∃ w ∈ L, v = algebraMap R K ϖ • w := by
  classical
  have hex : ∃ m, m ∈ M ∧ m ∉ L := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hLM hcon)
  obtain ⟨m, hmM, hmL⟩ := hex
  have hexn : ∃ n : ℕ, ((piU (K := K) hϖ ^ n : Kˣ) : K) • m ∈ L :=
    exists_pow_smul_mem hϖ hL m
  set n := Nat.find hexn with hn_def
  have hn : ((piU (K := K) hϖ ^ n : Kˣ) : K) • m ∈ L := Nat.find_spec hexn
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0, pow_zero, Units.val_one, one_smul] at hn
    exact hmL hn
  obtain ⟨i, hi'⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hi : n = i + 1 := hi'
  clear hi'
  have hnotin : ((piU (K := K) hϖ ^ i : Kˣ) : K) • m ∉ L := by
    have := Nat.find_min hexn
      (show i < Nat.find hexn by rw [← hn_def, hi]; exact Nat.lt_succ_self i)
    exact this
  refine ⟨((piU (K := K) hϖ ^ n : Kˣ) : K) • m, hn,
    ⟨((piU (K := K) hϖ ^ i : Kˣ) : K) • m, ?_, ?_⟩, ?_⟩
  · rw [piU_pow_coe]
    exact algebraMap_smul_mem M _ hmM
  · rw [hi, pow_succ, Units.val_mul, mul_comm, mul_smul, piU_coe]
  · rintro ⟨w, hw, hw'⟩
    apply hnotin
    have hπ : algebraMap R K ϖ ≠ 0 := alg_ne_zero hϖ.ne_zero
    have : ((piU (K := K) hϖ ^ i : Kˣ) : K) • m = w := by
      apply smul_right_injective (Fin 2 → K) hπ
      change algebraMap R K ϖ • (((piU (K := K) hϖ ^ i : Kˣ) : K) • m) = algebraMap R K ϖ • w
      rw [← hw', smul_smul, ← piU_coe hϖ, ← Units.val_mul, ← pow_succ', hi]
    rw [this]
    exact hw

end Scaling

end CerednikDrinfeld.FormalOmega.EdgeNondegUnique

end
