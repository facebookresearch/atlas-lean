/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from https://github.com/anthropics/fermats-last-theorem, compared with the
source files at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`:
`Definitions/Def_LatticeTreeOrbital.lean`
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.AlgebraicGeometry.FormalOmega.LatticeVertex
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Tactic.LinearCombination

/-!
# Neighbours of the standard lattice

The proper nonzero subspaces of a two-dimensional vector space are the points of its projective
line, so over a finite field `k` there are `|k| + 1` of them. For `ϖ, c, d ∈ R`, the submodule
`LT.LatticeTree.interLattice R K ϖ c d` consists of the vectors `v` with integral coordinates and
`d v₀ - c v₁ ∈ ϖ R`; for arbitrary `(c, d)` it need not be a lattice.
`LT.LatticeTree.neighborOfOption` indexes the normalized pairs by `Option (R ⧸ (ϖ))`, with `none`
for `(c, d) = (0, 1)` and `some a` for `(1, a)`; this index type is the projective line over
`R ⧸ (ϖ)` when that ring is a field. When `K` is the fraction field of `R` and `ϖ` is irreducible,
each submodule of this normalized family lies strictly between `ϖ R²` and `R²`, and the indexing
is injective.
-/

@[expose] public section

noncomputable section

open scoped Matrix

open Module
open scoped LinearAlgebra.Projectivization

namespace Submodule

section ResiduePlane

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- In a two-dimensional vector space, the proper nonzero subspaces are the lines. -/
theorem ne_bot_and_ne_top_iff_finrank_eq_one [FiniteDimensional k V]
    (hV : finrank k V = 2) (W : Submodule k V) :
    (W ≠ ⊥ ∧ W ≠ ⊤) ↔ finrank k W = 1 := by
  have hle : finrank k W ≤ 2 := hV ▸ W.finrank_le
  constructor
  · rintro ⟨hbot, htop⟩
    have h0 : finrank k W ≠ 0 := fun h => hbot (Submodule.finrank_eq_zero.mp h)
    have h2 : finrank k W ≠ 2 := fun h => htop (Submodule.eq_top_of_finrank_eq (h.trans hV.symm))
    omega
  · intro h1
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h, finrank_bot] at h1; exact absurd h1 (by norm_num)
    · rw [h, finrank_top, hV] at h1; exact absurd h1 (by norm_num)

/-- In a two-dimensional vector space, proper nonzero subspaces correspond to points of the
projective line. -/
noncomputable def neBotNeTopEquivProjectivization [FiniteDimensional k V]
    (hV : finrank k V = 2) :
    {W : Submodule k V // W ≠ ⊥ ∧ W ≠ ⊤} ≃ ℙ k V :=
  (Equiv.subtypeEquivRight (ne_bot_and_ne_top_iff_finrank_eq_one hV)).trans
    (Projectivization.equivSubmodule k V).symm

/-- A two-dimensional vector space over a finite field `k` has `|k| + 1` proper nonzero subspaces.
-/
theorem card_ne_bot_ne_top_of_finrank_two [Finite k] [FiniteDimensional k V]
    (hV : finrank k V = 2) :
    Nat.card {W : Submodule k V // W ≠ ⊥ ∧ W ≠ ⊤} = Nat.card k + 1 :=
  (Nat.card_congr (neBotNeTopEquivProjectivization hV)).trans
    (Projectivization.card_of_finrank_two k V hV)

end ResiduePlane

end Submodule

namespace IsLocalization

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]

theorem isInteger_neg {a : S} (ha : IsInteger R a) : IsInteger R (-a) := by
  obtain ⟨a', rfl⟩ := ha
  exact ⟨-a', map_neg _ _⟩

theorem isInteger_sub {a b : S} (ha : IsInteger R a) (hb : IsInteger R b) :
    IsInteger R (a - b) := by
  rw [sub_eq_add_neg]
  exact isInteger_add ha (isInteger_neg hb)

end IsLocalization

namespace LT.LatticeTree

attribute [local simp] mem_stdLattice latticeMap_one

section NeighbourFamily

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

variable (R K) in
/-- The `R`-submodule of the vectors `v ∈ K²` with integral coordinates and `d v₀ - c v₁ ∈ ϖ R`.
When `K` is the fraction field of `R`, `ϖ ≠ 0` and `ϖ` does not divide both `c` and `d`, it lies
strictly between `ϖ R²` and `R²`. -/
def interLattice (ϖ c d : R) : Submodule R (Fin 2 → K) where
  carrier := {v | (∀ i, IsLocalization.IsInteger R (v i)) ∧
    ∃ w : K, IsLocalization.IsInteger R w ∧
      algebraMap R K d * v 0 - algebraMap R K c * v 1 = algebraMap R K ϖ * w}
  add_mem' := by
    rintro v u ⟨hv, wv, hwv, hv'⟩ ⟨hu, wu, hwu, hu'⟩
    refine ⟨fun i => IsLocalization.isInteger_add (hv i) (hu i),
      wv + wu, IsLocalization.isInteger_add hwv hwu, ?_⟩
    simp only [Pi.add_apply]
    linear_combination hv' + hu'
  zero_mem' := by
    refine ⟨fun _ => IsLocalization.isInteger_zero, 0, IsLocalization.isInteger_zero, ?_⟩
    simp
  smul_mem' := by
    rintro r v ⟨hv, w, hw, hv'⟩
    refine ⟨fun i => by rw [Pi.smul_apply]; exact IsLocalization.isInteger_smul (hv i),
      r • w, IsLocalization.isInteger_smul hw, ?_⟩
    simp only [Pi.smul_apply, Algebra.smul_def]
    linear_combination algebraMap R K r * hv'

theorem mem_interLattice {ϖ c d : R} {v : Fin 2 → K} :
    v ∈ interLattice R K ϖ c d ↔
      (∀ i, IsLocalization.IsInteger R (v i)) ∧
        ∃ w : K, IsLocalization.IsInteger R w ∧
          algebraMap R K d * v 0 - algebraMap R K c * v 1 = algebraMap R K ϖ * w :=
  Iff.rfl

theorem interLattice_le_stdLattice (ϖ c d : R) :
    interLattice R K ϖ c d ≤ stdLattice R K :=
  fun _ hv => hv.1

variable (R K) in
/-- The vector `(c, d) ∈ K²` of a pair of elements of `R`. -/
def vecPair (c d : R) : Fin 2 → K := ![algebraMap R K c, algebraMap R K d]

@[simp] theorem vecPair_zero (c d : R) : vecPair R K c d 0 = algebraMap R K c := rfl

@[simp] theorem vecPair_one (c d : R) : vecPair R K c d 1 = algebraMap R K d := rfl

theorem vecPair_mem_stdLattice (c d : R) : vecPair R K c d ∈ stdLattice R K := by
  intro i
  fin_cases i
  · exact ⟨c, rfl⟩
  · exact ⟨d, rfl⟩

theorem vecPair_mem_interLattice (ϖ c d : R) :
    vecPair R K c d ∈ interLattice R K ϖ c d := by
  refine ⟨vecPair_mem_stdLattice c d, 0, IsLocalization.isInteger_zero, ?_⟩
  simp [mul_comm]

variable [IsFractionRing R K]

theorem exists_isInteger_eq_algebraMap_mul_iff_dvd {ϖ x : R} :
    (∃ w : K, IsLocalization.IsInteger R w ∧ algebraMap R K x = algebraMap R K ϖ * w) ↔
      ϖ ∣ x := by
  constructor
  · rintro ⟨w, ⟨w', rfl⟩, hw⟩
    rw [← map_mul] at hw
    exact ⟨w', IsFractionRing.injective R K hw⟩
  · rintro ⟨y, rfl⟩
    exact ⟨algebraMap R K y, ⟨y, rfl⟩, by rw [map_mul]⟩

theorem vecPair_mem_interLattice_iff_dvd {ϖ c d x y : R} :
    vecPair R K x y ∈ interLattice R K ϖ c d ↔ ϖ ∣ d * x - c * y := by
  rw [mem_interLattice]
  constructor
  · rintro ⟨-, w, hw, hweq⟩
    refine exists_isInteger_eq_algebraMap_mul_iff_dvd.mp ⟨w, hw, ?_⟩
    rw [map_sub, map_mul, map_mul, ← vecPair_zero (K := K) x y, ← vecPair_one (K := K) x y]
    exact hweq
  · intro hdvd
    obtain ⟨w, hw, hweq⟩ := exists_isInteger_eq_algebraMap_mul_iff_dvd (K := K).mpr hdvd
    refine ⟨vecPair_mem_stdLattice x y, w, hw, ?_⟩
    rw [vecPair_zero, vecPair_one, ← hweq, map_sub, map_mul, map_mul]

theorem dvd_of_interLattice_eq {ϖ c d c' d' : R}
    (h : interLattice R K ϖ c d = interLattice R K ϖ c' d') :
    ϖ ∣ d' * c - c' * d := by
  have hmem := vecPair_mem_interLattice (R := R) (K := K) ϖ c d
  rw [h, vecPair_mem_interLattice_iff_dvd] at hmem
  exact hmem

omit [IsFractionRing R K] in
theorem interLattice_one_eq_of_dvd_sub {ϖ a a' : R} (h : ϖ ∣ a - a') :
    interLattice R K ϖ 1 a = interLattice R K ϖ 1 a' := by
  have key : ∀ {b b' : R}, ϖ ∣ b - b' →
      interLattice R K ϖ 1 b ≤ interLattice R K ϖ 1 b' := by
    rintro b b' ⟨y, hy⟩ v ⟨hv, w, hw, hweq⟩
    obtain ⟨r, hr⟩ := hv 0
    refine ⟨hv, w - algebraMap R K (y * r), IsLocalization.isInteger_sub hw ⟨y * r, rfl⟩, ?_⟩
    have hb : algebraMap R K b' =
        algebraMap R K b - algebraMap R K ϖ * algebraMap R K y := by
      rw [← map_mul, ← map_sub]
      exact congrArg _ (by linear_combination -hy)
    rw [hb]
    simp only [map_mul, map_one, one_mul] at hweq ⊢
    linear_combination hweq + algebraMap R K ϖ * algebraMap R K y * hr
  exact le_antisymm (key h) (key (dvd_sub_comm.mp h))

theorem latticeMap_scalarGL_le_interLattice {ϖ : R} (hϖ : ϖ ≠ 0) (c d : R) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) ≤
      interLattice R K ϖ c d := by
  intro v hv
  rw [mem_latticeMap_scalarGL_stdLattice hϖ] at hv
  choose w hw hw' using hv
  refine ⟨fun i => by rw [← hw' i]; exact IsLocalization.isInteger_mul ⟨ϖ, rfl⟩ (hw i),
    algebraMap R K d * w 0 - algebraMap R K c * w 1,
    IsLocalization.isInteger_sub (IsLocalization.isInteger_mul ⟨d, rfl⟩ (hw 0))
      (IsLocalization.isInteger_mul ⟨c, rfl⟩ (hw 1)),
    by rw [← hw' 0, ← hw' 1]; ring⟩

theorem dvd_of_vecPair_mem_latticeMap_scalarGL {ϖ : R} (hϖ : ϖ ≠ 0) {x y : R}
    (h : vecPair R K x y ∈
      latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K)) :
    ϖ ∣ x ∧ ϖ ∣ y := by
  rw [mem_latticeMap_scalarGL_stdLattice hϖ] at h
  obtain ⟨w0, hw0, hw0'⟩ := h 0
  obtain ⟨w1, hw1, hw1'⟩ := h 1
  rw [vecPair_zero] at hw0'
  rw [vecPair_one] at hw1'
  exact ⟨exists_isInteger_eq_algebraMap_mul_iff_dvd.mp ⟨w0, hw0, hw0'.symm⟩,
    exists_isInteger_eq_algebraMap_mul_iff_dvd.mp ⟨w1, hw1, hw1'.symm⟩⟩

/-- When `K` is the fraction field of `R`, `ϖ ≠ 0` and `ϖ` does not divide both `c` and `d`, the
submodule `interLattice ϖ c d` strictly contains `ϖ R²`. -/
theorem latticeMap_scalarGL_lt_interLattice {ϖ : R} (hϖ : ϖ ≠ 0) {c d : R}
    (hcd : ¬(ϖ ∣ c ∧ ϖ ∣ d)) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) <
      interLattice R K ϖ c d := by
  refine lt_of_le_of_ne (latticeMap_scalarGL_le_interLattice hϖ c d) (fun h => hcd ?_)
  exact dvd_of_vecPair_mem_latticeMap_scalarGL hϖ
    (h ▸ vecPair_mem_interLattice (R := R) (K := K) ϖ c d)

/-- When `K` is the fraction field of `R` and `ϖ` does not divide both `c` and `d`, the submodule
`interLattice ϖ c d` is properly contained in `R²`. -/
theorem interLattice_lt_stdLattice {ϖ : R} {c d : R} (hcd : ¬(ϖ ∣ c ∧ ϖ ∣ d)) :
    interLattice R K ϖ c d < stdLattice R K := by
  rw [lt_iff_le_and_ne]
  refine ⟨interLattice_le_stdLattice ϖ c d, fun h => ?_⟩
  rcases not_and_or.mp hcd with hc | hd
  · have he : vecPair R K 0 1 ∈ stdLattice R K := vecPair_mem_stdLattice 0 1
    rw [← h, vecPair_mem_interLattice_iff_dvd] at he
    rw [mul_zero, mul_one, zero_sub] at he
    exact hc (dvd_neg.mp he)
  · have he : vecPair R K 1 0 ∈ stdLattice R K := vecPair_mem_stdLattice 1 0
    rw [← h, vecPair_mem_interLattice_iff_dvd] at he
    rw [mul_zero, mul_one, sub_zero] at he
    exact hd he

variable (R K) in
/-- The submodules `interLattice R K ϖ c d` of the normalized pairs, indexed by `Option (R ⧸ (ϖ))`:
`none` gives `(c, d) = (0, 1)` and `some a` gives `(1, a')` for the chosen representative `a'` of
`a`. The index type is the projective line over `R ⧸ (ϖ)` when that ring is a field. -/
noncomputable def neighborOfOption (ϖ : R) (x : Option (R ⧸ Ideal.span {ϖ})) :
    Submodule R (Fin 2 → K) :=
  x.elim (interLattice R K ϖ 0 1) (fun y => interLattice R K ϖ 1 y.out)

/-- When `K` is the fraction field of `R` and `ϖ` is irreducible, each `neighborOfOption ϖ x` lies
strictly between `ϖ R²` and `R²`. -/
theorem neighborOfOption_mem_interval {ϖ : R} (hϖ : Irreducible ϖ)
    (x : Option (R ⧸ Ideal.span {ϖ})) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) <
        neighborOfOption R K ϖ x ∧
      neighborOfOption R K ϖ x < stdLattice R K := by
  have hcd : ∀ y : R, ¬(ϖ ∣ (1 : R) ∧ ϖ ∣ y) := fun y h =>
    hϖ.not_isUnit (isUnit_of_dvd_one h.1)
  have hcd' : ¬(ϖ ∣ (0 : R) ∧ ϖ ∣ (1 : R)) := fun h =>
    hϖ.not_isUnit (isUnit_of_dvd_one h.2)
  cases x with
  | none => exact ⟨latticeMap_scalarGL_lt_interLattice hϖ.ne_zero hcd',
      interLattice_lt_stdLattice hcd'⟩
  | some y => exact ⟨latticeMap_scalarGL_lt_interLattice hϖ.ne_zero (hcd _),
      interLattice_lt_stdLattice (hcd _)⟩

/-- When `K` is the fraction field of `R` and `ϖ` is irreducible, distinct elements of
`Option (R ⧸ (ϖ))` give distinct submodules `neighborOfOption R K ϖ x`. -/
theorem neighborOfOption_injective {ϖ : R} (hϖ : Irreducible ϖ) :
    Function.Injective (neighborOfOption R K ϖ) := by
  have haff : ∀ (a : R), interLattice R K ϖ 0 1 ≠ interLattice R K ϖ 1 a := by
    intro a h
    have := dvd_of_interLattice_eq h
    rw [mul_zero, one_mul, zero_sub] at this
    exact hϖ.not_isUnit (isUnit_of_dvd_one (dvd_neg.mp this))
  rintro (_ | a) (_ | b) h
  · rfl
  · exact absurd h (haff _)
  · exact absurd h.symm (haff _)
  · have hd := dvd_of_interLattice_eq h
    rw [mul_one, one_mul] at hd
    rw [Option.some.injEq, ← Ideal.Quotient.mk_out a, ← Ideal.Quotient.mk_out b,
      Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton.mpr (dvd_sub_comm.mp hd)

theorem neighborOfOption_injective_into_interval {ϖ : R} (hϖ : Irreducible ϖ) :
    Function.Injective (fun x : Option (R ⧸ Ideal.span {ϖ}) =>
      (⟨neighborOfOption R K ϖ x, neighborOfOption_mem_interval hϖ x⟩ :
        {L : Submodule R (Fin 2 → K) //
          latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) < L ∧
            L < stdLattice R K})) :=
  fun _ _ h => neighborOfOption_injective hϖ (congrArg Subtype.val h)

end NeighbourFamily

section Gates

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

theorem interLattice_zero_zero (ϖ : R) : interLattice R K ϖ 0 0 = stdLattice R K := by
  refine le_antisymm (interLattice_le_stdLattice ϖ 0 0) (fun v hv => ?_)
  exact ⟨hv, 0, IsLocalization.isInteger_zero, by simp⟩

variable [IsFractionRing R K]

/-- When `K` is the fraction field of `R` and `ϖ ≠ 0`, `interLattice ϖ 1 0` is `diag(1, ϖ) R²`. -/
theorem interLattice_one_zero {ϖ : R} (hϖ : ϖ ≠ 0) :
    interLattice R K ϖ 1 0 =
      latticeMap (diagSnd (unitOfNeZero (K := K) hϖ)) (stdLattice R K) := by
  ext v
  rw [mem_interLattice, mem_latticeMap_diagSnd_stdLattice]
  constructor
  · rintro ⟨hv, w, hw, hweq⟩
    rw [map_zero, zero_mul, map_one, one_mul, zero_sub] at hweq
    refine ⟨hv 0, -w, IsLocalization.isInteger_neg hw, ?_⟩
    rw [unitOfNeZero_coe, mul_neg, ← hweq, neg_neg]
  · rintro ⟨h0, w, hw, hweq⟩
    rw [unitOfNeZero_coe] at hweq
    refine ⟨fun i => ?_, -w, IsLocalization.isInteger_neg hw, ?_⟩
    · fin_cases i
      · exact h0
      · exact hweq ▸ IsLocalization.isInteger_mul ⟨ϖ, rfl⟩ hw
    · rw [map_zero, zero_mul, map_one, one_mul, zero_sub, ← hweq, mul_neg]

end Gates

end LT.LatticeTree

end
