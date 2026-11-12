/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.MetricSpace.Bounded
/-!

# Reaction extent, limiting reagents and yield

From nonnegative initial amounts a reaction advances over a closed interval of extents whose
upper end, set by a limiting reagent, bounds the yield of every product.

## i. Overview

Species are indexed by a finite type `ι`. A single reaction is a vector `ν : ι → ℝ` of signed
stoichiometric coefficients, positive for products and negative for reactants, the consumed
species. Starting from the initial amounts `n₀ : ι → ℝ`, advancing the reaction by the extent
`ξ : ℝ` gives the amounts `n₀ i + ν i * ξ`.

An extent is feasible when it leaves every amount nonnegative. With nonnegative initial amounts
and at least one consumed species, the feasible forward extents `0 ≤ ξ` form the closed interval
from `0` to `maxExtent ν n₀ h`, the smallest ratio `n₀ i / |ν i|` over the consumed species. A
consumed species attaining that minimum is a limiting reagent: it runs out first, and one always
exists. Without consumed species every nonnegative extent is feasible. Running the reaction
backward, the feasible reverse extents `ξ ≤ 0` form the closed interval from
`minExtent ν n₀ h`, minus the smallest ratio `n₀ i / ν i` over the produced species, to `0`, or
every nonpositive extent when nothing is produced. The forward and reverse bounds are separate
definitions and separate results.

For a product species `P`, the increment `ν P * ξ` over feasible extents is greatest at
`maxExtent ν n₀ h`, which gives the theoretical yield. When the actual increment of `P` comes
from this reaction alone, the percent yield `100 * actual / theoretical` is at most `100`. If the
amounts `n` come from `n₀` by some extent `ξ`, every species with a nonzero coefficient recovers
the same extent `(n i - n₀ i) / ν i = ξ`.

For a finite family of reactions with stoichiometric matrix `N : Matrix ι κ ℝ` (rows species,
columns reactions), the reachable slice is the affine set of amounts `n₀ + N *ᵥ ξ`. Its
nonnegative part is convex. A weight in the left kernel of `N` is conserved on the slice, and a
strictly positive conserved weight bounds every coordinate of a nonnegative point by the
conserved total divided by the smallest weight, so the nonnegative part is bounded. Being the
intersection of an affine subspace with finitely many closed half-spaces `0 ≤ n i`, it is then a
bounded polyhedron, that is, a polytope in the standard sense. That reading is a documented
consequence: no Mathlib polytope structure is constructed here.

Amounts and extents are numerical coordinates after a consistent choice of amount unit, such as
the mole; following the IUPAC convention the extent of reaction carries the unit of amount of
substance, while stoichiometric coefficients are dimensionless. A later bridge to dimensional
quantities may wrap these coordinates without changing the statements. No balance condition on
`ν` for a composition matrix is assumed or used: every result depends only on the stoichiometric
coefficients.

The results do not assert that a feasible extent or a point of the reachable slice is reached,
which kinetics and equilibrium decide; they give no equilibrium constants or rate laws; they do
not assert that every vector in the left kernel of `N` is chemically realizable as a
conservation law such as an element count, only that it is conserved on the slice, nor that a
strictly positive conserved weight exists, which is a hypothesis.

## ii. Key results

- `forwardFeasibleExtents_eq_Icc` : with nonnegative initial amounts and a consumed species, the
  feasible forward extents are `Set.Icc 0 (maxExtent ν n₀ h)`.
- `forwardFeasibleExtents_eq_Ici` : with nonnegative initial amounts and no consumed species,
  they are `Set.Ici 0`.
- `reverseFeasibleExtents_eq_Icc` : with nonnegative initial amounts and a produced species, the
  feasible reverse extents are `Set.Icc (minExtent ν n₀ h) 0`.
- `reverseFeasibleExtents_eq_Iic` : with nonnegative initial amounts and no produced species,
  they are `Set.Iic 0`.
- `exists_div_abs_eq_maxExtent` : some consumed species attains the minimum `maxExtent ν n₀ h`.
- `isLimitingReagent_iff` : a limiting reagent is a consumed species whose ratio
  `n₀ i / |ν i|` equals `maxExtent ν n₀ h`.
- `exists_isLimitingReagent` : a reaction that consumes some species has a limiting reagent.
- `mul_le_mul_maxExtent` : the increment of a product at a feasible extent is at most its
  increment at `maxExtent ν n₀ h`.
- `maxExtent_mem_forwardFeasibleExtents` : `maxExtent ν n₀ h` is itself feasible.
- `isGreatest_mul_maxExtent` : the increment of a product over feasible extents is greatest at
  `maxExtent ν n₀ h`.
- `percentYield_self` : the theoretical amount has percent yield `100`.
- `percentYield_le_hundred` : the percent yield of a product made only by this reaction is at
  most `100`.
- `sub_div_eq_extent` : every species with a nonzero coefficient recovers the extent.
- `sub_div_eq_sub_div_of_extent` : every species with a nonzero coefficient gives the same
  extent.
- `convex_reachableSlice_inter_nonneg` : the nonnegative part of the reachable slice is convex.
- `sum_mul_eq_of_mem_reachableSlice` : a left-kernel weight is conserved on the reachable slice.
- `le_sum_mul_div_inf'_of_mem_reachableSlice` : a strictly positive conserved weight bounds the
  nonnegative part of the slice explicitly.
- `isBounded_reachableSlice_inter_nonneg` : the nonnegative part of the slice is bounded.

## iii. Table of contents

- A. Consumed and produced species
- B. Extremal extents
- C. Feasible extents
- D. Limiting reagents
- E. Product increment and percent yield
- F. Species independence of the extent
- G. The reachable slice

## iv. References

- OpenStax, *Chemistry 2e*, §4.1, "Writing and Balancing Chemical Equations".
- OpenStax, *Chemistry 2e*, §4.3, "Reaction Stoichiometry".
- OpenStax, *Chemistry 2e*, §4.4, "Reaction Yields".
- IUPAC, *Quantities, Units and Symbols in Physical Chemistry* (the Green Book).

-/

@[expose] public section

namespace Chemistry.Stoichiometry

open Matrix

/-!

## A. Consumed and produced species

-/

/-- The species consumed by the reaction `ν`: those with a negative stoichiometric coefficient,
`ν i < 0`, that is, the reactants. -/
noncomputable def consumedSpecies {ι : Type*} [Fintype ι] (ν : ι → ℝ) : Finset ι :=
  Finset.univ.filter fun i => ν i < 0

/-- The species produced by the reaction `ν`: those with a positive stoichiometric coefficient,
`0 < ν i`, that is, the products. -/
noncomputable def producedSpecies {ι : Type*} [Fintype ι] (ν : ι → ℝ) : Finset ι :=
  Finset.univ.filter fun i => 0 < ν i

/-- A species is consumed exactly when its coefficient is negative. -/
@[simp]
lemma mem_consumedSpecies {ι : Type*} [Fintype ι] {ν : ι → ℝ} {i : ι} :
    i ∈ consumedSpecies ν ↔ ν i < 0 := by
  simp [consumedSpecies]

/-- A species is produced exactly when its coefficient is positive. -/
@[simp]
lemma mem_producedSpecies {ι : Type*} [Fintype ι] {ν : ι → ℝ} {i : ι} :
    i ∈ producedSpecies ν ↔ 0 < ν i := by
  simp [producedSpecies]

/-- A reaction with a negative coefficient has a nonempty set of consumed species. -/
lemma consumedSpecies_nonempty {ι : Type*} [Fintype ι] {ν : ι → ℝ} (h : ∃ i, ν i < 0) :
    (consumedSpecies ν).Nonempty :=
  h.imp fun _ hi => mem_consumedSpecies.2 hi

/-- A reaction with a positive coefficient has a nonempty set of produced species. -/
lemma producedSpecies_nonempty {ι : Type*} [Fintype ι] {ν : ι → ℝ} (h : ∃ i, 0 < ν i) :
    (producedSpecies ν).Nonempty :=
  h.imp fun _ hi => mem_producedSpecies.2 hi

/-!

## B. Extremal extents

-/

/-- The maximal forward extent `ξmax` of the reaction `ν` from the initial amounts `n₀`: the
smallest ratio `n₀ i / |ν i|` over the consumed species, which form a nonempty set by `h`. -/
noncomputable def maxExtent {ι : Type*} [Fintype ι] (ν n₀ : ι → ℝ) (h : ∃ i, ν i < 0) : ℝ :=
  (consumedSpecies ν).inf' (consumedSpecies_nonempty h) fun i => n₀ i / |ν i|

/-- The minimal reverse extent `ξmin` of the reaction `ν` from the initial amounts `n₀`: minus
the smallest ratio `n₀ i / ν i` over the produced species, which form a nonempty set by `h` and
are the species that running the reaction backward consumes. -/
noncomputable def minExtent {ι : Type*} [Fintype ι] (ν n₀ : ι → ℝ) (h : ∃ i, 0 < ν i) : ℝ :=
  -(producedSpecies ν).inf' (producedSpecies_nonempty h) fun i => n₀ i / ν i

/-- `maxExtent ν n₀ h` is at most the ratio `n₀ i / |ν i|` of every consumed species. -/
lemma maxExtent_le {ι : Type*} [Fintype ι] {ν : ι → ℝ} (n₀ : ι → ℝ) (h : ∃ i, ν i < 0) {i : ι}
    (hi : ν i < 0) : maxExtent ν n₀ h ≤ n₀ i / |ν i| :=
  Finset.inf'_le _ (mem_consumedSpecies.2 hi)

/-- A real number is at most `maxExtent ν n₀ h` exactly when it is at most the ratio
`n₀ i / |ν i|` of every consumed species. -/
lemma le_maxExtent_iff {ι : Type*} [Fintype ι] {ν n₀ : ι → ℝ} (h : ∃ i, ν i < 0) {x : ℝ} :
    x ≤ maxExtent ν n₀ h ↔ ∀ i, ν i < 0 → x ≤ n₀ i / |ν i| := by
  simp [maxExtent, Finset.le_inf'_iff]

/-- `minExtent ν n₀ h` is at least `-(n₀ i / ν i)` for every produced species. -/
lemma neg_div_le_minExtent {ι : Type*} [Fintype ι] {ν : ι → ℝ} (n₀ : ι → ℝ) (h : ∃ i, 0 < ν i)
    {i : ι} (hi : 0 < ν i) : -(n₀ i / ν i) ≤ minExtent ν n₀ h :=
  neg_le_neg (Finset.inf'_le _ (mem_producedSpecies.2 hi))

/-- A real number is at least `minExtent ν n₀ h` exactly when it is at least `-(n₀ i / ν i)`
for every produced species. -/
lemma minExtent_le_iff {ι : Type*} [Fintype ι] {ν n₀ : ι → ℝ} (h : ∃ i, 0 < ν i) {x : ℝ} :
    minExtent ν n₀ h ≤ x ↔ ∀ i, 0 < ν i → -(n₀ i / ν i) ≤ x := by
  rw [minExtent, neg_le, Finset.le_inf'_iff]
  refine forall_congr' fun i => ?_
  rw [mem_producedSpecies, neg_le]

/-!

## C. Feasible extents

-/

/-- The forward-feasible extents of the reaction `ν` from the initial amounts `n₀`: the
nonnegative extents `ξ` that leave every amount `n₀ i + ν i * ξ` nonnegative. -/
def forwardFeasibleExtents {ι : Type*} (ν n₀ : ι → ℝ) : Set ℝ :=
  {ξ | 0 ≤ ξ ∧ ∀ i, 0 ≤ n₀ i + ν i * ξ}

/-- The reverse-feasible extents of the reaction `ν` from the initial amounts `n₀`: the
nonpositive extents `ξ` that leave every amount `n₀ i + ν i * ξ` nonnegative. -/
def reverseFeasibleExtents {ι : Type*} (ν n₀ : ι → ℝ) : Set ℝ :=
  {ξ | ξ ≤ 0 ∧ ∀ i, 0 ≤ n₀ i + ν i * ξ}

/-- For a consumed species, `ν < 0`, the amount `n₀ + ν * ξ` after the extent `ξ` is nonnegative
exactly when `ξ ≤ n₀ / |ν|`. -/
lemma nonneg_add_mul_iff_le_div_abs {n₀ ν ξ : ℝ} (hν : ν < 0) :
    0 ≤ n₀ + ν * ξ ↔ ξ ≤ n₀ / |ν| := by
  rw [abs_of_neg hν, le_div_iff₀ (neg_pos.2 hν)]
  constructor <;> intro h <;> linarith

/-- For a produced species, `0 < ν`, the amount `n₀ + ν * ξ` after the extent `ξ` is nonnegative
exactly when `-(n₀ / ν) ≤ ξ`. -/
lemma nonneg_add_mul_iff_neg_div_le {n₀ ν ξ : ℝ} (hν : 0 < ν) :
    0 ≤ n₀ + ν * ξ ↔ -(n₀ / ν) ≤ ξ := by
  rw [neg_le, le_div_iff₀ hν]
  constructor <;> intro h <;> linarith

/-- **Feasible forward extents.** If every initial amount is nonnegative and some species is
consumed, the feasible forward extents form the closed interval from `0` to
`maxExtent ν n₀ h`, the smallest ratio `n₀ i / |ν i|` over the consumed species. -/
lemma forwardFeasibleExtents_eq_Icc {ι : Type*} [Fintype ι] (ν n₀ : ι → ℝ)
    (hn₀ : ∀ i, 0 ≤ n₀ i) (h : ∃ i, ν i < 0) :
    forwardFeasibleExtents ν n₀ = Set.Icc 0 (maxExtent ν n₀ h) := by
  ext ξ
  change (0 ≤ ξ ∧ ∀ i, 0 ≤ n₀ i + ν i * ξ) ↔ 0 ≤ ξ ∧ ξ ≤ maxExtent ν n₀ h
  rw [le_maxExtent_iff]
  refine and_congr_right fun hξ =>
    ⟨fun hn i hi => (nonneg_add_mul_iff_le_div_abs hi).1 (hn i), fun hle i => ?_⟩
  rcases lt_or_ge (ν i) 0 with hi | hi
  · exact (nonneg_add_mul_iff_le_div_abs hi).2 (hle i hi)
  · exact add_nonneg (hn₀ i) (mul_nonneg hi hξ)

/-- **No consumed species.** If every initial amount is nonnegative and no species is consumed,
every nonnegative extent is feasible: the feasible forward extents are `Set.Ici 0`, unbounded
above. -/
lemma forwardFeasibleExtents_eq_Ici {ι : Type*} (ν n₀ : ι → ℝ) (hn₀ : ∀ i, 0 ≤ n₀ i)
    (h : ∀ i, 0 ≤ ν i) : forwardFeasibleExtents ν n₀ = Set.Ici 0 := by
  ext ξ
  change (0 ≤ ξ ∧ ∀ i, 0 ≤ n₀ i + ν i * ξ) ↔ 0 ≤ ξ
  exact and_iff_left_of_imp fun hξ i => add_nonneg (hn₀ i) (mul_nonneg (h i) hξ)

/-- **Feasible reverse extents.** If every initial amount is nonnegative and some species is
produced, the feasible reverse extents form the closed interval from `minExtent ν n₀ h`, minus
the smallest ratio `n₀ i / ν i` over the produced species, to `0`. -/
lemma reverseFeasibleExtents_eq_Icc {ι : Type*} [Fintype ι] (ν n₀ : ι → ℝ)
    (hn₀ : ∀ i, 0 ≤ n₀ i) (h : ∃ i, 0 < ν i) :
    reverseFeasibleExtents ν n₀ = Set.Icc (minExtent ν n₀ h) 0 := by
  ext ξ
  change (ξ ≤ 0 ∧ ∀ i, 0 ≤ n₀ i + ν i * ξ) ↔ minExtent ν n₀ h ≤ ξ ∧ ξ ≤ 0
  rw [minExtent_le_iff]
  constructor
  · rintro ⟨hξ, hn⟩
    exact ⟨fun i hi => (nonneg_add_mul_iff_neg_div_le hi).1 (hn i), hξ⟩
  · rintro ⟨hle, hξ⟩
    refine ⟨hξ, fun i => ?_⟩
    rcases lt_or_ge 0 (ν i) with hi | hi
    · exact (nonneg_add_mul_iff_neg_div_le hi).2 (hle i hi)
    · exact add_nonneg (hn₀ i) (mul_nonneg_of_nonpos_of_nonpos hi hξ)

/-- **No produced species.** If every initial amount is nonnegative and no species is produced,
every nonpositive extent is feasible: the feasible reverse extents are `Set.Iic 0`, unbounded
below. -/
lemma reverseFeasibleExtents_eq_Iic {ι : Type*} (ν n₀ : ι → ℝ) (hn₀ : ∀ i, 0 ≤ n₀ i)
    (h : ∀ i, ν i ≤ 0) : reverseFeasibleExtents ν n₀ = Set.Iic 0 := by
  ext ξ
  change (ξ ≤ 0 ∧ ∀ i, 0 ≤ n₀ i + ν i * ξ) ↔ ξ ≤ 0
  exact and_iff_left_of_imp fun hξ i =>
    add_nonneg (hn₀ i) (mul_nonneg_of_nonpos_of_nonpos (h i) hξ)

/-!

## D. Limiting reagents

-/

/-- The species `i` is a limiting reagent of the reaction `ν` from the initial amounts `n₀` when
it is consumed and its ratio `n₀ i / |ν i|` is the smallest over the consumed species, so that it
runs out first as the extent grows. -/
def IsLimitingReagent {ι : Type*} (ν n₀ : ι → ℝ) (i : ι) : Prop :=
  ν i < 0 ∧ ∀ j, ν j < 0 → n₀ i / |ν i| ≤ n₀ j / |ν j|

/-- **Attainment.** Some consumed species has ratio `n₀ i / |ν i|` equal to
`maxExtent ν n₀ h`. -/
lemma exists_div_abs_eq_maxExtent {ι : Type*} [Fintype ι] (ν n₀ : ι → ℝ) (h : ∃ i, ν i < 0) :
    ∃ i, ν i < 0 ∧ n₀ i / |ν i| = maxExtent ν n₀ h := by
  obtain ⟨i, hi, heq⟩ :=
    Finset.exists_mem_eq_inf' (consumedSpecies_nonempty h) fun i => n₀ i / |ν i|
  exact ⟨i, mem_consumedSpecies.1 hi, heq.symm⟩

/-- A species is a limiting reagent exactly when it is consumed and its ratio `n₀ i / |ν i|`
equals `maxExtent ν n₀ h`. -/
lemma isLimitingReagent_iff {ι : Type*} [Fintype ι] {ν n₀ : ι → ℝ} (h : ∃ i, ν i < 0)
    {i : ι} : IsLimitingReagent ν n₀ i ↔ ν i < 0 ∧ n₀ i / |ν i| = maxExtent ν n₀ h :=
  and_congr_right fun hi =>
    ⟨fun hmin => le_antisymm ((le_maxExtent_iff h).2 hmin) (maxExtent_le n₀ h hi),
      fun heq _ hj => heq.trans_le (maxExtent_le n₀ h hj)⟩

/-- **A limiting reagent exists.** A reaction that consumes some species has a limiting
reagent. -/
lemma exists_isLimitingReagent {ι : Type*} [Finite ι] (ν n₀ : ι → ℝ) (h : ∃ i, ν i < 0) :
    ∃ i, IsLimitingReagent ν n₀ i := by
  have := Fintype.ofFinite ι
  exact (exists_div_abs_eq_maxExtent ν n₀ h).imp fun _ hi => (isLimitingReagent_iff h).2 hi

/-!

## E. Product increment and percent yield

-/

/-- Every feasible forward extent is at most `maxExtent ν n₀ h`. -/
lemma le_maxExtent_of_mem_forwardFeasibleExtents {ι : Type*} [Fintype ι] {ν n₀ : ι → ℝ}
    (h : ∃ i, ν i < 0) {ξ : ℝ} (hξ : ξ ∈ forwardFeasibleExtents ν n₀) :
    ξ ≤ maxExtent ν n₀ h :=
  (le_maxExtent_iff h).2 fun i hi => (nonneg_add_mul_iff_le_div_abs hi).1 (hξ.2 i)

/-- With nonnegative initial amounts, `maxExtent ν n₀ h` is itself a feasible forward
extent. -/
lemma maxExtent_mem_forwardFeasibleExtents {ι : Type*} [Fintype ι] {ν n₀ : ι → ℝ}
    (hn₀ : ∀ i, 0 ≤ n₀ i) (h : ∃ i, ν i < 0) :
    maxExtent ν n₀ h ∈ forwardFeasibleExtents ν n₀ := by
  rw [forwardFeasibleExtents_eq_Icc ν n₀ hn₀ h]
  exact ⟨(le_maxExtent_iff h).2 fun i _ => div_nonneg (hn₀ i) (abs_nonneg _), le_rfl⟩

/-- **Maximal product increment.** For a product species `P`, the increment `ν P * ξ` at every
feasible forward extent is at most `ν P * maxExtent ν n₀ h`. -/
lemma mul_le_mul_maxExtent {ι : Type*} [Fintype ι] {ν n₀ : ι → ℝ} (h : ∃ i, ν i < 0) {P : ι}
    (hP : 0 < ν P) : ∀ ξ ∈ forwardFeasibleExtents ν n₀, ν P * ξ ≤ ν P * maxExtent ν n₀ h :=
  fun _ hξ => mul_le_mul_of_nonneg_left (le_maxExtent_of_mem_forwardFeasibleExtents h hξ) hP.le

/-- **Theoretical yield.** With nonnegative initial amounts, the increment `ν P * ξ` of a product
species `P` over the feasible forward extents has greatest value `ν P * maxExtent ν n₀ h`,
attained at `ξ = maxExtent ν n₀ h`. -/
lemma isGreatest_mul_maxExtent {ι : Type*} [Fintype ι] {ν n₀ : ι → ℝ} (hn₀ : ∀ i, 0 ≤ n₀ i)
    (h : ∃ i, ν i < 0) {P : ι} (hP : 0 < ν P) :
    IsGreatest ((fun ξ => ν P * ξ) '' forwardFeasibleExtents ν n₀)
      (ν P * maxExtent ν n₀ h) := by
  refine ⟨⟨_, maxExtent_mem_forwardFeasibleExtents hn₀ h, rfl⟩, ?_⟩
  rintro _ ⟨ξ, hξ, rfl⟩
  exact mul_le_mul_maxExtent h hP ξ hξ

/-- The percent yield `100 * actual / theoretical` of a product, from its actual and its
theoretical amount. -/
noncomputable def percentYield (actual theoretical : ℝ) : ℝ :=
  100 * actual / theoretical

/-- The percent yield of a nonzero theoretical amount, measured against itself, is `100`. -/
lemma percentYield_self {theoretical : ℝ} (h : theoretical ≠ 0) :
    percentYield theoretical theoretical = 100 := by
  rw [percentYield, mul_div_assoc, div_self h, mul_one]

/-- **Percent yield at most 100.** Let the theoretical yield `ν P * maxExtent ν n₀ h` of the
species `P` be positive and the reaction reach an extent `ξ` between `0` and
`maxExtent ν n₀ h`. If the actual increment of `P` is `ν P * ξ`, which holds when this reaction
is the only source of `P` (hypothesis `hactual`), the percent yield is at most `100`. A measured
percent yield above `100` therefore signals impure or wet product or another source of `P`, a
problem with the data rather than a failure of this lemma. -/
lemma percentYield_le_hundred {ι : Type*} [Fintype ι] {ν n₀ : ι → ℝ} (h : ∃ i, ν i < 0)
    {P : ι} {ξ actual : ℝ} (htheo : 0 < ν P * maxExtent ν n₀ h)
    (hξ : ξ ∈ Set.Icc 0 (maxExtent ν n₀ h)) (hactual : actual = ν P * ξ) :
    percentYield actual (ν P * maxExtent ν n₀ h) ≤ 100 := by
  have hP : 0 < ν P := pos_of_mul_pos_left htheo (hξ.1.trans hξ.2)
  have hle : ν P * ξ ≤ ν P * maxExtent ν n₀ h := mul_le_mul_of_nonneg_left hξ.2 hP.le
  rw [percentYield, div_le_iff₀ htheo, hactual]
  linarith

/-!

## F. Species independence of the extent

-/

/-- If the amounts `n` come from `n₀` by the extent `ξ`, every species with a nonzero coefficient
recovers the extent as `(n i - n₀ i) / ν i`. -/
lemma sub_div_eq_extent {ι : Type*} {ν n₀ n : ι → ℝ} {ξ : ℝ} (h : ∀ i, n i = n₀ i + ν i * ξ)
    {i : ι} (hi : ν i ≠ 0) : (n i - n₀ i) / ν i = ξ := by
  rw [h i, add_sub_cancel_left, mul_div_cancel_left₀ ξ hi]

/-- **Species independence of the extent.** If the amounts `n` come from `n₀` by some extent,
any two species with nonzero coefficients give the same ratio `(n i - n₀ i) / ν i`, namely the
extent. -/
lemma sub_div_eq_sub_div_of_extent {ι : Type*} {ν n₀ n : ι → ℝ} {ξ : ℝ}
    (h : ∀ i, n i = n₀ i + ν i * ξ) {i j : ι} (hi : ν i ≠ 0) (hj : ν j ≠ 0) :
    (n i - n₀ i) / ν i = (n j - n₀ j) / ν j := by
  rw [sub_div_eq_extent h hi, sub_div_eq_extent h hj]

/-!

## G. The reachable slice

-/

/-- The reachable slice from the initial amounts `n₀` for the stoichiometric matrix `N`, with
rows indexed by species and columns by reactions: the amounts `n₀ + N *ᵥ ξ` over all extent
vectors `ξ`, of any sign. -/
def reachableSlice {ι κ : Type*} [Fintype κ] (n₀ : ι → ℝ) (N : Matrix ι κ ℝ) : Set (ι → ℝ) :=
  {n | ∃ ξ : κ → ℝ, n = n₀ + N *ᵥ ξ}

/-- The reachable slice is convex. -/
lemma convex_reachableSlice {ι κ : Type*} [Fintype κ] (n₀ : ι → ℝ) (N : Matrix ι κ ℝ) :
    Convex ℝ (reachableSlice n₀ N) := by
  rintro _ ⟨ξ₁, rfl⟩ _ ⟨ξ₂, rfl⟩ a b - - hab
  refine ⟨a • ξ₁ + b • ξ₂, ?_⟩
  rw [mulVec_add, mulVec_smul, mulVec_smul]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination n₀ i * hab

/-- **Convexity.** The nonnegative part of the reachable slice is convex. -/
lemma convex_reachableSlice_inter_nonneg {ι κ : Type*} [Fintype κ] (n₀ : ι → ℝ)
    (N : Matrix ι κ ℝ) : Convex ℝ (reachableSlice n₀ N ∩ {n | ∀ i, 0 ≤ n i}) :=
  (convex_reachableSlice n₀ N).inter fun _ hx _ hy _ _ ha hb _ i =>
    add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))

/-- **Linear invariants.** A weight `w` in the left kernel of `N`, `∑ i, w i * N i j = 0` for
every reaction `j`, is conserved on the reachable slice. -/
lemma sum_mul_eq_of_mem_reachableSlice {ι κ : Type*} [Fintype ι] [Fintype κ] {n₀ : ι → ℝ}
    {N : Matrix ι κ ℝ} {w : ι → ℝ} (hw : ∀ j, ∑ i, w i * N i j = 0) :
    ∀ n ∈ reachableSlice n₀ N, ∑ i, w i * n i = ∑ i, w i * n₀ i := by
  rintro _ ⟨ξ, rfl⟩
  have hker : w ᵥ* N = 0 := funext hw
  change w ⬝ᵥ (n₀ + N *ᵥ ξ) = w ⬝ᵥ n₀
  rw [dotProduct_add, dotProduct_mulVec, hker, zero_dotProduct, add_zero]

/-- If `w` is a strictly positive weight in the left kernel of `N`, each coordinate `n i` of a
nonnegative point of the reachable slice is at most the conserved total `∑ j, w j * n₀ j`
divided by its weight `w i`. -/
lemma le_sum_mul_div_of_mem_reachableSlice {ι κ : Type*} [Fintype ι] [Fintype κ]
    {n₀ : ι → ℝ} {N : Matrix ι κ ℝ} {w : ι → ℝ} (hw : ∀ j, ∑ i, w i * N i j = 0)
    (hpos : ∀ i, 0 < w i) :
    ∀ n ∈ reachableSlice n₀ N ∩ {n | ∀ i, 0 ≤ n i}, ∀ i, n i ≤ (∑ j, w j * n₀ j) / w i := by
  rintro n ⟨hn, hnonneg⟩ i
  rw [le_div_iff₀ (hpos i), ← sum_mul_eq_of_mem_reachableSlice hw n hn, mul_comm]
  exact Finset.single_le_sum (fun j _ => mul_nonneg (hpos j).le (hnonneg j)) (Finset.mem_univ i)

/-- **Explicit bound from a positive conserved weight.** If the species type is nonempty, so that
the smallest weight exists, and `w` is a strictly positive weight in the left kernel of `N`, every
coordinate of a nonnegative point of the reachable slice is at most
`B = (∑ j, w j * n₀ j) / Finset.univ.inf' Finset.univ_nonempty w`, the conserved total divided
by the smallest weight. -/
lemma le_sum_mul_div_inf'_of_mem_reachableSlice {ι κ : Type*} [Fintype ι] [Nonempty ι]
    [Fintype κ] {n₀ : ι → ℝ} {N : Matrix ι κ ℝ} {w : ι → ℝ} (hw : ∀ j, ∑ i, w i * N i j = 0)
    (hpos : ∀ i, 0 < w i) :
    ∀ n ∈ reachableSlice n₀ N ∩ {n | ∀ i, 0 ≤ n i}, ∀ i,
      n i ≤ (∑ j, w j * n₀ j) / Finset.univ.inf' Finset.univ_nonempty w := by
  rintro n ⟨hn, hnonneg⟩ i
  have hmin : 0 < Finset.univ.inf' Finset.univ_nonempty w :=
    (Finset.lt_inf'_iff Finset.univ_nonempty).2 fun j _ => hpos j
  rw [le_div_iff₀ hmin, ← sum_mul_eq_of_mem_reachableSlice hw n hn]
  calc n i * Finset.univ.inf' Finset.univ_nonempty w ≤ n i * w i :=
        mul_le_mul_of_nonneg_left (Finset.inf'_le _ (Finset.mem_univ i)) (hnonneg i)
    _ = w i * n i := mul_comm _ _
    _ ≤ ∑ j, w j * n j :=
        Finset.single_le_sum (fun j _ => mul_nonneg (hpos j).le (hnonneg j)) (Finset.mem_univ i)

/-- **Boundedness.** If some strictly positive weight lies in the left kernel of `N`, the
nonnegative part of the reachable slice is bounded. Being convex and the intersection of an
affine subspace with the finitely many closed half-spaces `0 ≤ n i`, it is then a bounded
polyhedron, that is, a polytope in the standard sense; no Mathlib polytope structure is
constructed here. -/
lemma isBounded_reachableSlice_inter_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    {n₀ : ι → ℝ} {N : Matrix ι κ ℝ} {w : ι → ℝ} (hw : ∀ j, ∑ i, w i * N i j = 0)
    (hpos : ∀ i, 0 < w i) : Bornology.IsBounded (reachableSlice n₀ N ∩ {n | ∀ i, 0 ≤ n i}) :=
  (Metric.isBounded_Icc 0 fun i => (∑ j, w j * n₀ j) / w i).subset fun n hn =>
    ⟨hn.2, le_sum_mul_div_of_mem_reachableSlice hw hpos n hn⟩

end Chemistry.Stoichiometry
