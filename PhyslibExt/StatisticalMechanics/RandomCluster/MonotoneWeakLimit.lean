/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.WiredDomChain
/-!
# The wired infinite-volume limit at `q = 2`

At `q = 2` the wired box measures of an increasing cylinder event decrease with the volume, so
they converge, and the limit is the value under `wiredInfiniteVolume`.

## i. Overview

For an increasing event `S` of the box `Λ_N` and `m ≥ N`, the wired box measures satisfy
`φ¹_(m+1)(S) ≤ φ¹_m(S)` (`wiredFiniteMeasure_succ_le_smallerBox`). Hence `φ¹_m(S)` converges as
`m → ∞` to its infimum `fkWiredLimitValue`. The chosen wired infinite-volume measure is the
weak limit along a subsequence and cylinder events are clopen, so its value on `S` equals this
limit. The statements are for `q = 2`, the case in which the volume monotonicity is proved in
`WiredDomChain`.

## ii. Key results

- `fkWiredLimit_antitone` : `φ¹_(N+k)(S)` is antitone in `k`.
- `fk_wired_limit_exists` : convergence of `φ¹_m(S)` to `fkWiredLimitValue`.
- `fk_wired_infinite_measure` : the limit is `wiredInfiniteVolume(S)`.

## iii. Table of contents

- A. Monotonicity in the volume
- B. The limit

## iv. References

- G. R. Grimmett, *The Random-Cluster Model*, Springer, 2006.
-/

@[expose] public section

open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK

variable {d : ℕ}

/-!
## A. Monotonicity in the volume
-/

/-- At `q = 2`, enlarging the wired box from `Λ_m` to `Λ_(m+1)` does not increase the probability of
an increasing cylinder event of `Λ_N`, `N ≤ m`. -/
lemma fkWiredLimit_succ_le (N m : ℕ) (hNm : N ≤ m) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    (wiredFiniteMeasure d (m + 1) hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
      ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
  set T := boxRestrictLE d hNm ⁻¹' S with hT
  have hTinc : IsIncreasing T := fun a b hab ha => hS (boxRestrictLE_monotone d hNm hab) ha
  have heq : boxRestrict d N ⁻¹' S = boxRestrict d m ⁻¹' T := by
    ext ω; simp only [hT, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have hmeas : MeasurableSet (boxRestrict d m ⁻¹' T) :=
    (continuous_boxRestrict d m).measurable (MeasurableSet.of_discrete)
  rw [heq, wiredFiniteMeasure_real_boxRestrictEvent m hp hp1 T hmeas]
  exact wiredFiniteMeasure_succ_le_smallerBox m hp hp1 hTinc hmeas

lemma fkWiredLimit_antitone (N : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    Antitone (fun k => (wiredFiniteMeasure d (N + k) hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) := by
  apply antitone_nat_of_succ_le
  intro k
  have h := fkWiredLimit_succ_le N (N + k) (Nat.le_add_right N k) hp hp1 hS
  rw [show N + (k + 1) = (N + k) + 1 from by ring]
  exact h

/-!
## B. The limit
-/

/-- The infimum over `k` of `φ¹_(N+k)(S)` for an event `S` of the box `Λ_N`, at `q = 2`. -/
noncomputable def fkWiredLimitValue (N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) : ℝ :=
  ⨅ k, (wiredFiniteMeasure d (N + k) hp hp1 (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)

/-- At `q = 2` the wired box probabilities of an increasing cylinder event converge to
`fkWiredLimitValue`. -/
lemma fk_wired_limit_exists (N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop
      (𝓝 (fkWiredLimitValue N hp hp1 S)) := by
  set f := fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) with hf
  have hanti := fkWiredLimit_antitone N hp hp1 hS
  have hbdd : BddBelow (Set.range (fun k => f (N + k))) :=
    ⟨0, by rintro x ⟨k, rfl⟩; exact measureReal_nonneg⟩
  have hshift : Tendsto (fun k => f (N + k)) atTop (𝓝 (fkWiredLimitValue N hp hp1 S)) :=
    tendsto_atTop_ciInf hanti hbdd
  have key : Tendsto (fun k => f (k + N)) atTop (𝓝 (fkWiredLimitValue N hp hp1 S)) := by
    have hcomm : (fun k => f (k + N)) = (fun k => f (N + k)) := by funext k; rw [Nat.add_comm]
    rw [hcomm]; exact hshift
  exact (Filter.tendsto_add_atTop_iff_nat N).mp key

lemma fk_wired_limit_le (N m : ℕ) (hNm : N ≤ m) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    fkWiredLimitValue N hp hp1 S
      ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNm
  have hbdd : BddBelow (Set.range (fun k => (wiredFiniteMeasure d (N + k) hp hp1
        (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real
        (boxRestrict d N ⁻¹' S))) :=
    ⟨0, by rintro x ⟨k, rfl⟩; exact measureReal_nonneg⟩
  exact ciInf_le hbdd k

/-- At `q = 2` the chosen wired infinite-volume measure gives an increasing cylinder event the value
`fkWiredLimitValue`. -/
lemma fkWiredLimit_wiredInfiniteVolume_eq (N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
      = fkWiredLimitValue N hp hp1 S := by
  obtain ⟨ψ, hψ, hconv⟩ := wiredInfiniteVolume_isLimit d hp hp1 (by norm_num : (0 : ℝ) < 2)
  have hclopen := isClopen_boxRestrict_preimage N S
  have hport := hconv.tendsto_real_of_isClopen (A := boxRestrict d N ⁻¹' S) hclopen
  have hsub := (fk_wired_limit_exists N hp hp1 hS).comp hψ.tendsto_atTop
  exact tendsto_nhds_unique hport hsub

/-- Existence of the wired infinite-volume random-cluster measure as the limit of wired box
measures, on increasing cylinder events at `q = 2`: `φ¹_m(S) → φ¹(S)` as `m → ∞`. The general
statement (all `q ≥ 1`, weak convergence) is in Grimmett, *The Random-Cluster Model* (2006), Chapter
4. -/
theorem fk_wired_infinite_measure (N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop
      (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S))) := by
  rw [fkWiredLimit_wiredInfiniteVolume_eq N hp hp1 hS]
  exact fk_wired_limit_exists N hp hp1 hS

end FK

end StatMech
