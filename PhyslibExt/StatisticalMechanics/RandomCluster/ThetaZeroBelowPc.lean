/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.MonotoneInPBoundaryCondition
public import PhyslibExt.StatisticalMechanics.RandomCluster.WiredDomChain
public import PhyslibExt.StatisticalMechanics.RandomCluster.MonotoneWeakLimit
public import PhyslibExt.StatisticalMechanics.RandomCluster.TailLimit
public import PhyslibExt.StatisticalMechanics.RandomCluster.BoxTailLimit
public import PhyslibExt.StatisticalMechanics.RandomCluster.PcNontrivial
/-!
# No percolation below the `q = 2` random-cluster critical point

For the wired `q = 2` random-cluster model on `ℤ^d`, `θ¹(p, 2)` is monotone in `p`, so
`θ¹(p, 2) = 0` for every `p < p_c(2, d)`.

## i. Overview

`p_c(q, d)` is defined as the supremum of the set of `p` with `θ¹(p, q) = 0`. Without monotonicity
of `θ¹` in `p`, this supremum need not separate a non-percolating phase from a percolating one.
For `q = 2`, the wired box measures are monotone in `p` on increasing box events, the wired
infinite-volume measure is their limit on those events, and the box-boundary connection
probabilities converge to `θ¹(p, 2)`. Together these give monotonicity of `θ¹(p, 2)` in `p`, and
hence no percolation strictly below `p_c(2, d)`. At `p = p_c(2, d)` itself, `θ¹ = 0` is a
hypothesis of `tzp_fkTheta_eq_zero_of_le_pc_of_pc`, not proved here.

## ii. Key results

- `tzp_fkTheta_monotone_in_p` : `θ¹(p, 2)` is monotone in `p`.
- `tzp_fkTheta_eq_zero_of_lt_pc` : `θ¹(p, 2) = 0` for `p < p_c(2, d)`.
- `tzp_fkTheta_eq_zero_of_le_pc_of_pc` : `θ¹(p, 2) = 0` for `p ≤ p_c(2, d)`, given `θ¹ = 0` at
  `p_c(2, d)`.

## iii. Table of contents

- A. Monotonicity of the percolation probability in `p`
- B. No percolation below the critical point

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Theorem 3.21 and Section 5.1.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped BigOperators NNReal

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK StatMech.Percolation

variable {d : ℕ}

/-! ## A. Monotonicity of the percolation probability in `p` -/

/-- For `q = 2`, the wired infinite-volume probability that the origin is connected to the boundary
of the box of radius `n` is monotone in `p`. -/
lemma tzp_fkTheta_iv_monotone_boxBdry (n : ℕ) {p₁ p₂ : ℝ}
    (hp₁ : 0 < p₁) (hp₁' : p₁ < 1) (hp₂ : 0 < p₂) (hp₂' : p₂ < 1) (hle : p₁ ≤ p₂) :
    (wiredInfiniteVolume d hp₁ hp₁' (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n)
      ≤ (wiredInfiniteVolume d hp₂ hp₂' (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) := by
  set S : Set (ConfigSpace (Sym2 (boxVerts d n))) :=
    {ω' : ConfigSpace (Sym2 (boxVerts d n)) |
      ConnToBdry (boxGraph d n) (boxBoundary d n) ω' (IsingFK.boxOrigin d n)} with hS
  have hSinc : IsIncreasing S := isIncreasing_connToBdryEvent n
  have hEvent : boxBdryConnEvent d n = boxRestrict d n ⁻¹' S := rfl
  have htend₁ := fk_wired_infinite_measure n hp₁ hp₁' hSinc
  have htend₂ := fk_wired_infinite_measure n hp₂ hp₂' hSinc
  have hmono : ∀ᶠ m in atTop,
      (wiredFiniteMeasure d m hp₁ hp₁' (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d n ⁻¹' S)
        ≤ (wiredFiniteMeasure d m hp₂ hp₂' (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d n ⁻¹' S) := by
    filter_upwards [Filter.eventually_ge_atTop n] with m hnm
    exact wiredFiniteMeasure_real_monotone_in_p_inner n m hnm hp₁ hp₁' hp₂ hp₂' hle hSinc
  rw [hEvent]
  exact le_of_tendsto_of_tendsto htend₁ htend₂ hmono

/-- For `q = 2`, the wired percolation probability `θ¹(p, 2)` is monotone in `p`. -/
lemma tzp_fkTheta_monotone_in_p {p₁ p₂ : ℝ}
    (hp₁ : 0 < p₁) (hp₁' : p₁ < 1) (hp₂ : 0 < p₂) (hp₂' : p₂ < 1) (hle : p₁ ≤ p₂) :
    fkTheta d hp₁ hp₁' (by norm_num : (0 : ℝ) < 2) (q := 2)
      ≤ fkTheta d hp₂ hp₂' (by norm_num : (0 : ℝ) < 2) (q := 2) := by
  have htend₁ := wiredIv_boxBdryConnEvent_tendsto (d := d) hp₁ hp₁' (by norm_num : (0 : ℝ) < 2)
  have htend₂ := wiredIv_boxBdryConnEvent_tendsto (d := d) hp₂ hp₂' (by norm_num : (0 : ℝ) < 2)
  have hmono : ∀ᶠ n in atTop,
      (wiredInfiniteVolume d hp₁ hp₁' (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n)
        ≤ (wiredInfiniteVolume d hp₂ hp₂' (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) :=
    Filter.Eventually.of_forall
      (fun n => tzp_fkTheta_iv_monotone_boxBdry n hp₁ hp₁' hp₂ hp₂' hle)
  exact le_of_tendsto_of_tendsto htend₁ htend₂ hmono

/-! ## B. No percolation below the critical point -/

/-- For `q = 2`, there is no percolation below the critical point: `θ¹(p, 2) = 0` for `p < p_c(2,
d)`. -/
lemma tzp_fkTheta_eq_zero_of_lt_pc {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hpc : p < FK.fkPc d 2) :
    FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0 := by
  have hne : (FK.fkSubcriticalSet d 2).Nonempty := by
    rcases (FK.fkSubcriticalSet d 2).eq_empty_or_nonempty with hempty | hne
    · exfalso; rw [FK.fkPc, hempty, Real.sSup_empty] at hpc; linarith
    · exact hne
  obtain ⟨p', hp'mem, hpp'⟩ := exists_lt_of_lt_csSup hne hpc
  obtain ⟨hp'0, hp'1, _hq, hθ'⟩ := hp'mem
  have hmono : FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2)
      ≤ FK.fkTheta d hp'0 hp'1 (by norm_num : (0 : ℝ) < 2) (q := 2) :=
    tzp_fkTheta_monotone_in_p hp hp1 hp'0 hp'1 hpp'.le
  refine le_antisymm ?_ (FK.fkTheta_nonneg d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2))
  calc FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2)
      ≤ FK.fkTheta d hp'0 hp'1 (by norm_num : (0 : ℝ) < 2) (q := 2) := hmono
    _ = 0 := hθ'

/-- For `q = 2`, if `θ¹(p_c, 2) = 0` (hypothesis `hθpc`, not proved here), then `θ¹(p, 2) = 0` for
every `p ≤ p_c(2, d)`. -/
lemma tzp_fkTheta_eq_zero_of_le_pc_of_pc
    (hθpc : ∀ (hp : 0 < FK.fkPc d 2) (hp1 : FK.fkPc d 2 < 1),
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0) :
    ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0 := by
  intro p hp hp1 hple
  rcases lt_or_eq_of_le hple with hlt | heq
  · exact tzp_fkTheta_eq_zero_of_lt_pc hp hp1 hlt
  · subst heq
    exact hθpc hp hp1

end FK

end StatMech
