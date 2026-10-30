/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GridBoxConnected
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneZeroOrOne

/-!
# The merge geometry for Burton–Keane

Two infinite clusters meeting a box give a merge witness, so the merge geometry hypothesis of the
Burton–Keane argument always holds; with the trifurcation count this gives the Burton–Keane
conclusion.

## i. Overview

`twoMeetBox d n k` is the event that `N = k` and two distinct infinite clusters meet the box of
radius `n`; it is contained in the merge witness for the box edges. If `N = k ≥ 2` almost surely,
some box has `twoMeetBox` of positive probability, which discharges the merge geometry hypothesis
(`hmergeGeom_discharged`).

`burton_keane_uniqueness_full` combines this with the trifurcation count: a bound
`Tcount d ω n ≤ bdry n` for every configuration with `bdry n / |Λₙ| → 0`, and the trifurcation step.
From these, `P(trifurcation at 0) = 0`, `N ≠ ⊤` almost surely, and the merge argument gives the
conclusion.

**Fidelity.** `IsTrifurcation` lets an arm neighbour equal the centre, so every site of a line
configuration is a trifurcation and `Tcount` equals the volume. The counting hypotheses of
`burton_keane_uniqueness_full` are therefore unsatisfiable for `d ≥ 1` (`tfc_not_hbound_hdens`), and
the theorem has content only for `d = 0`.

## ii. Key results

- `hmergeGeom_discharged` : the merge geometry hypothesis holds.
- `burton_keane_uniqueness_full` : the Burton–Keane conclusion from the counting hypotheses (content
  only for `d = 0`).

## iii. Table of contents

- A. Two clusters meeting a box
- B. The Burton–Keane conclusion

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), Section 8.2.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}

/-! ## A. Two clusters meeting a box -/

/-- The event that `N = k` and two distinct infinite clusters meet the box of radius `n`. -/
def twoMeetBox (d n : ℕ) (k : ℕ∞) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | numInfiniteClusters d ω = k ∧
    ∃ x y : Site d, x ∈ box d n ∧ y ∈ box d n ∧
      (cluster d ω x).Infinite ∧ (cluster d ω y).Infinite ∧
      cluster d ω x ≠ cluster d ω y}

lemma twoMeetBox_subset_mergeWitness (n : ℕ) (k : ℕ∞) :
    twoMeetBox d n k ⊆ MergeWitness d (boxEdges d n) k := by
  rintro ω ⟨hkeq, x, y, hx, hy, hxinf, hyinf, hne⟩
  refine ⟨hkeq, x, y, hxinf, hyinf, hne, ?_⟩
  exact box_allOpen_connected ω hx hy

lemma iEqLevel_subset_iUnion_twoMeetBox {k : ℕ∞} (hk2 : 2 ≤ k) :
    {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = k}
      ⊆ ⋃ n, twoMeetBox d n k := by
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  have hcard : (2 : ℕ∞) ≤ (infiniteClusters d ω).encard := by
    have heq : numInfiniteClusters d ω = (infiniteClusters d ω).encard := rfl
    rw [heq] at hω; rw [hω]; exact hk2
  have hnt : (infiniteClusters d ω).Nontrivial := by
    apply Set.one_lt_encard_iff_nontrivial.mp
    exact lt_of_lt_of_le (by decide : (1 : ℕ∞) < 2) hcard
  obtain ⟨C₁, hC₁mem, C₂, hC₂mem, hCne⟩ := hnt
  simp only [infiniteClusters, Set.mem_ofPred_eq] at hC₁mem hC₂mem
  obtain ⟨hinf1, x, hxeq⟩ := hC₁mem
  obtain ⟨hinf2, y, hyeq⟩ := hC₂mem
  have hxinf : (cluster d ω x).Infinite := by rw [← hxeq]; exact hinf1
  have hyinf : (cluster d ω y).Infinite := by rw [← hyeq]; exact hinf2
  have hclne : cluster d ω x ≠ cluster d ω y := by rw [← hxeq, ← hyeq]; exact hCne
  obtain ⟨n, hn⟩ := finite_subset_box ({x, y} : Set (Site d)) (Set.toFinite _)
  have hxbox : x ∈ box d n := hn (Set.mem_insert x {y})
  have hybox : y ∈ box d n := hn (Set.mem_insert_of_mem x rfl)
  exact Set.mem_iUnion.mpr ⟨n, hω, x, y, hxbox, hybox, hxinf, hyinf, hclne⟩

lemma exists_twoMeetBox_pos
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    {k : ℕ∞} (hk2 : 2 ≤ k) (hk : μ {ω | numInfiniteClusters d ω = k} = 1) :
    ∃ n : ℕ, 0 < μ (twoMeetBox d n k) := by
  by_contra hcon
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
  have hunion0 : μ (⋃ n, twoMeetBox d n k) = 0 := by
    refine le_antisymm ?_ bot_le
    calc μ (⋃ n, twoMeetBox d n k) ≤ ∑' n, μ (twoMeetBox d n k) :=
          measure_iUnion_le _
      _ = 0 := by simp [hcon]
  have hle : μ {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = k}
      ≤ μ (⋃ n, twoMeetBox d n k) :=
    measure_mono (iEqLevel_subset_iUnion_twoMeetBox hk2)
  rw [hk, hunion0] at hle
  exact absurd hle (by norm_num)

lemma hmergeGeom_discharged
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (k : ℕ∞) (hk2 : 2 ≤ k) (_hktop : k ≠ ⊤)
    (hk : μ {ω | numInfiniteClusters d ω = k} = 1) :
    ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k) := by
  obtain ⟨n, hpos⟩ := exists_twoMeetBox_pos μ hk2 hk
  refine ⟨boxEdges d n, lt_of_lt_of_le hpos ?_⟩
  exact measure_mono (twoMeetBox_subset_mergeWitness n k)

/-! ## B. The Burton–Keane conclusion -/

/-- Burton–Keane conclusion from the counting hypotheses: for an ergodic measure with finite energy,
a
bound `Tcount d ω n ≤ bdry n` for every configuration with `bdry n / |Λₙ| → 0`, and the trifurcation
step, a.s. `N ∈ {0, 1}`. The counting hypotheses are unsatisfiable for `d ≥ 1`
(`tfc_not_hbound_hdens`), so the statement has content only for `d = 0`. -/
lemma burton_keane_uniqueness_full
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | IsTrifurcation d ω 0}) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  have hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ := herg.1
  -- Step 1: `|Λₙ| · P(trifurcation at 0) = E[Tₙ] ≤ bdry n`, and `bdry n / |Λₙ| → 0`.
  have htri0 : μ {ω | IsTrifurcation d ω 0} = 0 := by
    set P := (μ {ω | IsTrifurcation d ω 0}).toReal with hP
    have hle : ∀ n, ((boxFinsetBK d n).card : ℝ) * P ≤ bdry n := by
      intro n
      have h1 : (boxFinsetBK d n).card • μ {ω | IsTrifurcation d ω 0} ≤ (bdry n : ℝ≥0∞) := by
        rw [← expected_Tcount μ hinv n]
        calc ∫⁻ ω, (Tcount d ω n : ℝ≥0∞) ∂μ ≤ ∫⁻ _, (bdry n : ℝ≥0∞) ∂μ :=
              lintegral_mono fun ω => Nat.cast_le.mpr (hbound ω n)
          _ = bdry n := by simp
      have h2 := ENNReal.toReal_mono (by simp) h1
      rw [nsmul_eq_mul, ENNReal.toReal_mul] at h2
      simpa [hP] using h2
    have hPle : ∀ n, P ≤ (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ) := fun n => by
      rw [le_div_iff₀ (by exact_mod_cast hvol n)]
      linarith [hle n]
    have hP0 : P = 0 :=
      le_antisymm (ge_of_tendsto hdens (Filter.Eventually.of_forall hPle)) ENNReal.toReal_nonneg
    exact ((ENNReal.toReal_eq_zero_iff _).mp hP0).resolve_right (measure_ne_top _ _)
  -- Step 2: the number of infinite clusters is a.s. not `⊤`.
  have hkne_top : ∀ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 → k ≠ ⊤ := by
    rintro k hk rfl
    have hpos := htrif (by rw [hk]; exact one_pos)
    rw [htri0] at hpos
    exact lt_irrefl _ hpos
  -- Step 3: the merge argument.
  have hmerge : μ (atLeastTwoInfinite d) = 0 :=
    merge_event_null μ herg hfe hkne_top
      (fun k hk2 hktop hk => hmergeGeom_discharged μ k hk2 hktop hk)
  exact ⟨numInfiniteClusters_zero_or_one μ herg hmerge, hmerge,
    infiniteCluster_unique_ae μ herg hmerge⟩

end Percolation

end StatMech
