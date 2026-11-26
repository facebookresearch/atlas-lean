/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SingleSiteRewiring

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SingleSiteRewiring`

* the all-closed configuration has no classical trifurcation (`bc89_GenuineTrif`), and the
  classical-trifurcation event is measurable (`bc96_measurableSet_genuineTrif`), so its point mass
  gives it probability `0`;
* `bc96_genuineTrif_of_reachOrigin_full` used contrapositively on the all-closed configuration;
* `bc96_arm_reaches_boundary_perConfig` and `bc96_bk_from_precursor` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.SingleSiteRewiring

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls
open _root_.StatMech.ConfigSpace MeasureTheory

variable {d : ℕ}

/-- The all-closed configuration has no classical trifurcation. -/
theorem not_genuine_closed (x : Site d) : ¬ bc89_GenuineTrif d (fun _ => false) x := by
  rintro ⟨a, -, -, -, -, ⟨h, -, -⟩, -⟩
  exact Bool.false_ne_true h.2

-- The point mass at the all-closed configuration gives the classical-trifurcation event mass `0`.
example (x : Site d) : Measure.dirac (fun _ => false)
    {ω : ConfigSpace (Sym2 (Site d)) | bc89_GenuineTrif d ω x} = 0 := by
  rw [Measure.dirac_apply' _ (bc96_measurableSet_genuineTrif x)]
  simp [Set.indicator, not_genuine_closed x]

-- Reaching distinct infinite clusters fails for the all-closed configuration (contrapositive).
example (a₁ a₂ a₃ x₁ x₂ x₃ : Site d)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (hconn : Connected d (removeSite 0 (fun _ => false)) a₁ x₁ ∧
      Connected d (removeSite 0 (fun _ => false)) a₂ x₂ ∧
      Connected d (removeSite 0 (fun _ => false)) a₃ x₃)
    (hinf : (cluster d (removeSite 0 (fun _ => false)) x₁).Infinite ∧
      (cluster d (removeSite 0 (fun _ => false)) x₂).Infinite ∧
      (cluster d (removeSite 0 (fun _ => false)) x₃).Infinite)
    (hdist : cluster d (removeSite 0 (fun _ => false)) x₁ ≠
        cluster d (removeSite 0 (fun _ => false)) x₂ ∧
      cluster d (removeSite 0 (fun _ => false)) x₁ ≠ cluster d (removeSite 0 (fun _ => false)) x₃ ∧
      cluster d (removeSite 0 (fun _ => false)) x₂ ≠ cluster d (removeSite 0 (fun _ => false)) x₃) :
    ¬ ((fun _ => false) s(0, a₁) = true) :=
  fun h => not_genuine_closed 0
    (bc96_genuineTrif_of_reachOrigin_full _ hadj hconn hinf hdist ⟨h, h, h⟩)

-- An infinite arm reaches outside every box.
example (ω : ConfigSpace (Sym2 (Site d))) (x a : Site d)
    (hinf : (cluster d (removeSite x ω) a).Infinite) (n : ℕ) :
    ∃ z, z ∉ box d n ∧ Connected d (removeSite x ω) a z :=
  bc96_arm_reaches_boundary_perConfig ω x a hinf n

-- Zero classical-trifurcation probability with precursors excludes `N = ∞`.
example (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) (hprob0 : μ {ω | bc89_GenuineTrif d ω 0} = 0)
    (hpre : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ (G : Finset (Sym2 (Site d))) (A : Set (ConfigSpace (Sym2 (Site d)))),
        0 < μ A ∧ A ⊆ (fun ω => forceOpenFinset G ω) ⁻¹' {ω | bc89_GenuineTrif d ω 0}) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc96_bk_from_precursor μ hfe hprob0 hpre

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.SingleSiteRewiring
