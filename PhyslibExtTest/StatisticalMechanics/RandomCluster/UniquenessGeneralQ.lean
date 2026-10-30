/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.UniquenessGeneralQ

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.FKGeneralQConsumer`

On `ℤ²` with `q = 2` (FK–Ising) and `q = 3` (FK–Potts), box `Λ_1`:
* the headline `fkgq_countable_free_wired_disagreement` is applied with every hypothesis
  discharged (`d = 2`, `N = 1`, `q = 2`), and its conclusion is used: the exceptional set of
  `t` is countable, so its complement is dense and there is a parameter `t ∈ (0, 1)` (hence
  `p = logistic t ∈ (1/2, e/(1+e))`) at which the free and wired measures agree on every
  increasing event of `Λ_1`;
* the same at `q = 3` in dimension `1`;
* `fkgq_free_infinite_measure` and `fkgq_wired_infinite_measure` (convergence of increasing box
  events along the full sequence of boxes) are applied to the increasing event `Set.univ` at
  `p = 1/2`, `q = 2`;
* `fkgq_freeMass` and `fkgq_wiredMass` are nonnegative mass functions.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.FKGeneralQConsumer

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice MeasureTheory Filter

/-- The set of logistic parameters at which the free and wired FK–Ising measures on `ℤ²` disagree
on some increasing event of `Λ_1`. -/
def badSet : Set ℝ :=
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts 2 1))), IsIncreasing A ∧
      eventMassProb (fkgq_freeMass 2 1 2 (by norm_num) t) A ≠
        eventMassProb (fkgq_wiredMass 2 1 2 (by norm_num) t) A}

-- The headline at `d = 2`, `N = 1`, `q = 2`: the disagreement set is countable.
theorem badSet_countable : badSet.Countable :=
  fkgq_countable_free_wired_disagreement (d := 2) (by norm_num) 1 2 (by norm_num)

-- Consequence: in the interval `t ∈ (0, 1)` there is a parameter at which the free and wired
-- measures give the same mass to every increasing event of `Λ_1`.
example : ∃ t ∈ Set.Ioo (0 : ℝ) 1, ∀ A : Set (ConfigSpace (Sym2 (boxVerts 2 1))),
    IsIncreasing A → eventMassProb (fkgq_freeMass 2 1 2 (by norm_num) t) A =
      eventMassProb (fkgq_wiredMass 2 1 2 (by norm_num) t) A := by
  obtain ⟨t, ht, hbad⟩ := (badSet_countable.dense_compl ℝ).inter_open_nonempty
    (Set.Ioo 0 1) isOpen_Ioo (Set.nonempty_Ioo.mpr (by norm_num))
  refine ⟨t, ht, fun A hA => ?_⟩
  by_contra hne
  exact hbad ⟨A, hA, hne⟩

-- The same headline at `q = 3` (Potts) in dimension `1`, box `Λ_0`.
example : {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts 1 0))), IsIncreasing A ∧
      eventMassProb (fkgq_freeMass 1 0 3 (by norm_num) t) A ≠
        eventMassProb (fkgq_wiredMass 1 0 3 (by norm_num) t) A}.Countable :=
  fkgq_countable_free_wired_disagreement (d := 1) le_rfl 0 3 (by norm_num)

-- The whole space is an increasing event of `Λ_1`.
example : IsIncreasing (Set.univ : Set (ConfigSpace (Sym2 (boxVerts 2 1)))) :=
  fun _ _ _ _ => trivial

-- Free box measures of an increasing event of `Λ_1` converge along the full box sequence.
example : Tendsto (fun m => (freeFiniteMeasure 2 m (p := 1 / 2) (q := 2) (by norm_num)
      (by norm_num) (by norm_num) : Measure _).real (boxRestrict 2 1 ⁻¹' Set.univ)) atTop
    (nhds ((freeInfiniteVolume 2 (p := 1 / 2) (q := 2) (by norm_num) (by norm_num)
      (by norm_num) : Measure _).real (boxRestrict 2 1 ⁻¹' Set.univ))) :=
  fkgq_free_infinite_measure 1 (by norm_num) (by norm_num) (by norm_num) fun _ _ _ _ => trivial

-- Wired box measures of an increasing event of `Λ_1` converge along the full box sequence.
example : Tendsto (fun m => (wiredFiniteMeasure 2 m (p := 1 / 2) (q := 2) (by norm_num)
      (by norm_num) (by norm_num) : Measure _).real (boxRestrict 2 1 ⁻¹' Set.univ)) atTop
    (nhds ((wiredInfiniteVolume 2 (p := 1 / 2) (q := 2) (by norm_num) (by norm_num)
      (by norm_num) : Measure _).real (boxRestrict 2 1 ⁻¹' Set.univ))) :=
  fkgq_wired_infinite_measure 1 (by norm_num) (by norm_num) (by norm_num) fun _ _ _ _ => trivial

-- The box mass functions of the infinite-volume measures are nonnegative.
example (t : ℝ) (ω : ConfigSpace (Sym2 (boxVerts 2 1))) :
    0 ≤ fkgq_freeMass 2 1 2 (by norm_num) t ω ∧ 0 ≤ fkgq_wiredMass 2 1 2 (by norm_num) t ω :=
  ⟨measureReal_nonneg, measureReal_nonneg⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.FKGeneralQConsumer
