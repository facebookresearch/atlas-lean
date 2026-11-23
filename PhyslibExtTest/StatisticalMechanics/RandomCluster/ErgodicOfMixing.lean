/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.ErgodicOfMixing

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.FKMixingClose`

* the predicate `fmc_SelfMixing` holds for a translation-invariant probability measure: the point
  mass at the all-closed configuration of `ℤ²`, which is also translation invariant, so
  `fmc_isErgodic_of_selfMixing` applies to it;
* `fmc_wiredIV_isErgodic_of_mixing` is applied at `p = 1/2` on `ℤ²` with the self-mixing
  hypothesis as a variable (the hypothesis is true by Grimmett, Theorem 4.19, but is not proved
  here; the conclusion is proved unconditionally by `cbk_wiredIV_isErgodic`). This replaces the
  smoke check removed from the source file in stage 3.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.FKMixingClose

open MeasureTheory _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice
  _root_.StatMech.ConfigSpace

/-- The all-closed configuration of `ℤ²`. -/
def allClosed : ConfigSpace (Sym2 (Site 2)) := fun _ => false

/-- The all-closed configuration is fixed by every shift. -/
theorem shift_allClosed (g : Multiplicative (Site 2)) : shift g allClosed = allClosed := rfl

/-- The point mass at the all-closed configuration is translation invariant. -/
theorem dirac_isTranslationInvariant : IsTranslationInvariant (G := Multiplicative (Site 2))
    (Measure.dirac allClosed : Measure (ConfigSpace (Sym2 (Site 2)))) := fun g =>
  ⟨measurable_shift g, by rw [Measure.map_dirac' (measurable_shift g), shift_allClosed]⟩

/-- The point mass at the all-closed configuration is self-mixing. -/
theorem dirac_selfMixing : fmc_SelfMixing (G := Multiplicative (Site 2))
    (Measure.dirac allClosed : Measure (ConfigSpace (Sym2 (Site 2)))) := by
  intro A hA ε hε
  refine ⟨1, ?_⟩
  have hAm : MeasurableSet A := MeasurableSet.of_mem_measurableCylinders hA
  rw [shift_one, Set.preimage_id, Set.inter_self, Measure.real,
    Measure.dirac_apply' _ hAm]
  by_cases h : allClosed ∈ A <;> simp [h, hε]

-- `fmc_isErgodic_of_selfMixing` applies to the point mass.
example : IsErgodic (G := Multiplicative (Site 2))
    (Measure.dirac allClosed : Measure (ConfigSpace (Sym2 (Site 2)))) :=
  fmc_isErgodic_of_selfMixing dirac_isTranslationInvariant dirac_selfMixing

-- The headline lemma at `p = 1/2` on `ℤ²`, given self-mixing of the wired measure.
example (hmix : fmc_SelfMixing (G := Multiplicative (Site 2))
      (wiredInfiniteVolume 2 (p := 1 / 2) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site 2))))) :
    IsErgodic (G := Multiplicative (Site 2))
      (wiredInfiniteVolume 2 (p := 1 / 2) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site 2)))) :=
  fmc_wiredIV_isErgodic_of_mixing (by norm_num) (by norm_num) hmix

end PhyslibExtTest.StatisticalMechanics.RandomCluster.FKMixingClose
