/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Code.Universality.CrossingReflection
import Code.Universality.DualEventSetEquality
import Code.Universality.G3PercDualityFull

open Set MeasureTheory ProbabilityTheory SimpleGraph
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice
open StatMech.RSW.Box













theorem r90_reindex_measurePreserving :
    MeasurePreserving (Equiv.piCongrLeft (fun _ => Bool) (crossEdge : Sym2 (Site 2) ≃ Sym2 (Site 2)))
      rba_selfDualMeasure rba_selfDualMeasure :=
  ⟨measurable_reindex, by
    rw [rba_selfDualMeasure]; exact map_reindex (2⁻¹ : ℝ≥0) half_le_one⟩






theorem r90_complement_measurePreserving :
    MeasurePreserving (fun (η : ConfigSpace (Sym2 (Site 2))) e => !(η e))
      rba_selfDualMeasure rba_selfDualMeasure :=
  ⟨measurable_complement, by
    rw [rba_selfDualMeasure, map_complement (2⁻¹ : ℝ≥0) half_le_one]
    congr 1
    exact one_sub_half_eq⟩


















theorem r90_dual_measurePreserving :
    MeasurePreserving (dualConfig : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2)))
      rba_selfDualMeasure rba_selfDualMeasure :=
  ⟨rba_measurable_dualConfig, by
    rw [rba_selfDualMeasure]; exact bernoulliProductMeasure_selfDual_half⟩






theorem r90_dual_eq_complement_comp_reindex :
    MeasurePreserving
      ((fun (η : ConfigSpace (Sym2 (Site 2))) e => !(η e))
        ∘ (Equiv.piCongrLeft (fun _ => Bool) (crossEdge : Sym2 (Site 2) ≃ Sym2 (Site 2))))
      rba_selfDualMeasure rba_selfDualMeasure :=
  r90_complement_measurePreserving.comp r90_reindex_measurePreserving
















theorem r90_negConfig_measurePreserving :
    MeasurePreserving (des_negConfig : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2)))
      rba_selfDualMeasure rba_selfDualMeasure := by
  have hfun : (des_negConfig : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2)))
      = (fun (η : ConfigSpace (Sym2 (Site 2))) e => !(η e)) := by
    funext ω e; rfl
  rw [hfun]; exact r90_complement_measurePreserving
























theorem r90_dualV_prob_eq (n : ℤ)
    (hmeasV : MeasurableSet (verticalCrossingEvent 0 n 0 n)) :
    rba_selfDualMeasure.real (dualVerticalCrossingEvent 0 n 0 n)
      = rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n) := by
  have hpre : dualVerticalCrossingEvent 0 n 0 n
      = dualConfig ⁻¹' verticalCrossingEvent 0 n 0 n := rfl
  rw [hpre, r90_dual_measurePreserving.measureReal_preimage hmeasV.nullMeasurableSet]













theorem r90_dualV_eq_primalH (n : ℤ)
    (hmeasV : MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n)) :
    rba_selfDualMeasure.real (dualVerticalCrossingEvent 0 n 0 n)
      = rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
  rw [r90_dualV_prob_eq n hmeasV,
    crf_verticalCrossing_eq_horizontal_swap 0 n 0 n hmeasH]

end Universality

end StatMech
