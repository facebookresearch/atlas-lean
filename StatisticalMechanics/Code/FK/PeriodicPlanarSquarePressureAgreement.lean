/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarStrictNoCoexistenceClosure
import Code.FrontierD.FKQgt4SquareBufferedIdentification










open MeasureTheory Set

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.FK StatMech.FK.PeriodicPlanar BeffaraDC

noncomputable section




theorem fkSquarePeriodic_freeWiredIncreasingCylinderAgreementOffCountableAtLogistic
    (q : Real) (hq : 1 <= q) :
    square.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q := by
  intro n
  let r := square.bufferedRadius n
  let E := fkSquarePeriodicConfigEquiv r
  apply (fkgq_countable_free_wired_disagreement (d := 2) (by omega) r q hq).mono
  intro t ht
  obtain ⟨S, hS, hne⟩ := ht
  refine ⟨E ⁻¹' S, ?_, ?_⟩
  · intro omega eta home homega
    exact hS (fkSquarePeriodicConfigEquiv_monotone r home) homega
  · intro heq
    apply hne
    have hq0 : 0 < q := zero_lt_one.trans_le hq
    unfold PeriodicGraph.freeBufferedCylinderProbability
      PeriodicGraph.wiredBufferedCylinderProbability
    rw [dif_pos ⟨⟨fsc_logistic_pos t, fsc_logistic_lt_one t⟩, hq0⟩,
      dif_pos ⟨⟨fsc_logistic_pos t, fsc_logistic_lt_one t⟩, hq0⟩,
      fkSquarePeriodic_freeBufferedInfiniteVolume_eq
        (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq,
      fkSquarePeriodic_wiredBufferedInfiniteVolume_eq
        (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq,
      fkSquarePeriodic_bufferedCylinder_eq_boxCylinder]
    rw [fkgq_eventMass_free, fkgq_eventMass_wired] at heq
    exact heq


theorem fkSquarePeriodic_freeWiredIncreasingCylinderAgreementOffCountable
    (q : Real) (hq : 1 <= q) :
    square.FreeWiredIncreasingCylinderAgreementOffCountable q :=
  square.freeWiredIncreasingCylinderAgreementOffCountable_of_logistic
    (fkSquarePeriodic_freeWiredIncreasingCylinderAgreementOffCountableAtLogistic q hq)

end

end StatMech.FrontierD
