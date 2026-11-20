/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectCutSquareEmbedding










open MeasureTheory SimpleGraph StatMech.Lattice

namespace StatMech.FrontierD

noncomputable section



def FKRectPrimalUnexploredConnectionEvent
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration)
    (source target : FKRectPrimalUnexploredVertex R S eta) :
    Set (ConfigSpace
      (Sym2 (FKRectPrimalUnexploredVertex R S eta))) :=
  {omega |
    (FK.openSub (fkRectPrimalUnexploredInducedGraph R S eta) omega).Reachable
      source target}

theorem fkRectPrimalUnexploredConnectionEvent_isIncreasing
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration)
    (source target : FKRectPrimalUnexploredVertex R S eta) :
    IsIncreasing
      (FKRectPrimalUnexploredConnectionEvent R S eta source target) := by
  intro omega omega' homega hreach
  exact hreach.mono (FK.openSub_mono _ homega)



theorem fkRectPrimalUnexplored_connectionCylinder_subset_boxConnEvent
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration)
    (source target : FKRectPrimalUnexploredVertex R S eta) :
    FK.boxRestrict 2 (R.width + R.height) ⁻¹'
        (FK.ocd_innerRestrict
          (fkRectPrimalUnexploredBoxEmbedding R S eta) ⁻¹'
            FKRectPrimalUnexploredConnectionEvent R S eta source target) ⊆
      FK.boxConnEvent 2 (R.width + R.height)
        (fkRectPrimalUnexploredBoxEmbedding R S eta source)
        (fkRectPrimalUnexploredBoxEmbedding R S eta target) := by
  intro omega hreach
  exact fkRectPrimalUnexplored_reachable_box R S eta
    (FK.boxRestrict 2 (R.width + R.height) omega) hreach



theorem fkRectPrimalUnexploredConnection_freeMass_le_boxConn
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration)
    (source target : FKRectPrimalUnexploredVertex R S eta)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) :
    (∑ omega,
        (FKRectPrimalUnexploredConnectionEvent R S eta source target).indicator
            (fun _ => (1 : Real)) omega *
          FK.fkProb (fkRectPrimalUnexploredInducedGraph R S eta)
            p q omega) <=
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (FK.boxConnEvent 2 (R.width + R.height)
            (fkRectPrimalUnexploredBoxEmbedding R S eta source)
            (fkRectPrimalUnexploredBoxEmbedding R S eta target)) := by
  let mu : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq)
  let C := FK.boxRestrict 2 (R.width + R.height) ⁻¹'
    (FK.ocd_innerRestrict
      (fkRectPrimalUnexploredBoxEmbedding R S eta) ⁻¹'
        FKRectPrimalUnexploredConnectionEvent R S eta source target)
  have hdomain := fkRectPrimalUnexplored_freeEvent_le_freeInfinite
    R S eta hp hp1 hq
      (fkRectPrimalUnexploredConnectionEvent_isIncreasing
        R S eta source target)
  have hmono : mu.real C <=
      mu.real (FK.boxConnEvent 2 (R.width + R.height)
        (fkRectPrimalUnexploredBoxEmbedding R S eta source)
        (fkRectPrimalUnexploredBoxEmbedding R S eta target)) :=
    measureReal_mono
      (fkRectPrimalUnexplored_connectionCylinder_subset_boxConnEvent
        R S eta source target)
  exact hdomain.trans hmono

end

end StatMech.FrontierD
