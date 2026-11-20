/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TwoPointInfinite
import Code.FK.TwoPointPositiveFull









open MeasureTheory SimpleGraph

namespace StatMech.FK

noncomputable section

open StatMech.Lattice



theorem boxConnEvent_subset_connected (d n : Nat)
    (x y : boxVerts d n) :
    boxConnEvent d n x y ⊆
      {omega | StatMech.Lattice.Connected d omega x.1 y.1} := by
  intro omega hreach
  let f : openSub (boxGraph d n) (boxRestrict d n omega) →g
      openSubgraph d omega :=
    { toFun := Subtype.val
      map_rel' := fun {u v} huv => by
        refine ⟨huv.1, ?_⟩
        simpa [boxRestrict, edgeIncl] using huv.2 }
  exact hreach.map f



theorem measureReal_boxConnEvent_le_infiniteTwoPointReal
    (d n : Nat)
    (mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (x y : boxVerts d n) :
    (mu : Measure (ConfigSpace (Sym2 (Site d)))).real
        (boxConnEvent d n x y) ≤
      infiniteTwoPointReal
        (mu : Measure (ConfigSpace (Sym2 (Site d)))) x.1 y.1 := by
  exact measureReal_mono (boxConnEvent_subset_connected d n x y)

end

end StatMech.FK
