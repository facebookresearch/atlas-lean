/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Mathlib

open Filter Topology

namespace StatMech.Ising





theorem antitone_cylinderWidthLimit_of_diagonal
    (a : Nat -> Nat -> Real) (m : Nat -> Real) (M : Real)
    (hwidth : forall H, Antitone (fun L => a L H))
    (hheight : forall L, Antitone (a L))
    (hrow : forall L, Tendsto (a L) atTop (nhds (m L)))
    (hdiag : Tendsto (fun L => a L L) atTop (nhds M)) :
    Tendsto m atTop (nhds M) := by
  have hlower : forall L, M <= m L := by
    intro L
    apply le_of_tendsto_of_tendsto hdiag (hrow L)
    filter_upwards [eventually_ge_atTop L] with H hHL
    exact hwidth H hHL
  have hupper : forall L, m L <= a L L := by
    intro L
    apply le_of_tendsto (hrow L)
    filter_upwards [eventually_ge_atTop L] with H hLH
    exact hheight L hLH
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hdiag hlower hupper


theorem monotone_cylinderWidthLimit_of_diagonal
    (a : Nat -> Nat -> Real) (m : Nat -> Real) (M : Real)
    (hwidth : forall H, Monotone (fun L => a L H))
    (hheight : forall L, Monotone (a L))
    (hrow : forall L, Tendsto (a L) atTop (nhds (m L)))
    (hdiag : Tendsto (fun L => a L L) atTop (nhds M)) :
    Tendsto m atTop (nhds M) := by
  have hnegWidth : forall H, Antitone (fun L => -a L H) := by
    intro H L K hLK
    exact neg_le_neg (hwidth H hLK)
  have hnegHeight : forall L, Antitone (fun H => -a L H) := by
    intro L H K hHK
    exact neg_le_neg (hheight L hHK)
  have hnegRow : forall L,
      Tendsto (fun H => -a L H) atTop (nhds (-m L)) :=
    fun L => (hrow L).neg
  have hnegDiag : Tendsto (fun L => -a L L) atTop (nhds (-M)) :=
    hdiag.neg
  have h := antitone_cylinderWidthLimit_of_diagonal
    (fun L H => -a L H) (fun L => -m L) (-M)
    hnegWidth hnegHeight hnegRow hnegDiag
  simpa using h.neg

end StatMech.Ising
