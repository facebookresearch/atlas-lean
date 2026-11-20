/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldBoundaryGrid









open Filter MeasureTheory Set Topology

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}



theorem PeriodicPlaneEmbedding.rectLeftConnection_tangential_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (z : Nat → Site 2) (hz : ∀ n, z n 0 = 0)
    (a b c d b' c' d' : Nat → Real) (S : Nat → Set V)
    (hb : ∀ n, b n + (z n 0 : Real) ≤ b' n)
    (hc : ∀ n, c' n ≤ c n + (z n 1 : Real))
    (hd : ∀ n, d n + (z n 1 : Real) ≤ d' n)
    (hlimit : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) (S n)
        (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n))))
      atTop (nhds 1)) :
    Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (a n) (b' n) (c' n) (d' n)
        (P.shift (z n) '' S n)
        (E.rectLeftBoundaryVertices (a n) (b' n) (c' n) (d' n))))
      atTop (nhds 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlimit tendsto_const_nhds
  · intro n
    exact E.rectLeftConnection_tangential_measureReal_le
      mu hTI (z n) (hz n) (a n) (b n) (c n) (d n)
        (b' n) (c' n) (d' n) (S n) (hb n) (hc n) (hd n)
  · intro n
    exact measureReal_le_one



theorem PeriodicPlaneEmbedding.rectRightConnection_tangential_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (z : Nat → Site 2) (hz : ∀ n, z n 0 = 0)
    (a b c d a' c' d' : Nat → Real) (S : Nat → Set V)
    (ha : ∀ n, a' n ≤ a n + (z n 0 : Real))
    (hc : ∀ n, c' n ≤ c n + (z n 1 : Real))
    (hd : ∀ n, d n + (z n 1 : Real) ≤ d' n)
    (hlimit : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) (S n)
        (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n))))
      atTop (nhds 1)) :
    Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (a' n) (b n) (c' n) (d' n)
        (P.shift (z n) '' S n)
        (E.rectRightBoundaryVertices (a' n) (b n) (c' n) (d' n))))
      atTop (nhds 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlimit tendsto_const_nhds
  · intro n
    exact E.rectRightConnection_tangential_measureReal_le
      mu hTI (z n) (hz n) (a n) (b n) (c n) (d n)
        (a' n) (c' n) (d' n) (S n) (ha n) (hc n) (hd n)
  · intro n
    exact measureReal_le_one



theorem PeriodicPlaneEmbedding.rectBottomConnection_tangential_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (z : Nat → Site 2) (hz : ∀ n, z n 1 = 0)
    (a b c d a' b' d' : Nat → Real) (S : Nat → Set V)
    (ha : ∀ n, a' n ≤ a n + (z n 0 : Real))
    (hb : ∀ n, b n + (z n 0 : Real) ≤ b' n)
    (hd : ∀ n, d n + (z n 1 : Real) ≤ d' n)
    (hlimit : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) (S n)
        (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n))))
      atTop (nhds 1)) :
    Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (a' n) (b' n) (c n) (d' n)
        (P.shift (z n) '' S n)
        (E.rectBottomBoundaryVertices (a' n) (b' n) (c n) (d' n))))
      atTop (nhds 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlimit tendsto_const_nhds
  · intro n
    exact E.rectBottomConnection_tangential_measureReal_le
      mu hTI (z n) (hz n) (a n) (b n) (c n) (d n)
        (a' n) (b' n) (d' n) (S n) (ha n) (hb n) (hd n)
  · intro n
    exact measureReal_le_one



theorem PeriodicPlaneEmbedding.rectTopConnection_tangential_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (z : Nat → Site 2) (hz : ∀ n, z n 1 = 0)
    (a b c d a' b' c' : Nat → Real) (S : Nat → Set V)
    (ha : ∀ n, a' n ≤ a n + (z n 0 : Real))
    (hb : ∀ n, b n + (z n 0 : Real) ≤ b' n)
    (hc : ∀ n, c' n ≤ c n + (z n 1 : Real))
    (hlimit : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) (S n)
        (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n))))
      atTop (nhds 1)) :
    Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (a' n) (b' n) (c' n) (d n)
        (P.shift (z n) '' S n)
        (E.rectTopBoundaryVertices (a' n) (b' n) (c' n) (d n))))
      atTop (nhds 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlimit tendsto_const_nhds
  · intro n
    exact E.rectTopConnection_tangential_measureReal_le
      mu hTI (z n) (hz n) (a n) (b n) (c n) (d n)
        (a' n) (b' n) (c' n) (S n) (ha n) (hb n) (hc n)
  · intro n
    exact measureReal_le_one

end StatMech.FK.PeriodicPlanar
