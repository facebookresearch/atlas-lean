/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Lattice.JordanExteriorClosure



open SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice
open StatMech.RSW.Box



theorem fkRectFaithful_bottomTop_leftRight_support_intersects
    (alpha beta lower upper bottomX topX : Int)
    (hAlphaBeta : alpha < beta) (hLowerUpper : lower <= upper)
    (hBottomLeft : alpha <= bottomX) (hBottomRight : bottomX <= beta)
    (hTopLeft : alpha <= topX) (hTopRight : topX <= beta)
    (V : (hypercubicLattice 2).Walk
      ![bottomX, lower] ![topX, upper])
    (hVBox : ∀ z ∈ V.support, z ∈ rect alpha beta lower upper)
    {x y : Site 2}
    (hx : x ∈ rect alpha beta lower upper)
    (hy : y ∈ rect alpha beta lower upper)
    (hxLeft : x 0 = alpha) (hyRight : y 0 = beta)
    (W : (hypercubicLattice 2).Walk x y)
    (hWBox : ∀ z ∈ W.support, z ∈ rect alpha beta lower upper) :
    ∃ z, z ∈ W.support ∧ z ∈ V.support := by
  have hsep : ArcSeparatingSet
      {z : Site 2 | z ∈ V.support} alpha beta lower upper :=
    jec_arcSeparatingSet alpha beta lower upper bottomX topX
      hAlphaBeta hLowerUpper hBottomLeft hBottomRight hTopLeft hTopRight
      V hVBox {z : Site 2 | z ∈ V.support} (by
        intro z hz
        exact hz)
  obtain ⟨z, hzW, hzV⟩ :=
    tpc_two_paths_cross_of_sep hsep hx hy hxLeft hyRight W hWBox
  exact ⟨z, hzW, hzV⟩

end StatMech.FrontierD
