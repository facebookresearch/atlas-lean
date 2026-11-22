/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.LoopSpaceBasedPositive
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.LoopConnectingHomotopy

/-!
# Weak equivalences of loops and based positive homotopy

The existing based-path fibration proves that positive homotopy bijections
at the chosen basepoint make the entire strict loop map weak. Conversely,
the original connecting equivalences and their full naturality recover
each based positive homotopy map from a weak loop map. The degree-zero
loop homotopy type is retained in this reverse implication.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe v
open CategoryTheory Simplicial
open scoped Simplicial

namespace SSet.OriginalAllLoopPointGeometry
open SSet.LoopShiftOriginalGeometry

/-- The original entire loop-map weak class is exactly detected by based positive maps. -/
theorem loopMap_W_iff_base {X Y : SSet.{v}} [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    KanComplex.W (loopSpaceMap f h) ↔
      ∀ n : ℕ, Function.Bijective (KanComplex.π.map f h (n + 1)) := by
  constructor
  · intro hw n
    let e := loopConnectingEquiv n X x
    let t := loopConnectingEquiv n Y y
    have hLoop : ∀ (z : loopSpace X x _⦋0⦌) (w : loopSpace Y y _⦋0⦌)
        (p : (loopSpaceMap f h).app _ z = w),
        Function.Bijective (KanComplex.π.map (loopSpaceMap f h) p n) := by
      intro z w p
      subst w
      exact hw.bijective_piMap n z
    have hc := (hLoop (originalLoopPoint X x) (originalLoopPoint Y y)
      (loopSpaceMap_app_point f h)).comp e.bijective
    have hn := loopConnectingEquiv_naturality_function f h n
    have ht : Function.Bijective (t ∘ KanComplex.π.map f h (n + 1)) := hn ▸ hc
    exact (Function.Bijective.of_comp_iff' t.bijective _).mp ht
  · exact loopSpaceMap_mem_W_of_based_positive f h

end SSet.OriginalAllLoopPointGeometry
