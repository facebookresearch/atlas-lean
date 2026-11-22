/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverCellSmallObject
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MonoLifting

/-!
# The original marked slice monomorphism right class

The actual existing monomorphism WFS transfers to the original marked
slice. Its right-class equality identifies slice right lifting with
underlying marked right lifting. The latter retains the original
simplicial boundary lifting and actual mark reflection. No marked weak
class or model recognition is assumed.
-/

noncomputable section
universe u
open CategoryTheory MorphismProperty

namespace SSet.Marked

/-- The original marked slice monomorphism right class is exactly underlying original marked monomorphism
  right lifting. -/
theorem over_monomorphisms_rlp_iff {B : SSet.{u}} {X Y : Over (max B)} (f : X ⟶ Y) :
    (monomorphisms (Over (max B))).rlp f ↔ (monomorphisms Marked.{u}).rlp f.left := by
  let _ : IsWeakFactorizationSystem (monomorphisms Marked.{u}) (monomorphisms Marked.{u}).rlp :=
    mono_isWeakFactorizationSystem
  have h := IsWeakFactorizationSystem.over (monomorphisms Marked.{u})
    (monomorphisms Marked.{u}).rlp (max B)
  have hm : (monomorphisms Marked.{u}).inverseImage (Over.forget (max B)) = monomorphisms (Over (max B)) := by
    ext U V g
    constructor
    · intro hg
      let _ : Mono g.left := hg
      exact Over.mono_of_mono_left g
    · intro hg
      let _ : Mono g := hg
      exact Over.mono_left_of_mono g
  rw [hm] at h
  exact (congrArg (fun W => W f) h.rlp).to_iff

end SSet.Marked
