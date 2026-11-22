/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Quiver.Path.Vertices

/-!
# Length of a relabeled native quiver path

Relabeling keeps the length of the whole native path. Source and target
object and Hom universes remain independent. This is the existing
`Quiver.Path.mapPath_length` theorem, extracted from PathCutNaturality
without changing its statement or proof.
-/

@[expose] public section

universe u v u' v'

namespace Quiver.Path

variable {V : Type u} [Quiver.{v} V] {W : Type u'} [Quiver.{v'} W]

/-- Every original prefunctor retains the length of the whole native path. -/
lemma mapPath_length (F : V ⥤q W) {x y : V} (p : Path x y) :
    (F.mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p a ih => exact congrArg Nat.succ ih

end Quiver.Path
