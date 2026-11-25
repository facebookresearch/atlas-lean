/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidCoverVertices

/-!
# The SAME original generating quiver over native free-groupoid paths

Cover vertices retain individual original endpoints and full native
paths from the SAME base vertex. A cover arrow is a full original
quiver generator whose actual append gives the specified target
path. The whole map to the original quiver retains that generator;
no completed inverse or arbitrary groupoid arrow is substituted.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)

/-- An actual original generating arrow and its whole native cover-path triangle. -/
structure CoverArrow (a b : CoverVertex V z) where
  /-- The SAME full original generating coefficient. -/
  arrow : a.target ⟶ b.target
  /-- Appending the original generator gives the SAME specified full target path. -/
  path_eq : a.path ≫ (Quiver.FreeGroupoid.of V).map arrow = b.path

/-- The actual original generating cover quiver, retaining each generator and its full path
equality. -/
@[instance_reducible]
def coverQuiver : Quiver.{v} (CoverVertex V z) where
  Hom := CoverArrow V z

/-- The full original cover quiver projection keeps the SAME individual objects and actual
generating arrows. -/
def coverProjection :
    letI := coverQuiver V z
    CoverVertex V z ⥤q V := by
  letI := coverQuiver V z
  exact { obj a := a.target, map f := f.arrow }

/-- Every SAME original generator has its actual native cover lift at every original full path. -/
def liftCoverArrow (a : CoverVertex V z) {y : V} (e : a.target ⟶ y) :
    CoverArrow V z a (CoverVertex.append V z a e) := ⟨e, rfl⟩

/-- The native original cover lift retains the SAME full original generator coefficient. -/
lemma liftCoverArrow_readback (a : CoverVertex V z) {y : V} (e : a.target ⟶ y) :
    (liftCoverArrow V z a e).arrow = e := rfl

/-- Full original cover arrows are determined by their SAME original generator coefficient. -/
lemma CoverArrow.ext_coefficient {a b : CoverVertex V z} (f g : CoverArrow V z a b)
    (h : f.arrow = g.arrow) : f = g := by
  cases f
  cases g
  cases h
  rfl

end Quiver.FreeGroupoid.OriginalWords
