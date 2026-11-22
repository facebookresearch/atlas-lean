/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeRelations
import MathlibExt.CategoryTheory.NerveHomotopy

/-!
# Actual original full-path contraction data of the right cube

Every original source-to-last path is included in its actual full
interval path. This gives a genuine natural transformation and nerve
homotopy. Descent of that homotopy through the original front-composition
quotient must be proved from its defining relations.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightCubeFullPath
open PathLastMaximum
variable {n : ℕ}

/-- The original full interval path from a supplied front vertex to the original last target. -/
def fullPath (i : Fin (n + 1)) : LastPath.{u} i where
  I := Set.Ici (ULift.up.{u} i.castSucc)
  left := by change ULift.up.{u} i.castSucc ≤ ULift.up i.castSucc; exact le_rfl
  right := Fin.le_last i.castSucc
  left_le _ hi := hi
  le_right k _ := Fin.le_last k.down

/-- Every original last path is contained in the same full interval at its supplied original front source. -/
theorem path_le_full (i : Fin (n + 1)) (p : LastPath.{u} i) : p.I ⊆ (fullPath i).I :=
  by
    intro k hk
    change ULift.up.{u} i.castSucc ≤ k
    exact p.left_le k hk

/-- The actual original natural inclusion into the constant full interval path. -/
def inclusion (i : Fin (n + 1)) : 𝟭 (LastPath.{u} i) ⟶ (Functor.const (LastPath.{u} i)).obj (fullPath i) where
  app p := ⟨homOfLE (path_le_full i p)⟩
  naturality p q f := by
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

/-- The actual whole original nerve homotopy toward the full interval path. -/
def homotopy (i : Fin (n + 1)) : SSet.Homotopy (𝟙 (nerve (LastPath.{u} i)))
    (nerveMap ((Functor.const (LastPath.{u} i)).obj (fullPath i))) := by
  have H := NatTrans.nerveHomotopy (inclusion.{u} i)
  simpa only [nerveMap_id] using H

/-- The actual full-path inclusion preserves the entire original starting path at the zero cylinder endpoint. -/
theorem homotopy_zero (i : Fin (n + 1)) : SSet.ι₀ ≫ (homotopy.{u} i).h = 𝟙 (nerve (LastPath.{u} i)) :=
  SSet.Homotopy.h₀ _

/-- The actual full-path inclusion has the full original interval at the one cylinder endpoint. -/
theorem homotopy_one (i : Fin (n + 1)) : SSet.ι₁ ≫ (homotopy.{u} i).h =
    nerveMap ((Functor.const (LastPath.{u} i)).obj (fullPath i)) := SSet.Homotopy.h₁ _

end CategoryTheory.CoherentRealization.RightCubeFullPath
