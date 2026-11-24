/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectFreeMonadEquivalence
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Actual full Hom isomorphisms detect the original fixed-label isomorphism

The SAME original whole-Hom functor is the forgetful functor of the
proved canonical free-path algebra comparison. The genuine comparison
and native algebra forgetful functor reflect isomorphisms. Thus every
original full Hom map being an isomorphism detects the original full
enriched map, with every original object label unchanged.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects
open FixedObjectFree
variable {O : Type u} {C D : FixedObjects O}

/-- Every SAME whole original fixed-label map is an isomorphism when all its actual full Hom
maps are. -/
theorem isIso_of_homMap (f : C ⟶ D) (h : ∀ x y : O, IsIso (homMap f x y)) : IsIso f := by
  let _ : (comparison (O := O)).IsEquivalence := comparison_isEquivalence (O := O)
  let _ : IsIso ((pathMonad O).forget.map ((comparison (O := O)).map f)) :=
    (isIso_pi_iff _).mpr (fun p => h p.1 p.2)
  let _ : IsIso ((comparison (O := O)).map f) :=
    isIso_of_reflects_iso ((comparison (O := O)).map f) (pathMonad O).forget
  exact isIso_of_reflects_iso f (comparison (O := O))

end CategoryTheory.SimplicialEnrichment.FixedObjects
