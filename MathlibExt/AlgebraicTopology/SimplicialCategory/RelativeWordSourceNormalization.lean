/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordNormalizedSourceChange

/-!
# Original normalization and whole source-word comparison commute

Every original raw letter is retained under source change. Its actual
attaching-domain normalization therefore commutes with the SAME whole
enriched source map, by the original generator and composition equations.
Every normalized layer and boundary keeps the exact original scalar maps.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
open RelativeWords
variable {O : Type u} {C D : FixedObjects O}

/-- The SAME full original normalization commutes with actual raw and enriched source changes. -/
theorem sourceChange_normalize (T : Data C) (F : C ⟶ D) (q : SimplexCategoryᵒᵖ)
    {a b : O} (p : RawWordAt T q a b) :
    normalizeAt (sourceChange T F) q (rawSourceChange T F q p) =
      (homMap (sourceChangeMap T F) a b).app q (normalizeAt T q p) := by
  induction p with
  | @old a b h =>
    exact (sourceChangeMap_old T F q h).symm
  | @cons a x y b h e p ih =>
    have hletter :
        (homMap (sourceChangeMap T F) x y).app q (letter T q e) =
          letter (sourceChange T F) q e :=
      congrArg (fun k => k.app q e) (newHom_sourceChangeMap T F x y)
    have hold :
        (homMap (sourceChangeMap T F) a x).app q (oldWord T q h) =
          oldWord (sourceChange T F) q ((homMap F a x).app q h) :=
      sourceChangeMap_old T F q h
    have hcomp {i j k : O} (p : WordAt T q i j) (r : WordAt T q j k) :
        (homMap (sourceChangeMap T F) i k).app q (compWords T q p r) =
          compWords (sourceChange T F) q ((homMap (sourceChangeMap T F) i j).app q p)
            ((homMap (sourceChangeMap T F) j k).app q r) :=
      congrArg (fun h => h.app q (p, r)) (compositionMap_homMap (sourceChangeMap T F) i j k)
    have hraw := rawSourceChange_cons T F q h e p
    have htarget := @normalizeAt_cons O D (sourceChange T F) q a x y b
      ((homMap F a x).app q h) e (rawSourceChange T F q p)
    have hsource := @normalizeAt_cons O C T q a x y b h e p
    have houter := hcomp (oldWord T q h) (compWords T q (letter T q e) (normalizeAt T q p))
    have hinner := hcomp (letter T q e) (normalizeAt T q p)
    have hright := (congrArg (fun p => (homMap (sourceChangeMap T F) a b).app q p) hsource).trans
      (houter.trans ((congrArg (fun p => compWords (sourceChange T F) q
        ((homMap (sourceChangeMap T F) a x).app q (oldWord T q h)) p) hinner).trans
          (congrArg₂ (fun old v => compWords (sourceChange T F) q old
            (compWords (sourceChange T F) q v
              ((homMap (sourceChangeMap T F) y b).app q (normalizeAt T q p)))) hold hletter)))
    exact (congrArg (normalizeAt (sourceChange T F) q) hraw).trans
      (htarget.trans ((congrArg (fun p => compWords (sourceChange T F) q
        (oldWord (sourceChange T F) q ((homMap F a x).app q h))
        (compWords (sourceChange T F) q (letter (sourceChange T F) q e) p)) ih).trans hright.symm))


end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
