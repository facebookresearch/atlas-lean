/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFilteredBergnerHomMonicity
import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
import Mathlib.CategoryTheory.Presentable.Finite

/-!
# Compact full original Hom maps factor through actual filtered C0 stages

The actual source-under tail cocone retains its same original Hom map.
Genuine finite scalar presentability factors a complete scalar map
through a whole actual later-stage Hom. Both original source images
and both true original cocone endpoint equations are retained.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.OriginalFilteredUnderHom

/-- A compact original scalar map factors through a same complete original Hom at an actual later tail stage. -/
theorem hom_factor {J : Type u} [Category.{u} J] [IsFiltered J]
    (F : J ⥤ Carrier.{u}) (s : Cocone F) (hs : IsColimit s)
    (hC : ∀ {i j : J} (f : i ⟶ j), Bergner.cofibrations (F.map f))
    (j : J) (x y : F.obj j) (K : SSet.{u}) [IsFinitelyPresentable.{u} K]
    (m : K ⟶ (s.ι.app j).obj x ⟶[SSet.{u}] (s.ι.app j).obj y) :
    ∃ (a : Under j)
      (n : K ⟶ (F.map a.hom).obj x ⟶[SSet.{u}] (F.map a.hom).obj y),
      n ≫ OriginalUnderHom.map (F.obj j) x y (coconeUnderMap F s j a) = m := by
  let U := sourceDiagram F j
  let c := sourceCocone F s j
  have hc : IsColimit ((OriginalUnderHom.functor (F.obj j) x y).mapCocone c) :=
    OriginalUnderHomColimit.originalIsColimit U c (sourceIsColimit F s j hs) x y
      (fun h => Bergner.cofibration_objects_injective _ (hC h.right))
  obtain ⟨a, n, hn⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc m
  exact ⟨a, n, hn⟩

end CategoryTheory.SimplicialEnrichment.OriginalFilteredUnderHom
