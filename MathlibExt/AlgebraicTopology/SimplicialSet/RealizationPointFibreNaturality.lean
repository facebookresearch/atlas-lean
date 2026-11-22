/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPointFibre
import MathlibExt.AlgebraicTopology.SimplicialSet.SharpWeakCospanComparison

/-!
# The original point-fibre comparison under a changing base

The full simplicial pullback map realizes to the actual strict point-fibre
map of the same square. Its endpoint is the image of the original point.
Sharpness and weak total and base maps derive weakness of that actual map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet

/-- The entire original point pullback after the prescribed simplicial base map. -/
def pointFibreMap {X B X' B' : SSet.{u}} (p : X ⟶ B) (q : X' ⟶ B')
    (s : X ⟶ X') (h : B ⟶ B') (hsq : p ≫ h = s ≫ q)
    (b : (Δ[0] : SSet.{u}) ⟶ B) : pullback p b ⟶ pullback q (b ≫ h) :=
  pullback.map p b q (b ≫ h) s (𝟙 _) h hsq (by simp)

/-- The original image point pullback realizes over the actual image of the selected point. -/
def realizationPointFibreImageIsPullback {X B B' : SSet.{u}}
    (q : X ⟶ B') (b : (Δ[0] : SSet.{u}) ⟶ B) (h : B ⟶ B') :
    IsPullback (SSet.toTop.map (pullback.fst q (b ≫ h)))
      (SSet.toTop.map (pullback.snd q (b ≫ h)) ≫ realizedZeroIso.hom)
      (SSet.toTop.map q) (TopCat.const (SSet.toTop.map h (realizedPoint b))) := by
  simpa only [realizedPoint_comp] using isPullback_realizationPointFibre q (b ≫ h)

/-- The whole image-fibre isomorphism uses the same image point as the topological square. -/
def realizationPointFibreImageIso {X B B' : SSet.{u}}
    (q : X ⟶ B') (b : (Δ[0] : SSet.{u}) ⟶ B) (h : B ⟶ B') :
    SSet.toTop.obj (pullback q (b ≫ h)) ≅
      pullback (SSet.toTop.map q)
        (TopCat.const (X := TopCat.of PUnit) (SSet.toTop.map h (realizedPoint b))) :=
  (realizationPointFibreImageIsPullback q b h).isoPullback

/-- The actual image-fibre isomorphism retains the complete original total-space leg. -/
@[reassoc]
theorem realizationPointFibreImageIso_fst {X B B' : SSet.{u}}
    (q : X ⟶ B') (b : (Δ[0] : SSet.{u}) ⟶ B) (h : B ⟶ B') :
    (realizationPointFibreImageIso q b h).hom ≫ pullback.fst _ _ =
      SSet.toTop.map (pullback.fst q (b ≫ h)) :=
  (realizationPointFibreImageIsPullback q b h).isoPullback_hom_fst

/-- The original simplicial square realizes to the literal topological square. -/
theorem toTop_pointFibre_square {X B X' B' : SSet.{u}}
    (p : X ⟶ B) (q : X' ⟶ B') (s : X ⟶ X') (h : B ⟶ B')
    (hsq : p ≫ h = s ≫ q) :
    SSet.toTop.map p ≫ SSet.toTop.map h = SSet.toTop.map s ≫ SSet.toTop.map q := by
  rw [← Functor.map_comp, ← Functor.map_comp, hsq]

/-- Both whole fibre isomorphisms intertwine the same original strict-fibre map. -/
theorem pointFibreMap_realization_naturality {X B X' B' : SSet.{u}}
    (p : X ⟶ B) (q : X' ⟶ B') (s : X ⟶ X') (h : B ⟶ B')
    (hsq : p ≫ h = s ≫ q) (b : (Δ[0] : SSet.{u}) ⟶ B) :
    SSet.toTop.map (pointFibreMap p q s h hsq b) ≫
        (realizationPointFibreImageIso q b h).hom =
      (realizationPointFibreIso p b).hom ≫
        TopCat.strictFiberMapOfSquare (SSet.toTop.map s) (SSet.toTop.map h)
          (toTop_pointFibre_square p q s h hsq) (realizedPoint b) := by
  apply pullback.hom_ext
  · rw [Category.assoc, realizationPointFibreImageIso_fst,
      Category.assoc, TopCat.strictFiberMapOfSquare_fst,
      ← Category.assoc, realizationPointFibreIso_fst]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    simp [pointFibreMap, pullback.map]
  · exact TopCat.isTerminalPUnit.hom_ext _ _

/-- Sharp original maps and weak total and base maps make the actual topological strict-fibre map weak. -/
theorem strictFiberMap_realization_weak {X B X' B' : SSet.{u}}
    (p : X ⟶ B) (q : X' ⟶ B') (s : X ⟶ X') (h : B ⟶ B')
    (hsq : p ≫ h = s ≫ q) (b : (Δ[0] : SSet.{u}) ⟶ B)
    (hs : WeakEquivalence s) (hh : WeakEquivalence h)
    (hp : SharpComparisonDraft.Sharp p) (hq : SharpComparisonDraft.Sharp q) :
    TopCat.weakHomotopyEquivalences
      (TopCat.strictFiberMapOfSquare (SSet.toTop.map s) (SSet.toTop.map h)
        (toTop_pointFibre_square p q s h hsq) (realizedPoint b)) := by
  have hf : WeakEquivalence (pointFibreMap p q s h hsq b) :=
    SharpComparisonDraft.pullbackMap_weak p b q (b ≫ h) s (𝟙 _) h hsq
      (by simp) hs (by infer_instance) hh hp hq
  have hfTop : TopCat.weakHomotopyEquivalences
      (SSet.toTop.map (pointFibreMap p q s h hsq b)) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mp hf
  have hc := TopCat.weakHomotopyEquivalences.comp_mem _ _ hfTop
    (TopCat.weakHomotopyEquivalences.of_isIso (realizationPointFibreImageIso q b h).hom)
  rw [pointFibreMap_realization_naturality] at hc
  exact TopCat.weakHomotopyEquivalences.of_precomp _ _
    (TopCat.weakHomotopyEquivalences.of_isIso (realizationPointFibreIso p b).hom) hc

end SSet
