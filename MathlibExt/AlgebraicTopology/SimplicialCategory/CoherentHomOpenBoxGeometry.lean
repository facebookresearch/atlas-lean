/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
/-
The geometric definitions are factored from:
https://github.com/facebookresearch/atlas-lean/blob/73d538abe769683f30cd004b2f85f6b3b1d9297c/MathlibExt/AlgebraicTopology/SimplicialCategory/CoherentHomOpenBox.lean
-/
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentCubeBoundary

/-!
# The geometric inclusion of a coherent Hom open box

The distinguished-coordinate scalar box maps into the interval-subset Hom nerve
through the interval-cube isomorphism. Its range is kept on that same Hom object.
The geometric construction is separate from its intrinsic horn-path description.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory Opposite HomotopicalAlgebra
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HomOpenBox
open MappingCube CubeBoxes CubeBoundary

/-- The actual range inclusion of a monomorphic anodyne map is itself anodyne by its genuine
domain isomorphism. -/
theorem range_anodyne {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (hf : SSet.anodyneExtensions f) :
    SSet.anodyneExtensions (SSet.Subcomplex.range f).ι := by
  have e : CategoryTheory.Arrow.mk f ≅ CategoryTheory.Arrow.mk (SSet.Subcomplex.range f).ι :=
    CategoryTheory.Arrow.isoMk (asIso (SSet.Subcomplex.toRange f)) (Iso.refl _) (by simp)
  exact (SSet.anodyneExtensions.arrow_mk_iso_iff e).mp hf

private instance {I : Type u} (k : I) : Mono (boxι k (boundary (Remaining k))) := by
  change Mono ((OpenBox.upper (boundary (Remaining k))).ι ≫ (splitIso k).inv)
  infer_instance

/-- The intrinsic original cube upper-box inclusion is an actual scalar anodyne map. -/
theorem upperBox_anodyne {I : Type u} (k : I) : SSet.anodyneExtensions (upperBox k).ι :=
  range_anodyne _ (boxι_anodyne k (boundary (Remaining k)))

variable {J : Type u} [LinearOrder J] {i j : J}

/-- The actual box domain with the original strict interior labels of the supplied coherent
Hom interval. -/
abbrev domain (k : IntervalHom.Interior i j) : SSet.{u} :=
  boxDomain k (boundary (Remaining k))

/-- The actual coherent Hom open-box map through the inverse of the proved interval-cube
isomorphism. -/
def ι (hij : i ≤ j) (k : IntervalHom.Interior i j) : domain k ⟶ nerve
  (SimplicialThickening.Path i j) :=
  boxι k (boundary (Remaining k)) ≫ (intervalCubeIso hij).inv

private instance (hij : i ≤ j) (k : IntervalHom.Interior i j) : Mono (ι hij k) := by
  change Mono (boxι k (boundary (Remaining k)) ≫ (intervalCubeIso hij).inv)
  infer_instance

/-- This actual coherent Hom box map is anodyne by genuine scalar geometry and the proved
Hom isomorphism. -/
theorem ι_anodyne (hij : i ≤ j) (k : IntervalHom.Interior i j) : SSet.anodyneExtensions (ι hij k) :=
  MorphismProperty.comp_mem SSet.anodyneExtensions _ _ (boxι_anodyne k (boundary (Remaining k)))
    (SSet.anodyneExtensions.of_isIso _)

/-- The actual original coherent Hom box as a subcomplex of its literal interval-subset nerve. -/
def subcomplex (hij : i ≤ j) (k : IntervalHom.Interior i j) :
    (nerve (SimplicialThickening.Path i j)).Subcomplex := SSet.Subcomplex.range (ι hij k)

end CategoryTheory.CoherentRealization.HomOpenBox
