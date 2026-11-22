/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeSupportedFaces
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeInjectedFaces
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeSupportedSubcomplex

/-!
# Genuine original right-cube face isomorphisms onto their supported ranges

The actual injected operator identifies its entire source cube with
the supported target subcomplex. Injectivity and the supported-suffix
preimage prove both whole inverse equations. Original cofaces are
therefore the same omitted-support inclusions, including the zero face.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightCubeFaceRangeIso
open RightCubeSupport RightCubeSupportOperators RightCubeSupportedFaces
  RightCubeInjectedFaces RightCubeSupportedSubcomplex RightCubeSupportBoundary
variable {n m : ℕ}

/-- The actual original quotient operator with values in its retained supported target range. -/
def rangeMap (θ : ⦋n⦌ ⟶ ⦋m⦌) : RightCubeRelations.object.{u} n ⟶ supported.{u} m (Set.range θ.toOrderHom) where
  app q := ↾fun a => ⟨(RightCubeCosimplicialMaps.map θ).app q a, by
    change quotientSupport ((RightCubeCosimplicialMaps.map θ).app q a) ⊆ Set.range θ.toOrderHom
    rw [quotientSupport_image]
    exact Set.image_subset_range _ _⟩
  naturality q r η := by
    ext a
    apply Subtype.ext
    exact congr($((RightCubeCosimplicialMaps.map θ).naturality η) a)

/-- The entire actual supported range map followed by inclusion is exactly the original quotient operator. -/
theorem rangeMap_inclusion (θ : ⦋n⦌ ⟶ ⦋m⦌) :
    rangeMap.{u} θ ≫ (supported m (Set.range θ.toOrderHom)).ι = RightCubeCosimplicialMaps.map θ := by ext q a; rfl

/-- The original supported-range map of a genuine injected operator is actually an isomorphism in every
  scalar degree. -/
theorem rangeMap_isIso (θ : ⦋n⦌ ⟶ ⦋m⦌) (hθ : Function.Injective θ.toOrderHom) : IsIso (rangeMap.{u} θ) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro q
  rw [isIso_iff_bijective]
  constructor
  · intro a b h
    exact app_injective θ hθ q (congrArg Subtype.val h)
  · intro b
    obtain ⟨a, ha⟩ := (map_range_iff_support θ hθ b.1).mpr b.2
    exact ⟨a, Subtype.ext ha⟩

/-- The genuine whole original cube isomorphism onto the supported range of the same supplied injected operator. -/
def rangeIso (θ : ⦋n⦌ ⟶ ⦋m⦌) (hθ : Function.Injective θ.toOrderHom) :
    RightCubeRelations.object.{u} n ≅ supported.{u} m (Set.range θ.toOrderHom) := by
  let : IsIso (rangeMap.{u} θ) := rangeMap_isIso θ hθ
  exact asIso (rangeMap θ)

/-- The actual original coface's supported range is precisely omission of its same original front label. -/
theorem coface_supported_eq (j : Fin (n + 2)) :
    supported.{u} (n + 1) (Set.range (SimplexCategory.δ j).toOrderHom) = missing (n + 1) j :=
  (congrArg (supported.{u} (n + 1)) (Fin.range_succAboveOrderEmb j)).trans
    (supported_compl_singleton (n + 1) j)

/-- The actual whole original coface cube isomorphism onto the same omitted-support target subcomplex. -/
def cofaceIso (j : Fin (n + 2)) : RightCubeRelations.object.{u} n ≅ missing.{u} (n + 1) j :=
  rangeIso (SimplexCategory.δ j) (Fin.succAboveOrderEmb j).injective ≪≫
    SSet.Subcomplex.eqToIso (coface_supported_eq j)

/-- The entire genuine coface isomorphism followed by its original target inclusion reads the same original
  quotient coface map. -/
theorem cofaceIso_inclusion (j : Fin (n + 2)) :
    (cofaceIso.{u} j).hom ≫ (missing (n + 1) j).ι = RightCubeCosimplicialMaps.map (SimplexCategory.δ j) :=
  (Category.assoc (rangeIso (SimplexCategory.δ j) (Fin.succAboveOrderEmb j).injective).hom
    (SSet.Subcomplex.eqToIso (coface_supported_eq j)).hom (missing (n + 1) j).ι).trans
    ((congrArg (fun f => (rangeIso (SimplexCategory.δ j) (Fin.succAboveOrderEmb j).injective).hom ≫ f)
      (SSet.Subcomplex.homOfLE_ι (coface_supported_eq j).le)).trans (rangeMap_inclusion (SimplexCategory.δ j)))

end CategoryTheory.CoherentRealization.RightCubeFaceRangeIso
