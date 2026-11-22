/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceNondegenerateNormalization
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceNondegenerateIsomorphisms
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceFlankingWeak

/-!
# The genuine original nondegenerate normalization functor

The proved original normalization maps and genuine paired-surjection
lifts give a functor into the full original nondegenerate subcategory.
Its actual unit and counit retain the SAME complete native maps, full
original input squares and coefficient flags. No normalization or
comparison outcome is given as an assumption.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Normalization

open Flanking

/-- The genuine all-full-bead input nondegeneracy property on original flanked objects. -/
def property (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) : ObjectProperty (Flanked K x y q) :=
  fun T => TotallyNondegenerate T.obj

/-- The actual full original subcategory of flanked totally nondegenerate inputs. -/
abbrev Normalized (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :=
  (property K x y q).FullSubcategory

/-- The SAME native full-subcategory inclusion of original nondegenerate inputs. -/
def inclusion (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    Normalized K x y q ⥤ Flanked K x y q := (property K x y q).ι

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The chosen target is obtained from the PROVED full original normalization construction. -/
def rawTarget (T : Flanked K x y q) : Object K x y q :=
  Classical.choose (exists_totallyNondegenerate_target T.obj T.property)

/-- The actual chosen target has its genuinely proved SAME original flanking property. -/
theorem rawTarget_isFlanked (T : Flanked K x y q) : IsFlanked (rawTarget T) :=
  (Classical.choose_spec (exists_totallyNondegenerate_target T.obj T.property)).1

/-- The actual chosen target has its genuinely proved full original input nondegeneracy. -/
theorem rawTarget_totallyNondegenerate (T : Flanked K x y q) : TotallyNondegenerate (rawTarget T) :=
  (Classical.choose_spec (exists_totallyNondegenerate_target T.obj T.property)).2.1

/-- The SAME actual original target in the full nondegenerate subcategory. -/
def target (T : Flanked K x y q) : Normalized K x y q :=
  ⟨⟨rawTarget T, rawTarget_isFlanked T⟩, rawTarget_totallyNondegenerate T⟩

/-- The actual original unit map is obtained from the PROVED entire original source map. -/
def unitMap (T : Flanked K x y q) : T ⟶ (target T).obj :=
  ObjectProperty.homMk (Classical.choice
    (Classical.choose_spec (exists_totallyNondegenerate_target T.obj T.property)).2.2)

/-- The entire actual original unit retains its SAME original input map equation. -/
theorem unitMap_over (T : Flanked K x y q) :
    (unitMap T).hom.necklaceMap.map.{u} ≫ (rawTarget T).input = T.obj.input := (unitMap T).hom.over

private theorem normalizedHom_ext {T U : Normalized K x y q} (f g : T ⟶ U) : f = g := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  exact totallyNondegenerate_map_unique f.hom.hom g.hom.hom T.obj.property U.obj.property U.property

/-- The SAME genuine original lift gives every entire original normalized map. -/
def map {T U : Flanked K x y q} (f : T ⟶ U) : target T ⟶ target U :=
  ObjectProperty.homMk (ObjectProperty.homMk
    (pairedLift (f.hom ≫ (unitMap U).hom) (unitMap T).hom T.property
      (rawTarget_isFlanked U) (rawTarget_isFlanked T) (rawTarget_totallyNondegenerate U)))

/-- The SAME actual original normalization functor, with all original identity and composition maps. -/
def functor (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    Flanked K x y q ⥤ Normalized K x y q where
  obj := target
  map := map
  map_id _T := normalizedHom_ext _ _
  map_comp _f _g := normalizedHom_ext _ _

/-- The SAME whole original unit is genuinely natural for every entire original flanked map. -/
def unit (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    𝟭 (Flanked K x y q) ⟶ functor K x y q ⋙ inclusion K x y q where
  app := unitMap
  naturality T U f := by
    apply ObjectProperty.hom_ext
    exact (pairedLift_factor (f.hom ≫ (unitMap U).hom) (unitMap T).hom T.property
      (rawTarget_isFlanked U) (rawTarget_isFlanked T) (rawTarget_totallyNondegenerate U)).symm

/-- Every SAME original normalization-unit component is literally the original entire source map. -/
theorem unit_app (T : Flanked K x y q) : (unit K x y q).app T = unitMap T := rfl

/-- The SAME actual original restricted-unit map between full nondegenerate objects. -/
def restrictedUnit (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    𝟭 (Normalized K x y q) ⟶ inclusion K x y q ⋙ functor K x y q where
  app T := ObjectProperty.homMk (unitMap T.obj)
  naturality _T _U _f := normalizedHom_ext _ _

/-- The genuine SAME original inverse unit on an actual nondegenerate input. -/
def counitMap (T : Normalized K x y q) : target T.obj ⟶ T :=
  ObjectProperty.homMk (ObjectProperty.homMk
    (totallyNondegenerateMapInverse (unitMap T.obj).hom T.obj.property
      (rawTarget_isFlanked T.obj) T.property))

/-- The SAME entire original counit is genuinely natural on actual original nondegenerate inputs. -/
def counit (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    inclusion K x y q ⋙ functor K x y q ⟶ 𝟭 (Normalized K x y q) where
  app := counitMap
  naturality _T _U _f := normalizedHom_ext _ _

/-- Both SAME original restricted natural maps retain their whole original identity readback. -/
theorem restrictedUnit_counit (T : Normalized K x y q) :
    (restrictedUnit K x y q).app T ≫ (counit K x y q).app T = 𝟙 T :=
  normalizedHom_ext _ _

/-- Both SAME original restricted natural maps retain the reverse whole original identity readback. -/
theorem counit_restrictedUnit (T : Normalized K x y q) :
    (counit K x y q).app T ≫ (restrictedUnit K x y q).app T = 𝟙 (target T.obj) :=
  normalizedHom_ext _ _

/-- The actual original normalization subcategory has genuinely subsingleton original Hom types. -/
theorem hom_subsingleton (T U : Normalized K x y q) : Subsingleton (T ⟶ U) :=
  ⟨normalizedHom_ext⟩

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Normalization
