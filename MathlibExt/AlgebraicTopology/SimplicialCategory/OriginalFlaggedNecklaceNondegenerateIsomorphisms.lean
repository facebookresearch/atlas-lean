/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklacePairedLift

/-!
# Genuine isomorphisms between original nondegenerate flagged inputs

An actual map between two genuinely flanked totally nondegenerate
original inputs is an isomorphism. Its inverse is the SAME original
paired-surjection lift, with both complete native maps and full original
input and flag equations retained.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The SAME actual original paired-surjection inverse of a nondegenerate flagged map. -/
def totallyNondegenerateMapInverse {T U : Object K x y q} (f : T ⟶ U)
    (hT : IsFlanked T) (hU : IsFlanked U) (hNT : TotallyNondegenerate T) : U ⟶ T :=
  pairedLift (𝟙 T) f hT hT hU hNT

/-- The inverse retains its SAME complete original map readback on the original source. -/
theorem totallyNondegenerateMap_hom_inv {T U : Object K x y q} (f : T ⟶ U)
    (hT : IsFlanked T) (hU : IsFlanked U) (hNT : TotallyNondegenerate T) :
    f ≫ totallyNondegenerateMapInverse f hT hU hNT = 𝟙 T :=
  pairedLift_factor (𝟙 T) f hT hT hU hNT

/-- The inverse retains its SAME complete original map readback on the original target. -/
theorem totallyNondegenerateMap_inv_hom {T U : Object K x y q} (f : T ⟶ U)
    (hT : IsFlanked T) (hU : IsFlanked U) (hNT : TotallyNondegenerate T) (hNU : TotallyNondegenerate U) :
    totallyNondegenerateMapInverse f hT hU hNT ≫ f = 𝟙 U :=
  totallyNondegenerate_map_unique _ _ hU hU hNU

/-- BOTH SAME original full maps form the genuine isomorphism of nondegenerate flagged inputs. -/
def totallyNondegenerateMapIso {T U : Object K x y q} (f : T ⟶ U)
    (hT : IsFlanked T) (hU : IsFlanked U) (hNT : TotallyNondegenerate T) (hNU : TotallyNondegenerate U) : T ≅ U where
  hom := f
  inv := totallyNondegenerateMapInverse f hT hU hNT
  hom_inv_id := totallyNondegenerateMap_hom_inv f hT hU hNT
  inv_hom_id := totallyNondegenerateMap_inv_hom f hT hU hNT hNU

/-- The genuine nondegenerate-object isomorphism retains the SAME original forward morphism. -/
theorem totallyNondegenerateMapIso_hom {T U : Object K x y q} (f : T ⟶ U)
    (hT : IsFlanked T) (hU : IsFlanked U) (hNT : TotallyNondegenerate T) (hNU : TotallyNondegenerate U) :
    (totallyNondegenerateMapIso f hT hU hNT hNU).hom = f := rfl

/-- The SAME actual original nondegenerate flagged map is genuinely invertible. -/
theorem totallyNondegenerate_map_isIso {T U : Object K x y q} (f : T ⟶ U)
    (hT : IsFlanked T) (hU : IsFlanked U) (hNT : TotallyNondegenerate T) (hNU : TotallyNondegenerate U) : IsIso f :=
  (totallyNondegenerateMapIso f hT hU hNT hNU).isIso_hom

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
