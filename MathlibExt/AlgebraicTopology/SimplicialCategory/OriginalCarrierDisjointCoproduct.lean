/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.SimplicialDisjointSumFunctors
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierSmallColimits

/-!
# The SAME original disjoint-sum enrichment is the genuine carrier coproduct

The two original object families and every complete Hom are retained by
the actual disjoint-sum enrichment. Its whole original enriched functor
bijection gives the genuine binary-coproduct universal property. The
comparison to any original carrier coproduct fixes both actual full
family inclusions, including empty families and coincident image objects.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.DisjointCoproduct
attribute [local instance] SSet.DisjointSum.enrichment

/-- The actual disjoint sum of both SAME original carrier object and Hom families. -/
def object (C D : Carrier.{u}) : Carrier.{u} := of (C ⊕ D)

/-- Include the SAME whole original left enriched family with every original Hom map unchanged. -/
def inl (C D : Carrier.{u}) : C ⟶ object C D := SSet.DisjointSum.inl C D

/-- Include the SAME whole original right enriched family with every original Hom map unchanged. -/
def inr (C D : Carrier.{u}) : D ⟶ object C D := SSet.DisjointSum.inr C D

/-- The complete original sum descender evaluates both original whole enriched maps. -/
def desc {C D E : Carrier.{u}} (F : C ⟶ E) (G : D ⟶ E) : object C D ⟶ E :=
  SSet.DisjointSum.desc F G

/-- The SAME whole original left enriched map is retained by the actual descender. -/
theorem inl_desc {C D E : Carrier.{u}} (F : C ⟶ E) (G : D ⟶ E) :
    inl C D ≫ desc F G = F := SSet.DisjointSum.inl_desc F G

/-- The SAME whole original right enriched map is retained by the actual descender. -/
theorem inr_desc {C D E : Carrier.{u}} (F : C ⟶ E) (G : D ⟶ E) :
    inr C D ≫ desc F G = G := SSet.DisjointSum.inr_desc F G

/-- Every original whole carrier sum map is determined by its SAME two actual enriched restrictions. -/
theorem desc_unique {C D E : Carrier.{u}} (F : C ⟶ E) (G : D ⟶ E) (H : object C D ⟶ E)
    (hF : inl C D ≫ H = F) (hG : inr C D ≫ H = G) : H = desc F G :=
  SSet.DisjointSum.desc_unique F G H hF hG

/-- The actual original full disjoint-sum coproduct cocone. -/
def cofan (C D : Carrier.{u}) : BinaryCofan C D := BinaryCofan.mk (inl C D) (inr C D)

/-- Both original full disjoint enriched families have the genuine carrier coproduct universal property. -/
def isColimit (C D : Carrier.{u}) : IsColimit (cofan C D) :=
  BinaryCofan.IsColimit.mk _ (fun F G => desc F G)
    (fun F G => inl_desc F G) (fun F G => inr_desc F G)
    (fun F G m hF hG => desc_unique F G m hF hG)

/-- Compare the SAME original complete disjoint sum with any supplied genuine original coproduct. -/
def comparison (C D : Carrier.{u}) (s : BinaryCofan C D) (hs : IsColimit s) :
    object C D ≅ s.pt := IsColimit.coconePointUniqueUpToIso (isColimit C D) hs

/-- The comparison retains the SAME whole original left coproduct inclusion. -/
theorem inl_comparison (C D : Carrier.{u}) (s : BinaryCofan C D) (hs : IsColimit s) :
    inl C D ≫ (comparison C D s hs).hom = s.inl :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (isColimit C D) hs ⟨WalkingPair.left⟩

/-- The comparison retains the SAME whole original right coproduct inclusion. -/
theorem inr_comparison (C D : Carrier.{u}) (s : BinaryCofan C D) (hs : IsColimit s) :
    inr C D ≫ (comparison C D s hs).hom = s.inr :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (isColimit C D) hs ⟨WalkingPair.right⟩

/-- The SAME original left full Hom coefficient is retained literally under the actual disjoint inclusion. -/
theorem inl_hom (C D : Carrier.{u}) (x y : C) : (inl C D).map x y = 𝟙 (x ⟶[SSet.{u}] y) := rfl

/-- The SAME original right full Hom coefficient is retained literally under the actual disjoint inclusion. -/
theorem inr_hom (C D : Carrier.{u}) (x y : D) : (inr C D).map x y = 𝟙 (x ⟶[SSet.{u}] y) := rfl

end CategoryTheory.SimplicialEnrichment.DisjointCoproduct
