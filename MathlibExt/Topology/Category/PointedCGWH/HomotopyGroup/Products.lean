/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Homotopy.HomotopyGroupProducts
import MathlibExt.Topology.Category.CGWH.Products
import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CompactlyGeneratedCoreflectionWeakHomotopy
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.TopCatHomotopyGroupInvariance
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# The original pointed CGWH product and its positive homotopy groups

The actual pointed product is compared with the native CGWH product fan.
Its comparison to the ordinary product is the proved weak compact-generation
counit, with all original points and projections retained. The entire
positive cube quotient then uses the actual product homotopy equivalence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace PointedCGWH.HomotopyProductGeometry

private theorem compactProduct_projection {ι : Type v} (X : ι → CompactlyGenerated.{u, v}) (i : ι) :
    CompactlyGenerated.piComparisonToTop X ≫
      (TopCat.piFan (fun j => CompactlyGenerated.compactlyGeneratedToTop.obj (X j))).π.app ⟨i⟩ =
        CompactlyGenerated.compactlyGeneratedToTop.map (CompactlyGenerated.piπ X i) := by
  let U := CompactlyGenerated.compactlyGeneratedToTop.{u, v}
  let p := (TopCat.piFan (fun j => U.obj (X j))).π.app ⟨i⟩
  have hCounit : CompactlyGenerated.adj.counit.app (U.obj (X i)) =
      U.map (asIso (CompactlyGenerated.adj.unit.app (X i))).inv := by
    apply (cancel_epi (U.map (CompactlyGenerated.adj.unit.app (X i)))).mp
    calc
      _ = 𝟙 _ := CompactlyGenerated.adj.left_triangle_components (X i)
      _ = U.map ((asIso (CompactlyGenerated.adj.unit.app (X i))).hom ≫
          (asIso (CompactlyGenerated.adj.unit.app (X i))).inv) :=
        (U.map_id (X i)).symm.trans
          (U.congr_map (Iso.hom_inv_id (asIso (CompactlyGenerated.adj.unit.app (X i))))).symm
      _ = _ := U.map_comp _ _
  exact (CompactlyGenerated.adj.counit.naturality p).symm.trans
    ((congrArg (fun m => U.map (TopCat.toCompactlyGenerated.map p) ≫ m) hCounit).trans
      (U.map_comp _ _).symm)

private theorem projectedMapOfEq {A B D : Type v}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace D]
    (f : C(A, B)) (g : C(B, D)) (r : C(A, D))
    {a : A} {b : B} {d : D} (hf : f a = b) (hg : g b = d) (hr : r a = d)
    (h : g.comp f = r) (k : ℕ) (z : HomotopyGroup.Pi (k + 1) A a) :
    HomotopyGroup.mapHomOfEq g hg k (HomotopyGroup.mapHomOfEq f hf k z) =
      HomotopyGroup.mapHomOfEq r hr k z := by
  cases h
  exact (HomotopyGroup.mapHomOfEq_comp f g hf hg hr k z).symm

private theorem mapOfEq_cast_back {A B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) {a : A} {b : B} (h : f a = b) (k : ℕ)
    (z : HomotopyGroup.Pi (k + 1) A a) :
    Eq.mp (congrArg (fun y => HomotopyGroup.Pi (k + 1) B y) h.symm)
      (HomotopyGroup.mapHomOfEq f h k z) = HomotopyGroup.map f z := by
  cases h
  rfl

private theorem nativeMapOfEq (k : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (z : PointedCGWH.piN (k + 1) X) :
    HomotopyGroup.mapHomOfEq (CGWH.cgwhToTop.map f.right).hom
      (PointedCGWH.underlyingBasepoint_naturality f) k z = PointedCGWH.piNMap (k + 1) f z := by
  let h := PointedCGWH.underlyingBasepoint_naturality f
  apply (Equiv.cast (congrArg (fun y => HomotopyGroup.Pi (k + 1)
    (CGWH.cgwhToTop.obj Y.right) y) h.symm)).injective
  have he := mapOfEq_cast_back (CGWH.cgwhToTop.map f.right).hom h k z
  exact he.trans (PointedCGWH.piNMap_apply (k + 1) f z).symm

variable {ι : Type v} (X : ι → PointedCGWH.{u, v})

/-- The native CGWH product has the whole original family of selected point maps. -/
def productPoint : CGWH.point.{u, v} ⟶ CGWH.piObj (fun i => (X i).right) :=
  (CGWH.piFanIsLimit (fun i => (X i).right)).lift (Fan.mk _ (fun i => (X i).hom))

/-- Every original selected point is retained by its native product projection. -/
theorem productPoint_projection (i : ι) :
    productPoint X ≫ CGWH.piπ (fun i => (X i).right) i = (X i).hom :=
  (CGWH.piFanIsLimit (fun i => (X i).right)).fac (Fan.mk _ (fun i => (X i).hom)) ⟨i⟩

/-- The explicit native product with its entire original family of selected points. -/
def productObject : PointedCGWH.{u, v} := Under.mk (productPoint X)

/-- The whole original pointed projection is the same native CGWH projection. -/
def projection (i : ι) : productObject X ⟶ X i :=
  Under.homMk (CGWH.piπ (fun i => (X i).right) i) (productPoint_projection X i)

/-- The full pointed product fan retains every original native projection. -/
def productFan : Fan X := Fan.mk (productObject X) (projection X)

private def underlyingFan (s : Fan X) : Fan (fun i => (X i).right) :=
  Fan.mk s.pt.right (fun i => (s.π.app ⟨i⟩).right)

private def underlyingLift (s : Fan X) : s.pt.right ⟶ CGWH.piObj (fun i => (X i).right) :=
  (CGWH.piFanIsLimit (fun i => (X i).right)).lift (underlyingFan X s)

private theorem underlyingLift_point (s : Fan X) :
    s.pt.hom ≫ underlyingLift X s = productPoint X := by
  apply (CGWH.piFanIsLimit (fun i => (X i).right)).hom_ext
  rintro ⟨i⟩
  exact (Category.assoc s.pt.hom (underlyingLift X s) (CGWH.piπ (fun i => (X i).right) i)).trans
    ((congrArg (fun m => s.pt.hom ≫ m)
      ((CGWH.piFanIsLimit (fun i => (X i).right)).fac (underlyingFan X s) ⟨i⟩)).trans
      ((Under.w (s.π.app ⟨i⟩)).trans (productPoint_projection X i).symm))

private def pointedLift (s : Fan X) : s.pt ⟶ productObject X :=
  Under.homMk (underlyingLift X s) (underlyingLift_point X s)

/-- The actual native product fan satisfies the complete pointed product universal property. -/
def productFanIsLimit : IsLimit (productFan X) where
  lift := pointedLift X
  fac s j := by
    apply Under.UnderMorphism.ext
    exact (CGWH.piFanIsLimit (fun i => (X i).right)).fac (underlyingFan X s) j
  uniq s m hm := by
    apply Under.UnderMorphism.ext
    apply (CGWH.piFanIsLimit (fun i => (X i).right)).uniq
      (underlyingFan X s) m.right
    intro j
    exact congrArg (fun f => f.right) (hm j)

/-- The chosen original pointed product is isomorphic to the explicit native product fan. -/
def productIso [HasProduct X] : (∏ᶜ X) ≅ productObject X :=
  (limit.isLimit (Discrete.functor X)).conePointUniqueUpToIso (productFanIsLimit X)

/-- Every actual pointed projection is unchanged by the chosen-product chart. -/
theorem productIso_projection [HasProduct X] (i : ι) :
    (productIso X).hom ≫ projection X i = Pi.π X i :=
  IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _) (productFanIsLimit X) ⟨i⟩

/-- The exact original native product comparison is the compact-generation counit on its right carrier. -/
def rawComparison : CGWH.cgwhToTop.obj (productObject X).right ⟶
    TopCat.of (∀ i, CGWH.cgwhToTop.obj (X i).right) :=
  CGWH.piComparisonToTop (fun i => (X i).right)

/-- The ordinary comparison and each native projection have the same entire original coordinate function. -/
theorem rawComparison_projection (z : CGWH.cgwhToTop.obj (productObject X).right) (i : ι) :
    rawComparison X z i = (CGWH.cgwhToTop.map (projection X i).right) z := by
  let z' : CGWH.piObj (fun i => (X i).right) := z
  let U := fun i => CGWH.cgwhToCompactlyGenerated.obj (X i).right
  have hp : CGWH.cgwhToCompactlyGenerated.map (CGWH.piπ (fun i => (X i).right) i) =
      CompactlyGenerated.piπ U i :=
    CGWH.fullyFaithfulCgwhToCompactlyGenerated.map_preimage _
  have h := ConcreteCategory.congr_hom (compactProduct_projection U i) z'
  have hproj := congrArg (fun f :
      CompactlyGenerated.piObj U ⟶ U i =>
        (CompactlyGenerated.compactlyGeneratedToTop.map f) z') hp
  exact h.trans hproj.symm

/-- The entire original selected point maps to the tuple of the original selected coordinate points. -/
theorem rawComparison_point :
    rawComparison X (PointedCGWH.underlyingBasepoint (productObject X)) =
      fun i => PointedCGWH.underlyingBasepoint (X i) := by
  funext i
  have h := PointedCGWH.underlyingBasepoint_naturality (projection X i)
  exact (rawComparison_projection X _ i).trans h

/-- The actual native-to-ordinary product comparison is weak without an ordinary product topology premise. -/
theorem rawComparison_weak : TopCat.weakHomotopyEquivalences (rawComparison X) :=
  CompactlyGenerated.adjCounit_mem_weakHomotopyEquivalences _

/-- The same actual compact-generation map compares the native positive group with the ordinary product group. -/
def rawPositiveEquiv (k : ℕ) :
    PointedCGWH.piN (k + 1) (productObject X) ≃*
      HomotopyGroup.Pi (k + 1) (∀ i, CGWH.cgwhToTop.obj (X i).right)
        (fun i => PointedCGWH.underlyingBasepoint (X i)) :=
  TopCat.piPositiveMulEquivOfWeakEquivalence k (rawComparison X)
    (PointedCGWH.underlyingBasepoint (productObject X))
    (fun i => PointedCGWH.underlyingBasepoint (X i))
    (rawComparison_point X) (rawComparison_weak X)

/-- The full positive homotopy group of the native pointed product is the original coordinate group family. -/
def positiveEquiv (k : ℕ) :
    PointedCGWH.piN (k + 1) (productObject X) ≃* ∀ i, PointedCGWH.piN (k + 1) (X i) :=
  (rawPositiveEquiv X k).trans
    (HomotopyGroup.ProductGeometry.mulEquiv (N := Fin (k + 1))
      (fun i => PointedCGWH.underlyingBasepoint (X i)))

/-- Each positive coordinate of the full product Iso is the same original pointed projection map. -/
theorem positiveEquiv_projection (k : ℕ) (z : PointedCGWH.piN (k + 1) (productObject X)) (i : ι) :
    positiveEquiv X k z i = PointedCGWH.piNMap (k + 1) (projection X i) z := by
  let c : C(CGWH.cgwhToTop.obj (productObject X).right,
      ∀ j, CGWH.cgwhToTop.obj (X j).right) := (rawComparison X).hom
  let p : C(CGWH.cgwhToTop.obj (productObject X).right, CGWH.cgwhToTop.obj (X i).right) :=
    (CGWH.cgwhToTop.map (projection X i).right).hom
  have h : (ContinuousMap.eval i).comp c = p := by
    ext a
    exact rawComparison_projection X a i
  have hm := projectedMapOfEq c (ContinuousMap.eval i) p
    (rawComparison_point X) rfl (PointedCGWH.underlyingBasepoint_naturality (projection X i)) h k z
  exact hm.trans (nativeMapOfEq k (projection X i) z)

/-- The whole selected-product comparison uses the original positive projection group maps. -/
def selectedComparison [HasProduct X] (k : ℕ) :
    (PointedCGWH.piNPositiveFunctor k).obj (∏ᶜ X) ⟶
      GrpCat.of (∀ i, (PointedCGWH.piNPositiveFunctor k).obj (X i)) :=
  GrpCat.ofHom {
    toFun := fun z i => ((PointedCGWH.piNPositiveFunctor k).map (Pi.π X i)).hom z
    map_one' := by funext i; exact map_one _
    map_mul' := by intro a b; funext i; exact map_mul _ _ _ }

/-- Both original group functions of the selected product are retained by the complete native chart. -/
def selectedEquiv [HasProduct X] (k : ℕ) :
    PointedCGWH.piN (k + 1) (∏ᶜ X) ≃* ∀ i, PointedCGWH.piN (k + 1) (X i) :=
  (((PointedCGWH.piNPositiveFunctor k).mapIso (productIso X)).groupIsoToMulEquiv).trans
    (positiveEquiv X k)

/-- The actual selected-product group equivalence has the identical original projection function. -/
theorem selectedEquiv_projection [HasProduct X] (k : ℕ)
    (z : PointedCGWH.piN (k + 1) (∏ᶜ X)) (i : ι) :
    selectedEquiv X k z i = ((PointedCGWH.piNPositiveFunctor k).map (Pi.π X i)).hom z := by
  let a : PointedCGWH.piN (k + 1) (productObject X) :=
    ((PointedCGWH.piNPositiveFunctor k).map (productIso X).hom).hom z
  have h := positiveEquiv_projection X k a i
  have hm := ConcreteCategory.congr_hom
    ((PointedCGWH.piNPositiveFunctor k).map_comp (productIso X).hom (projection X i)) z
  exact h.trans ((PointedCGWH.piNPositiveMap_apply k (projection X i) a).symm.trans
    (hm.symm.trans (ConcreteCategory.congr_hom
      ((PointedCGWH.piNPositiveFunctor k).congr_map (productIso_projection X i)) z)))

/-- The actual complete finite or arbitrary selected-product comparison is a genuine group isomorphism. -/
def selectedComparisonIso [HasProduct X] (k : ℕ) :
    (PointedCGWH.piNPositiveFunctor k).obj (∏ᶜ X) ≅
      GrpCat.of (∀ i, (PointedCGWH.piNPositiveFunctor k).obj (X i)) :=
  (selectedEquiv X k).toGrpIso

/-- Its entire forward morphism is the unchanged original projection group comparison. -/
theorem selectedComparisonIso_hom [HasProduct X] (k : ℕ) :
    (selectedComparisonIso X k).hom = selectedComparison X k := by
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro z
  funext i
  exact selectedEquiv_projection X k z i

/-- Every whole family of pointed maps acts on the original positive quotient coordinates. -/
def coordinateMap {X Y : ι → PointedCGWH.{u, v}} (f : ∀ i, X i ⟶ Y i) (k : ℕ) :
    GrpCat.of (∀ i, (PointedCGWH.piNPositiveFunctor k).obj (X i)) ⟶
      GrpCat.of (∀ i, (PointedCGWH.piNPositiveFunctor k).obj (Y i)) :=
  GrpCat.ofHom {
    toFun := fun z i => ((PointedCGWH.piNPositiveFunctor k).map (f i)).hom (z i)
    map_one' := by funext i; exact map_one _
    map_mul' := by intro a b; funext i; exact map_mul _ _ _ }

/-- The whole original selected-product comparison is natural in every actual coordinate map. -/
theorem selectedComparison_naturality {X Y : ι → PointedCGWH.{u, v}}
    [HasProduct X] [HasProduct Y] (f : ∀ i, X i ⟶ Y i) (k : ℕ) :
    (PointedCGWH.piNPositiveFunctor k).map (CategoryTheory.Limits.Pi.map f) ≫ selectedComparison Y k =
      selectedComparison X k ≫ coordinateMap f k := by
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro z
  funext i
  have h := (PointedCGWH.piNPositiveFunctor k).congr_map (CategoryTheory.Limits.Pi.map_π f i)
  have hm := (PointedCGWH.piNPositiveFunctor k).map_comp (CategoryTheory.Limits.Pi.map f) (Pi.π Y i)
  have hn := (PointedCGWH.piNPositiveFunctor k).map_comp (Pi.π X i) (f i)
  exact (ConcreteCategory.congr_hom hm z).symm.trans
    ((ConcreteCategory.congr_hom h z).trans (ConcreteCategory.congr_hom hn z))

end PointedCGWH.HomotopyProductGeometry
