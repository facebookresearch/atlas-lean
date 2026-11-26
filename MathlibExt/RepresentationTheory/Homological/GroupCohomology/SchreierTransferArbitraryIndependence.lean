/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferInducedBar
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierCorestrictionH3
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferArbitraryLowDegree
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferArbitraryEquiv
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferArbitraryTransitivity

/-!
# Canonical Schreier corestriction in every degree

For a finite-index subgroup H ≤ G and a G-representation A over a commutative ring, the
universal maps from the G-bar resolution to the induced H-bar resolution associated to two
right transversals lift the same norm map and are chain homotopic. The induction adjunction
and bar-to-inhomogeneous comparisons identify their induced Hom-cochain maps with the explicit
Schreier transfers. Their cohomology maps therefore agree in every degree.

This defines canonical corestriction Hⁿ(H,A|H) → Hⁿ(G,A), computed by every right transversal.
It is natural in coefficients and under group equivalences, is transitive in finite-index
subgroup towers, and satisfies corestriction after restriction = [G:H] times the identity. Its
first three degrees recover the low-degree corestriction maps.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable (H : Subgroup G) [H.FiniteIndex]

-- Expanding the explicit induction adjunction across arbitrary bar degrees
-- requires normalization of nested coinvariant maps.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The induction-adjunction isomorphism of bar Hom-cochain complexes.

For A a G-representation, the degreewise adjunction Hom_H(B_H,A|H) ≃ Hom_G(ind B_H,A)
assembles into an isomorphism of linear Yoneda cochain complexes. -/
noncomputable def inducedBarLinearYonedaIso (A : Rep k G) :
    (Rep.barResolution k H).complex.linearYonedaObj k
        (Rep.res H.subtype A) ≅
      (inducedBarResolution (k := k) H).complex.linearYonedaObj k A :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦
      (Rep.indResHomEquiv H.subtype
        ((Rep.barResolution k H).complex.X n) A).symm.toModuleIso)
    (fun i j hij ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      change (Rep.indFunctor.{u} k H.subtype).map
          ((Rep.barResolution k H).complex.d j i) ≫
            (Rep.indResHomEquiv H.subtype
              ((Rep.barResolution k H).complex.X i) A).symm f =
        (Rep.indResHomEquiv H.subtype
          ((Rep.barResolution k H).complex.X j) A).symm
            ((Rep.barResolution k H).complex.d j i ≫ f)
      symm
      ext
      simp [Rep.indMap, Rep.indResHomEquiv])

/-- Subgroup cochains as Hom-cochains on the induced bar.

The inhomogeneous complex C*(H,A|H) is isomorphic to the ambient linear Hom-cochain complex
Hom_G(ind B_H,A), by the bar comparison and the induction adjunction. -/
noncomputable def subgroupInhomogeneousInducedBarIso (A : Rep k G) :
    inhomogeneousCochains (Rep.res H.subtype A) ≅
      (HomologicalComplex.linearHomCochainComplexFunctor
        k (Rep k G) A).obj
          (Opposite.op (inducedBarResolution (k := k) H).complex) :=
  inhomogeneousCochainsIso (Rep.res H.subtype A) ≪≫
    barResolutionLinearYonedaIso (Rep.res H.subtype A) ≪≫
    inducedBarLinearYonedaIso H A ≪≫
    (linearHomCochainComplexObjIso A
      (inducedBarResolution (k := k) H).complex).symm

/-- The Hom-cochain map induced by the universal bar transfer.

Precomposition with the chosen-transversal chain map B_G → ind B_H gives a cochain map
Hom_G(ind B_H,A) → Hom_G(B_G,A). -/
noncomputable def schreierTransferInducedBarCochains
    (A : Rep k G) (T : H.RightTransversal) :
    (HomologicalComplex.linearHomCochainComplexFunctor
      k (Rep k G) A).obj
        (Opposite.op (inducedBarResolution (k := k) H).complex) ⟶
      (HomologicalComplex.linearHomCochainComplexFunctor
        k (Rep k G) A).obj
          (Opposite.op (Rep.barResolution k G).complex) :=
  (HomologicalComplex.linearHomCochainComplexFunctor
    k (Rep k G) A).map
      (schreierTransferInducedBar (k := k) H T).op

/-- Degreewise precomposition with the induced-bar transfer.

For φ : (ind B_H)ₙ → A, the degree-n Hom-cochain transfer is the composite of the universal
transfer component B_G,ₙ → (ind B_H)ₙ with φ. -/
theorem schreierTransferInducedBarCochains_f_apply
    (A : Rep k G) (T : H.RightTransversal) (n : ℕ)
    (phi : (inducedBarResolution (k := k) H).complex.X n ⟶ A) :
    ((schreierTransferInducedBarCochains H A T).f n).hom phi =
      (schreierTransferInducedBar (k := k) H T).f n ≫ phi :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The explicit Schreier map agrees with universal bar precomposition.

Under the source and target bar-to-inhomogeneous comparison isomorphisms, the explicit chosen-
transversal cochain map equals precomposition with the universal induced-bar transfer. -/
theorem corestrictionCochains_comp_inducedBarComparison
    (A : Rep k G) (T : H.RightTransversal) :
    corestrictionCochains A T ≫
        (inhomogeneousResolutionLinearHomCochainIso A).hom =
      (subgroupInhomogeneousInducedBarIso H A).hom ≫
        schreierTransferInducedBarCochains H A T := by
  ext n z
  change Rep.freeLift k G A (corestrictionCochain A T n z) =
    schreierTransferInducedBarComponent (k := k) H T n ≫
      (Rep.indResHomEquiv H.subtype
        ((Rep.barComplex k H).X n) A).symm
          (Rep.freeLift k H (Rep.res H.subtype A) z)
  exact (schreierTransferInducedBarComponent_comp_adjointFreeLift
    H A T n z).symm

set_option backward.isDefEq.respectTransparency false in
/-- The induced cohomology map is independent of the transversal.

For any right transversals T and U and every degree n, the homology maps of their explicit
Schreier cochain maps are equal. -/
theorem homologyMap_corestrictionCochains_eq
    (A : Rep k G) (T U : H.RightTransversal) (n : ℕ) :
    HomologicalComplex.homologyMap (corestrictionCochains A T) n =
      HomologicalComplex.homologyMap (corestrictionCochains A U) n := by
  let eS := subgroupInhomogeneousInducedBarIso H A
  let eT := inhomogeneousResolutionLinearHomCochainIso A
  let bT := schreierTransferInducedBarCochains H A T
  let bU := schreierTransferInducedBarCochains H A U
  have hSquareT : corestrictionCochains A T ≫ eT.hom =
      eS.hom ≫ bT :=
    corestrictionCochains_comp_inducedBarComparison H A T
  have hSquareU : corestrictionCochains A U ≫ eT.hom =
      eS.hom ≫ bU :=
    corestrictionCochains_comp_inducedBarComparison H A U
  have hBar : HomologicalComplex.homologyMap bT n =
      HomologicalComplex.homologyMap bU n :=
    ((schreierTransferInducedBarHomotopy (k := k) H T U
      ).mapLinearHomCochainComplex k A).homologyMap_eq n
  apply (cancel_mono (HomologicalComplex.homologyMap eT.hom n)).mp
  calc
    HomologicalComplex.homologyMap (corestrictionCochains A T) n ≫
        HomologicalComplex.homologyMap eT.hom n =
      HomologicalComplex.homologyMap
        (corestrictionCochains A T ≫ eT.hom) n := by
      rw [HomologicalComplex.homologyMap_comp]
    _ = HomologicalComplex.homologyMap (eS.hom ≫ bT) n := by
      rw [hSquareT]
    _ = HomologicalComplex.homologyMap eS.hom n ≫
        HomologicalComplex.homologyMap bT n := by
      rw [HomologicalComplex.homologyMap_comp]
    _ = HomologicalComplex.homologyMap eS.hom n ≫
        HomologicalComplex.homologyMap bU n := by rw [hBar]
    _ = HomologicalComplex.homologyMap (eS.hom ≫ bU) n := by
      rw [HomologicalComplex.homologyMap_comp]
    _ = HomologicalComplex.homologyMap
        (corestrictionCochains A U ≫ eT.hom) n := by
      rw [hSquareU]
    _ = HomologicalComplex.homologyMap (corestrictionCochains A U) n ≫
        HomologicalComplex.homologyMap eT.hom n := by
      rw [HomologicalComplex.homologyMap_comp]

/-- Equality of arbitrary-degree transfers from different transversals.

For all T,U and n, corestrictionOfRightTransversal A T n equals
corestrictionOfRightTransversal A U n. -/
theorem corestrictionOfRightTransversal_eq
    (A : Rep k G) (T U : H.RightTransversal) (n : ℕ) :
    corestrictionOfRightTransversal A T n =
      corestrictionOfRightTransversal A U n := by
  exact homologyMap_corestrictionCochains_eq H A T U n

/-- Canonical arbitrary-degree corestriction.

The common map induced by a right-transversal Schreier transfer defines Hⁿ(H,A|H) → Hⁿ(G,A)
for every n ≥ 0. -/
noncomputable def schreierCorestriction
    (A : Rep k G) (n : ℕ) :
    groupCohomology (Rep.res H.subtype A) n ⟶
      groupCohomology A n :=
  corestrictionOfRightTransversal A default n

/-- Every right transversal computes canonical corestriction.

For any finite right transversal T, the canonical degree-n corestriction equals
corestrictionOfRightTransversal A T n. -/
theorem schreierCorestriction_eq_of_rightTransversal
    (A : Rep k G) (T : H.RightTransversal) (n : ℕ) :
    schreierCorestriction H A n =
      corestrictionOfRightTransversal A T n := by
  exact corestrictionOfRightTransversal_eq H A default T n

/-- Canonical corestriction preserves the zero class.

For every n, canonical corestriction sends 0 in Hⁿ(H,A|H) to 0 in Hⁿ(G,A). -/
@[simp]
theorem schreierCorestriction_zero
    (A : Rep k G) (n : ℕ) :
    schreierCorestriction H A n 0 = 0 :=
  map_zero _

/-- Coefficient naturality of canonical corestriction.

For a G-equivariant linear map φ : A → B, corestriction for A followed by Hⁿ(G,φ) equals
Hⁿ(H,φ|H) followed by corestriction for B. -/
theorem schreierCorestriction_naturality
    {A B : Rep k G} (phi : A ⟶ B) (n : ℕ) :
    schreierCorestriction H A n ≫
        groupCohomology.map (MonoidHom.id G) phi n =
      groupCohomology.map (MonoidHom.id H)
          ((Rep.resFunctor H.subtype).map phi) n ≫
        schreierCorestriction H B n := by
  exact corestrictionOfRightTransversal_naturality phi default n

/-- Canonical corestriction as a coefficient natural transformation.

In degree n, the canonical maps are natural from the restricted H-cohomology functor to the
G-cohomology functor on G-representations. -/
noncomputable def schreierCorestrictionNatTrans (n : ℕ) :
    Rep.resFunctor H.subtype ⋙ groupCohomology.functor k H n ⟶
      groupCohomology.functor k G n where
  app A := schreierCorestriction H A n
  naturality {_A _B} phi :=
    (schreierCorestriction_naturality H phi n).symm

/-- Canonical corestriction commutes with group equivalences.

For e : G ≃* G′, pullback along e after corestriction from e(H) to G′ equals corestriction
from H to G after subgroup pullback along H ≃* e(H), with the specified coefficient
comparison. -/
theorem schreierCorestriction_mulEquiv
    {G' : Type u} [Group G'] (e : G ≃* G')
    (A : Rep k G') (n : ℕ) :
    letI : (H.map e.toMonoidHom).FiniteIndex :=
      Subgroup.FiniteIndex.map_of_surjective H e.surjective
    schreierCorestriction (H.map e.toMonoidHom) A n ≫
        groupCohomology.map e.toMonoidHom
          (𝟙 (Rep.res e.toMonoidHom A)) n =
      groupCohomology.map
          (H.mapMulEquivEquiv e).toMonoidHom
          (mulEquivSubgroupResIso e H A).hom n ≫
        schreierCorestriction H (Rep.res e.toMonoidHom A) n := by
  let _ : (H.map e.toMonoidHom).FiniteIndex :=
    Subgroup.FiniteIndex.map_of_surjective H e.surjective
  let T : H.RightTransversal := default
  rw [schreierCorestriction_eq_of_rightTransversal
      (H.map e.toMonoidHom) A (T.mapMulEquiv e) n,
    schreierCorestriction_eq_of_rightTransversal H
      (Rep.res e.toMonoidHom A) T n]
  exact corestrictionOfRightTransversal_mulEquiv e A T n

/-- Canonical corestriction under group and coefficient transport.

For e : G ≃* G′ and φ : e* A → B, the group-and-coefficient map after corestriction from e(H)
equals the restricted subgroup group-and-coefficient map followed by corestriction from H. -/
theorem schreierCorestriction_mulEquiv_hom
    {G' : Type u} [Group G'] (e : G ≃* G')
    {A : Rep k G'} {B : Rep k G}
    (phi : Rep.res e.toMonoidHom A ⟶ B) (n : ℕ) :
    letI : (H.map e.toMonoidHom).FiniteIndex :=
      Subgroup.FiniteIndex.map_of_surjective H e.surjective
    schreierCorestriction (H.map e.toMonoidHom) A n ≫
        groupCohomology.map e.toMonoidHom phi n =
      groupCohomology.map
          (H.mapMulEquivEquiv e).toMonoidHom
          (mulEquivSubgroupResHom e H phi) n ≫
        schreierCorestriction H B n := by
  let _ : (H.map e.toMonoidHom).FiniteIndex :=
    Subgroup.FiniteIndex.map_of_surjective H e.surjective
  let T : H.RightTransversal := default
  rw [schreierCorestriction_eq_of_rightTransversal
      (H.map e.toMonoidHom) A (T.mapMulEquiv e) n,
    schreierCorestriction_eq_of_rightTransversal H B T n]
  exact corestrictionOfRightTransversal_mulEquiv_hom e phi T n

/-- Group transport with an identified image subgroup.

If e(H) = H′, canonical corestriction for H′ commutes with transport by e and a coefficient
morphism φ : e* A → B. The subgroup map and coefficient comparison use the specified equality
e(H) = H′. -/
theorem schreierCorestriction_mulEquivOfEq_hom
    {G' : Type u} [Group G'] (e : G ≃* G')
    (H' : Subgroup G') (h : H.map e.toMonoidHom = H')
    {A : Rep k G'} {B : Rep k G}
    (phi : Rep.res e.toMonoidHom A ⟶ B)
    [H'.FiniteIndex] (n : ℕ) :
    schreierCorestriction H' A n ≫
        groupCohomology.map e.toMonoidHom phi n =
      groupCohomology.map
          (H.mapMulEquivEquivOfEq e H' h).toMonoidHom
          (mulEquivSubgroupResHomOfEq e H H' h phi) n ≫
        schreierCorestriction H B n := by
  subst H'
  exact schreierCorestriction_mulEquiv_hom (H := H) e phi n

/-- Restriction followed by canonical corestriction.

In every degree n, restricting Hⁿ(G,A) to H and then corestricting to G equals [G:H] times the
identity map. The index acts by natural-number scalar multiplication; no invertibility of the
index is required. -/
theorem schreierCorestriction_restriction
    (A : Rep k G) (n : ℕ) :
    groupCohomology.map H.subtype
        (𝟙 (Rep.res H.subtype A)) n ≫
      schreierCorestriction H A n =
        H.index • 𝟙 (groupCohomology A n) := by
  exact corestrictionOfRightTransversal_restriction A default n

/-- Canonical corestriction through a finite-index subgroup tower.

For K ≤ H ≤ G with both finite indices, corestriction from the image of K in G equals the
canonical subgroup-image comparison followed by corestriction K → H and then H → G. -/
theorem schreierCorestriction_trans
    {K : Subgroup H} [K.FiniteIndex] (A : Rep k G) (n : ℕ) :
    letI : (K.map H.subtype).FiniteIndex := finiteIndex_map_subtype
    schreierCorestriction (K.map H.subtype) A n =
      (groupCohomology.map
          (K.equivMapOfInjective H.subtype
            H.subtype_injective).toMonoidHom
          (mapSubtypeResIso (H := H) (K := K) A).hom n ≫
        schreierCorestriction K (Rep.res H.subtype A) n) ≫
      schreierCorestriction H A n := by
  let _ : (K.map H.subtype).FiniteIndex := finiteIndex_map_subtype
  let S : K.RightTransversal := default
  let T : H.RightTransversal := default
  rw [schreierCorestriction_eq_of_rightTransversal
      (K.map H.subtype) A (S.product T) n,
    schreierCorestriction_eq_of_rightTransversal H A T n,
    schreierCorestriction_eq_of_rightTransversal K
      (Rep.res H.subtype A) S n]
  exact corestrictionOfRightTransversal_product A S T n

/-- The first degree of canonical corestriction.

The underlying linear map of canonical Schreier corestriction in degree one equals
corestrictionH1 A. -/
theorem schreierCorestriction_one_eq (A : Rep k G) :
    (schreierCorestriction H A 1).hom = corestrictionH1 A := by
  unfold schreierCorestriction corestrictionH1
  exact corestrictionOfRightTransversal_one_eq A default

/-- The second degree of canonical corestriction.

The underlying linear map of canonical Schreier corestriction in degree two equals
corestrictionH2 A. -/
theorem schreierCorestriction_two_eq (A : Rep k G) :
    (schreierCorestriction H A 2).hom = corestrictionH2 A := by
  unfold schreierCorestriction corestrictionH2
  exact corestrictionOfRightTransversal_two_eq A default

/-- The third degree of canonical corestriction.

The underlying linear map of canonical Schreier corestriction in degree three equals
corestrictionH3 A. -/
theorem schreierCorestriction_three_eq (A : Rep k G) :
    (schreierCorestriction H A 3).hom = corestrictionH3 A := by
  unfold schreierCorestriction corestrictionH3
  exact corestrictionOfRightTransversal_three_eq A default

end groupCohomology
