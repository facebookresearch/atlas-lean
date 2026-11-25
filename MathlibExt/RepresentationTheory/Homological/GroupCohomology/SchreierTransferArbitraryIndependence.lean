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
# Transversal independence of arbitrary Schreier transfer

The universal induced-bar transfer maps attached to two right transversals
are lifts of the same canonical norm map and hence chain homotopic.  This
file transports that homotopy through the induction adjunction and the
inhomogeneous/bar comparisons.  As a result, chosen-transversal
corestriction is independent of the transversal in every cohomological
degree.
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
/-- Degreewise induction adjunction, assembled into an isomorphism between
the subgroup bar linear-Hom complex and the ambient linear-Hom complex of
the induced bar resolution. -/
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

/-- The subgroup inhomogeneous cochain complex identified with ambient
linear-Hom cochains on the induced subgroup bar resolution. -/
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

/-- The ambient linear-Hom cochain map induced contravariantly by the
universal chosen-transversal transfer into the induced bar resolution. -/
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

theorem schreierTransferInducedBarCochains_f_apply
    (A : Rep k G) (T : H.RightTransversal) (n : ℕ)
    (phi : (inducedBarResolution (k := k) H).complex.X n ⟶ A) :
    ((schreierTransferInducedBarCochains H A T).f n).hom phi =
      (schreierTransferInducedBar (k := k) H T).f n ≫ phi :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Under the subgroup/induced-bar and ambient/bar comparisons, the
universal induced-bar chain map computes the arbitrary Schreier cochain
transfer. -/
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
/-- The arbitrary Schreier cochain maps attached to two right transversals
induce the same map on cohomology. -/
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

/-- Arbitrary-degree chosen-transversal corestriction is independent of the
right transversal. -/
theorem corestrictionOfRightTransversal_eq
    (A : Rep k G) (T U : H.RightTransversal) (n : ℕ) :
    corestrictionOfRightTransversal A T n =
      corestrictionOfRightTransversal A U n := by
  exact homologyMap_corestrictionCochains_eq H A T U n

/-- Canonical explicit Schreier corestriction in arbitrary degree. -/
noncomputable def schreierCorestriction
    (A : Rep k G) (n : ℕ) :
    groupCohomology (Rep.res H.subtype A) n ⟶
      groupCohomology A n :=
  corestrictionOfRightTransversal A default n

/-- The canonical explicit Schreier corestriction is computed by every
chosen right transversal. -/
theorem schreierCorestriction_eq_of_rightTransversal
    (A : Rep k G) (T : H.RightTransversal) (n : ℕ) :
    schreierCorestriction H A n =
      corestrictionOfRightTransversal A T n := by
  exact corestrictionOfRightTransversal_eq H A default T n

@[simp]
theorem schreierCorestriction_zero
    (A : Rep k G) (n : ℕ) :
    schreierCorestriction H A n 0 = 0 :=
  map_zero _

/-- Canonical arbitrary-degree Schreier corestriction is natural in the
coefficient representation. -/
theorem schreierCorestriction_naturality
    {A B : Rep k G} (phi : A ⟶ B) (n : ℕ) :
    schreierCorestriction H A n ≫
        groupCohomology.map (MonoidHom.id G) phi n =
      groupCohomology.map (MonoidHom.id H)
          ((Rep.resFunctor H.subtype).map phi) n ≫
        schreierCorestriction H B n := by
  exact corestrictionOfRightTransversal_naturality phi default n

/-- Canonical arbitrary-degree Schreier corestriction as a natural
transformation in the coefficient representation. -/
noncomputable def schreierCorestrictionNatTrans (n : ℕ) :
    Rep.resFunctor H.subtype ⋙ groupCohomology.functor k H n ⟶
      groupCohomology.functor k G n where
  app A := schreierCorestriction H A n
  naturality {_A _B} phi :=
    (schreierCorestriction_naturality H phi n).symm

/-- Canonical arbitrary-degree Schreier corestriction commutes with an
equivalence of ambient groups. -/
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

/-- Canonical arbitrary-degree Schreier corestriction is natural under
simultaneous transport of the ambient group and coefficients. -/
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

/-- Arbitrary-degree Schreier corestriction is natural under simultaneous
ambient-group and coefficient transport when the image subgroup is supplied
through a separately bundled equal presentation. -/
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

/-- Canonical arbitrary-degree Schreier corestriction after restriction is
multiplication by the subgroup index. -/
theorem schreierCorestriction_restriction
    (A : Rep k G) (n : ℕ) :
    groupCohomology.map H.subtype
        (𝟙 (Rep.res H.subtype A)) n ≫
      schreierCorestriction H A n =
        H.index • 𝟙 (groupCohomology A n) := by
  exact corestrictionOfRightTransversal_restriction A default n

/-- Canonical arbitrary-degree Schreier corestriction is transitive along a
chain of finite-index subgroups. -/
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

/-- The canonical arbitrary-degree map recovers canonical degree-one
corestriction. -/
theorem schreierCorestriction_one_eq (A : Rep k G) :
    (schreierCorestriction H A 1).hom = corestrictionH1 A := by
  unfold schreierCorestriction corestrictionH1
  exact corestrictionOfRightTransversal_one_eq A default

/-- The canonical arbitrary-degree map recovers canonical degree-two
corestriction. -/
theorem schreierCorestriction_two_eq (A : Rep k G) :
    (schreierCorestriction H A 2).hom = corestrictionH2 A := by
  unfold schreierCorestriction corestrictionH2
  exact corestrictionOfRightTransversal_two_eq A default

/-- The canonical arbitrary-degree map recovers canonical degree-three
corestriction. -/
theorem schreierCorestriction_three_eq (A : Rep k G) :
    (schreierCorestriction H A 3).hom = corestrictionH3 A := by
  unfold schreierCorestriction corestrictionH3
  exact corestrictionOfRightTransversal_three_eq A default

end groupCohomology
