/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.Homology.FundamentalGroupHomologyComparison

/-!
# Naturality of the concrete simplicial H₁ comparison

A simplicial map induces maps on integral one-cycles and on the quotient by
two-boundaries.  These maps agree with Mathlib's abstract degree-one homology
map through `homologyOneConcreteQuotientIso`.

The proof uses only public chain-complex, cycles, homology projection, and
short-complex homology-map data APIs.  It does not unfold chosen colimits.
No connected Hurewicz isomorphism, connector naturality, finite-BGL result,
kernel statement, plus construction, or `Q = +` claim is made.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial

universe u

namespace SSet

/-- The morphism of displayed degree-one short complexes induced by a
simplicial map. -/
noncomputable def integralDegreeOneShortComplexMap
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    integralDegreeOneShortComplex X ⟶
      integralDegreeOneShortComplex Y := by
  let φ := SSet.chainComplexMap f
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
  exact
    { τ₁ := φ.f 2
      τ₂ := φ.f 1
      τ₃ := φ.f 0
      comm₁₂ := φ.comm 2 1
      comm₂₃ := φ.comm 1 0 }

/-- The map on concrete integral one-cycles induced by a simplicial map. -/
noncomputable def integralOneCyclesMap
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    integralOneCycles X →+ integralOneCycles Y := by
  let γ := ShortComplex.leftHomologyMapData
    (integralDegreeOneShortComplexMap f)
    (integralDegreeOneShortComplex X).abLeftHomologyData
    (integralDegreeOneShortComplex Y).abLeftHomologyData
  exact γ.φK.hom

private theorem integralOneCyclesMap_ofHom_eq
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    AddCommGrpCat.ofHom (integralOneCyclesMap f) =
      (ShortComplex.leftHomologyMapData
        (integralDegreeOneShortComplexMap f)
        (integralDegreeOneShortComplex X).abLeftHomologyData
        (integralDegreeOneShortComplex Y).abLeftHomologyData).φK := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

@[reassoc]
theorem integralOneCyclesMap_comp_subtype
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    AddCommGrpCat.ofHom (integralOneCyclesMap f) ≫
        AddCommGrpCat.ofHom (AddMonoidHom.ker
          ((Y.chainComplex
            (AlgebraicTopology.singularIntegralCoefficients :
              AddCommGrpCat.{u})).d 1 0).hom).subtype =
      AddCommGrpCat.ofHom (AddMonoidHom.ker
        ((X.chainComplex
          (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u})).d 1 0).hom).subtype ≫
        (SSet.chainComplexMap f
          (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u})).f 1 :=
  by
    let γ := ShortComplex.leftHomologyMapData
      (integralDegreeOneShortComplexMap f)
      (integralDegreeOneShortComplex X).abLeftHomologyData
      (integralDegreeOneShortComplex Y).abLeftHomologyData
    rw [integralOneCyclesMap_ofHom_eq]
    exact γ.commi

/-- The cycles map carries concrete two-boundaries to concrete
two-boundaries. -/
theorem integralOneCyclesMap_boundaries
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    AddMonoidHom.range (oneBoundariesToCycles X) ≤
      AddSubgroup.comap (integralOneCyclesMap f)
        (AddMonoidHom.range (oneBoundariesToCycles Y)) := by
  rintro z ⟨a, rfl⟩
  refine ⟨(SSet.chainComplexMap f
    (AlgebraicTopology.singularIntegralCoefficients :
      AddCommGrpCat.{u})).f 2 a, ?_⟩
  let γ := ShortComplex.leftHomologyMapData
    (integralDegreeOneShortComplexMap f)
    (integralDegreeOneShortComplex X).abLeftHomologyData
    (integralDegreeOneShortComplex Y).abLeftHomologyData
  have h := ConcreteCategory.congr_hom γ.commf' a
  have hX := congrArg (fun m ↦ m a)
    (integralDegreeOneShortComplex_abToCycles X)
  have hY := congrArg (fun m ↦ m
      ((SSet.chainComplexMap f
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{u})).f 2 a))
    (integralDegreeOneShortComplex_abToCycles Y)
  have hK := ConcreteCategory.congr_hom
    (integralOneCyclesMap_ofHom_eq f) (oneBoundariesToCycles X a)
  change γ.φK
      ((integralDegreeOneShortComplex X).abToCycles a) =
    (integralDegreeOneShortComplex Y).abToCycles
      ((SSet.chainComplexMap f
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{u})).f 2 a) at h
  exact hY.symm.trans (h.symm.trans
    ((congrArg γ.φK hX).trans hK.symm))

/-- The induced map on the concrete quotient of one-cycles by
two-boundaries. -/
noncomputable def integralHomologyOneQuotientMap
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    integralHomologyOneQuotient X →+
      integralHomologyOneQuotient Y :=
  QuotientAddGroup.map _ _ (integralOneCyclesMap f) (by
    exact integralOneCyclesMap_boundaries f)

@[simp]
theorem integralHomologyOneQuotientMap_mk
    {X Y : SSet.{u}} (f : X ⟶ Y) (z : integralOneCycles X) :
    integralHomologyOneQuotientMap f (QuotientAddGroup.mk' _ z) =
      QuotientAddGroup.mk' _ (integralOneCyclesMap f z) :=
  rfl

private noncomputable def integralDegreeOneLeftHomologyMapData
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    ShortComplex.LeftHomologyMapData
      (integralDegreeOneShortComplexMap f)
      (integralDegreeOneShortComplex X).abLeftHomologyData
      (integralDegreeOneShortComplex Y).abLeftHomologyData where
  φK := AddCommGrpCat.ofHom (integralOneCyclesMap f)
  φH := AddCommGrpCat.ofHom (integralHomologyOneQuotientMap f)
  commi := by
    let γ := ShortComplex.leftHomologyMapData
      (integralDegreeOneShortComplexMap f)
      (integralDegreeOneShortComplex X).abLeftHomologyData
      (integralDegreeOneShortComplex Y).abLeftHomologyData
    rw [integralOneCyclesMap_ofHom_eq]
    exact γ.commi
  commf' := by
    let γ := ShortComplex.leftHomologyMapData
      (integralDegreeOneShortComplexMap f)
      (integralDegreeOneShortComplex X).abLeftHomologyData
      (integralDegreeOneShortComplex Y).abLeftHomologyData
    rw [integralOneCyclesMap_ofHom_eq]
    exact γ.commf'
  commπ := by
    apply ConcreteCategory.hom_ext
    intro z
    rfl

private noncomputable def abstractOneCyclesToConcreteCycles
    (X : SSet.{u}) :
    (X.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{u})).cycles 1 ⟶
      AddCommGrpCat.of (integralOneCycles X) :=
  ((X.chainComplex
      (AlgebraicTopology.singularIntegralCoefficients :
        AddCommGrpCat.{u})).cyclesIsoSc' 2 1 0 (by simp) (by simp)).hom ≫
    ShortComplex.cyclesMap (integralDegreeOneShortComplexIso X).hom ≫
      (integralDegreeOneShortComplex X).abCyclesIso.hom

private noncomputable def abstractOneCyclesToConcreteQuotient
    (X : SSet.{u}) :
    (X.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{u})).cycles 1 ⟶
      AddCommGrpCat.of (integralHomologyOneQuotient X) :=
  abstractOneCyclesToConcreteCycles X ≫
    AddCommGrpCat.ofHom (QuotientAddGroup.mk' _)

set_option backward.isDefEq.respectTransparency false in
private theorem abstractOneCyclesToConcreteCycles_comp_subtype
    (X : SSet.{u}) :
    abstractOneCyclesToConcreteCycles X ≫
        (integralDegreeOneShortComplex X).abLeftHomologyData.i =
      (X.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{u})).iCycles 1 := by
  unfold abstractOneCyclesToConcreteCycles
  dsimp only [ShortComplex.abCyclesIso]
  slice_lhs 3 4 =>
    rw [ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i]
  slice_lhs 2 3 =>
    rw [ShortComplex.cyclesMap_i]
  slice_lhs 1 2 =>
    rw [HomologicalComplex.cyclesIsoSc'_hom_iCycles]
  rfl

private theorem integralDegreeOne_abLeftHomologyData_i
    (X : SSet.{u}) :
    (integralDegreeOneShortComplex X).abLeftHomologyData.i =
      AddCommGrpCat.ofHom (AddMonoidHom.ker
        ((X.chainComplex
          (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u})).d 1 0).hom).subtype :=
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem abstractOneCyclesToConcreteCycles_naturality
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    HomologicalComplex.cyclesMap
        (SSet.chainComplexMap f
          (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u})) 1 ≫
        abstractOneCyclesToConcreteCycles Y =
      abstractOneCyclesToConcreteCycles X ≫
        AddCommGrpCat.ofHom (integralOneCyclesMap f) := by
  apply (cancel_mono
    (integralDegreeOneShortComplex Y).abLeftHomologyData.i).1
  change (HomologicalComplex.cyclesMap
      (SSet.chainComplexMap f
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{u})) 1 ≫
        abstractOneCyclesToConcreteCycles Y) ≫
      (integralDegreeOneShortComplex Y).abLeftHomologyData.i =
    (abstractOneCyclesToConcreteCycles X ≫
      AddCommGrpCat.ofHom (integralOneCyclesMap f)) ≫
      (integralDegreeOneShortComplex Y).abLeftHomologyData.i
  rw [Category.assoc, abstractOneCyclesToConcreteCycles_comp_subtype,
    HomologicalComplex.cyclesMap_i]
  rw [Category.assoc]
  rw [integralDegreeOne_abLeftHomologyData_i]
  rw [integralOneCyclesMap_comp_subtype]
  rw [← integralDegreeOne_abLeftHomologyData_i X,
    ← Category.assoc,
    abstractOneCyclesToConcreteCycles_comp_subtype]

private theorem abstractOneCyclesToConcreteQuotient_naturality
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    HomologicalComplex.cyclesMap
        (SSet.chainComplexMap f
          (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u})) 1 ≫
        abstractOneCyclesToConcreteQuotient Y =
      abstractOneCyclesToConcreteQuotient X ≫
        AddCommGrpCat.ofHom (integralHomologyOneQuotientMap f) := by
  simp only [abstractOneCyclesToConcreteQuotient, Category.assoc]
  rw [← Category.assoc,
    abstractOneCyclesToConcreteCycles_naturality, Category.assoc]
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg
    (fun k ↦ abstractOneCyclesToConcreteCycles X ≫ k)
    (integralDegreeOneLeftHomologyMapData f).commπ.symm

private noncomputable def integralDegreeOneBoundaryQuotientIso
    (X : SSet.{u}) :
    AddCommGrpCat.of
        (integralOneCycles X ⧸
          AddMonoidHom.range (integralDegreeOneShortComplex X).abToCycles) ≅
      AddCommGrpCat.of (integralHomologyOneQuotient X) :=
  eqToIso (congrArg (fun H : AddSubgroup (integralOneCycles X) ↦
    AddCommGrpCat.of (integralOneCycles X ⧸ H))
      (integralDegreeOneShortComplex_boundary_range X))

private noncomputable def explicitHomologyOneConcreteQuotientIso
    (X : SSet.{u}) :
    X.homology
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{u}) 1 ≅
      AddCommGrpCat.of (integralHomologyOneQuotient X) := by
  let K := X.chainComplex
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
  exact K.homologyIsoSc' 2 1 0 (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (integralDegreeOneShortComplexIso X) ≪≫
      (integralDegreeOneShortComplex X).abHomologyIso ≪≫
        integralDegreeOneBoundaryQuotientIso X

private theorem homologyOneConcreteQuotientIso_eq_explicit
    (X : SSet.{u}) :
    homologyOneConcreteQuotientIso X =
      explicitHomologyOneConcreteQuotientIso X := by
  unfold homologyOneConcreteQuotientIso
  dsimp only [explicitHomologyOneConcreteQuotientIso,
    integralDegreeOneBoundaryQuotientIso]
  apply Iso.ext
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem homologyπ_comp_homologyOneConcreteQuotientIso_hom
    (X : SSet.{u}) :
    (X.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{u})).homologyπ 1 ≫
        (homologyOneConcreteQuotientIso X).hom =
      abstractOneCyclesToConcreteQuotient X := by
  rw [homologyOneConcreteQuotientIso_eq_explicit]
  simp only [explicitHomologyOneConcreteQuotientIso, Iso.trans_hom,
    abstractOneCyclesToConcreteQuotient,
    abstractOneCyclesToConcreteCycles, Category.assoc]
  rw [HomologicalComplex.π_homologyIsoSc'_hom_assoc]
  let e := ((X.chainComplex
    (AlgebraicTopology.singularIntegralCoefficients :
      AddCommGrpCat.{u})).cyclesIsoSc' 2 1 0 (by simp) (by simp)).hom
  change e ≫ _ = e ≫ _
  rw [cancel_epi e]
  change (HomologicalComplex.sc' (X.chainComplex
      (AlgebraicTopology.singularIntegralCoefficients :
        AddCommGrpCat.{u})) 2 1 0).homologyπ ≫
      ShortComplex.homologyMap
        (integralDegreeOneShortComplexIso X).hom ≫ _ = _
  rw [ShortComplex.homologyπ_naturality_assoc]
  rw [cancel_epi]
  dsimp only [ShortComplex.abHomologyIso, ShortComplex.abCyclesIso]
  rw [← Category.assoc,
    (integralDegreeOneShortComplex X).abLeftHomologyData.homologyπ_comp_homologyIso_hom]
  rw [Category.assoc]
  rw [cancel_epi]
  rfl

/-- The original abstract-to-concrete H₁ comparison sends an actual cycle
element to the class of its original chain under the actual cycles inclusion. -/
theorem homologyOneConcreteQuotientIso_hom_cycle
    (X : SSet.{u})
    (z : (X.chainComplex
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).cycles 1) :
    (homologyOneConcreteQuotientIso X).hom
        ((X.chainComplex
          (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).homologyπ 1 z) =
      QuotientAddGroup.mk' (AddMonoidHom.range (oneBoundariesToCycles X))
        (⟨(X.chainComplex
            (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).iCycles 1 z,
          by
            change (X.chainComplex
                (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).d 1 0
                  ((X.chainComplex
                    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).iCycles
                      1 z) = 0
            exact ConcreteCategory.congr_hom
              ((X.chainComplex
                (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).iCycles_d
                  1 0) z⟩ : integralOneCycles X) := by
  have h := ConcreteCategory.congr_hom
    (homologyπ_comp_homologyOneConcreteQuotientIso_hom X) z
  change (homologyOneConcreteQuotientIso X).hom
      ((X.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).homologyπ 1 z) =
    abstractOneCyclesToConcreteQuotient X z at h
  rw [h]
  change QuotientAddGroup.mk' (AddMonoidHom.range (oneBoundariesToCycles X))
      (abstractOneCyclesToConcreteCycles X z) = _
  congr 1
  apply Subtype.ext
  have hv := ConcreteCategory.congr_hom
    (abstractOneCyclesToConcreteCycles_comp_subtype X) z
  rw [integralDegreeOne_abLeftHomologyData_i] at hv
  change (abstractOneCyclesToConcreteCycles X z).val =
    (X.chainComplex
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).iCycles 1 z at hv
  exact hv

/-- The original fundamental-group H₁ forward map sends an ordinary based
edge to its positive original integral one-cycle class. -/
theorem fundamentalGroupHomologyOneHom_homMk
    (X : SSet.{u}) (x : X _⦋0⦌) (e : X.Edge x x) :
    fundamentalGroupHomologyOneHom X x (End.of (SSet.FundamentalGroupoid.homMk e)) =
      Multiplicative.ofAdd
        (((X.chainComplex
            (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).liftCycles
          (X.ιChainComplex
            (R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})) e.edge)
          0 (by simp) (by
            rw [ιChainComplex_d, Fin.sum_univ_two]
            simp [e.tgt_eq, e.src_eq]) ≫
          (X.chainComplex
            (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).homologyπ 1)
            (ULift.up (1 : ℤ))) := by
  let R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
  let C := X.chainComplex R
  let q : End (SSet.FundamentalGroupoid.mk x) :=
    End.of (SSet.FundamentalGroupoid.homMk e)
  have hd : X.ιChainComplex (R := R) e.edge ≫ C.d 1 0 = 0 := by
    rw [ιChainComplex_d, Fin.sum_univ_two]
    simp [e.tgt_eq, e.src_eq]
  let a : R ⟶ C.cycles 1 := C.liftCycles
    (X.ιChainComplex (R := R) e.edge) 0 (by simp) hd
  let z : C.cycles 1 := a (ULift.up (1 : ℤ))
  have hval : C.iCycles 1 z = simplexOneChain X e.edge := by
    change (a ≫ C.iCycles 1) (ULift.up (1 : ℤ)) = simplexOneChain X e.edge
    rw [HomologicalComplex.liftCycles_i]
    rfl
  have habstract : (homologyOneConcreteQuotientIso X).hom
      (Multiplicative.toAdd (fundamentalGroupHomologyOneHom X x q)) =
        Multiplicative.toAdd (fundamentalGroupConcreteHomologyOneHom X x q) := by
    change (homologyOneConcreteQuotientIso X).hom
      ((homologyOneConcreteQuotientIso X).inv
        (Multiplicative.toAdd (fundamentalGroupConcreteHomologyOneHom X x q))) = _
    exact ConcreteCategory.congr_hom (homologyOneConcreteQuotientIso X).inv_hom_id
      (Multiplicative.toAdd (fundamentalGroupConcreteHomologyOneHom X x q))
  change fundamentalGroupHomologyOneHom X x q = Multiplicative.ofAdd (C.homologyπ 1 z)
  apply Multiplicative.toAdd.injective
  change Multiplicative.toAdd (fundamentalGroupHomologyOneHom X x q) = C.homologyπ 1 z
  apply (homologyOneConcreteQuotientIso X).addCommGroupIsoToAddEquiv.injective
  change (homologyOneConcreteQuotientIso X).hom
      (Multiplicative.toAdd (fundamentalGroupHomologyOneHom X x q)) =
    (homologyOneConcreteQuotientIso X).hom (C.homologyπ 1 z)
  rw [habstract, homologyOneConcreteQuotientIso_hom_cycle]
  let c : integralOneCycles X := ⟨C.iCycles 1 z, by
    change C.d 1 0 (C.iCycles 1 z) = 0
    exact ConcreteCategory.congr_hom (C.iCycles_d 1 0) z⟩
  change Multiplicative.toAdd (fundamentalGroupConcreteHomologyOneHom X x q) =
    QuotientAddGroup.mk' _ c
  apply (homologyOneQuotientAddEquivOneChainBoundaryKer X).injective
  have he := (homologyOneQuotientAddEquivOneChainBoundaryKer X).apply_symm_apply
    (Multiplicative.toAdd (oneChainGroupoidEndMulEquivBoundaryKer X x
      ((fundamentalGroupoidToOneChainGroupoid X).mapEnd
        (SSet.FundamentalGroupoid.mk x) q)))
  change (homologyOneQuotientAddEquivOneChainBoundaryKer X)
      (Multiplicative.toAdd (fundamentalGroupConcreteHomologyOneHom X x q)) = _ at he
  rw [he]
  change _ = homologyOneQuotientToOneChainBoundaryKer X (QuotientAddGroup.mk' _ c)
  rw [homologyOneQuotientToOneChainBoundaryKer_mk]
  apply Subtype.ext
  change ((fundamentalGroupoidToOneChainGroupoid X).map
      (SSet.FundamentalGroupoid.homMk e)).val =
    (C.iCycles 1 z : oneChainQuotient X)
  rw [fundamentalGroupoidToOneChainGroupoid_map_homMk]
  change edgeOneChainClass e =
    QuotientAddGroup.mk' (oneChainBoundaries X) (C.iCycles 1 z)
  rw [hval]
  rfl

/-- The original fundamental-group H₁ forward map sends the inverse based
edge to the negative of its actual original integral one-cycle class. -/
theorem fundamentalGroupHomologyOneHom_inv_homMk
    (X : SSet.{u}) (x : X _⦋0⦌) (e : X.Edge x x) :
    fundamentalGroupHomologyOneHom X x
        (End.of (CategoryTheory.inv (SSet.FundamentalGroupoid.homMk e))) =
      Multiplicative.ofAdd
        (-(((X.chainComplex
            (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).liftCycles
          (X.ιChainComplex
            (R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})) e.edge)
          0 (by simp) (by
            rw [ιChainComplex_d, Fin.sum_univ_two]
            simp [e.tgt_eq, e.src_eq]) ≫
          (X.chainComplex
            (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).homologyπ 1)
            (ULift.up (1 : ℤ)))) := by
  have h := (fundamentalGroupHomologyOneHom X x).map_inv
    (End.of (SSet.FundamentalGroupoid.homMk e))
  change fundamentalGroupHomologyOneHom X x
      (End.of (Groupoid.inv (SSet.FundamentalGroupoid.homMk e))) =
    (fundamentalGroupHomologyOneHom X x
      (End.of (SSet.FundamentalGroupoid.homMk e)))⁻¹ at h
  rw [Groupoid.inv_eq_inv] at h
  rw [h, fundamentalGroupHomologyOneHom_homMk]
  rfl

/-- The concrete cycles-modulo-boundaries comparison is natural for
simplicial maps. -/
theorem homologyOneConcreteQuotientIso_hom_naturality
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.homologyMap f
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{u}) 1 ≫
        (homologyOneConcreteQuotientIso Y).hom =
      (homologyOneConcreteQuotientIso X).hom ≫
        AddCommGrpCat.ofHom (integralHomologyOneQuotientMap f) := by
  rw [← cancel_epi ((X.chainComplex
    (AlgebraicTopology.singularIntegralCoefficients :
      AddCommGrpCat.{u})).homologyπ 1)]
  rw [HomologicalComplex.homologyπ_naturality_assoc]
  rw [homologyπ_comp_homologyOneConcreteQuotientIso_hom Y]
  rw [← Category.assoc]
  rw [homologyπ_comp_homologyOneConcreteQuotientIso_hom X]
  exact abstractOneCyclesToConcreteQuotient_naturality f

end SSet

end
