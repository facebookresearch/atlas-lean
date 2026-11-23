/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.Homology.FundamentalGroupHomologyComparisonNaturality
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.Homology.FundamentalGroupHurewiczIso

/-!
# Naturality of the simplicial degree-one Hurewicz isomorphism

The connector-aware map on based fundamental groups agrees with the
degree-one integral homology map after abelianization.  Mapped chosen
connectors do not agree edgewise with the target choices: their discrepancy
is a source correction minus a target correction.  The correction vanishes
only after passing to cycles, so the proof is carried out through one-chain
quotients and never asserts an equality on arbitrary open edge generators.

This file stops at generic simplicial H₁ naturality.  It contains no
finite-BGL, kernel, homology-equivalence, plus-construction, or `Q = +`
statement.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial

universe u

namespace SSet

/-- The additive map on integral one-chains induced by a simplicial map. -/
noncomputable def integralOneChainsMap
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    integralOneChains X →+ integralOneChains Y :=
  ((SSet.chainComplexMap f
    (AlgebraicTopology.singularIntegralCoefficients :
      AddCommGrpCat.{u})).f 1).hom

/-- The additive map on integral zero-chains induced by a simplicial map. -/
noncomputable def integralZeroChainsMap
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    integralZeroChains X →+ integralZeroChains Y :=
  ((SSet.chainComplexMap f
    (AlgebraicTopology.singularIntegralCoefficients :
      AddCommGrpCat.{u})).f 0).hom

/-- The degree-one chain map carries two-boundaries to two-boundaries. -/
theorem integralOneChainsMap_boundaries
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    oneChainBoundaries X ≤
      AddSubgroup.comap (integralOneChainsMap f)
        (oneChainBoundaries Y) := by
  rintro z ⟨a, rfl⟩
  refine ⟨(SSet.chainComplexMap f
    (AlgebraicTopology.singularIntegralCoefficients :
      AddCommGrpCat.{u})).f 2 a, ?_⟩
  have h := ConcreteCategory.congr_hom
    ((SSet.chainComplexMap f
      (AlgebraicTopology.singularIntegralCoefficients :
        AddCommGrpCat.{u})).comm 2 1) a
  change ((Y.chainComplex
      (AlgebraicTopology.singularIntegralCoefficients :
        AddCommGrpCat.{u})).d 2 1)
        ((SSet.chainComplexMap f
          (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u})).f 2 a) =
    integralOneChainsMap f
      (((X.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{u})).d 2 1) a) at h
  exact h

/-- A simplicial map induces a map on integral one-chains modulo
two-boundaries. -/
noncomputable def oneChainQuotientMap
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    oneChainQuotient X →+ oneChainQuotient Y :=
  QuotientAddGroup.map _ _ (integralOneChainsMap f)
    (integralOneChainsMap_boundaries f)

@[simp]
theorem oneChainQuotientMap_mk
    {X Y : SSet.{u}} (f : X ⟶ Y) (c : integralOneChains X) :
    oneChainQuotientMap f (QuotientAddGroup.mk' _ c) =
      QuotientAddGroup.mk' _ (integralOneChainsMap f c) :=
  rfl

@[simp]
theorem integralOneChainsMap_simplex
    {X Y : SSet.{u}} (f : X ⟶ Y) (s : X _⦋1⦌) :
    integralOneChainsMap f (simplexOneChain X s) =
      simplexOneChain Y (f.app _ s) := by
  change ((X.ιChainComplex s ≫
    (SSet.chainComplexMap f
      (AlgebraicTopology.singularIntegralCoefficients :
        AddCommGrpCat.{u})).f 1).hom) (ULift.up (1 : ℤ)) = _
  rw [SSet.ι_chainComplexMap_f]
  rfl

@[simp]
theorem integralZeroChainsMap_vertex
    {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    integralZeroChainsMap f (vertexChain X x) =
      vertexChain Y (f.app _ x) := by
  change ((X.ιChainComplex x ≫
    (SSet.chainComplexMap f
      (AlgebraicTopology.singularIntegralCoefficients :
        AddCommGrpCat.{u})).f 0).hom) (ULift.up (1 : ℤ)) = _
  rw [SSet.ι_chainComplexMap_f]
  rfl

/-- Naturality of the descended one-chain boundary. -/
theorem oneChainBoundary_naturality
    {X Y : SSet.{u}} (f : X ⟶ Y) (q : oneChainQuotient X) :
    oneChainBoundary Y (oneChainQuotientMap f q) =
      integralZeroChainsMap f (oneChainBoundary X q) := by
  induction q using QuotientAddGroup.induction_on with
  | _ c =>
      change ((Y.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{u})).d 1 0)
          ((SSet.chainComplexMap f
            (AlgebraicTopology.singularIntegralCoefficients :
              AddCommGrpCat.{u})).f 1 c) =
        (SSet.chainComplexMap f
          (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u})).f 0
          ((X.chainComplex
            (AlgebraicTopology.singularIntegralCoefficients :
              AddCommGrpCat.{u})).d 1 0 c)
      exact ConcreteCategory.congr_hom
        ((SSet.chainComplexMap f
          (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u})).comm 1 0) c

@[simp]
theorem oneChainQuotientMap_edgeOneChainClass
    {X Y : SSet.{u}} (f : X ⟶ Y)
    {a b : X _⦋0⦌} (s : X.Edge a b) :
    oneChainQuotientMap f (edgeOneChainClass s) =
      edgeOneChainClass (s.map f) := by
  rw [edgeOneChainClass, edgeOneChainClass,
    oneChainQuotientMap_mk, integralOneChainsMap_simplex,
    SSet.Edge.map_edge]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The quotient one-chain carried by an arbitrary fundamental-groupoid
morphism is functorial under a simplicial map. -/
theorem oneChainQuotientMap_fundamentalGroupoid_map
    {X Y : SSet.{u}} (f : X ⟶ Y)
    {a b : SSet.FundamentalGroupoid X} (q : a ⟶ b) :
    oneChainQuotientMap f
        ((fundamentalGroupoidToOneChainGroupoid X).map q).val =
      ((fundamentalGroupoidToOneChainGroupoid Y).map
        ((SSet.mapFundamentalGroupoid f).map q)).val := by
  induction q using SSet.FundamentalGroupoid.hom_rec with
  | homMk s =>
      simpa only [fundamentalGroupoidToOneChainGroupoid_map_homMk,
        SSet.mapFundamentalGroupoid_map_homMk,
        OneChainGroupoid.edgeHom] using
        oneChainQuotientMap_edgeOneChainClass f s
  | inv q hq =>
      simp only [Functor.map_inv]
      rw [← Groupoid.inv_eq_inv, oneChainGroupoid_inv_val]
      rw [← Groupoid.inv_eq_inv, oneChainGroupoid_inv_val]
      rw [map_neg, hq]
  | comp q r hq hr =>
      simp only [Functor.map_comp]
      rw [oneChainGroupoid_comp_val, oneChainGroupoid_comp_val,
        map_add, hq, hr]

/-- Restriction of the one-chain quotient map to the kernels of the
descended boundaries. -/
noncomputable def oneChainBoundaryKerMap
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    AddMonoidHom.ker (oneChainBoundary X) →+
      AddMonoidHom.ker (oneChainBoundary Y) where
  toFun z := ⟨oneChainQuotientMap f z.val, by
    rw [AddMonoidHom.mem_ker, oneChainBoundary_naturality,
      AddMonoidHom.mem_ker.mp z.prop, map_zero]⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero (oneChainQuotientMap f)
  map_add' z z' := by
    apply Subtype.ext
    exact map_add (oneChainQuotientMap f) z.val z'.val

/-- The concrete cycles/boundaries quotient equivalence commutes with the
maps induced by a simplicial map. -/
theorem homologyOneQuotientAddEquivOneChainBoundaryKer_naturality
    {X Y : SSet.{u}} (f : X ⟶ Y)
    (q : integralHomologyOneQuotient X) :
    homologyOneQuotientAddEquivOneChainBoundaryKer Y
        (integralHomologyOneQuotientMap f q) =
      oneChainBoundaryKerMap f
        (homologyOneQuotientAddEquivOneChainBoundaryKer X q) := by
  induction q using QuotientAddGroup.induction_on with
  | _ z =>
      change homologyOneQuotientToOneChainBoundaryKer Y
          (integralHomologyOneQuotientMap f
            (QuotientAddGroup.mk' _ z)) =
        oneChainBoundaryKerMap f
          (homologyOneQuotientToOneChainBoundaryKer X
            (QuotientAddGroup.mk' _ z))
      rw [integralHomologyOneQuotientMap_mk,
        homologyOneQuotientToOneChainBoundaryKer_mk,
        homologyOneQuotientToOneChainBoundaryKer_mk]
      apply Subtype.ext
      change QuotientAddGroup.mk' (oneChainBoundaries Y)
          (integralOneCyclesMap f z).val =
        oneChainQuotientMap f
          (QuotientAddGroup.mk' (oneChainBoundaries X) z.val)
      rw [oneChainQuotientMap_mk]
      have h := ConcreteCategory.congr_hom
        (integralOneCyclesMap_comp_subtype f) z
      exact congrArg (QuotientAddGroup.mk' (oneChainBoundaries Y)) h.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On based loops, connector conjugation has zero total one-chain, so the
one-chain quotient map agrees with the connector-aware based fundamental
group homomorphism. -/
theorem oneChainQuotientMap_basedFundamentalGroupHom
    {X Y : SSet.{u}} (f : X ⟶ Y)
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (e : (SSet.mapFundamentalGroupoid f).obj
          (SSet.FundamentalGroupoid.mk x) ≅
        SSet.FundamentalGroupoid.mk y)
    (q : End (SSet.FundamentalGroupoid.mk x)) :
    oneChainQuotientMap f
        (((fundamentalGroupoidToOneChainGroupoid X).mapEnd
          (SSet.FundamentalGroupoid.mk x) q).asHom).val =
      (((fundamentalGroupoidToOneChainGroupoid Y).mapEnd
        (SSet.FundamentalGroupoid.mk y)
        (basedFundamentalGroupHom f x y e q)).asHom).val := by
  change oneChainQuotientMap f
      ((fundamentalGroupoidToOneChainGroupoid X).map q.asHom).val =
    ((fundamentalGroupoidToOneChainGroupoid Y).map
      ((basedFundamentalGroupHom f x y e q).asHom)).val
  rw [oneChainQuotientMap_fundamentalGroupoid_map]
  rw [basedFundamentalGroupHom_apply]
  let F := fundamentalGroupoidToOneChainGroupoid Y
  let q' := (SSet.mapFundamentalGroupoid f).map q.asHom
  have hinv : F.map e.inv = inv (F.map e.hom) :=
    IsIso.eq_inv_of_hom_inv_id (F.map_hom_inv' e)
  change (F.map q').val =
    (F.map (e.inv ≫ q' ≫ e.hom)).val
  rw [← Category.assoc, Functor.map_comp, Functor.map_comp,
    oneChainGroupoid_comp_val, oneChainGroupoid_comp_val, hinv,
    ← Groupoid.inv_eq_inv, oneChainGroupoid_inv_val]
  abel

/-- Naturality of the concrete nonabelian forward Hurewicz map on a based
loop.  Connector conjugation has already cancelled in the one-chain
quotient. -/
theorem fundamentalGroupConcreteHomologyOneHom_naturality
    {X Y : SSet.{u}} (f : X ⟶ Y)
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (e : (SSet.mapFundamentalGroupoid f).obj
          (SSet.FundamentalGroupoid.mk x) ≅
        SSet.FundamentalGroupoid.mk y)
    (q : End (SSet.FundamentalGroupoid.mk x)) :
    integralHomologyOneQuotientMap f
        (Multiplicative.toAdd
          (fundamentalGroupConcreteHomologyOneHom X x q)) =
      Multiplicative.toAdd
        (fundamentalGroupConcreteHomologyOneHom Y y
          (basedFundamentalGroupHom f x y e q)) := by
  apply (homologyOneQuotientAddEquivOneChainBoundaryKer Y).injective
  rw [homologyOneQuotientAddEquivOneChainBoundaryKer_naturality]
  change oneChainBoundaryKerMap f
      ((homologyOneQuotientAddEquivOneChainBoundaryKer X)
        ((homologyOneQuotientAddEquivOneChainBoundaryKer X).symm
          (Multiplicative.toAdd
            (oneChainGroupoidEndMulEquivBoundaryKer X x
              ((fundamentalGroupoidToOneChainGroupoid X).mapEnd
                (SSet.FundamentalGroupoid.mk x) q))))) =
    (homologyOneQuotientAddEquivOneChainBoundaryKer Y)
      ((homologyOneQuotientAddEquivOneChainBoundaryKer Y).symm
        (Multiplicative.toAdd
          (oneChainGroupoidEndMulEquivBoundaryKer Y y
            ((fundamentalGroupoidToOneChainGroupoid Y).mapEnd
              (SSet.FundamentalGroupoid.mk y)
              (basedFundamentalGroupHom f x y e q)))))
  rw [(homologyOneQuotientAddEquivOneChainBoundaryKer X).apply_symm_apply,
    (homologyOneQuotientAddEquivOneChainBoundaryKer Y).apply_symm_apply]
  apply Subtype.ext
  exact oneChainQuotientMap_basedFundamentalGroupHom f x y e q

/-- Naturality of the concrete forward Hurewicz map after factoring through
abelianization. -/
theorem fundamentalGroupAbelianizationConcreteHomologyOneHom_naturality
    {X Y : SSet.{u}} (f : X ⟶ Y)
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (e : (SSet.mapFundamentalGroupoid f).obj
          (SSet.FundamentalGroupoid.mk x) ≅
        SSet.FundamentalGroupoid.mk y) :
    (fundamentalGroupAbelianizationConcreteHomologyOneHom Y y).comp
        (Abelianization.map (basedFundamentalGroupHom f x y e)) =
      (integralHomologyOneQuotientMap f).toMultiplicative.comp
        (fundamentalGroupAbelianizationConcreteHomologyOneHom X x) := by
  apply Abelianization.hom_ext
  apply MonoidHom.ext
  intro q
  simp only [MonoidHom.comp_apply, Abelianization.map_of,
    fundamentalGroupAbelianizationConcreteHomologyOneHom_of]
  exact congrArg Multiplicative.ofAdd
    (fundamentalGroupConcreteHomologyOneHom_naturality f x y e q).symm

/-- Additive form of concrete Hurewicz naturality. -/
theorem fundamentalGroupAbelianizationConcreteHomologyOneAddHom_naturality
    {X Y : SSet.{u}} (f : X ⟶ Y)
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (e : (SSet.mapFundamentalGroupoid f).obj
          (SSet.FundamentalGroupoid.mk x) ≅
        SSet.FundamentalGroupoid.mk y) :
    AddCommGrpCat.ofHom
        ((Abelianization.map
          (basedFundamentalGroupHom f x y e)).toAdditive) ≫
      AddCommGrpCat.ofHom
        (fundamentalGroupAbelianizationConcreteHomologyOneAddHom Y y) =
    AddCommGrpCat.ofHom
        (fundamentalGroupAbelianizationConcreteHomologyOneAddHom X x) ≫
      AddCommGrpCat.ofHom (integralHomologyOneQuotientMap f) := by
  apply ConcreteCategory.hom_ext
  intro a
  have hEq :=
    fundamentalGroupAbelianizationConcreteHomologyOneHom_naturality
      f x y e
  have h := DFunLike.congr_fun hEq (Additive.toMul a)
  exact congrArg Multiplicative.toAdd h

private theorem homologyOneConcreteQuotientIso_inv_naturality
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    AddCommGrpCat.ofHom (integralHomologyOneQuotientMap f) ≫
        (homologyOneConcreteQuotientIso Y).inv =
      (homologyOneConcreteQuotientIso X).inv ≫
        SSet.homologyMap f
          (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u}) 1 := by
  apply (cancel_mono (homologyOneConcreteQuotientIso Y).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Category.assoc,
    homologyOneConcreteQuotientIso_hom_naturality]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Connector-aware naturality of the degree-one Hurewicz isomorphism. -/
@[reassoc]
theorem fundamentalGroupAbelianizationHomologyOneIso_hom_naturality
    {X Y : SSet.{u}} [X.IsConnected] [Y.IsConnected]
    (f : X ⟶ Y) (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (e : (SSet.mapFundamentalGroupoid f).obj
          (SSet.FundamentalGroupoid.mk x) ≅
        SSet.FundamentalGroupoid.mk y) :
    AddCommGrpCat.ofHom
        ((Abelianization.map
          (SSet.basedFundamentalGroupHom f x y e)).toAdditive) ≫
      (SSet.fundamentalGroupAbelianizationHomologyOneIso Y y).hom =
    (SSet.fundamentalGroupAbelianizationHomologyOneIso X x).hom ≫
      SSet.homologyMap f
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{u}) 1 := by
  unfold fundamentalGroupAbelianizationHomologyOneIso
  simp only [Iso.trans_hom]
  change (AddCommGrpCat.ofHom
        ((Abelianization.map
          (SSet.basedFundamentalGroupHom f x y e)).toAdditive) ≫
      AddCommGrpCat.ofHom
        (fundamentalGroupAbelianizationConcreteHomologyOneAddHom Y y)) ≫
        (homologyOneConcreteQuotientIso Y).inv =
    (AddCommGrpCat.ofHom
        (fundamentalGroupAbelianizationConcreteHomologyOneAddHom X x) ≫
      (homologyOneConcreteQuotientIso X).inv) ≫
        SSet.homologyMap f
          (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u}) 1
  rw [fundamentalGroupAbelianizationConcreteHomologyOneAddHom_naturality]
  rw [Category.assoc]
  rw [homologyOneConcreteQuotientIso_inv_naturality]
  exact (Category.assoc _ _ _).symm

end SSet

end
