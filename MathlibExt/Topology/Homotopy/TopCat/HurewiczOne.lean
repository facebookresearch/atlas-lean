/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.TopCat.SingularFundamentalGroupoidPath
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PathTransportNaturality
public import Mathlib.Algebra.Group.TypeTags.Hom
public import MathlibExt.AlgebraicTopology.SimplicialSet.Homology.FundamentalGroupHurewiczNaturality
public import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy
public import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-!
# The first singular Hurewicz comparison on the original space

The actual singular fundamental-groupoid equivalence and the native
simplicial Hurewicz isomorphism identify integral singular H₁ with the
abelianization of the ordinary based fundamental group. The comparison is
natural for the original maps. Its path formula is the positive singular
one-cycle of the original loop, with no supplied calibration or H₁ inverse.
-/

public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

universe u

namespace TopCat

/-- The first Hurewicz homomorphism on the actual ordinary based fundamental group. -/
def fundamentalGroupHomologyOneHom (X : TopCat.{u}) (x : X) :
    FundamentalGroup X x →*
      Multiplicative
        (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj
          (singularIntegralCoefficients : AddCommGrpCat.{u})).obj X) := by
  exact (SSet.fundamentalGroupHomologyOneHom (TopCat.toSSet.obj X)
    (TopCat.toSSetObj₀Equiv.symm x)).comp
      (TopCat.singularFundamentalGroupoidEndMulEquiv X x).symm.toMonoidHom

private def singularBasedEdge (X : TopCat.{u}) (x : X) (γ : _root_.Path x x) :
    (TopCat.toSSet.obj X).Edge (TopCat.toSSetObj₀Equiv.symm x)
      (TopCat.toSSetObj₀Equiv.symm x) :=
  (TopCat.toSSetObjEdgeEquiv (X := X) (x := x) (y := x)).symm
    ((TopCat.pathEquiv (X := X) (x := x) (y := x)).symm γ)

private theorem singularEnd_inverse_fromPath
    (X : TopCat.{u}) (x : X) (γ : _root_.Path x x) :
    (TopCat.singularFundamentalGroupoidEndMulEquiv X x).symm
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
        End.of (TopCat.singularPathHom X γ) := by
  apply (TopCat.singularFundamentalGroupoidEndMulEquiv X x).injective
  rw [MulEquiv.apply_symm_apply]
  symm
  rw [TopCat.singularPathHom, TopCat.singularFundamentalGroupoidEndMulEquiv_homMk,
    (TopCat.toSSetObjEdgeEquiv (X := X) (x := x) (y := x)).apply_symm_apply,
    (TopCat.pathEquiv (X := X) (x := x) (y := x)).apply_symm_apply]

/-- The ordinary loop gives its actual positive singular one-cycle homology class. -/
def pathHomologyOneClass (X : TopCat.{u}) (x : X) (γ : _root_.Path x x) :
    (singularIntegralCoefficients : AddCommGrpCat.{u}) ⟶
      (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj
        (singularIntegralCoefficients : AddCommGrpCat.{u})).obj X) := by
  let K := TopCat.toSSet.obj X
  let R := (singularIntegralCoefficients : AddCommGrpCat.{u})
  let e := singularBasedEdge X x γ
  let C := K.chainComplex R
  have hd : K.ιChainComplex (R := R) e.edge ≫ C.d 1 0 = 0 := by
    rw [SSet.ιChainComplex_d, Fin.sum_univ_two]
    simp
  exact C.liftCycles (K.ιChainComplex (R := R) e.edge) 0 (by simp) hd ≫ C.homologyπ 1

/-- The loop class is the homology projection of the literal canonical singular edge cycle. -/
theorem pathHomologyOneClass_eq_singularCycle
    (X : TopCat.{u}) (x : X) (γ : _root_.Path x x) :
    let K := TopCat.toSSet.obj X
    let R := (singularIntegralCoefficients : AddCommGrpCat.{u})
    let e : K.Edge (TopCat.toSSetObj₀Equiv.symm x)
        (TopCat.toSSetObj₀Equiv.symm x) :=
      (TopCat.toSSetObjEdgeEquiv (X := X) (x := x) (y := x)).symm
        ((TopCat.pathEquiv (X := X) (x := x) (y := x)).symm γ)
    pathHomologyOneClass X x γ =
      (K.chainComplex R).liftCycles (K.ιChainComplex (R := R) e.edge) 0 (by simp)
        (by
          rw [SSet.ιChainComplex_d, Fin.sum_univ_two]
          simp [e.tgt_eq, e.src_eq]) ≫ (K.chainComplex R).homologyπ 1 := by
  rfl

/-- Calibration of the original based loop against its actual singular one-cycle. -/
theorem fundamentalGroupHomologyOneHom_fromPath
    (X : TopCat.{u}) (x : X) (γ : _root_.Path x x) :
    fundamentalGroupHomologyOneHom X x
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
        Multiplicative.ofAdd (pathHomologyOneClass X x γ (ULift.up (1 : ℤ))) := by
  let K := TopCat.toSSet.obj X
  let sx := TopCat.toSSetObj₀Equiv.symm x
  let e := singularBasedEdge X x γ
  have hInv := singularEnd_inverse_fromPath X x γ
  have hValue := SSet.fundamentalGroupHomologyOneHom_homMk K sx e
  change SSet.fundamentalGroupHomologyOneHom K sx
      ((TopCat.singularFundamentalGroupoidEndMulEquiv X x).symm
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))) = _
  have hImage := congrArg (SSet.fundamentalGroupHomologyOneHom K sx) hInv
  exact hImage.trans hValue

/-- The actual first singular homology isomorphism of a path-connected space. -/
def fundamentalGroupAbelianizationHomologyOneIso
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X) :
    AddCommGrpCat.of (Additive (Abelianization (FundamentalGroup X x))) ≅
      (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj
        (singularIntegralCoefficients : AddCommGrpCat.{u})).obj X) := by
  let e := (TopCat.singularFundamentalGroupoidEndMulEquiv X x).symm
  let a :
      AddCommGrpCat.of (Additive (Abelianization (FundamentalGroup X x))) ≅
        AddCommGrpCat.of (Additive (Abelianization
          (End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm x))))) :=
    AddEquiv.toAddCommGrpIso
      (X := AddCommGrpCat.of (Additive (Abelianization (FundamentalGroup X x))))
      (Y := AddCommGrpCat.of (Additive (Abelianization
        (End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm x))))))
      e.abelianizationCongr.toAdditive
  exact a ≪≫ SSet.fundamentalGroupAbelianizationHomologyOneIso
    (TopCat.toSSet.obj X) (TopCat.toSSetObj₀Equiv.symm x)

/-- On each original based class the isomorphism is the calibrated Hurewicz map. -/
theorem fundamentalGroupAbelianizationHomologyOneIso_hom_of
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X) (γ : FundamentalGroup X x) :
    (fundamentalGroupAbelianizationHomologyOneIso X x).hom
      (Additive.ofMul (Abelianization.of γ)) =
        Multiplicative.toAdd (fundamentalGroupHomologyOneHom X x γ) := by
  let K := TopCat.toSSet.obj X
  let sx := TopCat.toSSetObj₀Equiv.symm x
  let e := (TopCat.singularFundamentalGroupoidEndMulEquiv X x).symm
  change (SSet.fundamentalGroupAbelianizationHomologyOneIso K sx).hom
      (Additive.ofMul (e.abelianizationCongr (Abelianization.of γ))) =
    Multiplicative.toAdd (SSet.fundamentalGroupHomologyOneHom K sx (e γ))
  rw [abelianizationCongr_of, SSet.fundamentalGroupAbelianizationHomologyOneIso_hom]
  change Multiplicative.toAdd
      (SSet.fundamentalGroupAbelianizationHomologyOneHom K sx
        (Abelianization.of (e γ))) = _
  rw [SSet.fundamentalGroupAbelianizationHomologyOneHom_of]

/-- The singular map sends the literal source base vertex to the literal image base vertex. -/
theorem singularMappedVertex_eq
    {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)).obj
        (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm x)) =
      SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm (f x)) := by
  have hv : (TopCat.toSSet.map f).app (Opposite.op ⦋0⦌)
      (TopCat.toSSetObj₀Equiv.symm x) = TopCat.toSSetObj₀Equiv.symm (f x) := by
    rw [TopCat.toSSetObj₀Equiv_symm_apply, TopCat.toSSetObj₀Equiv_symm_apply]
    apply ULift.ext
    apply TopCat.ext
    intro z
    rfl
  rw [SSet.mapFundamentalGroupoid_obj_mk]
  exact congrArg SSet.FundamentalGroupoid.mk hv

/-- The computed equality isomorphism between the two singular image base vertices. -/
def singularMappedVertexIso
    {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)).obj
        (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm x)) ≅
      SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm (f x)) :=
  eqToIso (singularMappedVertex_eq f x)

/-- The computed singular image-point isomorphism is its actual equality isomorphism. -/
theorem singularMappedVertexIso_eq
    {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    singularMappedVertexIso f x = eqToIso (singularMappedVertex_eq f x) := by
  rfl

/-- The original fundamental-group map is conjugate to the actual singular groupoid map. -/
theorem singularEnd_inverse_naturality
    {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) (γ : FundamentalGroup X x) :
    (TopCat.singularFundamentalGroupoidEndMulEquiv Y (f x)).symm
      (FundamentalGroup.mapOfEq f.hom rfl γ) =
        SSet.basedFundamentalGroupHom (TopCat.toSSet.map f)
          (TopCat.toSSetObj₀Equiv.symm x) (TopCat.toSSetObj₀Equiv.symm (f x))
          (singularMappedVertexIso f x)
              ((TopCat.singularFundamentalGroupoidEndMulEquiv X x).symm γ) := by
  classical
  obtain ⟨p, hp⟩ := Quotient.exists_rep γ.asHom
  have hγ : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) = γ := by
    apply End.ext
    exact hp
  rw [← hγ]
  have hmap : FundamentalGroup.mapOfEq f.hom rfl
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (p.map f.hom.continuous)) := by
    rw [FundamentalGroup.mapOfEq_rfl]
    apply End.ext
    change Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk p) f.hom =
      Path.Homotopic.Quotient.mk (p.map f.hom.continuous)
    exact (Path.Homotopic.Quotient.mk_map p f.hom).symm
  rw [hmap, singularEnd_inverse_fromPath, singularEnd_inverse_fromPath]
  rw [SSet.basedFundamentalGroupHom_apply]
  apply End.ext
  change TopCat.singularPathHom Y (p.map f.hom.continuous) =
    eqToHom (singularMappedVertex_eq f x).symm ≫
      (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)).map
        (TopCat.singularPathHom X p) ≫
      eqToHom (singularMappedVertex_eq f x)
  exact (CategoryTheory.conj_eqToHom_iff_heq
    (TopCat.singularPathHom Y (p.map f.hom.continuous))
    ((SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)).map
      (TopCat.singularPathHom X p))
    (singularMappedVertex_eq f x).symm
    (singularMappedVertex_eq f x).symm).2
      (heq_of_eq (TopCat.singularPathHom_map f p)).symm

private theorem fundamentalGroupHomologyOneHom_naturality
    {X Y : TopCat.{u}} [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : X ⟶ Y) (x : X) (γ : FundamentalGroup X x) :
    Multiplicative.toAdd (fundamentalGroupHomologyOneHom Y (f x)
      (FundamentalGroup.mapOfEq f.hom rfl γ)) =
        (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj
          (singularIntegralCoefficients : AddCommGrpCat.{u})).map f)
          (Multiplicative.toAdd (fundamentalGroupHomologyOneHom X x γ)) := by
  let K := TopCat.toSSet.obj X
  let L := TopCat.toSSet.obj Y
  let sx := TopCat.toSSetObj₀Equiv.symm x
  let sy := TopCat.toSSetObj₀Equiv.symm (f x)
  let sf := TopCat.toSSet.map f
  let q := (TopCat.singularFundamentalGroupoidEndMulEquiv X x).symm γ
  have hn := ConcreteCategory.congr_hom
    (SSet.fundamentalGroupAbelianizationHomologyOneIso_hom_naturality
      sf sx sy (singularMappedVertexIso f x)) (Additive.ofMul (Abelianization.of q))
  change (SSet.fundamentalGroupAbelianizationHomologyOneIso L sy).hom
      (Additive.ofMul (Abelianization.of
        (SSet.basedFundamentalGroupHom sf sx sy (singularMappedVertexIso f x) q))) =
    (SSet.homologyMap sf
      (singularIntegralCoefficients : AddCommGrpCat.{u}) 1)
        ((SSet.fundamentalGroupAbelianizationHomologyOneIso K sx).hom
          (Additive.ofMul (Abelianization.of q))) at hn
  rw [SSet.fundamentalGroupAbelianizationHomologyOneIso_hom,
    SSet.fundamentalGroupAbelianizationHomologyOneIso_hom] at hn
  change Multiplicative.toAdd
      (SSet.fundamentalGroupAbelianizationHomologyOneHom L sy
        (Abelianization.of (SSet.basedFundamentalGroupHom sf sx sy
            (singularMappedVertexIso f x) q))) =
    (SSet.homologyMap sf
      (singularIntegralCoefficients : AddCommGrpCat.{u}) 1)
        (Multiplicative.toAdd
          (SSet.fundamentalGroupAbelianizationHomologyOneHom K sx
            (Abelianization.of q))) at hn
  rw [SSet.fundamentalGroupAbelianizationHomologyOneHom_of,
    SSet.fundamentalGroupAbelianizationHomologyOneHom_of] at hn
  have hEnd := singularEnd_inverse_naturality f x γ
  have hFirst := congrArg
    (fun a => Multiplicative.toAdd (SSet.fundamentalGroupHomologyOneHom L sy a)) hEnd
  exact hFirst.trans hn

/-- Naturality for the actual original map on based groups and singular H₁. -/
@[reassoc]
theorem fundamentalGroupAbelianizationHomologyOneIso_hom_naturality
    {X Y : TopCat.{u}} [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : X ⟶ Y) (x : X) :
    AddCommGrpCat.ofHom
      ((Abelianization.map (FundamentalGroup.mapOfEq f.hom rfl)).toAdditive) ≫
        (fundamentalGroupAbelianizationHomologyOneIso Y (f x)).hom =
      (fundamentalGroupAbelianizationHomologyOneIso X x).hom ≫
        (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj
          (singularIntegralCoefficients : AddCommGrpCat.{u})).map f) := by
  apply ConcreteCategory.hom_ext
  intro a
  have hpoint (b : Abelianization (FundamentalGroup X x)) :
      (fundamentalGroupAbelianizationHomologyOneIso Y (f x)).hom
        (Additive.ofMul (Abelianization.map (FundamentalGroup.mapOfEq f.hom rfl) b)) =
      (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj
        (singularIntegralCoefficients : AddCommGrpCat.{u})).map f)
        ((fundamentalGroupAbelianizationHomologyOneIso X x).hom (Additive.ofMul b)) := by
    induction b using QuotientGroup.induction_on with
    | _ γ =>
      change (fundamentalGroupAbelianizationHomologyOneIso Y (f x)).hom
          (Additive.ofMul (Abelianization.of
            (FundamentalGroup.mapOfEq f.hom rfl γ))) =
        (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj
          (singularIntegralCoefficients : AddCommGrpCat.{u})).map f)
          ((fundamentalGroupAbelianizationHomologyOneIso X x).hom
            (Additive.ofMul (Abelianization.of γ)))
      rw [fundamentalGroupAbelianizationHomologyOneIso_hom_of,
        fundamentalGroupAbelianizationHomologyOneIso_hom_of]
      exact fundamentalGroupHomologyOneHom_naturality f x γ
  exact hpoint (Additive.toMul a)

end TopCat

end
