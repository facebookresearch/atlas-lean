/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.ParameterizedExtension
public import MathlibExt.Topology.Category.CGWH.ProductHomotopy
public import MathlibExt.Topology.Category.CGWH.NativeProductCurrying
public import MathlibExt.Topology.Category.CGWH.CompactOpenPathHomotopy
public import MathlibExt.Topology.Homotopy.FundamentalGroupProductRestriction
public import MathlibExt.GroupTheory.PerfectHomomorphism

/-!
# Filling the ORIGINAL perfect inactive native family

The original native product comparison obtains its actual inverse from
the genuine CW model. The actual product-plus extension then supplies a
whole triangle. Its native currying, with the original comparison homotopy,
proves nullity in the RAW compact-open mapping space. One path homotopy
there gives a jointly continuous square on every active parameter.

The target fundamental group is commutative only at the actual image of
the original pair point. This proves the initial inactive subgroup-killing
condition; it is not used as an inference of joint nullity on its own.
No filler, inverse, product CW model, product cofibration or desired
native-product comparison is an input.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory HomotopicalAlgebra
open scoped ContinuousMap TopCat.modelCategory

universe u

namespace CGWH

private theorem productComparison_whiskerLeft
    {A X D : CGWH.{u, u}} (j : X ⟶ D) :
    @Eq C((A ⊗ X : CGWH.{u, u}), A × D)
      ((prodComparisonToTop A D).hom.comp
        (ConcreteCategory.hom (C := CGWH.{u, u}) (A ◁ j)))
      (((ContinuousMap.id A).prodMap
        (ConcreteCategory.hom (C := CGWH.{u, u}) j)).comp
          (prodComparisonToTop A X).hom) := by
  apply ContinuousMap.ext
  intro z
  apply Prod.ext
  · have h₁ : CartesianMonoidalCategory.fst A D ((A ◁ j) z) =
        (prodComparisonToTop A D ((A ◁ j) z)).1 := by
      simpa only [tensorEquivProd_apply_fst] using congrArg Prod.fst
        (tensorEquivProd_eq_prodComparisonToTop A D ((A ◁ j) z))
    have h₂ := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerLeft_fst A j) z
    have h₂' : CartesianMonoidalCategory.fst A D ((A ◁ j) z) =
        CartesianMonoidalCategory.fst A X z := by
      simpa only [ConcreteCategory.comp_apply] using h₂
    have h₃ : CartesianMonoidalCategory.fst A X z =
        (prodComparisonToTop A X z).1 := by
      simpa only [tensorEquivProd_apply_fst] using congrArg Prod.fst
        (tensorEquivProd_eq_prodComparisonToTop A X z)
    exact h₁.symm.trans (h₂'.trans h₃)
  · have h₁ : CartesianMonoidalCategory.snd A D ((A ◁ j) z) =
        (prodComparisonToTop A D ((A ◁ j) z)).2 := by
      simpa only [tensorEquivProd_apply_snd] using congrArg Prod.snd
        (tensorEquivProd_eq_prodComparisonToTop A D ((A ◁ j) z))
    have h₂ := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerLeft_snd A j) z
    have h₂' : CartesianMonoidalCategory.snd A D ((A ◁ j) z) =
        j (CartesianMonoidalCategory.snd A X z) := by
      simpa only [ConcreteCategory.comp_apply] using h₂
    have h₃ : CartesianMonoidalCategory.snd A X z =
        (prodComparisonToTop A X z).2 := by
      simpa only [tensorEquivProd_apply_snd] using congrArg Prod.snd
        (tensorEquivProd_eq_prodComparisonToTop A X z)
    exact h₁.symm.trans (h₂'.trans (congrArg j h₃))

/-- One jointly continuous square with all four ORIGINAL native-family faces. -/
public structure NativeParameterLoopFiller
    {A X B : CGWH.{u, u}} {x : X} (φ : A ⊗ X ⟶ B) (γ : Path x x) where
  /-- The actual square-by-active-source map. -/
  map : C((unitInterval × unitInterval) × A, B)
  /-- The initial face is the entire original native loop family. -/
  zero : ∀ s a, map ((0, s), a) = φ (tensorMk a (γ s))
  /-- The terminal face is the original inactive-unit family. -/
  one : ∀ s a, map ((1, s), a) = φ (tensorMk a x)
  /-- The original loop source face is fixed for all time. -/
  source : ∀ t a, map ((t, 0), a) = φ (tensorMk a x)
  /-- The original loop target face is fixed for all time. -/
  target : ∀ t a, map ((t, 1), a) = φ (tensorMk a x)

section PerfectInactive

variable {A X D B : CGWH.{u, u}} [T2Space A]
  [PathConnectedSpace A] [PathConnectedSpace X] [PathConnectedSpace D]
  (a : A) (x : X)
  [Cofibration (TopCat.const a : TopCat.of PUnit.{u + 1} ⟶ A.toTop)]
  [Cofibration (TopCat.const x : TopCat.of PUnit.{u + 1} ⟶ X.toTop)]
  [Group.IsPerfect (FundamentalGroup X x)]
  {j : X ⟶ D}
  [Cofibration (TopCat.const (j x) : TopCat.of PUnit.{u + 1} ⟶ D.toTop)]
  (hj : @TopCat.IsPlusConstructionAt.{u} X.toTop D.toTop (cgwhToTop.map j)
    x (j x) rfl (⊤ : Subgroup (FundamentalGroup X x))
    _root_.Subgroup.normal_top
    ((Group.IsPerfect.top_iff (G := FundamentalGroup X x)).mpr
      (inferInstance : Group.IsPerfect (FundamentalGroup X x))))
  (φ : A ⊗ X ⟶ B)
  [IsMulCommutative (FundamentalGroup B (φ (tensorMk a x)))]

include a hj

/-- The ORIGINAL curried native family kills the entire perfect inactive
fundamental group. The whole product-plus triangle and original comparison
inverse homotopy are derived and curried before this conclusion is made. -/
public theorem perfectInactiveFamily_curried_pi1_eq_one
    (p : FundamentalGroup X x) :
    FundamentalGroup.mapOfEq (nativeCurriedProductMap φ).hom rfl p = 1 := by
  letI : (⊤ : Subgroup (FundamentalGroup X x)).Normal := _root_.Subgroup.normal_top
  letI : Group.IsPerfect (⊤ : Subgroup (FundamentalGroup X x)) :=
    (Group.IsPerfect.top_iff (G := FundamentalGroup X x)).mpr
      (inferInstance : Group.IsPerfect (FundamentalGroup X x))
  obtain ⟨E, hE, hInv, hL, _⟩ :=
    prodComparisonToTop_homotopyEquiv_of_cofibrant_points A X a x
  let U : CGWH.{u, u} := A ⊗ X
  let q : C(U, A × X) := (prodComparisonToTop A X).hom
  let ψ : TopCat.of (A × X) ⟶ B.toTop :=
    TopCat.ofHom ((ConcreteCategory.hom (C := CGWH.{u, u}) φ).comp E.invFun)
  have hψ : ψ.hom =
      (ConcreteCategory.hom (C := CGWH.{u, u}) φ).comp E.invFun :=
    TopCat.hom_ofHom _
  have hkill : ∀ v ∈ TopCat.productPlusSubgroup a x
      (⊥ : Subgroup (FundamentalGroup A a)) (⊤ : Subgroup (FundamentalGroup X x)),
      FundamentalGroup.mapOfEq ψ.hom rfl v = 1 := by
    intro v hv
    apply FundamentalGroup.mapOfEq_product_subgroup_bot_left_eq_one a x
      (⊤ : Subgroup (FundamentalGroup X x)) ψ.hom ?_ v hv
    intro r _
    let f := ψ.hom.comp (FundamentalGroup.secondProductInclusion a)
    have hf : f x = φ (tensorMk a x) := by
      dsimp only [f]
      rw [hψ, ContinuousMap.comp_apply, ContinuousMap.comp_apply]
      exact congrArg φ hInv
    letI : IsMulCommutative (FundamentalGroup B (f x)) := hf.symm ▸ (inferInstance :
      IsMulCommutative (FundamentalGroup B (φ (tensorMk a x))))
    exact MonoidHom.eq_one_of_mem_perfect_subgroup
      (FundamentalGroup.mapOfEq f rfl)
      (⊤ : Subgroup (FundamentalGroup X x)) (Subgroup.mem_top r)
  have hPoint : (cgwhToTop.map j) x = j x := rfl
  letI : Cofibration
      (TopCat.const ((cgwhToTop.map j) x) :
        TopCat.of PUnit.{u + 1} ⟶ D.toTop) := by
    rw [hPoint]
    infer_instance
  obtain ⟨F, K, _⟩ :=
    hj.exists_product_parameter_extension (A := A.toTop) (C := B.toTop)
      a x ψ hkill
  let Fnative : A ⊗ D ⟶ B := ConcreteCategory.ofHom
    (F.hom.comp (prodComparisonToTop A D).hom)
  have hFnative : ConcreteCategory.hom (C := CGWH.{u, u}) Fnative =
      F.hom.comp (prodComparisonToTop A D).hom :=
    ConcreteCategory.hom_ofHom _
  let sf : A ⊗ X ⟶ B := (A ◁ j) ≫ Fnative
  let jp : TopCat.of (A × X) ⟶ TopCat.of (A × D) :=
    TopCat.ofHom ((ContinuousMap.id A).prodMap (ConcreteCategory.hom (C := CGWH.{u, u}) j))
  have hs : (jp ≫ F).hom.comp q = ConcreteCategory.hom (C := CGWH.{u, u}) sf := by
    have hJP : jp.hom =
        (ContinuousMap.id A).prodMap (ConcreteCategory.hom (C := CGWH.{u, u}) j) :=
      TopCat.hom_ofHom _
    rw [TopCat.hom_comp, hJP]
    apply ContinuousMap.ext
    intro z
    have hright : ConcreteCategory.hom (C := CGWH.{u, u}) sf z =
        F.hom (prodComparisonToTop A D ((A ◁ j) z)) := by
      dsimp only [sf]
      rw [ConcreteCategory.comp_apply]
      exact congrArg (fun k : C((A ⊗ D : CGWH.{u, u}), B) => k ((A ◁ j) z)) hFnative
    exact (congrArg F
      (congrArg (fun f : C(U, A × D) => f z) (productComparison_whiskerLeft j)).symm).trans
        hright.symm
  have hr : ψ.hom.comp q =
      (ConcreteCategory.hom (C := CGWH.{u, u}) φ).comp (E.invFun.comp q) := by
    apply ContinuousMap.ext
    intro z
    rw [hψ]
    rfl
  let KL : ContinuousMap.Homotopy (E.invFun.comp q) (ContinuousMap.id U) :=
    hL.some.toHomotopy.cast (congrArg (fun f => E.invFun.comp f) hE) rfl
  let KR : ContinuousMap.Homotopy
      ((ConcreteCategory.hom (C := CGWH.{u, u}) φ).comp (E.invFun.comp q))
      (ConcreteCategory.hom (C := CGWH.{u, u}) φ) :=
    ((ContinuousMap.Homotopy.refl (ConcreteCategory.hom (C := CGWH.{u, u}) φ)).comp KL).cast
      rfl (by apply ContinuousMap.ext; intro z; rfl)
  let KN : ContinuousMap.Homotopy
      (ConcreteCategory.hom (C := CGWH.{u, u}) sf) (ConcreteCategory.hom (C := CGWH.{u, u}) φ) :=
    ((K.compContinuousMap q).cast hs hr).trans KR
  let cF := nativeCurriedProductMap Fnative
  let cφ := nativeCurriedProductMap φ
  let J : X.toTop ⟶ D.toTop := cgwhToTop.map j
  have hJPoint : J x = j x := rfl
  have he : (nativeCurriedProductMap sf).hom = (J ≫ cF).hom :=
    congrArg (fun f : X.toTop ⟶ TopCat.of C(A, B) => f.hom)
      (nativeCurriedProductMap_comp_second j Fnative)
  let HC : TopCat.Homotopy (J ≫ cF) cφ :=
    (nativeCurriedProductHomotopy KN).cast he rfl
  have hjp : FundamentalGroup.mapOfEq (x := x) (y := j x) J.hom hJPoint p = 1 := by
    have hKernel :
        (FundamentalGroup.mapOfEq (x := x) (y := j x) J.hom hJPoint).ker =
          (⊤ : Subgroup (FundamentalGroup X x)) :=
      TopCat.IsPlusConstructionAt.kernel_eq
        (X := X.toTop) (Y := D.toTop) (f := J) (x := x) (y := j x)
        (hxy := hJPoint) (P := (⊤ : Subgroup (FundamentalGroup X x))) hj
    have hMem : p ∈
        (FundamentalGroup.mapOfEq (x := x) (y := j x) J.hom hJPoint).ker :=
      Eq.mp (congrArg (fun P : Subgroup (FundamentalGroup X x) => p ∈ P)
        hKernel.symm) (Subgroup.mem_top p)
    exact MonoidHom.mem_ker.mp hMem
  have hCompEval (z : X) : (J ≫ cF) z = cF (J z) :=
    ConcreteCategory.comp_apply (C := TopCat.{u}) J cF z
  have hComp : (J ≫ cF).hom = cF.hom.comp J.hom := by
    apply ContinuousMap.ext
    intro z
    exact hCompEval z
  have hMid : cF (j x) = (J ≫ cF) x :=
    (congrArg cF hJPoint).symm.trans (hCompEval x).symm
  have hWhole : (cF.hom.comp J.hom) x = (J ≫ cF) x :=
    (hCompEval x).symm
  have hMap :
      FundamentalGroup.mapOfEq (x := x) (y := (J ≫ cF) x) (J ≫ cF).hom rfl =
        FundamentalGroup.mapOfEq (x := x) (y := (J ≫ cF) x)
          (cF.hom.comp J.hom) hWhole :=
    FundamentalGroup.mapOfEq_congr hComp rfl hWhole
  have hCompose := FundamentalGroup.mapOfEq_comp
    (x := x) (y := j x) (z := (J ≫ cF) x) J.hom cF.hom hJPoint hMid hWhole
  have hValue :
      ((FundamentalGroup.mapOfEq cF.hom hMid).comp
        (FundamentalGroup.mapOfEq J.hom hJPoint)) p = 1 :=
    (congrArg (FundamentalGroup.mapOfEq cF.hom hMid) hjp).trans
      (map_one (FundamentalGroup.mapOfEq cF.hom hMid))
  have hp : FundamentalGroup.mapOfEq (J ≫ cF).hom rfl p = 1 :=
    (congrArg (fun m : FundamentalGroup X x →*
        FundamentalGroup C(A, B) ((J ≫ cF) x) => m p)
      (hMap.trans hCompose)).trans hValue
  exact (FundamentalGroup.mapOfEq_eq_one_iff_of_homotopy HC x p).mp hp

/-- A complete jointly continuous filler for the ORIGINAL native loop
family, at all active parameters and with both loop edges fixed. The
mapping-space nullhomotopy is chosen only after its actual class is proved
one by the whole product-plus argument. -/
public def wholePerfectInactiveLoopFiller (γ : Path x x) :
    NativeParameterLoopFiller φ γ := by
  let f := nativeCurriedProductMap φ
  let p := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)
  have hp : FundamentalGroup.mapOfEq f.hom rfl p = 1 :=
    perfectInactiveFamily_curried_pi1_eq_one (a := a) (x := x) (hj := hj) (φ := φ) p
  have hmap : FundamentalGroup.mapOfEq f.hom rfl p =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (γ.map f.hom.continuous)) := by
    apply End.ext
    rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl]
    exact (Path.Homotopic.Quotient.mk_map γ f.hom).symm
  have he : Path.Homotopic.Quotient.mk (γ.map f.hom.continuous) =
      Path.Homotopic.Quotient.mk (Path.refl (f x)) :=
    congrArg End.asHom (hmap.symm.trans hp)
  let H : (γ.map f.hom.continuous).Homotopy (Path.refl (f x)) :=
    (Path.Homotopic.Quotient.exact he).some
  refine
    { map := compactOpenPathHomotopyEvaluation H
      zero := ?_
      one := ?_
      source := ?_
      target := ?_ }
  · intro s a₀
    exact (compactOpenPathHomotopyEvaluation_zero H s a₀).trans
      (nativeCurriedProductMap_apply φ (γ s) a₀)
  · intro s a₀
    exact (compactOpenPathHomotopyEvaluation_one H s a₀).trans
      (nativeCurriedProductMap_apply φ x a₀)
  · intro t a₀
    exact (compactOpenPathHomotopyEvaluation_source H t a₀).trans
      (nativeCurriedProductMap_apply φ x a₀)
  · intro t a₀
    exact (compactOpenPathHomotopyEvaluation_target H t a₀).trans
      (nativeCurriedProductMap_apply φ x a₀)

end PerfectInactive

end CGWH

end
