/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.FieldCoinductionCochainNaturality

public import MathlibExt.AlgebraicGeometry.Sites.AlternatingCofaceCoefficientComparison

/-! Actual original field native comparison proof components. -/

/-! Original qualified proof block: CoindInvariantAlternatingComm -/
/-! Exact identity-component commutation of the actual additive coinduction invariant complex. -/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe u w uC vC uD vD
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace AlgebraicGeometry.Scheme.DerivedSections

attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual field invariants complex identifies with invariants of the same
canonical coinduction complex, with no new choice of cochain maps. -/
def fieldCoindInvariantCanonicalIso
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    (fieldCoindInvariantComplexFunctor.{u, w} k Ω).obj M ≅
      (((DiscreteAbelianAction.invariantsFunctor.{u, max u w} (G := Gal(Ω/k))).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (fieldCoindCanonicalComplex.{u, w} k Ω M)) := by
  unfold fieldCoindInvariantComplexFunctor fieldCoindCanonicalComplex
  change AlternatingCofaceMapComplex.obj
      (Monad.coresolution (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)) M ⋙
        DiscreteAbelianAction.invariantsFunctor.{u, max u w} (G := Gal(Ω/k))) ≅ _
  exact actualAlternatingCoefficientIso
    (DiscreteAbelianAction.invariantsFunctor.{u, max u w} (G := Gal(Ω/k)))
    (Monad.coresolution (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)) M)

set_option backward.isDefEq.respectTransparency.types false in
/-- The same canonical field commutation has identity degree components. -/
theorem fieldCoindInvariantCanonicalIso_hom_f
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (n : ℕ) :
    (fieldCoindInvariantCanonicalIso.{u, w} k Ω M).hom.f n = 𝟙 _ := rfl

/-- The actual coefficient map of invariants-after-coinduction as a fixed functor composition. -/
abbrev fieldCoindInvariantMappedFunctor :
    DiscreteAbelianAction.{u, max u w} Gal(Ω/k) ⥤ CochainComplex AddCommGrpCat.{max u w} ℕ :=
  fieldCoindCanonicalComplexFunctor.{u, w} k Ω ⋙
    (DiscreteAbelianAction.invariantsFunctor.{u, max u w} (G := Gal(Ω/k))).mapHomologicalComplex
      (ComplexShape.up ℕ)

set_option backward.isDefEq.respectTransparency.types false in
/-- The same identity component comparison is natural in the literal coinduction coefficient functor. -/
def fieldCoindInvariantCanonicalNatIso :
    fieldCoindInvariantComplexFunctor.{u, w} k Ω ≅ fieldCoindInvariantMappedFunctor.{u, w} k Ω := by
  unfold fieldCoindInvariantComplexFunctor fieldCoindInvariantMappedFunctor fieldCoindCanonicalComplexFunctor
  exact Functor.isoWhiskerLeft
    (Monad.coresolutionFunctor (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)))
    (actualAlternatingCoefficientNatIso
      (DiscreteAbelianAction.invariantsFunctor.{u, max u w} (G := Gal(Ω/k))))

/-- The fixed natural comparison keeps identity maps on every actual degree object. -/
theorem fieldCoindInvariantCanonicalNatIso_hom_f
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (n : ℕ) :
    ((fieldCoindInvariantCanonicalNatIso.{u, w} k Ω).hom.app M).f n = 𝟙 _ := rfl

end AlgebraicGeometry.Scheme.DerivedSections
end

/-! Original qualified proof block: FieldCoindCoaugmentationCycle -/
/-! Actual constant coaugmentation cycle normalization for the SAME field native H0 map. -/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- The genuine canonical coaugmentation cycle on the actual invariants of the original coefficient. -/
def fieldCoindInvariantCoaugmentationCycle
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    (fieldInvariantFunctor.{u, w} k Ω).obj M ⟶
      ((fieldCoindInvariantComplexFunctor.{u, w} k Ω).obj M).cycles 0 :=
  let F := fieldInvariantFunctor.{u, w} k Ω
  let L := ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (fieldCoindCanonicalComplex.{u, w} k Ω M))
  L.liftCycles (F.map ((fieldCoindCanonicalCoaugmentation.{u, w} k Ω M).f 0))
    1 (by simp) (by
      change F.map ((fieldCoindCanonicalCoaugmentation.{u, w} k Ω M).f 0) ≫
        F.map ((fieldCoindCanonicalComplex.{u, w} k Ω M).d 0 1) = 0
      exact (F.map_comp _ _).symm.trans
        ((congrArg F.map ((congrArg
          (fun q => q ≫ (fieldCoindCanonicalComplex.{u, w} k Ω M).d 0 1)
          (fieldCoindCanonicalCoaugmentation_f_zero.{u, w} k Ω M)).trans
            (fieldCoindCanonicalCoaugmentation_closed.{u, w} k Ω M))).trans (F.map_zero _ _))) ≫
    HomologicalComplex.cyclesMap ((fieldCoindInvariantCanonicalNatIso.{u, w} k Ω).inv.app M) 0

end AlgebraicGeometry.Scheme.DerivedSections
end

/-! Original qualified proof block: CoaugmentationCycleTransport -/
/-! Actual cycle transport along the original comparison of augmented cochain complexes. -/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The actual cycle transported through a cochain comparison retains its original vector. -/
theorem transport_liftCycles_i
    {K L : CochainComplex C ℕ} (a : L ⟶ K) {A : C} (x : A ⟶ L.X 0)
    (hx : x ≫ L.d 0 1 = 0) :
    (L.liftCycles x 1 (by simp) hx ≫ HomologicalComplex.cyclesMap a 0) ≫ K.iCycles 0 =
      x ≫ a.f 0 := by
  rw [Category.assoc, HomologicalComplex.cyclesMap_i, HomologicalComplex.liftCycles_i_assoc]

end HomologicalComplex
end

/-! Original qualified proof block: FieldCoindH0VectorCurrent -/
@[expose] public section
section
/-! Characteristic of the actual invariant coaugmentation cycle through the fixed original cochain map. -/
public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- The original stored augmented unit map reaches the SAME original cochain degree. -/
def fieldCoindNativeCoaugmentationVectorCurrent
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    (fieldInvariantFunctor.{u, w} k Ω).obj M ⟶
      ((ContinuousCohomology.discreteCoefficientCochainFunctor.{u, w}
        (InfiniteGalois.profiniteGalGrp k Ω)).obj M).X 0 :=
  (fieldInvariantFunctor.{u, w} k Ω).map ((fieldCoindCanonicalCoaugmentation.{u, w} k Ω M).f 0) ≫
    (fieldCoindInvariantCochainIso.{u, w} k Ω M).hom.f 0

/-- The original augmented native cochain vector has its literal comparison composite. -/
theorem fieldCoindNativeCoaugmentationVectorCurrent_eq
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    fieldCoindNativeCoaugmentationVectorCurrent.{u, w} k Ω M =
      (fieldInvariantFunctor.{u, w} k Ω).map ((fieldCoindCanonicalCoaugmentation.{u, w} k Ω M).f 0) ≫
        (fieldCoindInvariantCochainIso.{u, w} k Ω M).hom.f 0 := by
  unfold fieldCoindNativeCoaugmentationVectorCurrent
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual native degree-zero coaugmentation has the literal constant coefficient value. -/
theorem fieldCoindNativeCoaugmentationVectorCurrent_value
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (x : (fieldInvariantFunctor.{u, w} k Ω).obj M) (g : Gal(Ω/k)) :
    (fieldCoindNativeCoaugmentationVectorCurrent.{u, w} k Ω M x).val g = x.val := by
  unfold fieldCoindNativeCoaugmentationVectorCurrent
  rw [fieldCoindInvariantCochainIso_hom_f, fieldCoindCanonicalCoaugmentation_f_zero]
  exact DiscreteAbelianAction.coindCoresolution_coaugmentation_apply.{u, w} Gal(Ω/k) M x.val g

end AlgebraicGeometry.Scheme.DerivedSections
end

/-! Original qualified proof block: NativeZeroCycleInclusion -/
/-! The actual generic invariant coefficient enters native H0 through the original constant cocycle. -/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe r v w
open CategoryTheory CategoryTheory.Limits

namespace ContinuousCohomology
variable {R : Type r} [Ring R] [TopologicalSpace R]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual constant invariant cocycle in the SAME native homogeneous complex. -/
def zeroCycleInclusion (G : ProfiniteGrp.{v}) (X : TopRep.{max v w, r, v} R G) :
    (TopRep.invariantsFunctor R G).obj X ⟶ (TopRep.homogeneousCochains X).cycles 0 :=
  (TopModuleCat.ofIso (ContinuousCohomology.d₀kerIso X)).inv ≫
    (ContinuousCohomology.cocycles₀Iso X).inv

/-- The native constant cocycle projection is the SAME stock zeroIso inverse. -/
theorem zeroCycleInclusion_projection
    (G : ProfiniteGrp.{v}) (X : TopRep.{max v w, r, v} R G) :
    zeroCycleInclusion G X ≫ ContinuousCohomology.π X 0 = (ContinuousCohomology.zeroIso X).inv := by
  exact (ContinuousCohomology.homogeneousZeroIso_inverse_projection.{r, v, w} X).symm

end ContinuousCohomology
end

/-! Original qualified proof block: NativeZeroCycleForgetNormalization -/
/-! Actual native H0 projection after the exact coefficient-forgetting homology comparison. -/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe v w
open CategoryTheory CategoryTheory.Limits

namespace ContinuousCohomology

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every genuine cycle of the actual original homogeneous complex retains its native
identity-evaluation H0 class after forgetting topology and scalar structure. -/
theorem discreteForgetZeroCycle_class
    (G : ProfiniteGrp.{v}) (X : TopRep.{max v w, 0, v} ℤ G)
    (A : AddCommGrpCat.{max v w}) (c : A ⟶
      (discreteCoefficientForget.{max v w}).obj ((TopRep.homogeneousCochains X).sc 0).cycles) :
    c ≫ (((TopRep.homogeneousCochains X).sc 0).mapCyclesIso
        discreteCoefficientForget.{max v w}).inv ≫
      (((discreteCoefficientForget.{max v w}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (TopRep.homogeneousCochains X)).homologyπ 0 ≫
      (((TopRep.homogeneousCochains X).sc 0).mapHomologyIso
        discreteCoefficientForget.{max v w}).hom =
    c ≫ discreteCoefficientForget.{max v w}.map (ContinuousCohomology.π X 0) := by
  let U := discreteCoefficientForget.{max v w}
  let K := TopRep.homogeneousCochains X
  let S := K.sc 0
  let eC := S.mapCyclesIso U
  let eH := S.mapHomologyIso U
  have h := CategoryTheory.ShortComplex.homologyπ_comp_mapHomologyIso_hom S U
  change c ≫ eC.inv ≫ (S.map U).homologyπ ≫ eH.hom = c ≫ U.map S.homologyπ
  exact (congrArg (fun q => c ≫ eC.inv ≫ q) h).trans
    ((congrArg (fun q => c ≫ q)
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ U.map S.homologyπ) eC.inv_hom_id).trans (Category.id_comp _)))))

end ContinuousCohomology
end
