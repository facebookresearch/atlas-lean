/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.RepresentationTheory.Homological.ContCohomology.NativeZeroCochainClasses
public import MathlibExt.CategoryTheory.Abelian.CoaugmentationCycles

/-! Actual original field native comparison proof components. -/

/-! Original qualified proof block: NativeZeroShortComplexClass -/
/-! Actual zero-cycle class comparison on the literal native short complex. -/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe v w
open CategoryTheory CategoryTheory.Limits

namespace ContinuousCohomology

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A true short-complex cycle with the actual constant invariant coefficient has
its SAME native H0 zeroIso class under the canonical forgetting homology comparison. -/
theorem nativeZeroShortComplexClass_of_constant_cycle
    (G : ProfiniteGrp.{v}) (X : TopRep.{max v w, 0, v} ℤ G)
    (T : ShortComplex AddCommGrpCat.{max v w})
    (e : T ≅ ((TopRep.homogeneousCochains X).sc 0).map discreteCoefficientForget.{max v w})
    (p : discreteCoefficientForget.{max v w}.obj ((TopRep.invariantsFunctor ℤ G).obj X) ⟶ T.cycles)
    (hc : p ≫ T.iCycles ≫ e.hom.τ₂ =
      discreteCoefficientForget.{max v w}.map
        (zeroCycleInclusion G X ≫ (TopRep.homogeneousCochains X).iCycles 0)) :
    p ≫ T.homologyπ ≫ ShortComplex.homologyMap e.hom ≫
      (((TopRep.homogeneousCochains X).sc 0).mapHomologyIso discreteCoefficientForget.{max v w}).hom =
      discreteCoefficientForget.{max v w}.map (zeroIso X).inv := by
  let U := discreteCoefficientForget.{max v w}
  let S := (TopRep.homogeneousCochains X).sc 0
  let c := zeroCycleInclusion G X
  let z := (S.mapCyclesIso U).inv
  have hz : z ≫ (S.map U).iCycles = U.map S.iCycles := by
    exact (congrArg (fun q => z ≫ q) (S.mapCyclesIso_hom_iCycles U).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ U.map S.iCycles) (S.mapCyclesIso U).inv_hom_id).trans
          (Category.id_comp _)))
  have hcycle : p ≫ ShortComplex.cyclesMap e.hom = U.map c ≫ z := by
    apply (cancel_mono (S.map U).iCycles).mp
    have hn := ShortComplex.cyclesMap_i e.hom
    have hr : (U.map c ≫ z) ≫ (S.map U).iCycles = U.map (c ≫ S.iCycles) :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun q => U.map c ≫ q) hz).trans (U.map_comp _ _).symm)
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun q => p ≫ q) hn).trans (hc.trans hr.symm))
  have hπ := ShortComplex.homologyπ_naturality e.hom
  have hforget := discreteForgetZeroCycle_class G X (U.obj ((TopRep.invariantsFunctor ℤ G).obj X)) (U.map c)
  have hπ' : p ≫ T.homologyπ ≫ ShortComplex.homologyMap e.hom =
      U.map c ≫ z ≫ (S.map U).homologyπ := by
    rw [hπ, ← Category.assoc, hcycle, Category.assoc]
  have hforget' : (U.map c ≫ z ≫ (S.map U).homologyπ) ≫ (S.mapHomologyIso U).hom =
      U.map c ≫ U.map (π X 0) := by
    exact (Category.assoc _ _ _).trans hforget
  exact (congrArg (fun q => q ≫ (S.mapHomologyIso U).hom) hπ').trans
    (hforget'.trans ((U.map_comp _ _).symm.trans (congrArg U.map (zeroCycleInclusion_projection G X))))

end ContinuousCohomology
end

/-! Original qualified proof block: NativeZeroCycleCoefficientSystem -/
/-! Complete native H0 class computation from the actual coefficient-cycle vector. -/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe v w
open CategoryTheory CategoryTheory.Limits

namespace ContinuousCohomology

/-- Actual coefficient-cycle data on the literal original homogeneous complex. -/
structure NativeZeroCoefficientCycle (G : ProfiniteGrp.{v})
    (X : TopRep.{max v w, 0, v} ℤ G) (T : ShortComplex AddCommGrpCat.{max v w}) where
  /-- The actual original coefficient-complex isomorphism. -/
  comparison : T ≅ ((TopRep.homogeneousCochains X).sc 0).map discreteCoefficientForget.{max v w}
  /-- The actual original invariant coaugmentation cycle. -/
  cycle : discreteCoefficientForget.{max v w}.obj ((TopRep.invariantsFunctor ℤ G).obj X) ⟶ T.cycles
  /-- The actual cycle vector is the original constant invariant coefficient. -/
  vector : cycle ≫ T.iCycles ≫ comparison.hom.τ₂ =
    discreteCoefficientForget.{max v w}.map
      (zeroCycleInclusion G X ≫ (TopRep.homogeneousCochains X).iCycles 0)

/-- The original native zeroIso inverse is internally computed from the actual
coefficient-cycle data; it is not an additional normalization assumption. -/
theorem NativeZeroCoefficientCycle.class_eq
    (G : ProfiniteGrp.{v}) (X : TopRep.{max v w, 0, v} ℤ G)
    (T : ShortComplex AddCommGrpCat.{max v w}) (d : NativeZeroCoefficientCycle G X T) :
    d.cycle ≫ T.homologyπ ≫ ShortComplex.homologyMap d.comparison.hom ≫
      (((TopRep.homogeneousCochains X).sc 0).mapHomologyIso discreteCoefficientForget.{max v w}).hom =
      discreteCoefficientForget.{max v w}.map (zeroIso X).inv :=
  nativeZeroShortComplexClass_of_constant_cycle G X T d.comparison d.cycle d.vector

end ContinuousCohomology
end

/-! Original qualified proof block: NativeZeroCycleVector -/
/-! Actual constant invariant cycle values in the original native homogeneous complex. -/
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
/-- The native constant-cycle inclusion keeps the exact original invariant coefficient. -/
theorem zeroCycleInclusion_constant
    (G : ProfiniteGrp.{v}) (X : TopRep.{max v w, r, v} R G)
    (x : X.ρ.invariants) (g : G) :
    (((zeroCycleInclusion G X ≫ (TopRep.homogeneousCochains X).iCycles 0) x).val g) = x.val := by
  unfold zeroCycleInclusion
  let c : (TopRep.invariantsFunctor R G).obj X ⟶
      (show TopModuleCat.{max v w} R from
        @TopModuleCat.of R _ _ (((TopRep.homogeneousCochains X).d 0 1).hom.ker)
          _ (((TopRep.homogeneousCochains X).d 0 1).hom.ker.module) _ _ _) :=
    (TopModuleCat.ofIso (ContinuousCohomology.d₀kerIso X)).inv
  let z := ContinuousCohomology.cocycles₀Iso X
  have hz : z.inv ≫ (TopRep.homogeneousCochains X).iCycles 0 =
      TopModuleCat.kerι ((TopRep.homogeneousCochains X).d 0 1) := by
    exact (congrArg (fun q => z.inv ≫ q) (homogeneousZeroCocycles_projection.{r, v, w} X).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ TopModuleCat.kerι ((TopRep.homogeneousCochains X).d 0 1)) z.inv_hom_id).trans
          (Category.id_comp _)))
  have h := congrArg
    (fun q : (show TopModuleCat.{max v w} R from
        @TopModuleCat.of R _ _ (((TopRep.homogeneousCochains X).d 0 1).hom.ker)
          _ (((TopRep.homogeneousCochains X).d 0 1).hom.ker.module) _ _ _) ⟶
        (TopRep.homogeneousCochains X).X 0 => ((c ≫ q) x).val g) hz
  exact h.trans (homogeneousZeroIso_inverse_constant.{r, v, w} X x g)

end ContinuousCohomology
end

/-! Original qualified proof block: NativeZeroCoefficientCycleConstructor -/
/-! Genuine native H0 coefficient-cycle construction from original vectors. -/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe v w
open CategoryTheory CategoryTheory.Limits

namespace ContinuousCohomology

/-- A genuine cycle whose actual coefficient vector is pointwise constant constructs
its native zero-class data, with no supplied homology equality. -/
def nativeZeroCoefficientCycleOfVector
    (G : ProfiniteGrp.{v}) (X : TopRep.{max v w, 0, v} ℤ G)
    (T : ShortComplex AddCommGrpCat.{max v w})
    (e : T ≅ ((TopRep.homogeneousCochains X).sc 0).map discreteCoefficientForget.{max v w})
    (p : discreteCoefficientForget.{max v w}.obj ((TopRep.invariantsFunctor ℤ G).obj X) ⟶ T.cycles)
    (hv : ∀ (x : discreteCoefficientForget.{max v w}.obj ((TopRep.invariantsFunctor ℤ G).obj X)) (g : G), ((p ≫ T.iCycles ≫ e.hom.τ₂) x).val g = x.val) :
    NativeZeroCoefficientCycle G X T where
  comparison := e
  cycle := p
  vector := by
    apply ConcreteCategory.ext
    apply AddMonoidHom.ext
    intro x
    apply Subtype.ext
    apply ContinuousMap.ext
    intro g
    exact (hv x g).trans (zeroCycleInclusion_constant G X x g).symm

end ContinuousCohomology
end
