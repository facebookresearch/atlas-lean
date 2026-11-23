/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.InactivePermutationFactor
public import MathlibExt.KTheory.Ring.StableGeneralLinear.PlusFundamentalGroupCommutativity
public import MathlibExt.CategoryTheory.ClassifyingSpace.CGWHProduct
public import MathlibExt.CategoryTheory.ClassifyingSpace.ProductLoop
public import MathlibExt.KTheory.Ring.StableGeneralLinear.InactiveNaturalLoop
public import MathlibExt.CategoryTheory.ClassifyingSpace.PerfectPlus
public import MathlibExt.AlgebraicTopology.PlusConstruction.NativeParameterizedLoopFiller
public import MathlibExt.Topology.CWComplex.NativeSingularModel

/-!
# The whole original finite BGL inactive family

The actual product-category realization and commuting block functor define
one family on the ORIGINAL BG_n parameter space and the genuine perfect
inactive image. Its selected image in the independently constructed plus
is lifted through the DERIVED pointed native singular model.

The perfect group's auxiliary plus map, both product comparison homotopies,
the raw mapping-space loop and its one joint contraction are all derived.
Target fundamental-group commutativity follows from the original stable
commutator kernel. No H-space structure, inactive factor, filler, model,
joint nullity, or inverse family is a caller premise.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory HomotopicalAlgebra
open scoped ContinuousMap TopCat.modelCategory

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R] {n N : ℕ}

/-- The actual native classifying map of the whole original finite active
and computed perfect inactive family, with the original opposite convention. -/
public def originalInactiveClassifyingNativeMap (h : n ≤ N) :
    CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R) ⊗
      CategoryTheory.groupClassifyingNative.{u, u}
        (InactivePerfectMatrixGroup R N (initialActiveIndices n N)) ⟶ BGL.{u} R :=
  (CategoryTheory.classifyingSpaceCGWHProductIso.{u}
    (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)
    (SingleObj (InactivePerfectMatrixGroup R N (initialActiveIndices n N))ᵐᵒᵖ)).inv ≫
      CategoryTheory.classifyingSpaceCGWH.{u, u, 0}.map
        (initialInactiveClassifyingFamilyFunctor R h).toCatHom

/-- The original pair of native vertices maps to the original BGL vertex. -/
public theorem originalInactiveClassifyingNativeMap_point (h : n ≤ N) :
    originalInactiveClassifyingNativeMap R h
        (CGWH.tensorMk
          (CategoryTheory.groupClassifyingNativePoint.{u, u} (Matrix.GeneralLinearGroup (Fin n) R))
          (CategoryTheory.groupClassifyingNativePoint.{u, u}
            (InactivePerfectMatrixGroup R N (initialActiveIndices n N)))) =
      BGLBasepoint.{u} R := by
  rw [CategoryTheory.groupClassifyingNativePoint_eq_categoryPoint.{u, u},
    CategoryTheory.groupClassifyingNativePoint_eq_categoryPoint.{u, u}]
  change CategoryTheory.classifyingSpaceCGWH.{u, u, 0}.map
      (initialInactiveClassifyingFamilyFunctor R h).toCatHom
        ((CategoryTheory.classifyingSpaceCGWHProductIso.{u}
          (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)
          (SingleObj (InactivePerfectMatrixGroup R N (initialActiveIndices n N))ᵐᵒᵖ)).inv
            (CGWH.tensorMk _ _)) = _
  rw [CategoryTheory.classifyingSpaceCGWHProductIso_inv_point.{u, u, 0},
    CategoryTheory.classifyingSpaceCGWH_map_point.{u, u, 0}]
  rfl

/-- The original whole native prism of the computed inactive natural loop. -/
public abbrev originalInactiveLoopNativePrism (h : n ≤ N)
    (g : InactivePerfectMatrixGroup R N (initialActiveIndices n N)) :
    CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R) ⊗
      CGWH.nativeInterval.{u, u} ⟶ BGL.{u} R :=
  CategoryTheory.productLoopNativeMap
    (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)
    (SingleObj (InactivePerfectMatrixGroup R N (initialActiveIndices n N))ᵐᵒᵖ)
    (SingleObj.star _) (MulOpposite.op g⁻¹) (initialInactiveClassifyingFamilyFunctor R h)

/-- At EVERY original active parameter, the native prism is the SAME
whole family evaluated on the ORIGINAL normalized inactive group loop. -/
public theorem originalInactiveLoopNativePrism_apply (h : n ≤ N)
    (g : InactivePerfectMatrixGroup R N (initialActiveIndices n N))
    (a : CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R))
    (t : unitInterval) :
    originalInactiveLoopNativePrism R h g
        (CGWH.tensorMk a (CGWH.nativeIntervalHomeomorph.{u, u}.symm t)) =
      originalInactiveClassifyingNativeMap R h
        (CGWH.tensorMk a (CategoryTheory.groupClassifyingNativeLoop.{u, u}
          (InactivePerfectMatrixGroup R N (initialActiveIndices n N)) g t)) := by
  rw [CategoryTheory.groupClassifyingNativeLoop_realized_edge.{u, u}]
  exact CategoryTheory.productLoopNativeMap_apply
    (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)
    (SingleObj (InactivePerfectMatrixGroup R N (initialActiveIndices n N))ᵐᵒᵖ)
    (SingleObj.star _) (MulOpposite.op g⁻¹) (initialInactiveClassifyingFamilyFunctor R h) a t

private theorem nativeCompPoint
    {S T U : CGWH.{u, u}} (f : S ⟶ T) (g : T ⟶ U)
    (s : S) (t : T) (z : U) (hf : f s = t) (hg : g t = z) :
    (f ≫ g) s = z := by
  exact (ConcreteCategory.comp_apply (C := CGWH.{u, u}) f g s).trans
    ((congrArg g hf).trans hg)

section ActualPlusTarget

variable {Y : TopCat.{u}} (i : ordinaryBGL R ⟶ Y) (y : Y)
  (hi : i (ordinaryBGLBasepoint R) = y)
  [Cofibration (TopCat.const y : TopCat.of PUnit.{u + 1} ⟶ Y)]

/-- The SAME original BGL-to-independent-plus map followed by its
DERIVED pointed native singular-model inverse. -/
public abbrev originalBGLToPlusNativeModel : BGL.{u} R ⟶ TopCat.nativeSingularSpace Y :=
  ConcreteCategory.ofHom
    ((TopCat.nativeSingularPointModelOfCofibrantPoint Y y).equiv.invFun.comp
      (i.hom.comp (BGLToOrdinaryTopIso.{u} R).hom.hom))

include hi in
/-- The ORIGINAL global inclusion followed by its derived pointed model
inverse retains the ORIGINAL marked BGL image point exactly. -/
public theorem originalBGLToPlusNativeModel_point :
    originalBGLToPlusNativeModel R i y (BGLBasepoint R) = TopCat.nativeSingularPoint Y y := by
  let β : C(BGL.{u} R, ordinaryBGL R) := (BGLToOrdinaryTopIso.{u} R).hom.hom
  let M := TopCat.nativeSingularPointModelOfCofibrantPoint Y y
  have hβ : β (BGLBasepoint R) = ordinaryBGLBasepoint R :=
    BGLToOrdinaryTopIso_hom_basepoint R
  have hImage : i (β (BGLBasepoint R)) = y := (congrArg i hβ).trans hi
  change M.equiv.invFun (i (β (BGLBasepoint R))) = TopCat.nativeSingularPoint Y y
  exact (congrArg M.equiv.invFun hImage).trans M.backwardPoint

/-- The original classifying family followed by the SAME independent
plus map and the derived pointed inverse into its native singular model. -/
public def originalInactiveFamilyToModel (h : n ≤ N) :
    CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R) ⊗
      CategoryTheory.groupClassifyingNative.{u, u}
        (InactivePerfectMatrixGroup R N (initialActiveIndices n N)) ⟶
      TopCat.nativeSingularSpace Y :=
  originalInactiveClassifyingNativeMap R h ≫ originalBGLToPlusNativeModel R i y

include hi in
/-- The actual native model image is its original singular vertex. -/
public theorem originalInactiveFamilyToModel_point (h : n ≤ N) :
    originalInactiveFamilyToModel R i y h
        (CGWH.tensorMk
          (CategoryTheory.groupClassifyingNativePoint.{u, u} (Matrix.GeneralLinearGroup (Fin n) R))
          (CategoryTheory.groupClassifyingNativePoint.{u, u}
            (InactivePerfectMatrixGroup R N (initialActiveIndices n N)))) =
      TopCat.nativeSingularPoint Y y := by
  let A : CGWH.{u, u} :=
    CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R)
  let X : CGWH.{u, u} :=
    CategoryTheory.groupClassifyingNative.{u, u}
      (InactivePerfectMatrixGroup R N (initialActiveIndices n N))
  let a : A := CategoryTheory.groupClassifyingNativePoint.{u, u}
    (Matrix.GeneralLinearGroup (Fin n) R)
  let x : X := CategoryTheory.groupClassifyingNativePoint.{u, u}
    (InactivePerfectMatrixGroup R N (initialActiveIndices n N))
  let z : (A ⊗ X : CGWH.{u, u}) := CGWH.tensorMk a x
  let f : (A ⊗ X : CGWH.{u, u}) ⟶ BGL.{u} R := originalInactiveClassifyingNativeMap R h
  let g : BGL.{u} R ⟶ TopCat.nativeSingularSpace Y := originalBGLToPlusNativeModel R i y
  have hf : f z = BGLBasepoint R :=
    originalInactiveClassifyingNativeMap_point (R := R) (h := h)
  have hg : g (BGLBasepoint R) = TopCat.nativeSingularPoint Y y :=
    originalBGLToPlusNativeModel_point (R := R) (i := i) (y := y) (hi := hi)
  exact nativeCompPoint (S := (A ⊗ X : CGWH.{u, u})) (T := BGL.{u} R)
    (U := TopCat.nativeSingularSpace Y) f g z (BGLBasepoint R)
    (TopCat.nativeSingularPoint Y y) hf hg

/-- The actual original inactive prism in the native model of the SAME plus target. -/
public abbrev originalInactiveLoopPrismToModel (h : n ≤ N)
    (g : InactivePerfectMatrixGroup R N (initialActiveIndices n N)) :
    CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R) ⊗
      CGWH.nativeInterval.{u, u} ⟶ TopCat.nativeSingularSpace Y :=
  originalInactiveLoopNativePrism R h g ≫ originalBGLToPlusNativeModel R i y

/-- Its complete original active-parameter path agrees with the SAME
native model family. No selected-vertex trace is substituted. -/
public theorem originalInactiveLoopPrismToModel_apply (h : n ≤ N)
    (g : InactivePerfectMatrixGroup R N (initialActiveIndices n N))
    (a : CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R))
    (t : unitInterval) :
    originalInactiveLoopPrismToModel R i y h g
        (CGWH.tensorMk a (CGWH.nativeIntervalHomeomorph.{u, u}.symm t)) =
      originalInactiveFamilyToModel R i y h
        (CGWH.tensorMk a (CategoryTheory.groupClassifyingNativeLoop.{u, u}
          (InactivePerfectMatrixGroup R N (initialActiveIndices n N)) g t)) := by
  change originalBGLToPlusNativeModel R i y
    (originalInactiveLoopNativePrism R h g (CGWH.tensorMk a
      (CGWH.nativeIntervalHomeomorph.{u, u}.symm t))) =
    originalBGLToPlusNativeModel R i y
      (originalInactiveClassifyingNativeMap R h (CGWH.tensorMk a
        (CategoryTheory.groupClassifyingNativeLoop.{u, u}
          (InactivePerfectMatrixGroup R N (initialActiveIndices n N)) g t)))
  exact congrArg (originalBGLToPlusNativeModel R i y)
    (originalInactiveLoopNativePrism_apply R h g a t)

/-- Every original inactive loop has one jointly continuous square on
ALL original BG_n parameters, with the original loop face and both edge
faces exactly fixed. All auxiliary plus/model/filler data are derived. -/
public theorem exists_originalInactiveFamilyFiller
    (hp : TopCat.IsPlusConstructionAt i (ordinaryBGLBasepoint R) y hi (BGLPlusSubgroup R))
    (h : n ≤ N)
    (γ : Path
      (CategoryTheory.groupClassifyingNativePoint.{u, u}
        (InactivePerfectMatrixGroup R N (initialActiveIndices n N)))
      (CategoryTheory.groupClassifyingNativePoint.{u, u}
        (InactivePerfectMatrixGroup R N (initialActiveIndices n N)))) :
    Nonempty (CGWH.NativeParameterLoopFiller (originalInactiveFamilyToModel R i y h) γ) := by
  let G := InactivePerfectMatrixGroup R N (initialActiveIndices n N)
  let A := CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R)
  let X := CategoryTheory.groupClassifyingNative.{u, u} G
  let a : A := CategoryTheory.groupClassifyingNativePoint.{u, u} (Matrix.GeneralLinearGroup (Fin n) R)
  let x : X := CategoryTheory.groupClassifyingNativePoint.{u, u} G
  let φ := originalInactiveFamilyToModel R i y h
  letI : Group.IsPerfect G := inactivePerfectMatrixGroup_isPerfect R N (initialActiveIndices n N)
  letI : T2Space A := CategoryTheory.groupClassifyingNative_t2Space.{u, u} _
  letI : PathConnectedSpace A := CategoryTheory.groupClassifyingNative_pathConnected.{u, u} _
  letI : PathConnectedSpace X := CategoryTheory.groupClassifyingNative_pathConnected.{u, u} G
  letI : Cofibration (TopCat.const a : TopCat.of PUnit.{u + 1} ⟶ A.toTop) :=
    CategoryTheory.groupClassifyingNative_pointMap_cofibration.{u, u} _
  letI : Cofibration (TopCat.const x : TopCat.of PUnit.{u + 1} ⟶ X.toTop) :=
    CategoryTheory.groupClassifyingNative_pointMap_cofibration.{u, u} G
  letI : Group.IsPerfect (FundamentalGroup X x) :=
    CategoryTheory.groupClassifyingNativeFundamental_isPerfect.{u, u} G
  obtain ⟨D, j, hD, hjPoint, hj⟩ :=
    CategoryTheory.exists_groupClassifying_native_perfectPlus G
  letI : PathConnectedSpace D := hD
  letI : Cofibration (TopCat.const (j x) : TopCat.of PUnit.{u + 1} ⟶ D.toTop) := hjPoint
  letI : IsMulCommutative (FundamentalGroup Y y) :=
    ordinaryBGL_plus_fundamentalGroup_isMulCommutative R hp
  let M := TopCat.nativeSingularPointModelOfCofibrantPoint Y y
  letI : IsMulCommutative (FundamentalGroup (TopCat.nativeSingularSpace Y)
      (TopCat.nativeSingularPoint Y y)) := M.fundamentalGroup_isMulCommutative
  letI : IsMulCommutative (FundamentalGroup (TopCat.nativeSingularSpace Y)
      (φ (CGWH.tensorMk a x))) :=
    (originalInactiveFamilyToModel_point (R := R) (i := i) (y := y) (hi := hi)
      (h := h)).symm ▸
      (inferInstance : IsMulCommutative (FundamentalGroup (TopCat.nativeSingularSpace Y)
        (TopCat.nativeSingularPoint Y y)))
  exact ⟨CGWH.wholePerfectInactiveLoopFiller a x hj φ γ⟩

end ActualPlusTarget

end AlgebraicKTheory.StableGL

end
