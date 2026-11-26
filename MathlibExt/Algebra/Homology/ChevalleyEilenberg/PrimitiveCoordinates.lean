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

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoalgebraPrimitive
public import MathlibExt.LinearAlgebra.ExteriorAlgebra.PrimitiveEquation
public import MathlibExt.Algebra.Category.ModuleCat.Monoidal.UniverseUnitor

/-!
# Homogeneous exterior coordinates of primitive CE chains

Let `R` be a commutative ring and `L` an `R`-Lie algebra. In exterior degree `n`, the CE
primitive-equation component realizes in the exterior tensor square as `Δ(a) - (a ⊗ 1 + 1 ⊗
a)`.

Its kernel is exactly the homogeneous primitive submodule of `⋀ⁿ[R] L`. The kernel inclusion
and homogeneous primitive inclusion give mutually inverse chain maps, identifying the
primitive chain kernel with the homogeneous primitive complex. In degree one this carrier is
linearly equivalent to `L`, and the degree-one-to-zero primitive differential vanishes. The
scalar and Lie carrier universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u v

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]



private theorem coaug_unit_value : ((show ⋀[R]^0 L from ((nativeComplexCoaug R L).f 0).hom
    ((HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
  (ModuleCat.of R (ULift.{v} R))).inv.hom (ULift.up (1 : R)))) : ExteriorAlgebra R L) = 1 := by
  have hv := nativeComplexCoaug_zero_value R L
    ((HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
      (ModuleCat.of R (ULift.{v} R))).inv.hom (ULift.up (1 : R)))
  have h := congrArg (fun f => f.hom (ULift.up (1 : R)))
    (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
      (ModuleCat.of R (ULift.{v} R))).inv_hom_id
  change _ = ULift.up (1 : R) at h
  exact hv.trans ((congrArg (fun x : ULift.{v} R => x.down • (1 : ExteriorAlgebra R L)) h).trans
    (one_smul R (1 : ExteriorAlgebra R L)))

private theorem rightUnitTerm_realize (n : ℕ) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
    ((HomologicalComplex.rightUnitor ((canonicalChainData R L).complex)).inv ≫
        HomologicalComplex.tensorHom (𝟙 ((canonicalChainData R L).complex)) (nativeComplexCoaug R L)).f n ≫
        ExteriorAlgebra.tensorDegreeRealize R L n =
      ModuleCat.ofHom (((TensorProduct.mk R (ExteriorAlgebra R L) (ExteriorAlgebra R L)).flip (1 : (ExteriorAlgebra R
    L))).comp (⋀[R]^n L).subtype) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  have ht := congrArg (fun f => f.hom (a ⊗ₜ[R] ((HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
  (ModuleCat.of R (ULift.{v} R))).inv.hom (ULift.up (1 : R)))))
    (HomologicalComplex.ιTensorObj_tensorHom (𝟙 ((canonicalChainData R L).complex)) (nativeComplexCoaug R L) n 0 n
    (add_zero n))
  have hr := congrArg (fun f => f.hom (a ⊗ₜ[R] ((nativeComplexCoaug R L).f 0).hom ((HomologicalComplex.singleObjXSelf
    (ComplexShape.down ℕ) 0
  (ModuleCat.of R (ULift.{v} R))).inv.hom (ULift.up (1 : R)))))
    (ExteriorAlgebra.tensorDegreeι_realize R L n 0 n (add_zero n))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.UniverseTensor.hom_tensorHom,
    ModuleCat.hom_id, LinearMap.id_apply, TensorProduct.map_tmul, ModuleCat.hom_ofHom] at ht hr
  change (ExteriorAlgebra.tensorDegreeRealize R L n).hom
      (((HomologicalComplex.tensorHom (𝟙 ((canonicalChainData R L).complex)) (nativeComplexCoaug R L)).f n).hom
        (((HomologicalComplex.rightUnitor' ((canonicalChainData R L).complex)).inv n).hom a)) = ((show ⋀[R]^n L from
    a) : ExteriorAlgebra R L) ⊗ₜ[R] (1 : (ExteriorAlgebra R L))
  rw [HomologicalComplex.rightUnitor'_inv]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.UniverseTensor.hom_whiskerLeft]
  rw [ModuleCat.UniverseTensor.rightUnitor_inv_apply.{u,v} R (((canonicalChainData R L).complex).X n) a,
    LinearMap.lTensor_tmul]
  have hr' := hr
  have ht' := congrArg (ExteriorAlgebra.tensorDegreeRealize R L n).hom ht
  have hValue := ht'.trans hr'
  exact hValue.trans (by
    simp only [TensorProduct.map_tmul, Submodule.subtype_apply]
    exact congrArg (fun x : ExteriorAlgebra R L => ((show ⋀[R]^n L from a) : ExteriorAlgebra R L) ⊗ₜ[R] x)
      (coaug_unit_value R L))

private theorem leftUnitTerm_realize (n : ℕ) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
    ((HomologicalComplex.leftUnitor ((canonicalChainData R L).complex)).inv ≫
        HomologicalComplex.tensorHom (nativeComplexCoaug R L) (𝟙 ((canonicalChainData R L).complex))).f n ≫
        ExteriorAlgebra.tensorDegreeRealize R L n =
      ModuleCat.ofHom ((TensorProduct.mk R (ExteriorAlgebra R L) (ExteriorAlgebra R L) (1 : (ExteriorAlgebra R
    L))).comp (⋀[R]^n L).subtype) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  have ht := congrArg (fun f => f.hom (((HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
  (ModuleCat.of R (ULift.{v} R))).inv.hom (ULift.up (1 : R))) ⊗ₜ[R] a))
    (HomologicalComplex.ιTensorObj_tensorHom (nativeComplexCoaug R L) (𝟙 ((canonicalChainData R L).complex)) 0 n n
    (zero_add n))
  have hr := congrArg (fun f => f.hom (((nativeComplexCoaug R L).f 0).hom ((HomologicalComplex.singleObjXSelf
    (ComplexShape.down ℕ) 0
  (ModuleCat.of R (ULift.{v} R))).inv.hom (ULift.up (1 : R))) ⊗ₜ[R] a))
    (ExteriorAlgebra.tensorDegreeι_realize R L 0 n n (zero_add n))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.UniverseTensor.hom_tensorHom,
    ModuleCat.hom_id, LinearMap.id_apply, TensorProduct.map_tmul, ModuleCat.hom_ofHom] at ht hr
  change (ExteriorAlgebra.tensorDegreeRealize R L n).hom
      (((HomologicalComplex.tensorHom (nativeComplexCoaug R L) (𝟙 ((canonicalChainData R L).complex))).f n).hom
        (((HomologicalComplex.leftUnitor' ((canonicalChainData R L).complex)).inv n).hom a)) = (1 : (ExteriorAlgebra R
    L)) ⊗ₜ[R] ((show ⋀[R]^n L from a) : ExteriorAlgebra R L)
  rw [HomologicalComplex.leftUnitor'_inv]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.UniverseTensor.hom_whiskerRight]
  rw [ModuleCat.UniverseTensor.leftUnitor_inv_apply.{u,v} R (((canonicalChainData R L).complex).X n) a,
    LinearMap.rTensor_tmul]
  have hr' := hr
  have ht' := congrArg (ExteriorAlgebra.tensorDegreeRealize R L n).hom ht
  have hValue := ht'.trans hr'
  exact hValue.trans (by
    simp only [TensorProduct.map_tmul, Submodule.subtype_apply]
    exact congrArg (fun x : ExteriorAlgebra R L => x ⊗ₜ[R] ((show ⋀[R]^n L from a) : ExteriorAlgebra R L))
      (coaug_unit_value R L))

/-- The exterior realization of the CE primitive equation.

The degree-`n` primitive map followed by tensor-degree realization equals the exterior-algebra
primitive equation restricted to homogeneous degree `n`. -/
theorem nativePrimitiveMap_realize (n : ℕ) :
    (nativePrimitiveMap R L).f n ≫ ExteriorAlgebra.tensorDegreeRealize R L n =
      ModuleCat.ofHom ((ExteriorAlgebra.primitiveEquation R L).comp (⋀[R]^n L).subtype) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  let right : ((canonicalChainData R L).complex) ⟶ nativeTensorComplex R L :=
    (HomologicalComplex.rightUnitor ((canonicalChainData R L).complex)).inv ≫
      HomologicalComplex.tensorHom (𝟙 ((canonicalChainData R L).complex)) (nativeComplexCoaug R L)
  let left : ((canonicalChainData R L).complex) ⟶ nativeTensorComplex R L :=
    (HomologicalComplex.leftUnitor ((canonicalChainData R L).complex)).inv ≫
      HomologicalComplex.tensorHom (nativeComplexCoaug R L) (𝟙 ((canonicalChainData R L).complex))
  have hF : (nativePrimitiveMap R L).f n =
      (nativeComplexComul R L).f n - (right.f n + left.f n) := rfl
  let Δ : ModuleCat.of R (⋀[R]^n L) ⟶ ExteriorAlgebra.tensorDegree R L n :=
    (nativeComplexComul R L).f n
  let r : ModuleCat.of R (⋀[R]^n L) ⟶ ExteriorAlgebra.tensorDegree R L n := right.f n
  let l : ModuleCat.of R (⋀[R]^n L) ⟶ ExteriorAlgebra.tensorDegree R L n := left.f n
  have hF' := congrArg (fun g => g ≫ ExteriorAlgebra.tensorDegreeRealize R L n) hF
  exact hF'.trans (by
    let A := ModuleCat.of R (⋀[R]^n L)
    let B := ExteriorAlgebra.tensorDegree R L n
    let D := ModuleCat.of R ((ExteriorAlgebra R L) ⊗[R] (ExteriorAlgebra R L))
    have hSub : (Δ - (r + l)) ≫ ExteriorAlgebra.tensorDegreeRealize R L n =
        Δ ≫ ExteriorAlgebra.tensorDegreeRealize R L n -
          (r ≫ ExteriorAlgebra.tensorDegreeRealize R L n +
            l ≫ ExteriorAlgebra.tensorDegreeRealize R L n) := by
      rw [Preadditive.sub_comp, Preadditive.add_comp]
    have hΔ := ExteriorAlgebra.gradedCoproduct_realize R L n
    have hR := rightUnitTerm_realize R L n
    have hL := leftUnitTerm_realize R L n
    exact hSub.trans (by
      dsimp only [Δ, r, l, right, left]
      have hΔ' : Δ ≫ ExteriorAlgebra.tensorDegreeRealize R L n =
          ModuleCat.ofHom ((ExteriorAlgebra.coproduct R L).comp (⋀[R]^n L).subtype) := hΔ
      have hR' : r ≫ ExteriorAlgebra.tensorDegreeRealize R L n = _ := hR
      have hL' : l ≫ ExteriorAlgebra.tensorDegreeRealize R L n = _ := hL
      rw [hΔ', hR', hL']
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      change ExteriorAlgebra.coproduct R L ((show ⋀[R]^n L from a) : ExteriorAlgebra R L) -
        (((show ⋀[R]^n L from a) : ExteriorAlgebra R L) ⊗ₜ[R] (1 : ExteriorAlgebra R L) +
          (1 : ExteriorAlgebra R L) ⊗ₜ[R] ((show ⋀[R]^n L from a) : ExteriorAlgebra R L)) = _
      exact (ExteriorAlgebra.primitiveEquation_apply R L _).symm))
/-- The homogeneous primitivity criterion for a CE chain.

The primitive-equation component vanishes on `a ∈ ⋀ⁿ[R] L` if and only if `a` belongs to the
homogeneous primitive submodule. -/
theorem nativePrimitiveMap_eq_zero_iff (n : ℕ) (a : ⋀[R]^n L) :
    ((nativePrimitiveMap R L).f n).hom a = 0 ↔ a ∈ primitiveDegree R L n := by
  have hr := congrArg (fun f => f.hom a) (nativePrimitiveMap_realize R L n)
  change (ExteriorAlgebra.tensorDegreeRealize R L n).hom
      (((nativePrimitiveMap R L).f n).hom a) =
    ExteriorAlgebra.primitiveEquation R L (a : ExteriorAlgebra R L) at hr
  rw [mem_primitiveDegree, ← ExteriorAlgebra.primitiveEquation_eq_zero_iff]
  constructor
  · intro ha
    exact hr.symm.trans ((congrArg (ExteriorAlgebra.tensorDegreeRealize R L n).hom ha).trans
      (map_zero _))
  · intro ha
    apply ExteriorAlgebra.tensorDegreeRealize_injective R L n
    exact hr.trans (ha.trans (map_zero _).symm)

/-- The homogeneous kernel of a CE primitive-equation component.

The linear kernel in degree `n` is exactly the homogeneous primitive submodule of the exterior
algebra. -/
theorem nativePrimitiveMap_ker (n : ℕ) :
    LinearMap.ker ((nativePrimitiveMap R L).f n).hom = primitiveDegree R L n := by
  ext a
  exact nativePrimitiveMap_eq_zero_iff R L n a

/-- The successor differential in homogeneous primitive coordinates.

The homogeneous primitive complex has successor map given by the restricted primitive
differential. -/
@[simp]
theorem primitiveComplex_d_succ (n : ℕ) :
    (primitiveComplex R L).d (n + 1) n = ModuleCat.ofHom (primitiveDifferential R L n) := by
  simp only [primitiveComplex, ChainComplex.of_d]

/-- The primitive equation of the homogeneous chain inclusion.

The homogeneous primitive inclusion followed by the CE primitive map is the zero chain map. -/
theorem homogeneousPrimitiveInclusion_zero :
    primitiveComplexInclusion R L ≫ nativePrimitiveMap R L = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  let a₀ : primitiveDegree R L n := a
  exact (nativePrimitiveMap_eq_zero_iff R L n a₀.1).mpr a₀.2

/-- The chain map from homogeneous primitive coordinates to the primitive kernel.

The homogeneous primitive inclusion lifts through the chain kernel of the CE primitive-
equation map. -/
def homogeneousPrimitiveToNative : primitiveComplex R L ⟶ nativePrimitiveComplex R L :=
  kernel.lift (nativePrimitiveMap R L) (primitiveComplexInclusion R L)
    (homogeneousPrimitiveInclusion_zero R L)

/-- The inclusion equation of the homogeneous-to-kernel map.

The homogeneous-to-kernel map followed by primitive kernel inclusion is the homogeneous
primitive chain inclusion. -/
@[reassoc]
theorem homogeneousPrimitiveToNative_inclusion :
    homogeneousPrimitiveToNative R L ≫ nativePrimitiveInclusion R L = primitiveComplexInclusion R L :=
  kernel.lift_ι _ _ _

/-- Homogeneous primitivity of a primitive-kernel element.

The degreewise image of the primitive kernel inclusion lies in the corresponding homogeneous
primitive submodule. -/
theorem nativeInclusion_mem (n : ℕ) (a : (nativePrimitiveComplex R L).X n) :
    ((nativePrimitiveInclusion R L).f n).hom a ∈ primitiveDegree R L n := by
  apply (nativePrimitiveMap_eq_zero_iff R L n _).mp
  exact congrArg (fun f => f.hom a) (nativePrimitiveInclusion_component R L n)

/-- The chain map from the primitive kernel to homogeneous coordinates.

Restrict each primitive kernel inclusion component to the homogeneous primitive submodule. -/
def nativePrimitiveToHomogeneous : nativePrimitiveComplex R L ⟶ primitiveComplex R L where
  f n := ModuleCat.ofHom
    (((nativePrimitiveInclusion R L).f n).hom.codRestrict (primitiveDegree R L n)
      (nativeInclusion_mem R L n))
  comm' i j h := by
    change j + 1 = i at h
    subst i
    rw [primitiveComplex_d_succ]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    have hc := congrArg (fun f => f.hom a) ((nativePrimitiveInclusion R L).comm (j + 1) j)
    rw [ChainData.complex_d_succ] at hc
    exact hc

/-- The inclusion equation of the kernel-to-homogeneous map.

The homogeneous-coordinate map followed by homogeneous primitive inclusion is the primitive
kernel inclusion. -/
@[reassoc]
theorem nativePrimitiveToHomogeneous_inclusion :
    nativePrimitiveToHomogeneous R L ≫ primitiveComplexInclusion R L = nativePrimitiveInclusion R L := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rfl

/-- The inverse identity on the primitive chain kernel.

The kernel-to-homogeneous map followed by the homogeneous-to-kernel map is the identity on the
primitive kernel complex. -/
theorem nativePrimitive_coordinate_hom_inv :
    nativePrimitiveToHomogeneous R L ≫ homogeneousPrimitiveToNative R L =
      𝟙 (nativePrimitiveComplex R L) := by
  letI : Mono (nativePrimitiveInclusion R L) := inferInstanceAs (Mono (kernel.ι (nativePrimitiveMap R L)))
  apply (cancel_mono (nativePrimitiveInclusion R L)).mp
  rw [Category.assoc, homogeneousPrimitiveToNative_inclusion,
    nativePrimitiveToHomogeneous_inclusion, Category.id_comp]

/-- The inverse identity on homogeneous primitive chains.

The homogeneous-to-kernel map followed by the kernel-to-homogeneous map is the identity on the
homogeneous primitive complex. -/
theorem nativePrimitive_coordinate_inv_hom :
    homogeneousPrimitiveToNative R L ≫ nativePrimitiveToHomogeneous R L =
      𝟙 (primitiveComplex R L) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  exact congrArg (fun f => (f.f n).hom a) (homogeneousPrimitiveToNative_inclusion R L)

/-- The chain isomorphism of primitive kernels and homogeneous primitives.

The two inclusion-preserving coordinate maps identify the CE primitive kernel complex with the
homogeneous exterior primitive complex. -/
def nativePrimitiveCoordinateIso : nativePrimitiveComplex R L ≅ primitiveComplex R L where
  hom := nativePrimitiveToHomogeneous R L
  inv := homogeneousPrimitiveToNative R L
  hom_inv_id := nativePrimitive_coordinate_hom_inv R L
  inv_hom_id := nativePrimitive_coordinate_inv_hom R L

/-- The degreewise linear equivalence of primitive CE coordinates.

In degree `n`, the primitive kernel chain term is linearly equivalent to the homogeneous
exterior primitive submodule. -/
def nativePrimitiveDegreeEquiv (n : ℕ) :
    (nativePrimitiveComplex R L).X n ≃ₗ[R] primitiveDegree R L n :=
  ((HomologicalComplex.eval (ModuleCat.{max u v} R) (ComplexShape.down ℕ) n).mapIso
    (nativePrimitiveCoordinateIso R L)).toLinearEquiv

/-- The Lie-module coordinate of primitive CE degree one.

The degree-one primitive chain term is linearly equivalent to `L` through homogeneous
primitive and exterior-degree-one coordinates. -/
def nativePrimitiveDegreeOneEquiv : (nativePrimitiveComplex R L).X 1 ≃ₗ[R] L :=
  (nativePrimitiveDegreeEquiv R L 1).trans (primitiveDegreeOneEquiv R L)

/-- Vanishing of the bottom primitive CE differential.

The primitive kernel differential from degree one to degree zero is zero, as follows from its
homogeneous primitive coordinate comparison. -/
theorem nativePrimitiveComplex_d_one_zero : (nativePrimitiveComplex R L).d 1 0 = 0 := by
  let e := (HomologicalComplex.eval (ModuleCat.{max u v} R) (ComplexShape.down ℕ) 0).mapIso
    (nativePrimitiveCoordinateIso R L)
  apply (cancel_mono e.hom).mp
  have hc := (nativePrimitiveCoordinateIso R L).hom.comm 1 0
  have hd : (primitiveComplex R L).d 1 0 = 0 := by
    rw [primitiveComplex_d_succ, primitiveDifferential_zero, ModuleCat.ofHom_zero]
    rfl
  have hc' := congrArg (fun d => (nativePrimitiveCoordinateIso R L).hom.f 1 ≫ d) hd
  have hZero : (nativePrimitiveCoordinateIso R L).hom.f 1 ≫
      (primitiveComplex R L).d 1 0 = 0 := hc'.trans comp_zero
  have h := hc.symm.trans hZero
  exact h.trans (zero_comp).symm

end ChevalleyEilenberg
