/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.TorBalancedNaturality
public import MathlibExt.Algebra.Category.ModuleCat.NativeTorLinearity
public import MathlibExt.Algebra.Category.ModuleCat.FlatScalarExtensionTorNaturality
public import MathlibExt.Algebra.Category.ModuleCat.FlatScalarExtensionTorResolvedNaturality
public import MathlibExt.RingTheory.Smooth.GraphFlatProjection
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import MathlibExt.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Original field tensor comparisons of native Tor

The actual scalar extension of an original coefficient is compared with
its original field tensor, with the canonical product-algebra action and
naturality for arbitrary original coefficient maps.

For original algebra coefficients V and W, two flat adjoining reductions
compare the standard ambient `(A ⊗[K] B) ⊗[K] C` with the ordered native
`Tor_B(V,W)`. The intrinsic graph ambient `(V ⊗[K] W) ⊗[K] B` reaches the
same ordered native Tor through its actual graph evaluations and two further
adjoining reductions. Both chains retain V and W multiplication.

The genuine commuting native coefficient operators supply the actual support
action of `T = V ⊗[B] W`. Stock additive transport makes both comparisons
T-linear and agrees with the endomorphism-valued support representation.
The field-only comparison derives every adjoining flatness from K and keeps
the original ring universes and an arbitrary common module universe.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct ModuleCat.UniverseTensor ChangeOfRings

namespace ModuleCat.UniverseTensor

private theorem transferredModule_smul_eq {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R N] (e : M ≃+ N)
    (r : R) (x y : M) (h : e y = r • e x) :
    let := e.module R
    r • x = y := by
  let := e.module R
  apply e.injective
  change e (e.symm (r • e x)) = e y
  rw [e.apply_symm_apply]
  exact h.symm


private theorem transferredEndMap_apply {R T M N : Type*}
    [CommRing R] [Semiring T] [Algebra R T] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module T N] (e : M ≃ₗ[R] N)
    (ρ : T →ₐ[R] Module.End R N) (hρ : ∀ t z, ρ t z = t • z) (t : T) (z : M) :
    letI := e.toAddEquiv.module T
    ((e.symm.conjAlgEquiv R).toAlgHom.comp ρ) t z = t • z := by
  let := e.toAddEquiv.module T
  change e.symm (ρ t (e z)) = e.symm (t • e z)
  exact congrArg e.symm (hρ t (e z))

private theorem transferredConj_eq {R M N : Type*}
    [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (e : M ≃ₗ[R] N) (f : Module.End R N) (z y : M) (h : e y = f (e z)) :
    e.symm.conjAlgEquiv R f z = y := by
  change e.symm (f (e z)) = y
  exact e.symm_apply_eq.mpr h.symm


universe u v w t

variable (K : Type u) (A : Type v) (B : Type w)
  [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
  (X : Type (max u v w t)) [AddCommGroup X] [Module K X] [Module B X]
  [IsScalarTower K B X]

/-- The original B operator on the field tensor is its actual canonical
scalar extension, as an A-linear endomorphism. -/
def tensorAdjoinCoefficientEndMap : B →ₐ[K] Module.End A (A ⊗[K] X) :=
  (Module.End.baseChangeHom K A X).comp (Algebra.lsmul K K X)

/-- The canonical original right coefficient action after field tensoring. -/
abbrev tensorAdjoinRightModule : Module B (A ⊗[K] X) :=
  Module.compHom (A ⊗[K] X) (tensorAdjoinCoefficientEndMap.{u,v,w,t} K A B X).toRingHom

/-- The original coefficient restriction remains compatible with K. -/
theorem tensorAdjoinRightModule_isScalarTower :
    letI : Module B (A ⊗[K] X) := tensorAdjoinRightModule.{u,v,w,t} K A B X
    IsScalarTower K B (A ⊗[K] X) := by
  let : Module B (A ⊗[K] X) := tensorAdjoinRightModule.{u,v,w,t} K A B X
  apply IsScalarTower.of_algebraMap_smul
  intro k z
  change tensorAdjoinCoefficientEndMap.{u,v,w,t} K A B X (algebraMap K B k) z = k • z
  rw [(tensorAdjoinCoefficientEndMap.{u,v,w,t} K A B X).commutes]
  rfl

/-- The original A and extended B operators commute by actual A-linearity. -/
theorem tensorAdjoinRightModule_smulCommClass :
    letI : Module B (A ⊗[K] X) := tensorAdjoinRightModule.{u,v,w,t} K A B X
    SMulCommClass A B (A ⊗[K] X) := by
  let : Module B (A ⊗[K] X) := tensorAdjoinRightModule.{u,v,w,t} K A B X
  refine ⟨fun a b z => ?_⟩
  change a • (tensorAdjoinCoefficientEndMap.{u,v,w,t} K A B X b z) =
    tensorAdjoinCoefficientEndMap.{u,v,w,t} K A B X b (a • z)
  exact ((tensorAdjoinCoefficientEndMap.{u,v,w,t} K A B X b).map_smul a z).symm

/-- The actual tensor coefficient carries the existing canonical product
algebra action, derived from its commuting original factor actions. -/
def tensorAdjoinCoefficientModule : ModuleCat.{max u v w t} (A ⊗[K] B) := by
  let : Module B (A ⊗[K] X) := tensorAdjoinRightModule.{u,v,w,t} K A B X
  let : IsScalarTower K B (A ⊗[K] X) := tensorAdjoinRightModule_isScalarTower.{u,v,w,t} K A B X
  let : SMulCommClass A B (A ⊗[K] X) := tensorAdjoinRightModule_smulCommClass.{u,v,w,t} K A B X
  let : Module (A ⊗[K] B) (A ⊗[K] X) := TensorProduct.Algebra.module
  exact ModuleCat.of (A ⊗[K] B) (A ⊗[K] X)

/-- The canonical product scalar acts by the actual two original factors. -/
theorem tensorAdjoinCoefficientModule_smul_tmul (a a' : A) (b : B) (x : X) :
    letI : Module B (A ⊗[K] X) := tensorAdjoinRightModule.{u,v,w,t} K A B X
    letI : IsScalarTower K B (A ⊗[K] X) := tensorAdjoinRightModule_isScalarTower.{u,v,w,t} K A B X
    letI : SMulCommClass A B (A ⊗[K] X) := tensorAdjoinRightModule_smulCommClass.{u,v,w,t} K A B X
    letI : Module (A ⊗[K] B) (A ⊗[K] X) := TensorProduct.Algebra.module
    (a ⊗ₜ[K] b : A ⊗[K] B) • (a' ⊗ₜ[K] x) = (a * a') ⊗ₜ[K] (b • x) := by
  let : Module B (A ⊗[K] X) := tensorAdjoinRightModule.{u,v,w,t} K A B X
  let : IsScalarTower K B (A ⊗[K] X) := tensorAdjoinRightModule_isScalarTower.{u,v,w,t} K A B X
  let : SMulCommClass A B (A ⊗[K] X) := tensorAdjoinRightModule_smulCommClass.{u,v,w,t} K A B X
  let : Module (A ⊗[K] B) (A ⊗[K] X) := TensorProduct.Algebra.module
  change a • (tensorAdjoinCoefficientEndMap.{u,v,w,t} K A B X b (a' ⊗ₜ[K] x)) = _
  change a • ((Algebra.lsmul K K X b).baseChange A (a' ⊗ₜ[K] x)) = _
  rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul']
  rfl

/-- The original underlying coefficient equivalence is stock tensor
commutation, actual right-algebra commutation and scalar cancellation. -/
def tensorAdjoinBaseEquiv :
    letI : Algebra B (A ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
    (A ⊗[K] B) ⊗[B] X ≃ₗ[K] A ⊗[K] X := by
  letI : Algebra B (A ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
  let e : (A ⊗[K] B) ≃ₐ[B] B ⊗[K] A := (Algebra.TensorProduct.commRight K B A).symm
  exact ((((TensorProduct.comm B (A ⊗[K] B) X).trans
      (TensorProduct.congr (LinearEquiv.refl B X) e.toLinearEquiv)).trans
        (TensorProduct.AlgebraTensorModule.cancelBaseChange K B B X A)).restrictScalars K).trans
    (TensorProduct.comm K X A)

/-- The original forward coefficient map retains both actual tensor factors. -/
theorem tensorAdjoinBaseEquiv_tmul (a : A) (b : B) (x : X) :
    letI : Algebra B (A ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
    tensorAdjoinBaseEquiv.{u,v,w,t} K A B X ((a ⊗ₜ[K] b) ⊗ₜ[B] x) = a ⊗ₜ[K] (b • x) := by
  let : Algebra B (A ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
  rfl

/-- The original inverse coefficient map inserts the actual B unit. -/
theorem tensorAdjoinBaseEquiv_symm_tmul (a : A) (x : X) :
    letI : Algebra B (A ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
    (tensorAdjoinBaseEquiv.{u,v,w,t} K A B X).symm (a ⊗ₜ[K] x) = (a ⊗ₜ[K] (1 : B)) ⊗ₜ[B] x := by
  let : Algebra B (A ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
  apply (tensorAdjoinBaseEquiv.{u,v,w,t} K A B X).injective
  rw [LinearEquiv.apply_symm_apply, tensorAdjoinBaseEquiv_tmul.{u,v,w,t}]
  rw [one_smul]

/-- The original scalar-extension coefficient isomorphism is linear for
the actual canonical product-algebra action. -/
def tensorAdjoinCoefficientEquiv :
    letI : Algebra B (A ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
    letI : Module B (A ⊗[K] X) := tensorAdjoinRightModule.{u,v,w,t} K A B X
    letI : IsScalarTower K B (A ⊗[K] X) := tensorAdjoinRightModule_isScalarTower.{u,v,w,t} K A B X
    letI : SMulCommClass A B (A ⊗[K] X) := tensorAdjoinRightModule_smulCommClass.{u,v,w,t} K A B X
    letI : Module (A ⊗[K] B) (A ⊗[K] X) := TensorProduct.Algebra.module
    (A ⊗[K] B) ⊗[B] X ≃ₗ[A ⊗[K] B] A ⊗[K] X := by
  letI : Algebra B (A ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
  letI : Module B (A ⊗[K] X) := tensorAdjoinRightModule.{u,v,w,t} K A B X
  letI : IsScalarTower K B (A ⊗[K] X) := tensorAdjoinRightModule_isScalarTower.{u,v,w,t} K A B X
  letI : SMulCommClass A B (A ⊗[K] X) := tensorAdjoinRightModule_smulCommClass.{u,v,w,t} K A B X
  letI : Module (A ⊗[K] B) (A ⊗[K] X) := TensorProduct.Algebra.module
  let e := tensorAdjoinBaseEquiv.{u,v,w,t} K A B X
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro s z
  change e (s • z) = s • e z
  induction s using TensorProduct.inductionOn with
  | add s₁ s₂ h₁ h₂ => simp only [add_smul, _root_.map_add, h₁, h₂]
  | tmul a b =>
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ h₁ h₂ => simp only [smul_add, _root_.map_add, h₁, h₂]
    | tmul s' x =>
      induction s' using TensorProduct.inductionOn with
      | add s₁ s₂ h₁ h₂ => simp only [TensorProduct.add_tmul, smul_add, _root_.map_add, h₁, h₂]
      | tmul a' b' =>
        change e (((a ⊗ₜ[K] b) * (a' ⊗ₜ[K] b')) ⊗ₜ[B] x) =
          (a ⊗ₜ[K] b : A ⊗[K] B) • e ((a' ⊗ₜ[K] b') ⊗ₜ[B] x)
        rw [Algebra.TensorProduct.tmul_mul_tmul,
          tensorAdjoinBaseEquiv_tmul.{u,v,w,t}, tensorAdjoinBaseEquiv_tmul.{u,v,w,t},
          tensorAdjoinCoefficientModule_smul_tmul.{u,v,w,t}]
        rw [mul_smul]

/-- The actual product-linear coefficient isomorphism has the original
forward pure-tensor formula. -/
theorem tensorAdjoinCoefficientEquiv_tmul (a : A) (b : B) (x : X) :
    letI : Algebra B (A ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
    letI : Module B (A ⊗[K] X) := tensorAdjoinRightModule.{u,v,w,t} K A B X
    letI : IsScalarTower K B (A ⊗[K] X) := tensorAdjoinRightModule_isScalarTower.{u,v,w,t} K A B X
    letI : SMulCommClass A B (A ⊗[K] X) := tensorAdjoinRightModule_smulCommClass.{u,v,w,t} K A B X
    letI : Module (A ⊗[K] B) (A ⊗[K] X) := TensorProduct.Algebra.module
    tensorAdjoinCoefficientEquiv.{u,v,w,t} K A B X ((a ⊗ₜ[K] b) ⊗ₜ[B] x) = a ⊗ₜ[K] (b • x) := by
  exact tensorAdjoinBaseEquiv_tmul.{u,v,w,t} K A B X a b x

/-- The actual product-linear inverse inserts the original B unit. -/
theorem tensorAdjoinCoefficientEquiv_symm_tmul (a : A) (x : X) :
    letI : Algebra B (A ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
    letI : Module B (A ⊗[K] X) := tensorAdjoinRightModule.{u,v,w,t} K A B X
    letI : IsScalarTower K B (A ⊗[K] X) := tensorAdjoinRightModule_isScalarTower.{u,v,w,t} K A B X
    letI : SMulCommClass A B (A ⊗[K] X) := tensorAdjoinRightModule_smulCommClass.{u,v,w,t} K A B X
    letI : Module (A ⊗[K] B) (A ⊗[K] X) := TensorProduct.Algebra.module
    (tensorAdjoinCoefficientEquiv.{u,v,w,t} K A B X).symm (a ⊗ₜ[K] x) = (a ⊗ₜ[K] (1 : B)) ⊗ₜ[B] x := by
  exact tensorAdjoinBaseEquiv_symm_tmul.{u,v,w,t} K A B X a x

variable {Y : Type (max u v w t)} [AddCommGroup Y] [Module K Y] [Module B Y]
  [IsScalarTower K B Y]

/-- The original tensor coefficient equivalence preserves every actual
B-linear coefficient map through the actual scalar extension. -/
theorem tensorAdjoinBaseEquiv_naturality (f : X →ₗ[B] Y) :
    letI : Algebra B (A ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
    (tensorAdjoinBaseEquiv.{u,v,w,t} K A B Y).toLinearMap ∘ₗ
        (f.baseChange (A ⊗[K] B)).restrictScalars K =
      TensorProduct.map (LinearMap.id : A →ₗ[K] A) (f.restrictScalars K) ∘ₗ
        (tensorAdjoinBaseEquiv.{u,v,w,t} K A B X).toLinearMap := by
  let : Algebra B (A ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ h₁ h₂ => simp only [_root_.map_add, h₁, h₂]
  | tmul s x =>
    induction s using TensorProduct.inductionOn with
    | add s₁ s₂ h₁ h₂ => simp only [TensorProduct.add_tmul, _root_.map_add, h₁, h₂]
    | tmul a b =>
      change tensorAdjoinBaseEquiv.{u,v,w,t} K A B Y
          (f.baseChange (A ⊗[K] B) ((a ⊗ₜ[K] b) ⊗ₜ[B] x)) =
        TensorProduct.map (LinearMap.id : A →ₗ[K] A) (f.restrictScalars K)
          (tensorAdjoinBaseEquiv.{u,v,w,t} K A B X ((a ⊗ₜ[K] b) ⊗ₜ[B] x))
      rw [LinearMap.baseChange_tmul, tensorAdjoinBaseEquiv_tmul.{u,v,w,t},
        tensorAdjoinBaseEquiv_tmul.{u,v,w,t}, TensorProduct.map_tmul]
      change a ⊗ₜ[K] (b • f x) = a ⊗ₜ[K] f (b • x)
      rw [f.map_smul]

/-- The original product-linear coefficient equivalence on the actual
existing scalar-extension module object. -/
def tensorAdjoinCoefficientIso :
    letI : Algebra B (A ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
    ((ModuleCat.extendScalars.{w,max v w,max u v w t} (algebraMap B (A ⊗[K] B))).obj
      (ModuleCat.of B X)) ≅ tensorAdjoinCoefficientModule.{u,v,w,t} K A B X := by
  letI : Algebra B (A ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
  letI : Module B (A ⊗[K] X) := tensorAdjoinRightModule.{u,v,w,t} K A B X
  letI : IsScalarTower K B (A ⊗[K] X) := tensorAdjoinRightModule_isScalarTower.{u,v,w,t} K A B X
  letI : SMulCommClass A B (A ⊗[K] X) := tensorAdjoinRightModule_smulCommClass.{u,v,w,t} K A B X
  letI : Module (A ⊗[K] B) (A ⊗[K] X) := TensorProduct.Algebra.module
  exact (tensorAdjoinCoefficientEquiv.{u,v,w,t} K A B X).toModuleIso

/-- The actual include-right adjoining map is flat when its original
adjoining factor is flat over K. Over a field this is derived automatically. -/
theorem tensorAdjoin_flat [Module.Flat K A] :
    letI : Algebra B (A ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
    Module.Flat B (A ⊗[K] B) := by
  let : Algebra B (A ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
  rw [← RingHom.flat_algebraMap_iff]
  exact Algebra.TensorProduct.graphProjection_flat (R := K) (A := B) (B := A)

/-- One genuine original flat adjoining Tor comparison, using the proved
actual coefficient isomorphism and the existing native cancellation. -/
def tensorAdjoinNativeTorIso [Module.Flat K A]
    (N : ModuleCat.{max u v w t} (A ⊗[K] B)) (q : ℕ) :
    letI : Algebra B (A ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
    letI : Module.Flat B (A ⊗[K] B) := tensorAdjoin_flat.{u,v,w} K A B
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w t} B) :=
      ModuleCat.UniverseTensor.tensorStructure.{w,max u v w t}
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w t} (A ⊗[K] B)) :=
      ModuleCat.UniverseTensor.tensorStructure.{max v w,max u t}
    letI : MonoidalCategory (ModuleCat.{max u v w t} B) :=
      ModuleCat.UniverseTensor.monoidalCategory.{w,max u v w t}
    letI : MonoidalCategory (ModuleCat.{max u v w t} (A ⊗[K] B)) :=
      ModuleCat.UniverseTensor.monoidalCategory.{max v w,max u t}
    letI : MonoidalPreadditive (ModuleCat.{max u v w t} B) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{w,max u v w t}
    letI : MonoidalPreadditive (ModuleCat.{max u v w t} (A ⊗[K] B)) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{max v w,max u t}
    ((ModuleCat.restrictScalars.{max u v w t,w,max v w} (algebraMap B (A ⊗[K] B))).obj
      (((Tor (ModuleCat.{max u v w t} (A ⊗[K] B)) q).obj N).obj
        (tensorAdjoinCoefficientModule.{u,v,w,t} K A B X))) ≅
      (((Tor (ModuleCat.{max u v w t} B) q).obj
        ((ModuleCat.restrictScalars.{max u v w t,w,max v w} (algebraMap B (A ⊗[K] B))).obj N)).obj
          (ModuleCat.of B X)) := by
  letI : Algebra B (A ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
  letI : Module.Flat B (A ⊗[K] B) := tensorAdjoin_flat.{u,v,w} K A B
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w t} B) :=
    ModuleCat.UniverseTensor.tensorStructure.{w,max u v w t}
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w t} (A ⊗[K] B)) :=
    ModuleCat.UniverseTensor.tensorStructure.{max v w,max u t}
  letI : MonoidalCategory (ModuleCat.{max u v w t} B) :=
    ModuleCat.UniverseTensor.monoidalCategory.{w,max u v w t}
  letI : MonoidalCategory (ModuleCat.{max u v w t} (A ⊗[K] B)) :=
    ModuleCat.UniverseTensor.monoidalCategory.{max v w,max u t}
  letI : MonoidalPreadditive (ModuleCat.{max u v w t} B) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{w,max u v w t}
  letI : MonoidalPreadditive (ModuleCat.{max u v w t} (A ⊗[K] B)) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{max v w,max u t}
  let H := ModuleCat.restrictScalars.{max u v w t,w,max v w} (algebraMap B (A ⊗[K] B))
  exact (H.mapIso (((Tor (ModuleCat.{max u v w t} (A ⊗[K] B)) q).obj N).mapIso
      (tensorAdjoinCoefficientIso.{u,v,w,t} K A B X))).symm ≪≫
    flatScalarExtensionTorCancellationIso.{w,max v w,max u t}
      B (A ⊗[K] B) N (ModuleCat.of B X) q

section LeftCoefficientAlgebra

universe k b c d lt

variable (K₀ : Type k) (B₀ : Type b) (C₀ : Type c) (V₀ : Type d)
  [CommRing K₀] [CommRing B₀] [CommRing C₀] [CommRing V₀]
  [Algebra K₀ B₀] [Algebra K₀ C₀] [Algebra K₀ V₀]
  [Algebra B₀ V₀] [IsScalarTower K₀ B₀ V₀]

/-- The actual left adjoining algebra coefficient equivalence uses only
original tensor commutation and scalar cancellation. -/
def tensorAdjoinLeftBaseAlgEquiv :
    ((B₀ ⊗[K₀] C₀) ⊗[B₀] V₀) ≃ₐ[K₀] V₀ ⊗[K₀] C₀ :=
  ((Algebra.TensorProduct.comm B₀ (B₀ ⊗[K₀] C₀) V₀).restrictScalars K₀).trans
    ((Algebra.TensorProduct.cancelBaseChange K₀ B₀ V₀ V₀ C₀).restrictScalars K₀)

/-- The actual left adjoining coefficient map keeps the original B map. -/
theorem tensorAdjoinLeftBaseAlgEquiv_tmul (b₀ : B₀) (c₀ : C₀) (v₀ : V₀) :
    tensorAdjoinLeftBaseAlgEquiv.{k,b,c,d} K₀ B₀ C₀ V₀
        ((b₀ ⊗ₜ[K₀] c₀) ⊗ₜ[B₀] v₀) = (b₀ • v₀) ⊗ₜ[K₀] c₀ := by
  rfl

/-- The original ambient algebra maps to its actual left coefficient. -/
def tensorAdjoinLeftCoefficientMap : B₀ ⊗[K₀] C₀ →ₐ[K₀] V₀ ⊗[K₀] C₀ :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom K₀ B₀ V₀) (AlgHom.id K₀ C₀)

/-- The left adjoining equivalence is linear over the actual ambient
product algebra, with its genuine coefficient-map scalar action. -/
def tensorAdjoinLeftCoefficientAlgEquiv :
    letI : Algebra (B₀ ⊗[K₀] C₀) (V₀ ⊗[K₀] C₀) :=
      (tensorAdjoinLeftCoefficientMap.{k,b,c,d} K₀ B₀ C₀ V₀).toRingHom.toAlgebra
    ((B₀ ⊗[K₀] C₀) ⊗[B₀] V₀) ≃ₐ[B₀ ⊗[K₀] C₀] V₀ ⊗[K₀] C₀ := by
  letI : Algebra (B₀ ⊗[K₀] C₀) (V₀ ⊗[K₀] C₀) :=
    (tensorAdjoinLeftCoefficientMap.{k,b,c,d} K₀ B₀ C₀ V₀).toRingHom.toAlgebra
  let e := tensorAdjoinLeftBaseAlgEquiv.{k,b,c,d} K₀ B₀ C₀ V₀
  refine { e.toRingEquiv with commutes' := ?_ }
  intro s
  change e (s ⊗ₜ[B₀] (1 : V₀)) = tensorAdjoinLeftCoefficientMap.{k,b,c,d} K₀ B₀ C₀ V₀ s
  induction s using TensorProduct.inductionOn with
  | add x y hx hy => simp only [TensorProduct.add_tmul, _root_.map_add, hx, hy]
  | tmul b₀ c₀ =>
    rw [tensorAdjoinLeftBaseAlgEquiv_tmul.{k,b,c,d}]
    rw [Algebra.smul_def, mul_one]
    rfl

/-- The actual left adjoining coefficient iso on the native scalar-extension
object retains its original coefficient ring and its common carrier lift. -/
def tensorAdjoinLeftCoefficientIso :
    letI : Algebra (B₀ ⊗[K₀] C₀) (V₀ ⊗[K₀] C₀) :=
      (tensorAdjoinLeftCoefficientMap.{k,b,c,d} K₀ B₀ C₀ V₀).toRingHom.toAlgebra
    (extendScalars.{b,max b c,max k b c d lt}
      (algebraMap B₀ (B₀ ⊗[K₀] C₀))).obj
        (ModuleCat.of B₀ (ULift.{max k b c d lt} V₀)) ≅
      ModuleCat.of (B₀ ⊗[K₀] C₀) (ULift.{max k b c d lt} (V₀ ⊗[K₀] C₀)) := by
  letI : Algebra (B₀ ⊗[K₀] C₀) (V₀ ⊗[K₀] C₀) :=
    (tensorAdjoinLeftCoefficientMap.{k,b,c,d} K₀ B₀ C₀ V₀).toRingHom.toAlgebra
  let SS := (restrictScalars (algebraMap B₀ (B₀ ⊗[K₀] C₀))).obj
    (ModuleCat.of (B₀ ⊗[K₀] C₀) (B₀ ⊗[K₀] C₀))
  letI : IsScalarTower B₀ (B₀ ⊗[K₀] C₀) SS :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let es : SS ≃ₗ[B₀ ⊗[K₀] C₀] B₀ ⊗[K₀] C₀ :=
    { (AddEquiv.refl (B₀ ⊗[K₀] C₀)) with map_smul' := fun _ _ => rfl }
  let e := (tensorAdjoinLeftCoefficientAlgEquiv.{k,b,c,d} K₀ B₀ C₀ V₀).toLinearEquiv
  exact ((TensorProduct.AlgebraTensorModule.congr
      es
      (ULift.moduleEquiv : ULift.{max k b c d lt} V₀ ≃ₗ[B₀] V₀))
    ≪≫ₗ e ≪≫ₗ (ULift.moduleEquiv :
      ULift.{max k b c d lt} (V₀ ⊗[K₀] C₀) ≃ₗ[B₀ ⊗[K₀] C₀] V₀ ⊗[K₀] C₀).symm).toModuleIso

end LeftCoefficientAlgebra

section RightCoefficientAlgebra

universe rk ra rb rx rm

variable (K₂ : Type rk) (A₂ : Type ra) (B₂ : Type rb) (W₂ : Type rx)
  [CommRing K₂] [CommRing A₂] [CommRing B₂] [CommRing W₂]
  [Algebra K₂ A₂] [Algebra K₂ B₂] [Algebra K₂ W₂]
  [Algebra B₂ W₂] [IsScalarTower K₂ B₂ W₂]

/-- The original right adjoining coefficient algebra uses the canonical
B-linear commutation and original scalar cancellation. -/
def tensorAdjoinRightBaseAlgEquiv :
    letI : Algebra B₂ (A₂ ⊗[K₂] B₂) := Algebra.TensorProduct.rightAlgebra
    (A₂ ⊗[K₂] B₂) ⊗[B₂] W₂ ≃ₐ[K₂] A₂ ⊗[K₂] W₂ := by
  letI : Algebra B₂ (A₂ ⊗[K₂] B₂) := Algebra.TensorProduct.rightAlgebra
  exact (((Algebra.TensorProduct.comm B₂ (A₂ ⊗[K₂] B₂) W₂).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : W₂ ≃ₐ[B₂] W₂)
      (Algebra.TensorProduct.commRight K₂ B₂ A₂).symm)).restrictScalars K₂).trans
    (((Algebra.TensorProduct.cancelBaseChange K₂ B₂ W₂ W₂ A₂).restrictScalars K₂).trans
      (Algebra.TensorProduct.comm K₂ W₂ A₂))

/-- The right adjoining map retains the original B multiplication. -/
theorem tensorAdjoinRightBaseAlgEquiv_tmul (a : A₂) (b : B₂) (w : W₂) :
    letI : Algebra B₂ (A₂ ⊗[K₂] B₂) := Algebra.TensorProduct.rightAlgebra
    tensorAdjoinRightBaseAlgEquiv K₂ A₂ B₂ W₂ ((a ⊗ₜ[K₂] b) ⊗ₜ[B₂] w) =
      a ⊗ₜ[K₂] (b • w) := by
  let : Algebra B₂ (A₂ ⊗[K₂] B₂) := Algebra.TensorProduct.rightAlgebra
  rfl

/-- The actual original product algebra maps to its right coefficient. -/
def tensorAdjoinRightCoefficientMap : A₂ ⊗[K₂] B₂ →ₐ[K₂] A₂ ⊗[K₂] W₂ :=
  Algebra.TensorProduct.map (AlgHom.id K₂ A₂) (IsScalarTower.toAlgHom K₂ B₂ W₂)

/-- The original right coefficient equivalence is linear over the actual
product algebra through its original coefficient map. -/
def tensorAdjoinRightCoefficientAlgEquiv :
    letI : Algebra B₂ (A₂ ⊗[K₂] B₂) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra (A₂ ⊗[K₂] B₂) (A₂ ⊗[K₂] W₂) :=
      (tensorAdjoinRightCoefficientMap K₂ A₂ B₂ W₂).toRingHom.toAlgebra
    (A₂ ⊗[K₂] B₂) ⊗[B₂] W₂ ≃ₐ[A₂ ⊗[K₂] B₂] A₂ ⊗[K₂] W₂ := by
  letI : Algebra B₂ (A₂ ⊗[K₂] B₂) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra (A₂ ⊗[K₂] B₂) (A₂ ⊗[K₂] W₂) :=
    (tensorAdjoinRightCoefficientMap K₂ A₂ B₂ W₂).toRingHom.toAlgebra
  let e := tensorAdjoinRightBaseAlgEquiv K₂ A₂ B₂ W₂
  refine { e.toRingEquiv with commutes' := ?_ }
  intro s
  change e (s ⊗ₜ[B₂] (1 : W₂)) = tensorAdjoinRightCoefficientMap K₂ A₂ B₂ W₂ s
  induction s using TensorProduct.inductionOn with
  | add x y hx hy => simp only [TensorProduct.add_tmul, _root_.map_add, hx, hy]
  | tmul a b =>
    rw [tensorAdjoinRightBaseAlgEquiv_tmul, Algebra.smul_def, mul_one]
    rfl

/-- The right adjoining iso on the native scalar-extension object keeps
its original ring coefficient and common carrier lift. -/
def tensorAdjoinRightCoefficientIso :
    letI : Algebra B₂ (A₂ ⊗[K₂] B₂) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra (A₂ ⊗[K₂] B₂) (A₂ ⊗[K₂] W₂) :=
      (tensorAdjoinRightCoefficientMap K₂ A₂ B₂ W₂).toRingHom.toAlgebra
    (extendScalars.{rb,max ra rb,max rk ra rb rx rm}
      (algebraMap B₂ (A₂ ⊗[K₂] B₂))).obj (ModuleCat.of B₂ (ULift.{max rk ra rb rx rm} W₂)) ≅
      ModuleCat.of (A₂ ⊗[K₂] B₂) (ULift.{max rk ra rb rx rm} (A₂ ⊗[K₂] W₂)) := by
  letI : Algebra B₂ (A₂ ⊗[K₂] B₂) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra (A₂ ⊗[K₂] B₂) (A₂ ⊗[K₂] W₂) :=
    (tensorAdjoinRightCoefficientMap K₂ A₂ B₂ W₂).toRingHom.toAlgebra
  let SS := (restrictScalars (algebraMap B₂ (A₂ ⊗[K₂] B₂))).obj
    (ModuleCat.of (A₂ ⊗[K₂] B₂) (A₂ ⊗[K₂] B₂))
  letI : IsScalarTower B₂ (A₂ ⊗[K₂] B₂) SS :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let es : SS ≃ₗ[A₂ ⊗[K₂] B₂] A₂ ⊗[K₂] B₂ :=
    { (AddEquiv.refl (A₂ ⊗[K₂] B₂)) with map_smul' := fun _ _ => rfl }
  exact ((TensorProduct.AlgebraTensorModule.congr es
      (ULift.moduleEquiv : ULift.{max rk ra rb rx rm} W₂ ≃ₗ[B₂] W₂))
    ≪≫ₗ (tensorAdjoinRightCoefficientAlgEquiv K₂ A₂ B₂ W₂).toLinearEquiv ≪≫ₗ
      (ULift.moduleEquiv : ULift.{max rk ra rb rx rm} (A₂ ⊗[K₂] W₂) ≃ₗ[A₂ ⊗[K₂] B₂]
        A₂ ⊗[K₂] W₂).symm).toModuleIso

end RightCoefficientAlgebra

/-- An original algebra coefficient in a common module universe is the
canonical restriction of its actual ring module and canonical carrier lift. -/
abbrev originalRingCoefficient.{rr,ss,mm} (R₃ : Type rr) (S₃ : Type ss)
    [CommRing R₃] [CommRing S₃] (f : R₃ →+* S₃) : ModuleCat.{max rr ss mm} R₃ :=
  (restrictScalars.{max rr ss mm,rr,ss} f).obj
    (ModuleCat.of S₃ (ULift.{max rr ss mm} S₃))

section NativeCoefficientOperators

universe nr nm

variable (R₇ : Type nr) [CommRing R₇]

/-- Original coefficient multiplication is mapped into endomorphisms
of the actual native Tor object, preserving its real algebra structure. -/
def nativeTorFirstEndAlgHom (N X : ModuleCat.{max nr nm} R₇) (q : ℕ) :
    Module.End R₇ N →ₐ[R₇] Module.End R₇ (((Tor (ModuleCat.{max nr nm} R₇) q).obj N).obj X) := by
  let F : ModuleCat.{max nr nm} R₇ ⥤ ModuleCat.{max nr nm} R₇ :=
    (Functor.flip (Tor (ModuleCat.{max nr nm} R₇) q)).obj X
  let h := nativeTorFirstMapLinear.{nr,nm} R₇ X q (X₁ := N) (X₂ := N)
  refine
    { toFun := fun f => (F.map (ModuleCat.ofHom f)).hom
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_
      commutes' := ?_ }
  · change (F.map (𝟙 N)).hom = (1 : Module.End R₇ (F.obj N))
    rw [F.map_id]
    rfl
  · intro f g
    change (F.map (ModuleCat.ofHom g ≫ ModuleCat.ofHom f)).hom =
      (F.map (ModuleCat.ofHom g) ≫ F.map (ModuleCat.ofHom f)).hom
    rw [F.map_comp]
  · exact congrArg ModuleCat.Hom.hom h.map_zero
  · intro f g
    exact congrArg ModuleCat.Hom.hom (h.map_add (ModuleCat.ofHom f) (ModuleCat.ofHom g))
  · intro r
    have hs := h.map_smul r (𝟙 N)
    change F.map (r • 𝟙 N) = r • F.map (𝟙 N) at hs
    rw [F.map_id] at hs
    exact congrArg ModuleCat.Hom.hom hs

/-- The original first native Tor coefficient operator is its literal
native functor map. -/
theorem nativeTorFirstEndAlgHom_apply (N X : ModuleCat.{max nr nm} R₇) (q : ℕ)
    (f : Module.End R₇ N) :
    nativeTorFirstEndAlgHom R₇ N X q f =
      (((Tor (ModuleCat.{max nr nm} R₇) q).map (ModuleCat.ofHom f)).app X).hom := by
  rfl

/-- The original resolved coefficient operator is transported through
actual native symmetry, retaining the genuine signed total flip. -/
def nativeTorSecondEndAlgHom (N X : ModuleCat.{max nr nm} R₇) (q : ℕ) :
    Module.End R₇ X →ₐ[R₇] Module.End R₇ (((Tor (ModuleCat.{max nr nm} R₇) q).obj N).obj X) := by
  let T := Tor (ModuleCat.{max nr nm} R₇) q
  let TX := (T.obj N).obj X
  let TN := (T.obj X).obj N
  let σ : TX ≅ TN := nativeTorSymmetry.{nr,nm} R₇ N X q
  let C : Module.End R₇ X →ₐ[R₇] Module.End R₇ TX :=
    (σ.symm.toLinearEquiv.conjAlgEquiv R₇).toAlgHom.comp
      (nativeTorFirstEndAlgHom.{nr,nm} R₇ X N q)
  have hC : ∀ f : Module.End R₇ X, C f = ((T.obj N).map (ModuleCat.ofHom f)).hom := by
    intro f
    let m : TN ⟶ TN := (T.map (ModuleCat.ofHom f)).app N
    let n : TX ⟶ TX := (T.obj N).map (ModuleCat.ofHom f)
    have h₁ : (T.map (𝟙 N)).app X = 𝟙 TX := by rw [T.map_id]; rfl
    have h₂ : (T.obj X).map (𝟙 N) = 𝟙 TN := (T.obj X).map_id N
    have hn : n ≫ σ.hom = σ.hom ≫ m := by
      have h : ((T.map (𝟙 N)).app X ≫ n) ≫ σ.hom = σ.hom ≫ m ≫ (T.obj X).map (𝟙 N) :=
        nativeTorSymmetry_hom_naturality.{nr,nm} R₇ (𝟙 N) (ModuleCat.ofHom f) q
      rw [h₁, h₂, Category.id_comp, Category.comp_id] at h
      exact h
    have h : n = σ.hom ≫ m ≫ σ.inv := by
      have hh := congrArg (fun k : TX ⟶ TN => k ≫ σ.inv) hn
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh
    change (σ.hom ≫ m ≫ σ.inv).hom = n.hom
    exact congrArg (fun k : TX ⟶ TX => k.hom) h.symm
  refine
    { toFun := fun f => ((T.obj N).map (ModuleCat.ofHom f)).hom
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_
      commutes' := ?_ }
  · have h := C.map_one
    change C 1 = 1 at h
    rw [hC] at h
    exact h
  · intro f g
    have h := C.map_mul f g
    change C (f * g) = C f * C g at h
    rw [hC, hC, hC] at h
    exact h
  · have h := C.map_zero
    change C 0 = 0 at h
    rw [hC] at h
    exact h
  · intro f g
    have h := C.map_add f g
    change C (f + g) = C f + C g at h
    rw [hC, hC, hC] at h
    exact h
  · intro r
    have h := C.commutes r
    rw [hC] at h
    exact h

/-- Earned both-variable native symmetry naturality equips the literal
original resolved-variable native Tor map with its genuine algebra laws. -/
theorem nativeTorSecondEndAlgHom_apply (N X : ModuleCat.{max nr nm} R₇) (q : ℕ)
    (f : Module.End R₇ X) :
    nativeTorSecondEndAlgHom R₇ N X q f =
      (((Tor (ModuleCat.{max nr nm} R₇) q).obj N).map (ModuleCat.ofHom f)).hom := by
  rfl

/-- The two actual original native Tor coefficient operators commute
by the actual native bifunctor's naturality square. -/
theorem nativeTorEndOperators_commute (N X : ModuleCat.{max nr nm} R₇) (q : ℕ)
    (f : Module.End R₇ N) (g : Module.End R₇ X) :
    Commute (nativeTorFirstEndAlgHom R₇ N X q f) (nativeTorSecondEndAlgHom R₇ N X q g) := by
  unfold Commute SemiconjBy
  rw [nativeTorFirstEndAlgHom_apply, nativeTorSecondEndAlgHom_apply]
  let T := Tor (ModuleCat.{max nr nm} R₇) q
  let Z := (T.obj N).obj X
  let fm : Z ⟶ Z := (T.map (ModuleCat.ofHom f)).app X
  let gm : Z ⟶ Z := (T.obj N).map (ModuleCat.ofHom g)
  have h : gm ≫ fm = fm ≫ gm := (T.map (ModuleCat.ofHom f)).naturality (ModuleCat.ofHom g)
  change (gm ≫ fm).hom = (fm ≫ gm).hom
  exact congrArg (fun k : Z ⟶ Z => k.hom) h

end NativeCoefficientOperators

section NativeTensorSupportAction

universe sr sv sw st

variable (R₈ : Type sr) (V₈ : Type sv) (W₈ : Type sw)
  [CommRing R₈] [CommRing V₈] [CommRing W₈] [Algebra R₈ V₈] [Algebra R₈ W₈]

/-- The original coefficient multiplication on its canonical carrier lift. -/
def originalLiftedMulEnd.{mr,mv,mt} (R₉ : Type mr) (V₉ : Type mv)
    [CommRing R₉] [CommRing V₉] [Algebra R₉ V₉] :
    V₉ →ₐ[R₉] Module.End R₉ (ULift.{max mr mv mt} V₉) :=
  Algebra.lsmul R₉ R₉ (ULift.{max mr mv mt} V₉)

/-- Original lifted multiplication has the actual ring multiplication value. -/
theorem originalLiftedMulEnd_apply.{mr,mv,mt} (R₉ : Type mr) (V₉ : Type mv)
    [CommRing R₉] [CommRing V₉] [Algebra R₉ V₉] (v v' : V₉) :
    originalLiftedMulEnd.{mr,mv,mt} R₉ V₉ v (ULift.up v') = ULift.up (v * v') := by
  rfl

/-- This is the actual original native middle-ring Tor of the two
original ring coefficients in their common carrier universe. -/
abbrev originalMiddleTor (q : ℕ) : ModuleCat.{max sr sv sw st} R₈ := by
  letI : MonoidalCategoryStruct (ModuleCat.{max sr sv sw st} R₈) :=
    tensorStructure.{sr,max sr sv sw st}
  letI : MonoidalCategory (ModuleCat.{max sr sv sw st} R₈) :=
    monoidalCategory.{sr,max sr sv sw st}
  letI : MonoidalPreadditive (ModuleCat.{max sr sv sw st} R₈) :=
    monoidalPreadditive.{sr,max sr sv sw st}
  exact ((Tor (ModuleCat.{max sr sv sw st} R₈) q).obj
    (ModuleCat.of R₈ (ULift.{max sr sv sw st} V₈))).obj
      (ModuleCat.of R₈ (ULift.{max sr sv sw st} W₈))

/-- Original V multiplication acts on the actual first native Tor coefficient. -/
def originalMiddleTorLeftEndMap (q : ℕ) :
    V₈ →ₐ[R₈] Module.End R₈ (originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) :=
  (nativeTorFirstEndAlgHom.{sr,max sr sv sw st} R₈
    (ModuleCat.of R₈ (ULift.{max sr sv sw st} V₈))
    (ModuleCat.of R₈ (ULift.{max sr sv sw st} W₈)) q).comp
      (originalLiftedMulEnd.{sr,sv,max sw st} R₈ V₈)

/-- Original W multiplication acts on the actual resolved native Tor coefficient. -/
def originalMiddleTorRightEndMap (q : ℕ) :
    W₈ →ₐ[R₈] Module.End R₈ (originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) :=
  (nativeTorSecondEndAlgHom.{sr,max sr sv sw st} R₈
    (ModuleCat.of R₈ (ULift.{max sr sv sw st} V₈))
    (ModuleCat.of R₈ (ULift.{max sr sv sw st} W₈)) q).comp
      (originalLiftedMulEnd.{sr,sw,max sv st} R₈ W₈)

/-- The original left factor representation of native Tor. -/
abbrev originalMiddleTorLeftModule (q : ℕ) :
    Module V₈ (originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) :=
  Module.compHom _ (originalMiddleTorLeftEndMap.{sr,sv,sw,st} R₈ V₈ W₈ q).toRingHom

/-- The original right factor representation of native Tor. -/
abbrev originalMiddleTorRightModule (q : ℕ) :
    Module W₈ (originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) :=
  Module.compHom _ (originalMiddleTorRightEndMap.{sr,sv,sw,st} R₈ V₈ W₈ q).toRingHom

/-- The actual V action retains the original middle-ring scalars. -/
theorem originalMiddleTorLeftTower (q : ℕ) :
    letI : Module V₈ (originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) :=
      originalMiddleTorLeftModule.{sr,sv,sw,st} R₈ V₈ W₈ q
    IsScalarTower R₈ V₈ (originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) := by
  let : Module V₈ (originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) :=
    originalMiddleTorLeftModule.{sr,sv,sw,st} R₈ V₈ W₈ q
  apply IsScalarTower.of_algebraMap_smul
  intro r z
  change originalMiddleTorLeftEndMap.{sr,sv,sw,st} R₈ V₈ W₈ q (algebraMap R₈ V₈ r) z = r • z
  rw [(originalMiddleTorLeftEndMap.{sr,sv,sw,st} R₈ V₈ W₈ q).commutes]
  rfl

/-- The actual W action retains the same original middle-ring scalars. -/
theorem originalMiddleTorRightTower (q : ℕ) :
    letI : Module W₈ (originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) :=
      originalMiddleTorRightModule.{sr,sv,sw,st} R₈ V₈ W₈ q
    IsScalarTower R₈ W₈ (originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) := by
  let : Module W₈ (originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) :=
    originalMiddleTorRightModule.{sr,sv,sw,st} R₈ V₈ W₈ q
  apply IsScalarTower.of_algebraMap_smul
  intro r z
  change originalMiddleTorRightEndMap.{sr,sv,sw,st} R₈ V₈ W₈ q (algebraMap R₈ W₈ r) z = r • z
  rw [(originalMiddleTorRightEndMap.{sr,sv,sw,st} R₈ V₈ W₈ q).commutes]
  rfl

/-- The original two support-algebra actions commute on actual native Tor. -/
theorem originalMiddleTorFactorsCommute (q : ℕ) :
    letI : Module V₈ (originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) :=
      originalMiddleTorLeftModule.{sr,sv,sw,st} R₈ V₈ W₈ q
    letI : Module W₈ (originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) :=
      originalMiddleTorRightModule.{sr,sv,sw,st} R₈ V₈ W₈ q
    SMulCommClass V₈ W₈ (originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) := by
  let : Module V₈ (originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) :=
    originalMiddleTorLeftModule.{sr,sv,sw,st} R₈ V₈ W₈ q
  let : Module W₈ (originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) :=
    originalMiddleTorRightModule.{sr,sv,sw,st} R₈ V₈ W₈ q
  refine ⟨fun v w z => ?_⟩
  have h := nativeTorEndOperators_commute.{sr,max sr sv sw st} R₈
    (ModuleCat.of R₈ (ULift.{max sr sv sw st} V₈))
    (ModuleCat.of R₈ (ULift.{max sr sv sw st} W₈)) q
    (originalLiftedMulEnd.{sr,sv,max sw st} R₈ V₈ v)
    (originalLiftedMulEnd.{sr,sw,max sv st} R₈ W₈ w)
  exact congrArg (fun f : Module.End R₈ (originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) => f z) h.eq

/-- The real T = V ⊗[R] W acts on the original native middle-ring Tor,
using the stock balanced product representation of its two derived actions. -/
abbrev originalMiddleTorTensorModule (q : ℕ) :
    Module (V₈ ⊗[R₈] W₈) (originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) := by
  letI : Module V₈ (originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) :=
    originalMiddleTorLeftModule.{sr,sv,sw,st} R₈ V₈ W₈ q
  letI : Module W₈ (originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) :=
    originalMiddleTorRightModule.{sr,sv,sw,st} R₈ V₈ W₈ q
  letI : IsScalarTower R₈ V₈ (originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) :=
    originalMiddleTorLeftTower.{sr,sv,sw,st} R₈ V₈ W₈ q
  letI : IsScalarTower R₈ W₈ (originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) :=
    originalMiddleTorRightTower.{sr,sv,sw,st} R₈ V₈ W₈ q
  letI : SMulCommClass V₈ W₈ (originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) :=
    originalMiddleTorFactorsCommute.{sr,sv,sw,st} R₈ V₈ W₈ q
  exact TensorProduct.Algebra.module

/-- A real pure support tensor acts by the actual original two native
coefficient multiplication operators. -/
theorem originalMiddleTorTensorModule_tmul (q : ℕ) (v : V₈) (w : W₈)
    (z : originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) :
    letI : Module (V₈ ⊗[R₈] W₈) (originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) :=
      originalMiddleTorTensorModule.{sr,sv,sw,st} R₈ V₈ W₈ q
    (v ⊗ₜ[R₈] w) • z =
      originalMiddleTorLeftEndMap.{sr,sv,sw,st} R₈ V₈ W₈ q v
        (originalMiddleTorRightEndMap.{sr,sv,sw,st} R₈ V₈ W₈ q w z) := by
  rfl

/-- The actual balanced support representation as an algebra map into
endomorphisms of the original native middle-ring Tor. -/
def originalMiddleTorTensorEndMap (q : ℕ) :
    V₈ ⊗[R₈] W₈ →ₐ[R₈] Module.End R₈ (originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) :=
  Algebra.TensorProduct.lift
    (originalMiddleTorLeftEndMap.{sr,sv,sw,st} R₈ V₈ W₈ q)
    (originalMiddleTorRightEndMap.{sr,sv,sw,st} R₈ V₈ W₈ q)
    (fun v w => nativeTorEndOperators_commute.{sr,max sr sv sw st} R₈
      (ModuleCat.of R₈ (ULift.{max sr sv sw st} V₈))
      (ModuleCat.of R₈ (ULift.{max sr sv sw st} W₈)) q
      (originalLiftedMulEnd.{sr,sv,max sw st} R₈ V₈ v)
      (originalLiftedMulEnd.{sr,sw,max sv st} R₈ W₈ w))

/-- The endomorphism-valued balanced support map is precisely the real
canonical tensor-product module action. -/
theorem originalMiddleTorTensorEndMap_apply (q : ℕ) (t : V₈ ⊗[R₈] W₈)
    (z : originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) :
    letI : Module (V₈ ⊗[R₈] W₈) (originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) :=
      originalMiddleTorTensorModule.{sr,sv,sw,st} R₈ V₈ W₈ q
    originalMiddleTorTensorEndMap.{sr,sv,sw,st} R₈ V₈ W₈ q t z = t • z := by
  let : Module (V₈ ⊗[R₈] W₈) (originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) :=
    originalMiddleTorTensorModule.{sr,sv,sw,st} R₈ V₈ W₈ q
  induction t using TensorProduct.inductionOn with
  | tmul v w => rfl
  | add t₁ t₂ h₁ h₂ => simp only [_root_.map_add, LinearMap.add_apply, add_smul, h₁, h₂]

/-- Every pure balanced support operator is the literal product of the
original two native Tor factor operators. -/
theorem originalMiddleTorTensorEndMap_tmul (q : ℕ) (v : V₈) (w : W₈)
    (z : originalMiddleTor.{sr,sv,sw,st} R₈ V₈ W₈ q) :
    originalMiddleTorTensorEndMap.{sr,sv,sw,st} R₈ V₈ W₈ q (v ⊗ₜ[R₈] w) z =
      originalMiddleTorLeftEndMap.{sr,sv,sw,st} R₈ V₈ W₈ q v
        (originalMiddleTorRightEndMap.{sr,sv,sw,st} R₈ V₈ W₈ q w z) := by
  rfl

end NativeTensorSupportAction

section ActualCoefficientMultiplication

universe ck cb cc cv ct

variable (K₁₀ : Type ck) (B₁₀ : Type cb) (C₁₀ : Type cc) (V₁₀ : Type cv)
  [CommRing K₁₀] [CommRing B₁₀] [CommRing C₁₀] [CommRing V₁₀]
  [Algebra K₁₀ B₁₀] [Algebra K₁₀ C₁₀] [Algebra K₁₀ V₁₀]
  [Algebra B₁₀ V₁₀] [IsScalarTower K₁₀ B₁₀ V₁₀]

/-- The actual left adjoining coefficient iso preserves original
coefficient multiplication, with both real scalar-extension and tensor maps. -/
theorem tensorAdjoinLeftCoefficientIso_mul_hom_naturality (v : V₁₀) :
    letI : Algebra (B₁₀ ⊗[K₁₀] C₁₀) (V₁₀ ⊗[K₁₀] C₁₀) :=
      (tensorAdjoinLeftCoefficientMap K₁₀ B₁₀ C₁₀ V₁₀).toRingHom.toAlgebra
    (extendScalars.{cb,max cb cc,max ck cb cc cv ct}
      (algebraMap B₁₀ (B₁₀ ⊗[K₁₀] C₁₀))).map
        (ModuleCat.ofHom (originalLiftedMulEnd.{cb,cv,max ck cb cc cv ct} B₁₀ V₁₀ v)) ≫
          (tensorAdjoinLeftCoefficientIso.{ck,cb,cc,cv,ct} K₁₀ B₁₀ C₁₀ V₁₀).hom =
      (tensorAdjoinLeftCoefficientIso.{ck,cb,cc,cv,ct} K₁₀ B₁₀ C₁₀ V₁₀).hom ≫
        ModuleCat.ofHom (originalLiftedMulEnd.{max cb cc,max cv cc,max ck cb cc cv ct}
          (B₁₀ ⊗[K₁₀] C₁₀) (V₁₀ ⊗[K₁₀] C₁₀) (v ⊗ₜ[K₁₀] (1 : C₁₀))) := by
  let : Algebra (B₁₀ ⊗[K₁₀] C₁₀) (V₁₀ ⊗[K₁₀] C₁₀) :=
    (tensorAdjoinLeftCoefficientMap K₁₀ B₁₀ C₁₀ V₁₀).toRingHom.toAlgebra
  let F := extendScalars.{cb,max cb cc,max ck cb cc cv ct} (algebraMap B₁₀ (B₁₀ ⊗[K₁₀] C₁₀))
  let e := tensorAdjoinLeftCoefficientIso.{ck,cb,cc,cv,ct} K₁₀ B₁₀ C₁₀ V₁₀
  let m := ModuleCat.ofHom (originalLiftedMulEnd.{cb,cv,max ck cb cc cv ct} B₁₀ V₁₀ v)
  let n := ModuleCat.ofHom (originalLiftedMulEnd.{max cb cc,max cv cc,max ck cb cc cv ct}
    (B₁₀ ⊗[K₁₀] C₁₀) (V₁₀ ⊗[K₁₀] C₁₀) (v ⊗ₜ[K₁₀] (1 : C₁₀)))
  change F.map m ≫ e.hom = e.hom ≫ n
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  rcases x with ⟨v'⟩
  change ULift.up (((1 : B₁₀) • (v * v')) ⊗ₜ[K₁₀] (1 : C₁₀)) =
    ULift.up ((v ⊗ₜ[K₁₀] (1 : C₁₀)) * (((1 : B₁₀) • v') ⊗ₜ[K₁₀] (1 : C₁₀)))
  rw [one_smul, one_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

end ActualCoefficientMultiplication

section ActualRightCoefficientMultiplication

universe dk da db dw dt

variable (K₁₁ : Type dk) (A₁₁ : Type da) (B₁₁ : Type db) (W₁₁ : Type dw)
  [CommRing K₁₁] [CommRing A₁₁] [CommRing B₁₁] [CommRing W₁₁]
  [Algebra K₁₁ A₁₁] [Algebra K₁₁ B₁₁] [Algebra K₁₁ W₁₁]
  [Algebra B₁₁ W₁₁] [IsScalarTower K₁₁ B₁₁ W₁₁]

/-- The actual right adjoining coefficient iso preserves original
coefficient multiplication, retaining both original algebra actions. -/
theorem tensorAdjoinRightCoefficientIso_mul_hom_naturality (w : W₁₁) :
    letI : Algebra B₁₁ (A₁₁ ⊗[K₁₁] B₁₁) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra (A₁₁ ⊗[K₁₁] B₁₁) (A₁₁ ⊗[K₁₁] W₁₁) :=
      (tensorAdjoinRightCoefficientMap K₁₁ A₁₁ B₁₁ W₁₁).toRingHom.toAlgebra
    (extendScalars.{db,max da db,max dk da db dw dt}
      (algebraMap B₁₁ (A₁₁ ⊗[K₁₁] B₁₁))).map
        (ModuleCat.ofHom (originalLiftedMulEnd.{db,dw,max dk da db dw dt} B₁₁ W₁₁ w)) ≫
          (tensorAdjoinRightCoefficientIso.{dk,da,db,dw,dt} K₁₁ A₁₁ B₁₁ W₁₁).hom =
      (tensorAdjoinRightCoefficientIso.{dk,da,db,dw,dt} K₁₁ A₁₁ B₁₁ W₁₁).hom ≫
        ModuleCat.ofHom (originalLiftedMulEnd.{max da db,max da dw,max dk da db dw dt}
          (A₁₁ ⊗[K₁₁] B₁₁) (A₁₁ ⊗[K₁₁] W₁₁) ((1 : A₁₁) ⊗ₜ[K₁₁] w)) := by
  let : Algebra B₁₁ (A₁₁ ⊗[K₁₁] B₁₁) := Algebra.TensorProduct.rightAlgebra
  let : Algebra (A₁₁ ⊗[K₁₁] B₁₁) (A₁₁ ⊗[K₁₁] W₁₁) :=
    (tensorAdjoinRightCoefficientMap K₁₁ A₁₁ B₁₁ W₁₁).toRingHom.toAlgebra
  let F := extendScalars.{db,max da db,max dk da db dw dt} (algebraMap B₁₁ (A₁₁ ⊗[K₁₁] B₁₁))
  let e := tensorAdjoinRightCoefficientIso.{dk,da,db,dw,dt} K₁₁ A₁₁ B₁₁ W₁₁
  let m := ModuleCat.ofHom (originalLiftedMulEnd.{db,dw,max dk da db dw dt} B₁₁ W₁₁ w)
  let n := ModuleCat.ofHom (originalLiftedMulEnd.{max da db,max da dw,max dk da db dw dt}
    (A₁₁ ⊗[K₁₁] B₁₁) (A₁₁ ⊗[K₁₁] W₁₁) ((1 : A₁₁) ⊗ₜ[K₁₁] w))
  change F.map m ≫ e.hom = e.hom ≫ n
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  rcases x with ⟨w'⟩
  change ULift.up ((1 : A₁₁) ⊗ₜ[K₁₁] ((1 : B₁₁) • (w * w'))) =
    ULift.up (((1 : A₁₁) ⊗ₜ[K₁₁] w) * ((1 : A₁₁) ⊗ₜ[K₁₁] ((1 : B₁₁) • w')))
  rw [one_smul, one_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end ActualRightCoefficientMultiplication

/-- Actual coefficient-ring multiplication with its original scalar map;
the native carrier and native scalar action are retained. -/
def originalRingCoefficientMul.{pr,pq,pm} (R₁₂ : Type pr) (Q₁₂ : Type pq)
    [CommRing R₁₂] [CommRing Q₁₂] (f : R₁₂ →+* Q₁₂) (d : Q₁₂) :
    Module.End R₁₂ (originalRingCoefficient.{pr,pq,pm} R₁₂ Q₁₂ f) := by
  letI : Algebra R₁₂ Q₁₂ := f.toAlgebra
  exact originalLiftedMulEnd.{pr,pq,pm} R₁₂ Q₁₂ d

/-- The actual original coefficient operator is literal ring multiplication. -/
theorem originalRingCoefficientMul_apply.{pr,pq,pm} (R₁₂ : Type pr) (Q₁₂ : Type pq)
    [CommRing R₁₂] [CommRing Q₁₂] (f : R₁₂ →+* Q₁₂) (d x : Q₁₂) :
    originalRingCoefficientMul.{pr,pq,pm} R₁₂ Q₁₂ f d (ULift.up x) = ULift.up (d * x) := by
  rfl

section ActualIntrinsicAlgebras

universe ik ib iv iw it

variable (K₅ : Type ik) (B₅ : Type ib) (V₅ : Type iv) (W₅ : Type iw)
  [CommRing K₅] [CommRing B₅] [CommRing V₅] [CommRing W₅]
  [Algebra K₅ B₅] [Algebra K₅ V₅] [Algebra K₅ W₅]
  (aV : B₅ →ₐ[K₅] V₅) (aW : B₅ →ₐ[K₅] W₅)

/-- The original intrinsic graph ambient is rearranged only by the
canonical algebra associators and original tensor commutation. -/
def intrinsicToStandardAmbientEquiv :
    (V₅ ⊗[K₅] W₅) ⊗[K₅] B₅ ≃ₐ[K₅] (V₅ ⊗[K₅] B₅) ⊗[K₅] W₅ :=
  (Algebra.TensorProduct.assoc K₅ K₅ K₅ V₅ W₅ B₅).trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : V₅ ≃ₐ[K₅] V₅)
      (Algebra.TensorProduct.comm K₅ W₅ B₅)).trans
        (Algebra.TensorProduct.assoc K₅ K₅ K₅ V₅ B₅ W₅).symm)

/-- The intrinsic rearrangement keeps all three original factors. -/
theorem intrinsicToStandardAmbientEquiv_tmul (v : V₅) (w : W₅) (b : B₅) :
    intrinsicToStandardAmbientEquiv K₅ B₅ V₅ W₅ ((v ⊗ₜ[K₅] w) ⊗ₜ[K₅] b) =
      (v ⊗ₜ[K₅] b) ⊗ₜ[K₅] w := by
  rfl

/-- The original first graph evaluation uses the actual B map to V. -/
def intrinsicGraphLeftEvaluation :
    (V₅ ⊗[K₅] W₅) ⊗[K₅] B₅ →ₐ[K₅] V₅ ⊗[K₅] W₅ :=
  Algebra.TensorProduct.etaleGraphEvaluation
    (Algebra.TensorProduct.includeLeft.comp aV)

/-- The original second graph evaluation uses the actual B map to W. -/
def intrinsicGraphRightEvaluation :
    (V₅ ⊗[K₅] W₅) ⊗[K₅] B₅ →ₐ[K₅] V₅ ⊗[K₅] W₅ :=
  Algebra.TensorProduct.etaleGraphEvaluation
    (Algebra.TensorProduct.includeRight.comp aW)

end ActualIntrinsicAlgebras

/-- Conjugation of a genuine module endomorphism preserves its original
linear comparison map. This is the stock endomorphism conjugation. -/
theorem originalConjugateEnd_naturality.{cr,cm,cn} (R₁₃ : Type cr) [CommRing R₁₃]
    {M₁₃ : Type cm} {N₁₃ : Type cn} [AddCommGroup M₁₃] [AddCommGroup N₁₃]
    [Module R₁₃ M₁₃] [Module R₁₃ N₁₃] (e : M₁₃ ≃ₗ[R₁₃] N₁₃) (f : Module.End R₁₃ N₁₃) :
    e.toLinearMap ∘ₗ (e.symm.conjAlgEquiv R₁₃ f) = f ∘ₗ e.toLinearMap := by
  apply LinearMap.ext
  intro x
  change e (e.symm (f (e x))) = f (e x)
  exact e.apply_symm_apply _

section OriginalAmbientAlgebras

universe ku au bu cu vu wu mu

variable (K₁ : Type ku) (A₁ : Type au) (B₁ : Type bu) (C₁ : Type cu)
  (V₁ : Type vu) (W₁ : Type wu)
  [CommRing K₁] [CommRing A₁] [CommRing B₁] [CommRing C₁]
  [CommRing V₁] [CommRing W₁]
  [Algebra K₁ A₁] [Algebra K₁ B₁] [Algebra K₁ C₁]
  [Algebra K₁ V₁] [Algebra K₁ W₁]
  (iV : A₁ ⊗[K₁] B₁ →ₐ[K₁] V₁) (iW : B₁ ⊗[K₁] C₁ →ₐ[K₁] W₁)

/-- The original middle-factor map on the first support algebra. -/
def originalMiddleLeftMap : B₁ →ₐ[K₁] V₁ :=
  iV.comp Algebra.TensorProduct.includeRight

/-- The original middle-factor map on the second support algebra. -/
def originalMiddleRightMap : B₁ →ₐ[K₁] W₁ :=
  iW.comp Algebra.TensorProduct.includeLeft

/-- The actual standard triple ambient maps to its first support coefficient. -/
def originalAmbientLeftMap :
    (A₁ ⊗[K₁] B₁) ⊗[K₁] C₁ →ₐ[K₁] V₁ ⊗[K₁] C₁ :=
  Algebra.TensorProduct.map iV (AlgHom.id K₁ C₁)

/-- The actual standard triple ambient maps to its second support coefficient. -/
def originalAmbientRightMap :
    (A₁ ⊗[K₁] B₁) ⊗[K₁] C₁ →ₐ[K₁] A₁ ⊗[K₁] W₁ :=
  (Algebra.TensorProduct.map (AlgHom.id K₁ A₁) iW).comp
    (Algebra.TensorProduct.assoc K₁ K₁ K₁ A₁ B₁ C₁).toAlgHom

/-- Restricting the second original coefficient keeps its actual B support map. -/
theorem originalAmbientRightMap_includeLeft (a : A₁) (b : B₁) :
    originalAmbientRightMap K₁ A₁ B₁ C₁ W₁ iW
      ((a ⊗ₜ[K₁] b) ⊗ₜ[K₁] (1 : C₁)) =
        a ⊗ₜ[K₁] originalMiddleRightMap K₁ B₁ C₁ W₁ iW b := by
  rfl

/-- The actual extended first coefficient, including its common carrier-universe
lift, is the original standard triple coefficient with its original scalar map. -/
def originalAmbientLeftCoefficientIso :
    letI : Algebra (A₁ ⊗[K₁] B₁) V₁ := iV.toRingHom.toAlgebra
    letI : Algebra ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁) (V₁ ⊗[K₁] C₁) :=
      (originalAmbientLeftMap K₁ A₁ B₁ C₁ V₁ iV).toRingHom.toAlgebra
    (extendScalars.{max au bu,max au bu cu,max ku au bu cu vu mu}
      (algebraMap (A₁ ⊗[K₁] B₁) ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁))).obj
        (ModuleCat.of (A₁ ⊗[K₁] B₁) (ULift.{max ku au bu cu vu mu} V₁)) ≅
      ModuleCat.of ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁)
        (ULift.{max ku au bu cu vu mu} (V₁ ⊗[K₁] C₁)) := by
  letI : Algebra (A₁ ⊗[K₁] B₁) V₁ := iV.toRingHom.toAlgebra
  letI : IsScalarTower K₁ (A₁ ⊗[K₁] B₁) V₁ := IsScalarTower.of_algHom iV
  letI : Algebra ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁) (V₁ ⊗[K₁] C₁) :=
    (originalAmbientLeftMap K₁ A₁ B₁ C₁ V₁ iV).toRingHom.toAlgebra
  exact tensorAdjoinLeftCoefficientIso.{ku,max au bu,cu,vu,mu}
    K₁ (A₁ ⊗[K₁] B₁) C₁ V₁

/-- The actual first standard ambient inclusion restricts the original
second support coefficient through precisely its original middle map. -/
theorem originalAmbientRightMap_comp_includeLeft :
    (originalAmbientRightMap K₁ A₁ B₁ C₁ W₁ iW).comp Algebra.TensorProduct.includeLeft =
      Algebra.TensorProduct.map (AlgHom.id K₁ A₁)
        (originalMiddleRightMap K₁ B₁ C₁ W₁ iW) := by
  apply AlgHom.ext
  intro s
  induction s using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add x y hx hy => simp only [_root_.map_add, hx, hy]

/-- The actual original standard ambient native Tor, restricted along
its two genuine original middle-ring inclusions. -/
abbrev originalStandardAmbientTorModule (q : ℕ) : ModuleCat.{max ku au bu cu vu wu mu} B₁ := by
  letI : Algebra B₁ (A₁ ⊗[K₁] B₁) := Algebra.TensorProduct.rightAlgebra
  letI : MonoidalCategoryStruct (ModuleCat.{max ku au bu cu vu wu mu} ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁)) :=
    tensorStructure.{max au bu cu,max ku au bu cu vu wu mu}
  letI : MonoidalCategory (ModuleCat.{max ku au bu cu vu wu mu} ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁)) :=
    monoidalCategory.{max au bu cu,max ku au bu cu vu wu mu}
  letI : MonoidalPreadditive (ModuleCat.{max ku au bu cu vu wu mu} ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁)) :=
    monoidalPreadditive.{max au bu cu,max ku au bu cu vu wu mu}
  let S₀ := A₁ ⊗[K₁] B₁
  let S := S₀ ⊗[K₁] C₁
  let H₀ := restrictScalars.{max ku au bu cu vu wu mu,max au bu,max au bu cu} (algebraMap S₀ S)
  let H := restrictScalars.{max ku au bu cu vu wu mu,bu,max au bu} (algebraMap B₁ S₀)
  let NS : ModuleCat.{max ku au bu cu vu wu mu} S :=
    originalRingCoefficient.{max au bu cu,max au wu,max ku au bu cu vu wu mu} _ _
      (originalAmbientRightMap K₁ A₁ B₁ C₁ W₁ iW).toRingHom
  let LS : ModuleCat.{max ku au bu cu vu wu mu} S :=
    originalRingCoefficient.{max au bu cu,max vu cu,max ku au bu cu vu wu mu} _ _
      (originalAmbientLeftMap K₁ A₁ B₁ C₁ V₁ iV).toRingHom
  exact H.obj (H₀.obj (((Tor (ModuleCat.{max ku au bu cu vu wu mu} S) q).obj NS).obj LS))

/-- Literal original V multiplication on the resolved standard coefficient
induces this actual original native Tor endomorphism. -/
def originalStandardAmbientLeftOperator (q : ℕ) (v : V₁) :
    Module.End B₁ (originalStandardAmbientTorModule.{ku,au,bu,cu,vu,wu,mu}
      K₁ A₁ B₁ C₁ V₁ W₁ iV iW q) := by
  letI : Algebra B₁ (A₁ ⊗[K₁] B₁) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁) (V₁ ⊗[K₁] C₁) :=
    (originalAmbientLeftMap K₁ A₁ B₁ C₁ V₁ iV).toRingHom.toAlgebra
  letI : MonoidalCategoryStruct (ModuleCat.{max ku au bu cu vu wu mu} ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁)) :=
    tensorStructure.{max au bu cu,max ku au bu cu vu wu mu}
  letI : MonoidalCategory (ModuleCat.{max ku au bu cu vu wu mu} ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁)) :=
    monoidalCategory.{max au bu cu,max ku au bu cu vu wu mu}
  letI : MonoidalPreadditive (ModuleCat.{max ku au bu cu vu wu mu} ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁)) :=
    monoidalPreadditive.{max au bu cu,max ku au bu cu vu wu mu}
  let S₀ := A₁ ⊗[K₁] B₁
  let S := S₀ ⊗[K₁] C₁
  let H₀ := restrictScalars.{max ku au bu cu vu wu mu,max au bu,max au bu cu} (algebraMap S₀ S)
  let H := restrictScalars.{max ku au bu cu vu wu mu,bu,max au bu} (algebraMap B₁ S₀)
  let NS : ModuleCat.{max ku au bu cu vu wu mu} S :=
    originalRingCoefficient.{max au bu cu,max au wu,max ku au bu cu vu wu mu} _ _
      (originalAmbientRightMap K₁ A₁ B₁ C₁ W₁ iW).toRingHom
  let LS : ModuleCat.{max ku au bu cu vu wu mu} S :=
    originalRingCoefficient.{max au bu cu,max vu cu,max ku au bu cu vu wu mu} _ _
      (originalAmbientLeftMap K₁ A₁ B₁ C₁ V₁ iV).toRingHom
  let m : LS ⟶ LS := ModuleCat.ofHom
    (originalLiftedMulEnd.{max au bu cu,max vu cu,max ku au bu cu vu wu mu} S (V₁ ⊗[K₁] C₁)
      (v ⊗ₜ[K₁] (1 : C₁)))
  exact (H.map (H₀.map (((Tor (ModuleCat.{max ku au bu cu vu wu mu} S) q).obj NS).map m))).hom

/-- Literal original W multiplication on the standard coefficient
induces this actual original native Tor endomorphism. -/
def originalStandardAmbientRightOperator (q : ℕ) (w : W₁) :
    Module.End B₁ (originalStandardAmbientTorModule.{ku,au,bu,cu,vu,wu,mu}
      K₁ A₁ B₁ C₁ V₁ W₁ iV iW q) := by
  letI : Algebra B₁ (A₁ ⊗[K₁] B₁) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁) (A₁ ⊗[K₁] W₁) :=
    (originalAmbientRightMap K₁ A₁ B₁ C₁ W₁ iW).toRingHom.toAlgebra
  letI : MonoidalCategoryStruct (ModuleCat.{max ku au bu cu vu wu mu} ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁)) :=
    tensorStructure.{max au bu cu,max ku au bu cu vu wu mu}
  letI : MonoidalCategory (ModuleCat.{max ku au bu cu vu wu mu} ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁)) :=
    monoidalCategory.{max au bu cu,max ku au bu cu vu wu mu}
  letI : MonoidalPreadditive (ModuleCat.{max ku au bu cu vu wu mu} ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁)) :=
    monoidalPreadditive.{max au bu cu,max ku au bu cu vu wu mu}
  let S₀ := A₁ ⊗[K₁] B₁
  let S := S₀ ⊗[K₁] C₁
  let H₀ := restrictScalars.{max ku au bu cu vu wu mu,max au bu,max au bu cu} (algebraMap S₀ S)
  let H := restrictScalars.{max ku au bu cu vu wu mu,bu,max au bu} (algebraMap B₁ S₀)
  let NS : ModuleCat.{max ku au bu cu vu wu mu} S :=
    originalRingCoefficient.{max au bu cu,max au wu,max ku au bu cu vu wu mu} _ _
      (originalAmbientRightMap K₁ A₁ B₁ C₁ W₁ iW).toRingHom
  let LS : ModuleCat.{max ku au bu cu vu wu mu} S :=
    originalRingCoefficient.{max au bu cu,max vu cu,max ku au bu cu vu wu mu} _ _
      (originalAmbientLeftMap K₁ A₁ B₁ C₁ V₁ iV).toRingHom
  let m : NS ⟶ NS := ModuleCat.ofHom
    (originalLiftedMulEnd.{max au bu cu,max au wu,max ku au bu cu vu wu mu} S (A₁ ⊗[K₁] W₁)
      ((1 : A₁) ⊗ₜ[K₁] w))
  exact (H.map (H₀.map (((Tor (ModuleCat.{max ku au bu cu vu wu mu} S) q).map m).app LS))).hom

/-- Both genuine standard field adjoining cancellations, retaining the
actual standard triple ambient and original support maps, reduce its native
Tor to the original ordered middle-ring Tor in every degree. -/
def originalStandardAmbientTorIso [Module.Flat K₁ A₁] [Module.Flat K₁ C₁] (q : ℕ) :
    letI : Algebra B₁ (A₁ ⊗[K₁] B₁) := Algebra.TensorProduct.rightAlgebra
    letI : MonoidalCategoryStruct (ModuleCat.{max ku au bu cu vu wu mu} B₁) :=
      tensorStructure.{bu,max ku au bu cu vu wu mu}
    letI : MonoidalCategoryStruct (ModuleCat.{max ku au bu cu vu wu mu} (A₁ ⊗[K₁] B₁)) :=
      tensorStructure.{max au bu,max ku au bu cu vu wu mu}
    letI : MonoidalCategoryStruct (ModuleCat.{max ku au bu cu vu wu mu}
        ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁)) :=
      tensorStructure.{max au bu cu,max ku au bu cu vu wu mu}
    letI : MonoidalCategory (ModuleCat.{max ku au bu cu vu wu mu} B₁) :=
      monoidalCategory.{bu,max ku au bu cu vu wu mu}
    letI : MonoidalCategory (ModuleCat.{max ku au bu cu vu wu mu} (A₁ ⊗[K₁] B₁)) :=
      monoidalCategory.{max au bu,max ku au bu cu vu wu mu}
    letI : MonoidalCategory (ModuleCat.{max ku au bu cu vu wu mu}
        ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁)) :=
      monoidalCategory.{max au bu cu,max ku au bu cu vu wu mu}
    letI : MonoidalPreadditive (ModuleCat.{max ku au bu cu vu wu mu} B₁) :=
      monoidalPreadditive.{bu,max ku au bu cu vu wu mu}
    letI : MonoidalPreadditive (ModuleCat.{max ku au bu cu vu wu mu} (A₁ ⊗[K₁] B₁)) :=
      monoidalPreadditive.{max au bu,max ku au bu cu vu wu mu}
    letI : MonoidalPreadditive (ModuleCat.{max ku au bu cu vu wu mu}
        ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁)) :=
      monoidalPreadditive.{max au bu cu,max ku au bu cu vu wu mu}
    (restrictScalars.{max ku au bu cu vu wu mu,bu,max au bu}
      (algebraMap B₁ (A₁ ⊗[K₁] B₁))).obj
        ((restrictScalars.{max ku au bu cu vu wu mu,max au bu,max au bu cu}
          (algebraMap (A₁ ⊗[K₁] B₁) ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁))).obj
            (((Tor (ModuleCat.{max ku au bu cu vu wu mu} ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁)) q).obj
              (originalRingCoefficient.{max au bu cu,max au wu,max ku au bu cu vu wu mu}
                _ _ (originalAmbientRightMap K₁ A₁ B₁ C₁ W₁ iW).toRingHom)).obj
                  (originalRingCoefficient.{max au bu cu,max vu cu,max ku au bu cu vu wu mu}
                    _ _ (originalAmbientLeftMap K₁ A₁ B₁ C₁ V₁ iV).toRingHom))) ≅
      (((Tor (ModuleCat.{max ku au bu cu vu wu mu} B₁) q).obj
        (originalRingCoefficient.{bu,vu,max ku au bu cu vu wu mu} _ _
          (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom)).obj
            (originalRingCoefficient.{bu,wu,max ku au bu cu vu wu mu} _ _
              (originalMiddleRightMap K₁ B₁ C₁ W₁ iW).toRingHom)) := by
  letI : Algebra B₁ (A₁ ⊗[K₁] B₁) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra (A₁ ⊗[K₁] B₁) V₁ := iV.toRingHom.toAlgebra
  letI : IsScalarTower K₁ (A₁ ⊗[K₁] B₁) V₁ := IsScalarTower.of_algHom iV
  letI : Algebra B₁ W₁ := (originalMiddleRightMap K₁ B₁ C₁ W₁ iW).toRingHom.toAlgebra
  letI : IsScalarTower K₁ B₁ W₁ :=
    IsScalarTower.of_algHom (originalMiddleRightMap K₁ B₁ C₁ W₁ iW)
  letI : Module.Flat (A₁ ⊗[K₁] B₁) ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁) := inferInstance
  letI : Module.Flat B₁ (A₁ ⊗[K₁] B₁) := tensorAdjoin_flat K₁ A₁ B₁
  letI : MonoidalCategoryStruct (ModuleCat.{max ku au bu cu vu wu mu} B₁) :=
    tensorStructure.{bu,max ku au bu cu vu wu mu}
  letI : MonoidalCategoryStruct (ModuleCat.{max ku au bu cu vu wu mu} (A₁ ⊗[K₁] B₁)) :=
    tensorStructure.{max au bu,max ku au bu cu vu wu mu}
  letI : MonoidalCategoryStruct (ModuleCat.{max ku au bu cu vu wu mu}
      ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁)) :=
    tensorStructure.{max au bu cu,max ku au bu cu vu wu mu}
  letI : MonoidalCategory (ModuleCat.{max ku au bu cu vu wu mu} B₁) :=
    monoidalCategory.{bu,max ku au bu cu vu wu mu}
  letI : MonoidalCategory (ModuleCat.{max ku au bu cu vu wu mu} (A₁ ⊗[K₁] B₁)) :=
    monoidalCategory.{max au bu,max ku au bu cu vu wu mu}
  letI : MonoidalCategory (ModuleCat.{max ku au bu cu vu wu mu}
      ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁)) :=
    monoidalCategory.{max au bu cu,max ku au bu cu vu wu mu}
  letI : MonoidalPreadditive (ModuleCat.{max ku au bu cu vu wu mu} B₁) :=
    monoidalPreadditive.{bu,max ku au bu cu vu wu mu}
  letI : MonoidalPreadditive (ModuleCat.{max ku au bu cu vu wu mu} (A₁ ⊗[K₁] B₁)) :=
    monoidalPreadditive.{max au bu,max ku au bu cu vu wu mu}
  letI : MonoidalPreadditive (ModuleCat.{max ku au bu cu vu wu mu}
      ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁)) :=
    monoidalPreadditive.{max au bu cu,max ku au bu cu vu wu mu}
  let S₀ := A₁ ⊗[K₁] B₁
  let S := S₀ ⊗[K₁] C₁
  let H₀ := restrictScalars.{max ku au bu cu vu wu mu,max au bu,max au bu cu} (algebraMap S₀ S)
  let H := restrictScalars.{max ku au bu cu vu wu mu,bu,max au bu} (algebraMap B₁ S₀)
  let F₀ := extendScalars.{max au bu,max au bu cu,max ku au bu cu vu wu mu} (algebraMap S₀ S)
  let F := extendScalars.{bu,max au bu,max ku au bu cu vu wu mu} (algebraMap B₁ S₀)
  let VR : ModuleCat.{max ku au bu cu vu wu mu} S₀ :=
    originalRingCoefficient.{max au bu,vu,max ku au bu cu vu wu mu} _ _ iV.toRingHom
  let VB : ModuleCat.{max ku au bu cu vu wu mu} B₁ :=
    originalRingCoefficient.{bu,vu,max ku au bu cu vu wu mu} _ _ (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom
  let WB : ModuleCat.{max ku au bu cu vu wu mu} B₁ :=
    originalRingCoefficient.{bu,wu,max ku au bu cu vu wu mu} _ _ (originalMiddleRightMap K₁ B₁ C₁ W₁ iW).toRingHom
  let LS : ModuleCat.{max ku au bu cu vu wu mu} S :=
    originalRingCoefficient.{max au bu cu,max vu cu,max ku au bu cu vu wu mu} _ _ (originalAmbientLeftMap K₁ A₁ B₁ C₁ V₁ iV).toRingHom
  let NS : ModuleCat.{max ku au bu cu vu wu mu} S :=
    originalRingCoefficient.{max au bu cu,max au wu,max ku au bu cu vu wu mu} _ _ (originalAmbientRightMap K₁ A₁ B₁ C₁ W₁ iW).toRingHom
  let eL : F₀.obj VR ≅ LS :=
    tensorAdjoinLeftCoefficientIso.{ku,max au bu,cu,vu,max wu mu} K₁ S₀ C₁ V₁
  let gf : S₀ →+* A₁ ⊗[K₁] W₁ :=
    (tensorAdjoinRightCoefficientMap K₁ A₁ B₁ W₁).toRingHom
  have hgf : gf = (originalAmbientRightMap K₁ A₁ B₁ C₁ W₁ iW).toRingHom.comp
      (algebraMap S₀ S) := by
    symm
    exact congrArg AlgHom.toRingHom
      (originalAmbientRightMap_comp_includeLeft K₁ A₁ B₁ C₁ W₁ iW)
  let rho : H₀.obj NS ≅ originalRingCoefficient.{max au bu,max au wu,max ku au bu cu vu wu mu}
      _ _ gf :=
    (restrictScalarsComp'App (algebraMap S₀ S)
      (originalAmbientRightMap K₁ A₁ B₁ C₁ W₁ iW).toRingHom gf hgf
        (ModuleCat.of (A₁ ⊗[K₁] W₁) (ULift.{max ku au bu cu vu wu mu} (A₁ ⊗[K₁] W₁)))).symm
  let eR : H₀.obj NS ≅ F.obj WB := rho ≪≫
    (tensorAdjoinRightCoefficientIso.{ku,au,bu,wu,max cu vu mu} K₁ A₁ B₁ W₁).symm
  let eV : H.obj VR ≅ VB :=
    (restrictScalarsComp'App (algebraMap B₁ S₀) iV.toRingHom
      (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom rfl
        (ModuleCat.of V₁ (ULift.{max ku au bu cu vu wu mu} V₁))).symm
  exact H.mapIso ((H₀.mapIso (((Tor (ModuleCat.{max ku au bu cu vu wu mu} S) q).obj NS).mapIso
      eL)).symm ≪≫
      flatScalarExtensionTorCancellationIso.{max au bu,max au bu cu,max ku au bu cu vu wu mu}
        S₀ S NS VR q ≪≫
      ((Tor (ModuleCat.{max ku au bu cu vu wu mu} S₀) q).mapIso eR).app VR ≪≫
      nativeTorSymmetry.{max au bu,max ku au bu cu vu wu mu} S₀ (F.obj WB) VR q) ≪≫
    flatScalarExtensionTorCancellationIso.{bu,max au bu,max ku au bu cu vu wu mu}
      B₁ S₀ VR WB q ≪≫
    ((Tor (ModuleCat.{max ku au bu cu vu wu mu} B₁) q).mapIso eV).app WB

/-- Both actual standard adjoining cancellations preserve original V
multiplication, including the genuine change of native Tor orientation. -/
theorem originalStandardAmbientTorIso_left_mul [Module.Flat K₁ A₁] [Module.Flat K₁ C₁]
    (q : ℕ) (v : V₁)
    (z : originalStandardAmbientTorModule.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q) :
    letI : Algebra B₁ V₁ := (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom.toAlgebra
    letI : Algebra B₁ W₁ := (originalMiddleRightMap K₁ B₁ C₁ W₁ iW).toRingHom.toAlgebra
    (originalStandardAmbientTorIso.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q).hom
        (originalStandardAmbientLeftOperator.{ku,au,bu,cu,vu,wu,mu}
          K₁ A₁ B₁ C₁ V₁ W₁ iV iW q v z) =
      originalMiddleTorLeftEndMap.{bu,vu,wu,max ku au cu mu} B₁ V₁ W₁ q v
        ((originalStandardAmbientTorIso.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q).hom z) := by
  let : Algebra B₁ V₁ := (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom.toAlgebra
  let : Algebra ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁) (V₁ ⊗[K₁] C₁) :=
    (originalAmbientLeftMap K₁ A₁ B₁ C₁ V₁ iV).toRingHom.toAlgebra
  let : Algebra B₁ (A₁ ⊗[K₁] B₁) := Algebra.TensorProduct.rightAlgebra
  let : Algebra (A₁ ⊗[K₁] B₁) V₁ := iV.toRingHom.toAlgebra
  let : IsScalarTower K₁ (A₁ ⊗[K₁] B₁) V₁ := IsScalarTower.of_algHom iV
  let : Algebra B₁ W₁ := (originalMiddleRightMap K₁ B₁ C₁ W₁ iW).toRingHom.toAlgebra
  let : IsScalarTower K₁ B₁ W₁ :=
    IsScalarTower.of_algHom (originalMiddleRightMap K₁ B₁ C₁ W₁ iW)
  let : Module.Flat (A₁ ⊗[K₁] B₁) ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁) := inferInstance
  let : Module.Flat B₁ (A₁ ⊗[K₁] B₁) := tensorAdjoin_flat K₁ A₁ B₁
  let : MonoidalCategoryStruct (ModuleCat.{max ku au bu cu vu wu mu} B₁) :=
    tensorStructure.{bu,max ku au bu cu vu wu mu}
  let : MonoidalCategoryStruct (ModuleCat.{max ku au bu cu vu wu mu} (A₁ ⊗[K₁] B₁)) :=
    tensorStructure.{max au bu,max ku au bu cu vu wu mu}
  let : MonoidalCategoryStruct (ModuleCat.{max ku au bu cu vu wu mu}
      ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁)) :=
    tensorStructure.{max au bu cu,max ku au bu cu vu wu mu}
  let : MonoidalCategory (ModuleCat.{max ku au bu cu vu wu mu} B₁) :=
    monoidalCategory.{bu,max ku au bu cu vu wu mu}
  let : MonoidalCategory (ModuleCat.{max ku au bu cu vu wu mu} (A₁ ⊗[K₁] B₁)) :=
    monoidalCategory.{max au bu,max ku au bu cu vu wu mu}
  let : MonoidalCategory (ModuleCat.{max ku au bu cu vu wu mu}
      ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁)) :=
    monoidalCategory.{max au bu cu,max ku au bu cu vu wu mu}
  let : MonoidalPreadditive (ModuleCat.{max ku au bu cu vu wu mu} B₁) :=
    monoidalPreadditive.{bu,max ku au bu cu vu wu mu}
  let : MonoidalPreadditive (ModuleCat.{max ku au bu cu vu wu mu} (A₁ ⊗[K₁] B₁)) :=
    monoidalPreadditive.{max au bu,max ku au bu cu vu wu mu}
  let : MonoidalPreadditive (ModuleCat.{max ku au bu cu vu wu mu}
      ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁)) :=
    monoidalPreadditive.{max au bu cu,max ku au bu cu vu wu mu}
  let S₀ := A₁ ⊗[K₁] B₁
  let S := S₀ ⊗[K₁] C₁
  let H₀ := restrictScalars.{max ku au bu cu vu wu mu,max au bu,max au bu cu} (algebraMap S₀ S)
  let H := restrictScalars.{max ku au bu cu vu wu mu,bu,max au bu} (algebraMap B₁ S₀)
  let F₀ := extendScalars.{max au bu,max au bu cu,max ku au bu cu vu wu mu} (algebraMap S₀ S)
  let F := extendScalars.{bu,max au bu,max ku au bu cu vu wu mu} (algebraMap B₁ S₀)
  let VR : ModuleCat.{max ku au bu cu vu wu mu} S₀ :=
    originalRingCoefficient.{max au bu,vu,max ku au bu cu vu wu mu} _ _ iV.toRingHom
  let VB : ModuleCat.{max ku au bu cu vu wu mu} B₁ :=
    originalRingCoefficient.{bu,vu,max ku au bu cu vu wu mu} _ _ (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom
  let WB : ModuleCat.{max ku au bu cu vu wu mu} B₁ :=
    originalRingCoefficient.{bu,wu,max ku au bu cu vu wu mu} _ _ (originalMiddleRightMap K₁ B₁ C₁ W₁ iW).toRingHom
  let LS : ModuleCat.{max ku au bu cu vu wu mu} S :=
    originalRingCoefficient.{max au bu cu,max vu cu,max ku au bu cu vu wu mu} _ _ (originalAmbientLeftMap K₁ A₁ B₁ C₁ V₁ iV).toRingHom
  let NS : ModuleCat.{max ku au bu cu vu wu mu} S :=
    originalRingCoefficient.{max au bu cu,max au wu,max ku au bu cu vu wu mu} _ _ (originalAmbientRightMap K₁ A₁ B₁ C₁ W₁ iW).toRingHom
  let eL : F₀.obj VR ≅ LS :=
    tensorAdjoinLeftCoefficientIso.{ku,max au bu,cu,vu,max wu mu} K₁ S₀ C₁ V₁
  let gf : S₀ →+* A₁ ⊗[K₁] W₁ :=
    (tensorAdjoinRightCoefficientMap K₁ A₁ B₁ W₁).toRingHom
  have hgf : gf = (originalAmbientRightMap K₁ A₁ B₁ C₁ W₁ iW).toRingHom.comp
      (algebraMap S₀ S) := by
    symm
    exact congrArg AlgHom.toRingHom
      (originalAmbientRightMap_comp_includeLeft K₁ A₁ B₁ C₁ W₁ iW)
  let rho : H₀.obj NS ≅ originalRingCoefficient.{max au bu,max au wu,max ku au bu cu vu wu mu}
      _ _ gf :=
    (restrictScalarsComp'App (algebraMap S₀ S)
      (originalAmbientRightMap K₁ A₁ B₁ C₁ W₁ iW).toRingHom gf hgf
        (ModuleCat.of (A₁ ⊗[K₁] W₁) (ULift.{max ku au bu cu vu wu mu} (A₁ ⊗[K₁] W₁)))).symm
  let eR : H₀.obj NS ≅ F.obj WB := rho ≪≫
    (tensorAdjoinRightCoefficientIso.{ku,au,bu,wu,max cu vu mu} K₁ A₁ B₁ W₁).symm
  let eV : H.obj VR ≅ VB :=
    (restrictScalarsComp'App (algebraMap B₁ S₀) iV.toRingHom
      (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom rfl
        (ModuleCat.of V₁ (ULift.{max ku au bu cu vu wu mu} V₁))).symm
  let T := Tor (ModuleCat.{max ku au bu cu vu wu mu} S) q
  let T₀ := Tor (ModuleCat.{max ku au bu cu vu wu mu} S₀) q
  let TB := Tor (ModuleCat.{max ku au bu cu vu wu mu} B₁) q
  let L := T.obj NS
  let μV : VR ⟶ VR := ModuleCat.ofHom (originalLiftedMulEnd.{max au bu,vu,max ku au bu cu vu wu mu} S₀ V₁ v)
  let μB : VB ⟶ VB := ModuleCat.ofHom (originalLiftedMulEnd.{bu,vu,max ku au bu cu vu wu mu} B₁ V₁ v)
  let μL : LS ⟶ LS := ModuleCat.ofHom (originalLiftedMulEnd.{max au bu cu,max vu cu,max ku au bu cu vu wu mu}
    S (V₁ ⊗[K₁] C₁) (v ⊗ₜ[K₁] (1 : C₁)))
  let A : H₀.obj (L.obj LS) ≅ H₀.obj (L.obj (F₀.obj VR)) := (H₀.mapIso (L.mapIso eL)).symm
  let B : H₀.obj (L.obj (F₀.obj VR)) ≅ (T₀.obj (H₀.obj NS)).obj VR :=
    flatScalarExtensionTorCancellationIso.{max au bu,max au bu cu,max ku au bu cu vu wu mu} S₀ S NS VR q
  let C : (T₀.obj (H₀.obj NS)).obj VR ≅ (T₀.obj (F.obj WB)).obj VR := (T₀.mapIso eR).app VR
  let D : (T₀.obj (F.obj WB)).obj VR ≅ (T₀.obj VR).obj (F.obj WB) :=
    nativeTorSymmetry.{max au bu,max ku au bu cu vu wu mu} S₀ (F.obj WB) VR q
  let E₅ : H.obj ((T₀.obj VR).obj (F.obj WB)) ≅ (TB.obj (H.obj VR)).obj WB :=
    flatScalarExtensionTorCancellationIso.{bu,max au bu,max ku au bu cu vu wu mu} B₁ S₀ VR WB q
  let E₆ : (TB.obj (H.obj VR)).obj WB ≅ (TB.obj VB).obj WB := (TB.mapIso eV).app WB
  let μ₀ : H₀.obj (L.obj LS) ⟶ H₀.obj (L.obj LS) := H₀.map (L.map μL)
  let μ₁ : H₀.obj (L.obj (F₀.obj VR)) ⟶ H₀.obj (L.obj (F₀.obj VR)) := H₀.map (L.map (F₀.map μV))
  let μ₂ : (T₀.obj (H₀.obj NS)).obj VR ⟶ (T₀.obj (H₀.obj NS)).obj VR := (T₀.obj (H₀.obj NS)).map μV
  let μ₃ : (T₀.obj (F.obj WB)).obj VR ⟶ (T₀.obj (F.obj WB)).obj VR := (T₀.obj (F.obj WB)).map μV
  let μ₄ : (T₀.obj VR).obj (F.obj WB) ⟶ (T₀.obj VR).obj (F.obj WB) := (T₀.map μV).app (F.obj WB)
  let μ₅ : (TB.obj (H.obj VR)).obj WB ⟶ (TB.obj (H.obj VR)).obj WB := (TB.map (H.map μV)).app WB
  let μ₆ : (TB.obj VB).obj WB ⟶ (TB.obj VB).obj WB := (TB.map μB).app WB
  have heL : F₀.map μV ≫ eL.hom = eL.hom ≫ μL :=
    tensorAdjoinLeftCoefficientIso_mul_hom_naturality.{ku,max au bu,cu,vu,max wu mu} K₁ S₀ C₁ V₁ v
  have hiL : μL ≫ eL.inv = eL.inv ≫ F₀.map μV := by
    have h := congrArg (fun k : F₀.obj VR ⟶ LS => eL.inv ≫ k ≫ eL.inv) heL
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using h.symm
  have hA : μ₀ ≫ A.hom = A.hom ≫ μ₁ := by
    have h := congrArg (fun k : LS ⟶ F₀.obj VR => H₀.map (L.map k)) hiL
    rw [L.map_comp μL eL.inv, L.map_comp eL.inv (F₀.map μV),
      H₀.map_comp (L.map μL) (L.map eL.inv), H₀.map_comp (L.map eL.inv) (L.map (F₀.map μV))] at h
    exact h
  have hB : μ₁ ≫ B.hom = B.hom ≫ μ₂ :=
    flatScalarExtensionTorCancellationIso_hom_naturality_resolved.{max au bu,max au bu cu,max ku au bu cu vu wu mu}
      S₀ S μV NS q
  have hC : μ₂ ≫ C.hom = C.hom ≫ μ₃ := (T₀.mapIso eR).hom.naturality μV
  have hD : μ₃ ≫ D.hom = D.hom ≫ μ₄ := by
    have h : ((T₀.map (𝟙 (F.obj WB))).app VR ≫ μ₃) ≫ D.hom =
        D.hom ≫ μ₄ ≫ (T₀.obj VR).map (𝟙 (F.obj WB)) :=
      nativeTorSymmetry_hom_naturality.{max au bu,max ku au bu cu vu wu mu} S₀ (𝟙 (F.obj WB)) μV q
    rw [T₀.map_id, NatTrans.id_app, (T₀.obj VR).map_id, Category.id_comp, Category.comp_id] at h
    exact h
  have hE : H.map μ₄ ≫ E₅.hom = E₅.hom ≫ μ₅ :=
    flatScalarExtensionTorCancellationIso_hom_naturality_coefficient.{bu,max au bu,max ku au bu cu vu wu mu}
      B₁ S₀ μV WB q
  have heV : H.map μV ≫ eV.hom = eV.hom ≫ μB := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  have hF : μ₅ ≫ E₆.hom = E₆.hom ≫ μ₆ := by
    let FB : ModuleCat.{max ku au bu cu vu wu mu} B₁ ⥤ ModuleCat.{max ku au bu cu vu wu mu} B₁ := (Functor.flip TB).obj WB
    have h := congrArg (fun k : H.obj VR ⟶ VB => FB.map k) heV
    rw [FB.map_comp (H.map μV) eV.hom, FB.map_comp eV.hom μB] at h
    exact h
  have hchain : μ₀ ≫ (A.hom ≫ B.hom ≫ C.hom ≫ D.hom) =
      (A.hom ≫ B.hom ≫ C.hom ≫ D.hom) ≫ μ₄ := by
    calc
      _ = A.hom ≫ μ₁ ≫ B.hom ≫ C.hom ≫ D.hom := by
        simpa only [Category.assoc] using congrArg (fun k => k ≫ B.hom ≫ C.hom ≫ D.hom) hA
      _ = A.hom ≫ B.hom ≫ μ₂ ≫ C.hom ≫ D.hom := by
        simpa only [Category.assoc] using congrArg (fun k => A.hom ≫ k ≫ C.hom ≫ D.hom) hB
      _ = A.hom ≫ B.hom ≫ C.hom ≫ μ₃ ≫ D.hom := by
        simpa only [Category.assoc] using congrArg (fun k => A.hom ≫ B.hom ≫ k ≫ D.hom) hC
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun k => A.hom ≫ B.hom ≫ C.hom ≫ k) hD
  have hH : H.map μ₀ ≫ H.map (A.hom ≫ B.hom ≫ C.hom ≫ D.hom) =
      H.map (A.hom ≫ B.hom ≫ C.hom ≫ D.hom) ≫ H.map μ₄ := by
    have h := congrArg (fun k => H.map k) hchain
    rw [H.map_comp μ₀ (A.hom ≫ B.hom ≫ C.hom ≫ D.hom),
      H.map_comp (A.hom ≫ B.hom ≫ C.hom ≫ D.hom) μ₄] at h
    exact h
  let E : H.obj (H₀.obj (L.obj LS)) ≅ (TB.obj VB).obj WB :=
    originalStandardAmbientTorIso.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q
  have h : H.map μ₀ ≫ E.hom = E.hom ≫ μ₆ := by
    change H.map μ₀ ≫ (H.map (A.hom ≫ B.hom ≫ C.hom ≫ D.hom) ≫ E₅.hom ≫ E₆.hom) =
      (H.map (A.hom ≫ B.hom ≫ C.hom ≫ D.hom) ≫ E₅.hom ≫ E₆.hom) ≫ μ₆
    calc
      _ = H.map (A.hom ≫ B.hom ≫ C.hom ≫ D.hom) ≫ H.map μ₄ ≫ E₅.hom ≫ E₆.hom := by
        simpa only [Category.assoc] using congrArg (fun k => k ≫ E₅.hom ≫ E₆.hom) hH
      _ = H.map (A.hom ≫ B.hom ≫ C.hom ≫ D.hom) ≫ E₅.hom ≫ μ₅ ≫ E₆.hom := by
        simpa only [Category.assoc] using congrArg
          (fun k => H.map (A.hom ≫ B.hom ≫ C.hom ≫ D.hom) ≫ k ≫ E₆.hom) hE
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun k => H.map (A.hom ≫ B.hom ≫ C.hom ≫ D.hom) ≫ E₅.hom ≫ k) hF
  change E.hom.hom ((H.map μ₀).hom z) = μ₆.hom (E.hom.hom z)
  exact congrArg (fun k : H.obj (H₀.obj (L.obj LS)) ⟶ (TB.obj VB).obj WB => k.hom z) h

/-- Both actual standard adjoining cancellations preserve original W
multiplication through the same genuine native Tor comparison. -/
theorem originalStandardAmbientTorIso_right_mul [Module.Flat K₁ A₁] [Module.Flat K₁ C₁]
    (q : ℕ) (w : W₁)
    (z : originalStandardAmbientTorModule.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q) :
    letI : Algebra B₁ V₁ := (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom.toAlgebra
    letI : Algebra B₁ W₁ := (originalMiddleRightMap K₁ B₁ C₁ W₁ iW).toRingHom.toAlgebra
    (originalStandardAmbientTorIso.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q).hom
        (originalStandardAmbientRightOperator.{ku,au,bu,cu,vu,wu,mu}
          K₁ A₁ B₁ C₁ V₁ W₁ iV iW q w z) =
      originalMiddleTorRightEndMap.{bu,vu,wu,max ku au cu mu} B₁ V₁ W₁ q w
        ((originalStandardAmbientTorIso.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q).hom z) := by
  let : Algebra B₁ V₁ := (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom.toAlgebra
  let : Algebra ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁) (A₁ ⊗[K₁] W₁) :=
    (originalAmbientRightMap K₁ A₁ B₁ C₁ W₁ iW).toRingHom.toAlgebra
  let : Algebra B₁ (A₁ ⊗[K₁] B₁) := Algebra.TensorProduct.rightAlgebra
  let : Algebra (A₁ ⊗[K₁] B₁) V₁ := iV.toRingHom.toAlgebra
  let : IsScalarTower K₁ (A₁ ⊗[K₁] B₁) V₁ := IsScalarTower.of_algHom iV
  let : Algebra B₁ W₁ := (originalMiddleRightMap K₁ B₁ C₁ W₁ iW).toRingHom.toAlgebra
  let : IsScalarTower K₁ B₁ W₁ :=
    IsScalarTower.of_algHom (originalMiddleRightMap K₁ B₁ C₁ W₁ iW)
  let : Module.Flat (A₁ ⊗[K₁] B₁) ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁) := inferInstance
  let : Module.Flat B₁ (A₁ ⊗[K₁] B₁) := tensorAdjoin_flat K₁ A₁ B₁
  let : MonoidalCategoryStruct (ModuleCat.{max ku au bu cu vu wu mu} B₁) :=
    tensorStructure.{bu,max ku au bu cu vu wu mu}
  let : MonoidalCategoryStruct (ModuleCat.{max ku au bu cu vu wu mu} (A₁ ⊗[K₁] B₁)) :=
    tensorStructure.{max au bu,max ku au bu cu vu wu mu}
  let : MonoidalCategoryStruct (ModuleCat.{max ku au bu cu vu wu mu}
      ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁)) :=
    tensorStructure.{max au bu cu,max ku au bu cu vu wu mu}
  let : MonoidalCategory (ModuleCat.{max ku au bu cu vu wu mu} B₁) :=
    monoidalCategory.{bu,max ku au bu cu vu wu mu}
  let : MonoidalCategory (ModuleCat.{max ku au bu cu vu wu mu} (A₁ ⊗[K₁] B₁)) :=
    monoidalCategory.{max au bu,max ku au bu cu vu wu mu}
  let : MonoidalCategory (ModuleCat.{max ku au bu cu vu wu mu}
      ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁)) :=
    monoidalCategory.{max au bu cu,max ku au bu cu vu wu mu}
  let : MonoidalPreadditive (ModuleCat.{max ku au bu cu vu wu mu} B₁) :=
    monoidalPreadditive.{bu,max ku au bu cu vu wu mu}
  let : MonoidalPreadditive (ModuleCat.{max ku au bu cu vu wu mu} (A₁ ⊗[K₁] B₁)) :=
    monoidalPreadditive.{max au bu,max ku au bu cu vu wu mu}
  let : MonoidalPreadditive (ModuleCat.{max ku au bu cu vu wu mu}
      ((A₁ ⊗[K₁] B₁) ⊗[K₁] C₁)) :=
    monoidalPreadditive.{max au bu cu,max ku au bu cu vu wu mu}
  let S₀ := A₁ ⊗[K₁] B₁
  let S := S₀ ⊗[K₁] C₁
  let H₀ := restrictScalars.{max ku au bu cu vu wu mu,max au bu,max au bu cu} (algebraMap S₀ S)
  let H := restrictScalars.{max ku au bu cu vu wu mu,bu,max au bu} (algebraMap B₁ S₀)
  let F₀ := extendScalars.{max au bu,max au bu cu,max ku au bu cu vu wu mu} (algebraMap S₀ S)
  let F := extendScalars.{bu,max au bu,max ku au bu cu vu wu mu} (algebraMap B₁ S₀)
  let VR : ModuleCat.{max ku au bu cu vu wu mu} S₀ :=
    originalRingCoefficient.{max au bu,vu,max ku au bu cu vu wu mu} _ _ iV.toRingHom
  let VB : ModuleCat.{max ku au bu cu vu wu mu} B₁ :=
    originalRingCoefficient.{bu,vu,max ku au bu cu vu wu mu} _ _ (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom
  let WB : ModuleCat.{max ku au bu cu vu wu mu} B₁ :=
    originalRingCoefficient.{bu,wu,max ku au bu cu vu wu mu} _ _ (originalMiddleRightMap K₁ B₁ C₁ W₁ iW).toRingHom
  let LS : ModuleCat.{max ku au bu cu vu wu mu} S :=
    originalRingCoefficient.{max au bu cu,max vu cu,max ku au bu cu vu wu mu} _ _ (originalAmbientLeftMap K₁ A₁ B₁ C₁ V₁ iV).toRingHom
  let NS : ModuleCat.{max ku au bu cu vu wu mu} S :=
    originalRingCoefficient.{max au bu cu,max au wu,max ku au bu cu vu wu mu} _ _ (originalAmbientRightMap K₁ A₁ B₁ C₁ W₁ iW).toRingHom
  let eL : F₀.obj VR ≅ LS :=
    tensorAdjoinLeftCoefficientIso.{ku,max au bu,cu,vu,max wu mu} K₁ S₀ C₁ V₁
  let gf : S₀ →+* A₁ ⊗[K₁] W₁ :=
    (tensorAdjoinRightCoefficientMap K₁ A₁ B₁ W₁).toRingHom
  have hgf : gf = (originalAmbientRightMap K₁ A₁ B₁ C₁ W₁ iW).toRingHom.comp
      (algebraMap S₀ S) := by
    symm
    exact congrArg AlgHom.toRingHom
      (originalAmbientRightMap_comp_includeLeft K₁ A₁ B₁ C₁ W₁ iW)
  let rho : H₀.obj NS ≅ originalRingCoefficient.{max au bu,max au wu,max ku au bu cu vu wu mu}
      _ _ gf :=
    (restrictScalarsComp'App (algebraMap S₀ S)
      (originalAmbientRightMap K₁ A₁ B₁ C₁ W₁ iW).toRingHom gf hgf
        (ModuleCat.of (A₁ ⊗[K₁] W₁) (ULift.{max ku au bu cu vu wu mu} (A₁ ⊗[K₁] W₁)))).symm
  let eR : H₀.obj NS ≅ F.obj WB := rho ≪≫
    (tensorAdjoinRightCoefficientIso.{ku,au,bu,wu,max cu vu mu} K₁ A₁ B₁ W₁).symm
  let eV : H.obj VR ≅ VB :=
    (restrictScalarsComp'App (algebraMap B₁ S₀) iV.toRingHom
      (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom rfl
        (ModuleCat.of V₁ (ULift.{max ku au bu cu vu wu mu} V₁))).symm
  let T := Tor (ModuleCat.{max ku au bu cu vu wu mu} S) q
  let T₀ := Tor (ModuleCat.{max ku au bu cu vu wu mu} S₀) q
  let TB := Tor (ModuleCat.{max ku au bu cu vu wu mu} B₁) q
  let L := T.obj NS
  let μW : WB ⟶ WB := ModuleCat.ofHom (originalLiftedMulEnd.{bu,wu,max ku au bu cu vu wu mu} B₁ W₁ w)
  let μN : NS ⟶ NS := ModuleCat.ofHom (originalLiftedMulEnd.{max au bu cu,max au wu,max ku au bu cu vu wu mu}
    S (A₁ ⊗[K₁] W₁) ((1 : A₁) ⊗ₜ[K₁] w))
  let A : H₀.obj (L.obj LS) ≅ H₀.obj (L.obj (F₀.obj VR)) := (H₀.mapIso (L.mapIso eL)).symm
  let B : H₀.obj (L.obj (F₀.obj VR)) ≅ (T₀.obj (H₀.obj NS)).obj VR :=
    flatScalarExtensionTorCancellationIso.{max au bu,max au bu cu,max ku au bu cu vu wu mu} S₀ S NS VR q
  let C : (T₀.obj (H₀.obj NS)).obj VR ≅ (T₀.obj (F.obj WB)).obj VR := (T₀.mapIso eR).app VR
  let D : (T₀.obj (F.obj WB)).obj VR ≅ (T₀.obj VR).obj (F.obj WB) :=
    nativeTorSymmetry.{max au bu,max ku au bu cu vu wu mu} S₀ (F.obj WB) VR q
  let E₅ : H.obj ((T₀.obj VR).obj (F.obj WB)) ≅ (TB.obj (H.obj VR)).obj WB :=
    flatScalarExtensionTorCancellationIso.{bu,max au bu,max ku au bu cu vu wu mu} B₁ S₀ VR WB q
  let E₆ : (TB.obj (H.obj VR)).obj WB ≅ (TB.obj VB).obj WB := (TB.mapIso eV).app WB
  let μ₀ : H₀.obj (L.obj LS) ⟶ H₀.obj (L.obj LS) := H₀.map ((T.map μN).app LS)
  let μ₁ : H₀.obj (L.obj (F₀.obj VR)) ⟶ H₀.obj (L.obj (F₀.obj VR)) := H₀.map ((T.map μN).app (F₀.obj VR))
  let μ₂ : (T₀.obj (H₀.obj NS)).obj VR ⟶ (T₀.obj (H₀.obj NS)).obj VR := (T₀.map (H₀.map μN)).app VR
  let μ₃ : (T₀.obj (F.obj WB)).obj VR ⟶ (T₀.obj (F.obj WB)).obj VR := (T₀.map (F.map μW)).app VR
  let μ₄ : (T₀.obj VR).obj (F.obj WB) ⟶ (T₀.obj VR).obj (F.obj WB) := (T₀.obj VR).map (F.map μW)
  let μ₅ : (TB.obj (H.obj VR)).obj WB ⟶ (TB.obj (H.obj VR)).obj WB := (TB.obj (H.obj VR)).map μW
  let μ₆ : (TB.obj VB).obj WB ⟶ (TB.obj VB).obj WB := (TB.obj VB).map μW
  have hA : μ₀ ≫ A.hom = A.hom ≫ μ₁ := by
    have h := congrArg (fun k : L.obj LS ⟶ L.obj (F₀.obj VR) => H₀.map k)
      ((T.map μN).naturality eL.inv).symm
    rw [H₀.map_comp ((T.map μN).app LS) (L.map eL.inv),
      H₀.map_comp (L.map eL.inv) ((T.map μN).app (F₀.obj VR))] at h
    exact h
  have hB : μ₁ ≫ B.hom = B.hom ≫ μ₂ :=
    flatScalarExtensionTorCancellationIso_hom_naturality_coefficient.{max au bu,max au bu cu,max ku au bu cu vu wu mu}
      S₀ S μN VR q
  let : Algebra S₀ (A₁ ⊗[K₁] W₁) := gf.toAlgebra
  let RR : ModuleCat.{max ku au bu cu vu wu mu} S₀ :=
    originalRingCoefficient.{max au bu,max au wu,max ku au bu cu vu wu mu} _ _ gf
  let ER : F.obj WB ≅ RR := tensorAdjoinRightCoefficientIso.{ku,au,bu,wu,max cu vu mu} K₁ A₁ B₁ W₁
  let μR : RR ⟶ RR := ModuleCat.ofHom
    (originalLiftedMulEnd.{max au bu,max au wu,max ku au bu cu vu wu mu} S₀ (A₁ ⊗[K₁] W₁) ((1 : A₁) ⊗ₜ[K₁] w))
  have heR : F.map μW ≫ ER.hom = ER.hom ≫ μR :=
    tensorAdjoinRightCoefficientIso_mul_hom_naturality.{ku,au,bu,wu,max cu vu mu} K₁ A₁ B₁ W₁ w
  have hiR : μR ≫ ER.inv = ER.inv ≫ F.map μW := by
    have h := congrArg (fun k : F.obj WB ⟶ RR => ER.inv ≫ k ≫ ER.inv) heR
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using h.symm
  have hrho : H₀.map μN ≫ rho.hom = rho.hom ≫ μR := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  have hER : H₀.map μN ≫ eR.hom = eR.hom ≫ F.map μW := by
    change H₀.map μN ≫ (rho.hom ≫ ER.inv) = (rho.hom ≫ ER.inv) ≫ F.map μW
    calc
      _ = rho.hom ≫ μR ≫ ER.inv := by
        simpa only [Category.assoc] using congrArg (fun k => k ≫ ER.inv) hrho
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun k => rho.hom ≫ k) hiR
  have hC : μ₂ ≫ C.hom = C.hom ≫ μ₃ := by
    let FC : ModuleCat.{max ku au bu cu vu wu mu} S₀ ⥤ ModuleCat.{max ku au bu cu vu wu mu} S₀ := (Functor.flip T₀).obj VR
    have h := congrArg (fun k : H₀.obj NS ⟶ F.obj WB => FC.map k) hER
    rw [FC.map_comp (H₀.map μN) eR.hom, FC.map_comp eR.hom (F.map μW)] at h
    exact h
  have hD : μ₃ ≫ D.hom = D.hom ≫ μ₄ := by
    have h : (μ₃ ≫ (T₀.obj (F.obj WB)).map (𝟙 VR)) ≫ D.hom =
        D.hom ≫ (T₀.map (𝟙 VR)).app (F.obj WB) ≫ μ₄ :=
      nativeTorSymmetry_hom_naturality.{max au bu,max ku au bu cu vu wu mu} S₀ (F.map μW) (𝟙 VR) q
    rw [(T₀.obj (F.obj WB)).map_id, T₀.map_id, NatTrans.id_app, Category.comp_id, Category.id_comp] at h
    exact h
  have hE : H.map μ₄ ≫ E₅.hom = E₅.hom ≫ μ₅ :=
    flatScalarExtensionTorCancellationIso_hom_naturality_resolved.{bu,max au bu,max ku au bu cu vu wu mu} B₁ S₀ μW VR q
  have hF : μ₅ ≫ E₆.hom = E₆.hom ≫ μ₆ := (TB.mapIso eV).hom.naturality μW
  have hchain : μ₀ ≫ (A.hom ≫ B.hom ≫ C.hom ≫ D.hom) =
      (A.hom ≫ B.hom ≫ C.hom ≫ D.hom) ≫ μ₄ := by
    calc
      _ = A.hom ≫ μ₁ ≫ B.hom ≫ C.hom ≫ D.hom := by
        simpa only [Category.assoc] using congrArg (fun k => k ≫ B.hom ≫ C.hom ≫ D.hom) hA
      _ = A.hom ≫ B.hom ≫ μ₂ ≫ C.hom ≫ D.hom := by
        simpa only [Category.assoc] using congrArg (fun k => A.hom ≫ k ≫ C.hom ≫ D.hom) hB
      _ = A.hom ≫ B.hom ≫ C.hom ≫ μ₃ ≫ D.hom := by
        simpa only [Category.assoc] using congrArg (fun k => A.hom ≫ B.hom ≫ k ≫ D.hom) hC
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun k => A.hom ≫ B.hom ≫ C.hom ≫ k) hD
  have hH : H.map μ₀ ≫ H.map (A.hom ≫ B.hom ≫ C.hom ≫ D.hom) =
      H.map (A.hom ≫ B.hom ≫ C.hom ≫ D.hom) ≫ H.map μ₄ := by
    have h := congrArg (fun k => H.map k) hchain
    rw [H.map_comp μ₀ (A.hom ≫ B.hom ≫ C.hom ≫ D.hom),
      H.map_comp (A.hom ≫ B.hom ≫ C.hom ≫ D.hom) μ₄] at h
    exact h
  let E : H.obj (H₀.obj (L.obj LS)) ≅ (TB.obj VB).obj WB :=
    originalStandardAmbientTorIso.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q
  have h : H.map μ₀ ≫ E.hom = E.hom ≫ μ₆ := by
    change H.map μ₀ ≫ (H.map (A.hom ≫ B.hom ≫ C.hom ≫ D.hom) ≫ E₅.hom ≫ E₆.hom) =
      (H.map (A.hom ≫ B.hom ≫ C.hom ≫ D.hom) ≫ E₅.hom ≫ E₆.hom) ≫ μ₆
    calc
      _ = H.map (A.hom ≫ B.hom ≫ C.hom ≫ D.hom) ≫ H.map μ₄ ≫ E₅.hom ≫ E₆.hom := by
        simpa only [Category.assoc] using congrArg (fun k => k ≫ E₅.hom ≫ E₆.hom) hH
      _ = H.map (A.hom ≫ B.hom ≫ C.hom ≫ D.hom) ≫ E₅.hom ≫ μ₅ ≫ E₆.hom := by
        simpa only [Category.assoc] using congrArg
          (fun k => H.map (A.hom ≫ B.hom ≫ C.hom ≫ D.hom) ≫ k ≫ E₆.hom) hE
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun k => H.map (A.hom ≫ B.hom ≫ C.hom ≫ D.hom) ≫ E₅.hom ≫ k) hF
  change E.hom.hom ((H.map μ₀).hom z) = μ₆.hom (E.hom.hom z)
  exact congrArg (fun k : H.obj (H₀.obj (L.obj LS)) ⟶ (TB.obj VB).obj WB => k.hom z) h

/-- The real original support algebra acts through the actual
comparison and its already derived native support representation. -/
def originalStandardAmbientTensorEndMap [Module.Flat K₁ A₁] [Module.Flat K₁ C₁] (q : ℕ) :
    letI : Algebra B₁ V₁ := (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom.toAlgebra
    letI : Algebra B₁ W₁ := (originalMiddleRightMap K₁ B₁ C₁ W₁ iW).toRingHom.toAlgebra
    (V₁ ⊗[B₁] W₁) →ₐ[B₁] Module.End B₁ (originalStandardAmbientTorModule.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q) := by
  letI : Algebra B₁ V₁ := (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom.toAlgebra
  letI : Algebra B₁ W₁ := (originalMiddleRightMap K₁ B₁ C₁ W₁ iW).toRingHom.toAlgebra
  let E : (originalStandardAmbientTorModule.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q) ≅ (originalMiddleTor.{bu,vu,wu,max ku au cu mu} B₁ V₁ W₁ q) := originalStandardAmbientTorIso.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q
  exact (E.symm.toLinearEquiv.conjAlgEquiv B₁).toAlgHom.comp (originalMiddleTorTensorEndMap.{bu,vu,wu,max ku au cu mu} B₁ V₁ W₁ q)

/-- The derived ambient support operator uses the literal original
forward and inverse comparison maps. -/
theorem originalStandardAmbientTensorEndMap_apply [Module.Flat K₁ A₁] [Module.Flat K₁ C₁] (q : ℕ) (t :
    letI : Algebra B₁ V₁ := (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom.toAlgebra
    letI : Algebra B₁ W₁ := (originalMiddleRightMap K₁ B₁ C₁ W₁ iW).toRingHom.toAlgebra
    (V₁ ⊗[B₁] W₁)) (z : originalStandardAmbientTorModule.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q) :
    letI : Algebra B₁ V₁ := (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom.toAlgebra
    letI : Algebra B₁ W₁ := (originalMiddleRightMap K₁ B₁ C₁ W₁ iW).toRingHom.toAlgebra
    originalStandardAmbientTensorEndMap.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q t z = (originalStandardAmbientTorIso.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q).inv
      (originalMiddleTorTensorEndMap.{bu,vu,wu,max ku au cu mu} B₁ V₁ W₁ q t ((originalStandardAmbientTorIso.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q).hom z)) := by
  rfl

/-- The real balanced original support action on this actual ambient
native Tor. Its factor operators are the literal original multiplication
maps proved compatible with the original native comparison above. -/
abbrev originalStandardAmbientTensorModule [Module.Flat K₁ A₁] [Module.Flat K₁ C₁] (q : ℕ) :
    letI : Algebra B₁ V₁ := (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom.toAlgebra
    letI : Algebra B₁ W₁ := (originalMiddleRightMap K₁ B₁ C₁ W₁ iW).toRingHom.toAlgebra
    Module (V₁ ⊗[B₁] W₁) (originalStandardAmbientTorModule.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q) := by
  letI : Algebra B₁ V₁ := (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom.toAlgebra
  letI : Algebra B₁ W₁ := (originalMiddleRightMap K₁ B₁ C₁ W₁ iW).toRingHom.toAlgebra
  letI : Module (V₁ ⊗[B₁] W₁) (originalMiddleTor.{bu,vu,wu,max ku au cu mu} B₁ V₁ W₁ q) := originalMiddleTorTensorModule.{bu,vu,wu,max ku au cu mu} B₁ V₁ W₁ q
  let E : (originalStandardAmbientTorModule.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q) ≅ (originalMiddleTor.{bu,vu,wu,max ku au cu mu} B₁ V₁ W₁ q) := originalStandardAmbientTorIso.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q
  exact E.toLinearEquiv.toAddEquiv.module (V₁ ⊗[B₁] W₁)

/-- The actual original ambient comparison is linear over the real
support algebra T = V ⊗[B] W, retaining every original native Tor degree. -/
def originalStandardAmbientTensorTorEquiv [Module.Flat K₁ A₁] [Module.Flat K₁ C₁] (q : ℕ) :
    letI : Algebra B₁ V₁ := (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom.toAlgebra
    letI : Algebra B₁ W₁ := (originalMiddleRightMap K₁ B₁ C₁ W₁ iW).toRingHom.toAlgebra
    letI : Module (V₁ ⊗[B₁] W₁) (originalStandardAmbientTorModule.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q) := originalStandardAmbientTensorModule.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q
    letI : Module (V₁ ⊗[B₁] W₁) (originalMiddleTor.{bu,vu,wu,max ku au cu mu} B₁ V₁ W₁ q) := originalMiddleTorTensorModule.{bu,vu,wu,max ku au cu mu} B₁ V₁ W₁ q
    (originalStandardAmbientTorModule.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q) ≃ₗ[(V₁ ⊗[B₁] W₁)] (originalMiddleTor.{bu,vu,wu,max ku au cu mu} B₁ V₁ W₁ q) := by
  let : Algebra B₁ V₁ := (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom.toAlgebra
  let : Algebra B₁ W₁ := (originalMiddleRightMap K₁ B₁ C₁ W₁ iW).toRingHom.toAlgebra
  let : Module (V₁ ⊗[B₁] W₁) (originalMiddleTor.{bu,vu,wu,max ku au cu mu} B₁ V₁ W₁ q) := originalMiddleTorTensorModule.{bu,vu,wu,max ku au cu mu} B₁ V₁ W₁ q
  let E : (originalStandardAmbientTorModule.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q) ≅ (originalMiddleTor.{bu,vu,wu,max ku au cu mu} B₁ V₁ W₁ q) := originalStandardAmbientTorIso.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q
  exact E.toLinearEquiv.toAddEquiv.linearEquiv (V₁ ⊗[B₁] W₁)

/-- The tensor-linear upgrade has exactly the original comparison map. -/
theorem originalStandardAmbientTensorTorEquiv_apply [Module.Flat K₁ A₁] [Module.Flat K₁ C₁] (q : ℕ) (z : originalStandardAmbientTorModule.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q) :
    letI : Algebra B₁ V₁ := (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom.toAlgebra
    letI : Algebra B₁ W₁ := (originalMiddleRightMap K₁ B₁ C₁ W₁ iW).toRingHom.toAlgebra
    (originalStandardAmbientTensorTorEquiv.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q) z = (originalStandardAmbientTorIso.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q).hom z := by
  rfl

/-- The inverse tensor-linear upgrade has exactly the original inverse
comparison map, with all original carrier coordinates retained. -/
theorem originalStandardAmbientTensorTorEquiv_symm_apply [Module.Flat K₁ A₁] [Module.Flat K₁ C₁] (q : ℕ) (z :
    letI : Algebra B₁ V₁ := (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom.toAlgebra
    letI : Algebra B₁ W₁ := (originalMiddleRightMap K₁ B₁ C₁ W₁ iW).toRingHom.toAlgebra
    originalMiddleTor.{bu,vu,wu,max ku au cu mu} B₁ V₁ W₁ q) :
    letI : Algebra B₁ V₁ := (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom.toAlgebra
    letI : Algebra B₁ W₁ := (originalMiddleRightMap K₁ B₁ C₁ W₁ iW).toRingHom.toAlgebra
    (originalStandardAmbientTensorTorEquiv.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q).symm z = (originalStandardAmbientTorIso.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q).inv z := by
  rfl
/-- Every pure original support tensor acts by the two genuine original
coefficient multiplication operators on the original ambient native Tor. -/
theorem originalStandardAmbientTensorModule_tmul [Module.Flat K₁ A₁] [Module.Flat K₁ C₁]
    (q : ℕ) (v : V₁) (w : W₁) (z : originalStandardAmbientTorModule.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q) :
    letI : Algebra B₁ V₁ := (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom.toAlgebra
    letI : Algebra B₁ W₁ := (originalMiddleRightMap K₁ B₁ C₁ W₁ iW).toRingHom.toAlgebra
    letI : Module (V₁ ⊗[B₁] W₁) (originalStandardAmbientTorModule.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q) := originalStandardAmbientTensorModule.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q
    (v ⊗ₜ[B₁] w) • z = originalStandardAmbientLeftOperator.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q v (originalStandardAmbientRightOperator.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q w z) := by
  let : Algebra B₁ V₁ := (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom.toAlgebra
  let : Algebra B₁ W₁ := (originalMiddleRightMap K₁ B₁ C₁ W₁ iW).toRingHom.toAlgebra
  let : Module (V₁ ⊗[B₁] W₁) (originalMiddleTor.{bu,vu,wu,max ku au cu mu} B₁ V₁ W₁ q) := originalMiddleTorTensorModule.{bu,vu,wu,max ku au cu mu} B₁ V₁ W₁ q
  let E : (originalStandardAmbientTorModule.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q) ≅ (originalMiddleTor.{bu,vu,wu,max ku au cu mu} B₁ V₁ W₁ q) := originalStandardAmbientTorIso.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q
  have hv := originalStandardAmbientTorIso_left_mul.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q v
    (originalStandardAmbientRightOperator.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q w z)
  have hw := originalStandardAmbientTorIso_right_mul.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q w z
  have hright := hv.trans (congrArg
    (fun y => originalMiddleTorLeftEndMap.{bu,vu,wu,max ku au cu mu} B₁ V₁ W₁ q v y) hw)
  have he := originalMiddleTorTensorModule_tmul.{bu,vu,wu,max ku au cu mu} B₁ V₁ W₁ q v w (E.hom z)
  exact transferredModule_smul_eq E.toLinearEquiv.toAddEquiv (v ⊗ₜ[B₁] w) z
    (originalStandardAmbientLeftOperator.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q v
      (originalStandardAmbientRightOperator.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q w z))
    (hright.trans he.symm)


/-- The original balanced endomorphism representation is exactly the
actual transported T action on standard ambient native Tor. -/
theorem originalStandardAmbientTensorEndMap_smul [Module.Flat K₁ A₁] [Module.Flat K₁ C₁]
    (q : ℕ) (t :
      letI : Algebra B₁ V₁ := (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom.toAlgebra
      letI : Algebra B₁ W₁ := (originalMiddleRightMap K₁ B₁ C₁ W₁ iW).toRingHom.toAlgebra
      V₁ ⊗[B₁] W₁)
    (z : originalStandardAmbientTorModule.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q) :
    letI : Algebra B₁ V₁ := (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom.toAlgebra
    letI : Algebra B₁ W₁ := (originalMiddleRightMap K₁ B₁ C₁ W₁ iW).toRingHom.toAlgebra
    letI : Module (V₁ ⊗[B₁] W₁) (originalStandardAmbientTorModule.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q) :=
      originalStandardAmbientTensorModule.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q
    originalStandardAmbientTensorEndMap.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q t z = t • z := by
  let : Algebra B₁ V₁ := (originalMiddleLeftMap K₁ A₁ B₁ V₁ iV).toRingHom.toAlgebra
  let : Algebra B₁ W₁ := (originalMiddleRightMap K₁ B₁ C₁ W₁ iW).toRingHom.toAlgebra
  let : Module (V₁ ⊗[B₁] W₁) (originalMiddleTor.{bu,vu,wu,max ku au cu mu} B₁ V₁ W₁ q) :=
    originalMiddleTorTensorModule.{bu,vu,wu,max ku au cu mu} B₁ V₁ W₁ q
  let : Module (V₁ ⊗[B₁] W₁) (originalStandardAmbientTorModule.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q) :=
    originalStandardAmbientTensorModule.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q
  let E : (originalStandardAmbientTorModule.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q) ≅
      (originalMiddleTor.{bu,vu,wu,max ku au cu mu} B₁ V₁ W₁ q) :=
    originalStandardAmbientTorIso.{ku,au,bu,cu,vu,wu,mu} K₁ A₁ B₁ C₁ V₁ W₁ iV iW q
  exact transferredEndMap_apply E.toLinearEquiv
    (originalMiddleTorTensorEndMap.{bu,vu,wu,max ku au cu mu} B₁ V₁ W₁ q)
    (fun t₀ z₀ => originalMiddleTorTensorEndMap_apply.{bu,vu,wu,max ku au cu mu} B₁ V₁ W₁ q t₀ z₀)
    t z


end OriginalAmbientAlgebras

section IntrinsicNativeComparison

universe jk jb jv jw jt

variable (K₆ : Type jk) (B₆ : Type jb) (V₆ : Type jv) (W₆ : Type jw)
  [CommRing K₆] [CommRing B₆] [CommRing V₆] [CommRing W₆]
  [Algebra K₆ B₆] [Algebra K₆ V₆] [Algebra K₆ W₆]
  (a : B₆ →ₐ[K₆] V₆) (b : B₆ →ₐ[K₆] W₆)

/-- The first intrinsic support map after the actual ambient rearrangement. -/
def intrinsicStandardLeftSupport : V₆ ⊗[K₆] B₆ →ₐ[K₆] V₆ :=
  Algebra.TensorProduct.etaleGraphEvaluation a

/-- The second intrinsic support map after the actual ambient rearrangement. -/
def intrinsicStandardRightSupport : B₆ ⊗[K₆] W₆ →ₐ[K₆] W₆ :=
  (Algebra.TensorProduct.etaleGraphEvaluation b).comp
    (Algebra.TensorProduct.comm K₆ B₆ W₆).toAlgHom

/-- The first graph evaluation is literally the rearranged original coefficient map. -/
theorem intrinsicGraphLeftEvaluation_comp_rearrangement :
    intrinsicGraphLeftEvaluation K₆ B₆ V₆ W₆ a =
      (originalAmbientLeftMap K₆ V₆ B₆ W₆ V₆
        (intrinsicStandardLeftSupport K₆ B₆ V₆ a)).comp
          (intrinsicToStandardAmbientEquiv K₆ B₆ V₆ W₆).toAlgHom := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [_root_.map_add, hx, hy]
  | tmul d b₀ =>
    induction d using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.add_tmul, _root_.map_add, hx, hy]
    | tmul v w =>
      change (v ⊗ₜ[K₆] w : V₆ ⊗[K₆] W₆) * (a b₀ ⊗ₜ[K₆] (1 : W₆)) =
        (v * a b₀) ⊗ₜ[K₆] w
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

/-- The second graph evaluation is literally the rearranged original coefficient map. -/
theorem intrinsicGraphRightEvaluation_comp_rearrangement :
    intrinsicGraphRightEvaluation K₆ B₆ V₆ W₆ b =
      (originalAmbientRightMap K₆ V₆ B₆ W₆ W₆
        (intrinsicStandardRightSupport K₆ B₆ W₆ b)).comp
          (intrinsicToStandardAmbientEquiv K₆ B₆ V₆ W₆).toAlgHom := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [_root_.map_add, hx, hy]
  | tmul d b₀ =>
    induction d using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.add_tmul, _root_.map_add, hx, hy]
    | tmul v w =>
      change (v ⊗ₜ[K₆] w : V₆ ⊗[K₆] W₆) * ((1 : V₆) ⊗ₜ[K₆] b b₀) =
        v ⊗ₜ[K₆] (w * b b₀)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

/-- The intrinsic rearrangement preserves the actual middle-ring inclusion. -/
theorem intrinsicToStandardAmbientEquiv_comp_includeRight :
    (intrinsicToStandardAmbientEquiv K₆ B₆ V₆ W₆).toAlgHom.comp
        (Algebra.TensorProduct.includeRight (R := K₆) (A := V₆ ⊗[K₆] W₆) (B := B₆)) =
      (Algebra.TensorProduct.includeLeft (R := K₆) (A := V₆ ⊗[K₆] B₆) (B := W₆)).comp
        (Algebra.TensorProduct.includeRight (R := K₆) (A := V₆) (B := B₆)) := by
  ext b₀
  change intrinsicToStandardAmbientEquiv K₆ B₆ V₆ W₆
    (((1 : V₆) ⊗ₜ[K₆] (1 : W₆)) ⊗ₜ[K₆] b₀) =
      ((1 : V₆) ⊗ₜ[K₆] b₀) ⊗ₜ[K₆] (1 : W₆)
  rfl

/-- The original first B support map is retained after both intrinsic cancellations. -/
theorem intrinsicStandardMiddleLeftMap :
    originalMiddleLeftMap K₆ V₆ B₆ V₆ (intrinsicStandardLeftSupport K₆ B₆ V₆ a) = a := by
  ext b₀
  change (1 : V₆) * a b₀ = a b₀
  exact one_mul _

/-- The original second B support map is retained after both intrinsic cancellations. -/
theorem intrinsicStandardMiddleRightMap :
    originalMiddleRightMap K₆ B₆ W₆ W₆ (intrinsicStandardRightSupport K₆ B₆ W₆ b) = b := by
  ext b₀
  change (1 : W₆) * b b₀ = b b₀
  exact one_mul _

/-- The actual original intrinsic native graph Tor is restricted
along its actual original B inclusion. -/
abbrev originalIntrinsicAmbientTorModule (q : ℕ) : ModuleCat.{max jk jb jv jw jt} B₆ := by
  letI : Algebra B₆ ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆) := Algebra.TensorProduct.rightAlgebra
  letI : MonoidalCategoryStruct (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆)) :=
    tensorStructure.{max jv jw jb,max jk jb jv jw jt}
  letI : MonoidalCategory (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆)) :=
    monoidalCategory.{max jv jw jb,max jk jb jv jw jt}
  letI : MonoidalPreadditive (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆)) :=
    monoidalPreadditive.{max jv jw jb,max jk jb jv jw jt}
  let G := (V₆ ⊗[K₆] W₆) ⊗[K₆] B₆
  let D := V₆ ⊗[K₆] W₆
  let HG := restrictScalars.{max jk jb jv jw jt,jb,max jv jw jb} (algebraMap B₆ G)
  let NG : ModuleCat.{max jk jb jv jw jt} G := originalRingCoefficient.{max jv jw jb,max jv jw,max jk jb jv jw jt}
    _ _ (intrinsicGraphRightEvaluation K₆ B₆ V₆ W₆ b).toRingHom
  let LG : ModuleCat.{max jk jb jv jw jt} G := originalRingCoefficient.{max jv jw jb,max jv jw,max jk jb jv jw jt}
    _ _ (intrinsicGraphLeftEvaluation K₆ B₆ V₆ W₆ a).toRingHom
  exact HG.obj (((Tor (ModuleCat.{max jk jb jv jw jt} G) q).obj NG).obj LG)

/-- Original V multiplication on the first intrinsic graph coefficient
induces this literal original native Tor endomorphism. -/
def originalIntrinsicAmbientLeftOperator (q : ℕ) (v : V₆) :
    Module.End B₆ (originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q) := by
  letI : Algebra B₆ ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆) := Algebra.TensorProduct.rightAlgebra
  letI : MonoidalCategoryStruct (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆)) :=
    tensorStructure.{max jv jw jb,max jk jb jv jw jt}
  letI : MonoidalCategory (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆)) :=
    monoidalCategory.{max jv jw jb,max jk jb jv jw jt}
  letI : MonoidalPreadditive (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆)) :=
    monoidalPreadditive.{max jv jw jb,max jk jb jv jw jt}
  let G := (V₆ ⊗[K₆] W₆) ⊗[K₆] B₆
  let D := V₆ ⊗[K₆] W₆
  let HG := restrictScalars.{max jk jb jv jw jt,jb,max jv jw jb} (algebraMap B₆ G)
  let NG : ModuleCat.{max jk jb jv jw jt} G := originalRingCoefficient.{max jv jw jb,max jv jw,max jk jb jv jw jt}
    _ _ (intrinsicGraphRightEvaluation K₆ B₆ V₆ W₆ b).toRingHom
  let LG : ModuleCat.{max jk jb jv jw jt} G := originalRingCoefficient.{max jv jw jb,max jv jw,max jk jb jv jw jt}
    _ _ (intrinsicGraphLeftEvaluation K₆ B₆ V₆ W₆ a).toRingHom
  let μ : LG ⟶ LG := ModuleCat.ofHom (X := LG) (Y := LG)
    (originalRingCoefficientMul.{max jv jw jb,max jv jw,max jk jb jv jw jt} G D
      (intrinsicGraphLeftEvaluation K₆ B₆ V₆ W₆ a).toRingHom (v ⊗ₜ[K₆] (1 : W₆)))
  exact (HG.map (((Tor (ModuleCat.{max jk jb jv jw jt} G) q).obj NG).map μ)).hom

/-- Original W multiplication on the second intrinsic graph coefficient
induces this literal original native Tor endomorphism. -/
def originalIntrinsicAmbientRightOperator (q : ℕ) (w : W₆) :
    Module.End B₆ (originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q) := by
  letI : Algebra B₆ ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆) := Algebra.TensorProduct.rightAlgebra
  letI : MonoidalCategoryStruct (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆)) :=
    tensorStructure.{max jv jw jb,max jk jb jv jw jt}
  letI : MonoidalCategory (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆)) :=
    monoidalCategory.{max jv jw jb,max jk jb jv jw jt}
  letI : MonoidalPreadditive (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆)) :=
    monoidalPreadditive.{max jv jw jb,max jk jb jv jw jt}
  let G := (V₆ ⊗[K₆] W₆) ⊗[K₆] B₆
  let D := V₆ ⊗[K₆] W₆
  let HG := restrictScalars.{max jk jb jv jw jt,jb,max jv jw jb} (algebraMap B₆ G)
  let NG : ModuleCat.{max jk jb jv jw jt} G := originalRingCoefficient.{max jv jw jb,max jv jw,max jk jb jv jw jt}
    _ _ (intrinsicGraphRightEvaluation K₆ B₆ V₆ W₆ b).toRingHom
  let LG : ModuleCat.{max jk jb jv jw jt} G := originalRingCoefficient.{max jv jw jb,max jv jw,max jk jb jv jw jt}
    _ _ (intrinsicGraphLeftEvaluation K₆ B₆ V₆ W₆ a).toRingHom
  let μ : NG ⟶ NG := ModuleCat.ofHom (X := NG) (Y := NG)
    (originalRingCoefficientMul.{max jv jw jb,max jv jw,max jk jb jv jw jt} G D
      (intrinsicGraphRightEvaluation K₆ B₆ V₆ W₆ b).toRingHom ((1 : V₆) ⊗ₜ[K₆] w))
  exact (HG.map (((Tor (ModuleCat.{max jk jb jv jw jt} G) q).map μ).app LG)).hom

/-- The actual intrinsic graph Tor is compared with the actual rearranged
standard ambient, keeping the original three rings, both graph evaluations,
and the original common coefficient universe. -/
def originalIntrinsicStandardTorIso (q : ℕ) :
    originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q ≅
      originalStandardAmbientTorModule.{jk,jv,jb,jw,jv,jw,jt} K₆ V₆ B₆ W₆ V₆ W₆
        (intrinsicStandardLeftSupport K₆ B₆ V₆ a)
        (intrinsicStandardRightSupport K₆ B₆ W₆ b) q := by
  letI : Algebra B₆ ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra B₆ (V₆ ⊗[K₆] B₆) := Algebra.TensorProduct.rightAlgebra
  letI : MonoidalCategoryStruct (ModuleCat.{max jk jb jv jw jt} B₆) :=
    tensorStructure.{jb,max jk jb jv jw jt}
  letI : MonoidalCategoryStruct (ModuleCat.{max jk jb jv jw jt} (V₆ ⊗[K₆] B₆)) :=
    tensorStructure.{max jv jb,max jk jb jv jw jt}
  letI : MonoidalCategoryStruct (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] B₆) ⊗[K₆] W₆)) :=
    tensorStructure.{max jv jb jw,max jk jb jv jw jt}
  letI : MonoidalCategoryStruct (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆)) :=
    tensorStructure.{max jv jw jb,max jk jb jv jw jt}
  letI : MonoidalCategory (ModuleCat.{max jk jb jv jw jt} B₆) :=
    monoidalCategory.{jb,max jk jb jv jw jt}
  letI : MonoidalCategory (ModuleCat.{max jk jb jv jw jt} (V₆ ⊗[K₆] B₆)) :=
    monoidalCategory.{max jv jb,max jk jb jv jw jt}
  letI : MonoidalCategory (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] B₆) ⊗[K₆] W₆)) :=
    monoidalCategory.{max jv jb jw,max jk jb jv jw jt}
  letI : MonoidalCategory (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆)) :=
    monoidalCategory.{max jv jw jb,max jk jb jv jw jt}
  letI : MonoidalPreadditive (ModuleCat.{max jk jb jv jw jt} B₆) :=
    monoidalPreadditive.{jb,max jk jb jv jw jt}
  letI : MonoidalPreadditive (ModuleCat.{max jk jb jv jw jt} (V₆ ⊗[K₆] B₆)) :=
    monoidalPreadditive.{max jv jb,max jk jb jv jw jt}
  letI : MonoidalPreadditive (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] B₆) ⊗[K₆] W₆)) :=
    monoidalPreadditive.{max jv jb jw,max jk jb jv jw jt}
  letI : MonoidalPreadditive (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆)) :=
    monoidalPreadditive.{max jv jw jb,max jk jb jv jw jt}
  let G := (V₆ ⊗[K₆] W₆) ⊗[K₆] B₆
  let S₀ := V₆ ⊗[K₆] B₆
  let S := S₀ ⊗[K₆] W₆
  let D := V₆ ⊗[K₆] W₆
  let e := intrinsicToStandardAmbientEquiv K₆ B₆ V₆ W₆
  let He := restrictScalars.{max jk jb jv jw jt,max jv jw jb,max jv jb jw} e.toRingHom
  let HG := restrictScalars.{max jk jb jv jw jt,jb,max jv jw jb} (algebraMap B₆ G)
  let H₀ := restrictScalars.{max jk jb jv jw jt,max jv jb,max jv jb jw} (algebraMap S₀ S)
  let H := restrictScalars.{max jk jb jv jw jt,jb,max jv jb} (algebraMap B₆ S₀)
  let iV := intrinsicStandardLeftSupport K₆ B₆ V₆ a
  let iW := intrinsicStandardRightSupport K₆ B₆ W₆ b
  let NS : ModuleCat.{max jk jb jv jw jt} S :=
    originalRingCoefficient.{max jv jb jw,max jv jw,max jk jb jv jw jt} _ _
      (originalAmbientRightMap K₆ V₆ B₆ W₆ W₆ iW).toRingHom
  let LS : ModuleCat.{max jk jb jv jw jt} S :=
    originalRingCoefficient.{max jv jb jw,max jv jw,max jk jb jv jw jt} _ _
      (originalAmbientLeftMap K₆ V₆ B₆ W₆ V₆ iV).toRingHom
  let NG : ModuleCat.{max jk jb jv jw jt} G :=
    originalRingCoefficient.{max jv jw jb,max jv jw,max jk jb jv jw jt} _ _
      (intrinsicGraphRightEvaluation K₆ B₆ V₆ W₆ b).toRingHom
  let LG : ModuleCat.{max jk jb jv jw jt} G :=
    originalRingCoefficient.{max jv jw jb,max jv jw,max jk jb jv jw jt} _ _
      (intrinsicGraphLeftEvaluation K₆ B₆ V₆ W₆ a).toRingHom
  let eN : NG ≅ He.obj NS :=
    restrictScalarsComp'App e.toRingHom
      (originalAmbientRightMap K₆ V₆ B₆ W₆ W₆ iW).toRingHom
      (intrinsicGraphRightEvaluation K₆ B₆ V₆ W₆ b).toRingHom
      (congrArg AlgHom.toRingHom (intrinsicGraphRightEvaluation_comp_rearrangement K₆ B₆ V₆ W₆ b))
      (ModuleCat.of D (ULift.{max jk jb jv jw jt} D))
  let eL : LG ≅ He.obj LS :=
    restrictScalarsComp'App e.toRingHom
      (originalAmbientLeftMap K₆ V₆ B₆ W₆ V₆ iV).toRingHom
      (intrinsicGraphLeftEvaluation K₆ B₆ V₆ W₆ a).toRingHom
      (congrArg AlgHom.toRingHom (intrinsicGraphLeftEvaluation_comp_rearrangement K₆ B₆ V₆ W₆ a))
      (ModuleCat.of D (ULift.{max jk jb jv jw jt} D))
  let Tₛ := ((Tor (ModuleCat.{max jk jb jv jw jt} S) q).obj NS).obj LS
  let ringComparison : He.obj Tₛ ≅
      ((Tor (ModuleCat.{max jk jb jv jw jt} G) q).obj (He.obj NS)).obj (He.obj LS) := by
    letI : Algebra G S := e.toRingHom.toAlgebra
    letI : Module.Flat G S := RingHom.Flat.of_bijective e.bijective
    let adj := extendRestrictScalarsAdj.{max jk jb jv jw jt,max jv jw jb,max jv jb jw} e.toRingHom
    letI : He.IsEquivalence := restrictScalars_isEquivalence_of_ringEquiv e.toRingEquiv
    let c : (extendScalars.{max jv jw jb,max jv jb jw,max jk jb jv jw jt} e.toRingHom).obj
        (He.obj LS) ≅ LS := asIso (adj.counit.app LS)
    exact (He.mapIso (((Tor (ModuleCat.{max jk jb jv jw jt} S) q).obj NS).mapIso c)).symm ≪≫
      flatScalarExtensionTorCancellationIso.{max jv jw jb,max jv jb jw,max jk jb jv jw jt}
        G S NS (He.obj LS) q
  let changeAmbient : ((Tor (ModuleCat.{max jk jb jv jw jt} G) q).obj NG).obj LG ≅ He.obj Tₛ :=
    ((Tor (ModuleCat.{max jk jb jv jw jt} G) q).mapIso eN).app LG ≪≫
      ((Tor (ModuleCat.{max jk jb jv jw jt} G) q).obj (He.obj NS)).mapIso eL ≪≫
        ringComparison.symm
  have hB : (algebraMap S₀ S).comp (algebraMap B₆ S₀) = e.toRingHom.comp (algebraMap B₆ G) := by
    symm
    exact congrArg AlgHom.toRingHom (intrinsicToStandardAmbientEquiv_comp_includeRight K₆ B₆ V₆ W₆)
  let rho : HG.obj (He.obj Tₛ) ≅ H.obj (H₀.obj Tₛ) :=
    (restrictScalarsComp'App (algebraMap B₆ G) e.toRingHom
      ((algebraMap S₀ S).comp (algebraMap B₆ S₀)) hB Tₛ).symm ≪≫
      restrictScalarsComp'App (algebraMap B₆ S₀) (algebraMap S₀ S)
        ((algebraMap S₀ S).comp (algebraMap B₆ S₀)) rfl Tₛ
  exact HG.mapIso changeAmbient ≪≫ rho


/-- The actual intrinsic graph rearrangement preserves original V
multiplication on the genuine resolved coefficient in every native degree. -/
theorem originalIntrinsicStandardTorIso_left_mul (q : ℕ) (v : V₆)
    (z : originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q) :
    (originalIntrinsicStandardTorIso.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q).hom
      (originalIntrinsicAmbientLeftOperator.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q v z) =
      originalStandardAmbientLeftOperator.{jk,jv,jb,jw,jv,jw,jt} K₆ V₆ B₆ W₆ V₆ W₆
        (intrinsicStandardLeftSupport K₆ B₆ V₆ a) (intrinsicStandardRightSupport K₆ B₆ W₆ b) q v
          ((originalIntrinsicStandardTorIso.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q).hom z) := by
  let : Algebra B₆ ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆) := Algebra.TensorProduct.rightAlgebra
  let : Algebra B₆ (V₆ ⊗[K₆] B₆) := Algebra.TensorProduct.rightAlgebra
  let : MonoidalCategoryStruct (ModuleCat.{max jk jb jv jw jt} B₆) :=
    tensorStructure.{jb,max jk jb jv jw jt}
  let : MonoidalCategoryStruct (ModuleCat.{max jk jb jv jw jt} (V₆ ⊗[K₆] B₆)) :=
    tensorStructure.{max jv jb,max jk jb jv jw jt}
  let : MonoidalCategoryStruct (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] B₆) ⊗[K₆] W₆)) :=
    tensorStructure.{max jv jb jw,max jk jb jv jw jt}
  let : MonoidalCategoryStruct (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆)) :=
    tensorStructure.{max jv jw jb,max jk jb jv jw jt}
  let : MonoidalCategory (ModuleCat.{max jk jb jv jw jt} B₆) :=
    monoidalCategory.{jb,max jk jb jv jw jt}
  let : MonoidalCategory (ModuleCat.{max jk jb jv jw jt} (V₆ ⊗[K₆] B₆)) :=
    monoidalCategory.{max jv jb,max jk jb jv jw jt}
  let : MonoidalCategory (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] B₆) ⊗[K₆] W₆)) :=
    monoidalCategory.{max jv jb jw,max jk jb jv jw jt}
  let : MonoidalCategory (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆)) :=
    monoidalCategory.{max jv jw jb,max jk jb jv jw jt}
  let : MonoidalPreadditive (ModuleCat.{max jk jb jv jw jt} B₆) :=
    monoidalPreadditive.{jb,max jk jb jv jw jt}
  let : MonoidalPreadditive (ModuleCat.{max jk jb jv jw jt} (V₆ ⊗[K₆] B₆)) :=
    monoidalPreadditive.{max jv jb,max jk jb jv jw jt}
  let : MonoidalPreadditive (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] B₆) ⊗[K₆] W₆)) :=
    monoidalPreadditive.{max jv jb jw,max jk jb jv jw jt}
  let : MonoidalPreadditive (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆)) :=
    monoidalPreadditive.{max jv jw jb,max jk jb jv jw jt}
  let G := (V₆ ⊗[K₆] W₆) ⊗[K₆] B₆
  let S₀ := V₆ ⊗[K₆] B₆
  let S := S₀ ⊗[K₆] W₆
  let D := V₆ ⊗[K₆] W₆
  let e := intrinsicToStandardAmbientEquiv K₆ B₆ V₆ W₆
  let He := restrictScalars.{max jk jb jv jw jt,max jv jw jb,max jv jb jw} e.toRingHom
  let HG := restrictScalars.{max jk jb jv jw jt,jb,max jv jw jb} (algebraMap B₆ G)
  let H₀ := restrictScalars.{max jk jb jv jw jt,max jv jb,max jv jb jw} (algebraMap S₀ S)
  let H := restrictScalars.{max jk jb jv jw jt,jb,max jv jb} (algebraMap B₆ S₀)
  let iV := intrinsicStandardLeftSupport K₆ B₆ V₆ a
  let iW := intrinsicStandardRightSupport K₆ B₆ W₆ b
  let NS : ModuleCat.{max jk jb jv jw jt} S :=
    originalRingCoefficient.{max jv jb jw,max jv jw,max jk jb jv jw jt} _ _
      (originalAmbientRightMap K₆ V₆ B₆ W₆ W₆ iW).toRingHom
  let LS : ModuleCat.{max jk jb jv jw jt} S :=
    originalRingCoefficient.{max jv jb jw,max jv jw,max jk jb jv jw jt} _ _
      (originalAmbientLeftMap K₆ V₆ B₆ W₆ V₆ iV).toRingHom
  let NG : ModuleCat.{max jk jb jv jw jt} G :=
    originalRingCoefficient.{max jv jw jb,max jv jw,max jk jb jv jw jt} _ _
      (intrinsicGraphRightEvaluation K₆ B₆ V₆ W₆ b).toRingHom
  let LG : ModuleCat.{max jk jb jv jw jt} G :=
    originalRingCoefficient.{max jv jw jb,max jv jw,max jk jb jv jw jt} _ _
      (intrinsicGraphLeftEvaluation K₆ B₆ V₆ W₆ a).toRingHom
  let eN : NG ≅ He.obj NS :=
    restrictScalarsComp'App e.toRingHom
      (originalAmbientRightMap K₆ V₆ B₆ W₆ W₆ iW).toRingHom
      (intrinsicGraphRightEvaluation K₆ B₆ V₆ W₆ b).toRingHom
      (congrArg AlgHom.toRingHom (intrinsicGraphRightEvaluation_comp_rearrangement K₆ B₆ V₆ W₆ b))
      (ModuleCat.of D (ULift.{max jk jb jv jw jt} D))
  let eL : LG ≅ He.obj LS :=
    restrictScalarsComp'App e.toRingHom
      (originalAmbientLeftMap K₆ V₆ B₆ W₆ V₆ iV).toRingHom
      (intrinsicGraphLeftEvaluation K₆ B₆ V₆ W₆ a).toRingHom
      (congrArg AlgHom.toRingHom (intrinsicGraphLeftEvaluation_comp_rearrangement K₆ B₆ V₆ W₆ a))
      (ModuleCat.of D (ULift.{max jk jb jv jw jt} D))
  let Tₛ := ((Tor (ModuleCat.{max jk jb jv jw jt} S) q).obj NS).obj LS
  let ringComparison : He.obj Tₛ ≅
      ((Tor (ModuleCat.{max jk jb jv jw jt} G) q).obj (He.obj NS)).obj (He.obj LS) := by
    let : Algebra G S := e.toRingHom.toAlgebra
    let : Module.Flat G S := RingHom.Flat.of_bijective e.bijective
    let adj := extendRestrictScalarsAdj.{max jk jb jv jw jt,max jv jw jb,max jv jb jw} e.toRingHom
    let : He.IsEquivalence := restrictScalars_isEquivalence_of_ringEquiv e.toRingEquiv
    let c : (extendScalars.{max jv jw jb,max jv jb jw,max jk jb jv jw jt} e.toRingHom).obj
        (He.obj LS) ≅ LS := asIso (adj.counit.app LS)
    exact (He.mapIso (((Tor (ModuleCat.{max jk jb jv jw jt} S) q).obj NS).mapIso c)).symm ≪≫
      flatScalarExtensionTorCancellationIso.{max jv jw jb,max jv jb jw,max jk jb jv jw jt}
        G S NS (He.obj LS) q
  let changeAmbient : ((Tor (ModuleCat.{max jk jb jv jw jt} G) q).obj NG).obj LG ≅ He.obj Tₛ :=
    ((Tor (ModuleCat.{max jk jb jv jw jt} G) q).mapIso eN).app LG ≪≫
      ((Tor (ModuleCat.{max jk jb jv jw jt} G) q).obj (He.obj NS)).mapIso eL ≪≫
        ringComparison.symm
  have hB : (algebraMap S₀ S).comp (algebraMap B₆ S₀) = e.toRingHom.comp (algebraMap B₆ G) := by
    symm
    exact congrArg AlgHom.toRingHom (intrinsicToStandardAmbientEquiv_comp_includeRight K₆ B₆ V₆ W₆)
  let rho : HG.obj (He.obj Tₛ) ≅ H.obj (H₀.obj Tₛ) :=
    (restrictScalarsComp'App (algebraMap B₆ G) e.toRingHom
      ((algebraMap S₀ S).comp (algebraMap B₆ S₀)) hB Tₛ).symm ≪≫
      restrictScalarsComp'App (algebraMap B₆ S₀) (algebraMap S₀ S)
        ((algebraMap S₀ S).comp (algebraMap B₆ S₀)) rfl Tₛ
  let : Algebra G S := e.toRingHom.toAlgebra
  let : Module.Flat G S := RingHom.Flat.of_bijective e.bijective
  let : He.IsEquivalence := restrictScalars_isEquivalence_of_ringEquiv e.toRingEquiv
  let Fe := extendScalars.{max jv jw jb,max jv jb jw,max jk jb jv jw jt} e.toRingHom
  let adj := extendRestrictScalarsAdj.{max jk jb jv jw jt,max jv jw jb,max jv jb jw} e.toRingHom
  let c : Fe.obj (He.obj LS) ≅ LS := asIso (adj.counit.app LS)
  let TG := Tor (ModuleCat.{max jk jb jv jw jt} G) q
  let TS := Tor (ModuleCat.{max jk jb jv jw jt} S) q
  let L := TS.obj NS
  let μG : LG ⟶ LG := ModuleCat.ofHom (X := LG) (Y := LG)
    (originalRingCoefficientMul.{max jv jw jb,max jv jw,max jk jb jv jw jt} G D
      (intrinsicGraphLeftEvaluation K₆ B₆ V₆ W₆ a).toRingHom (v ⊗ₜ[K₆] (1 : W₆)))
  let μS : LS ⟶ LS := ModuleCat.ofHom (X := LS) (Y := LS)
    (originalRingCoefficientMul.{max jv jb jw,max jv jw,max jk jb jv jw jt} S D
      (originalAmbientLeftMap K₆ V₆ B₆ W₆ V₆ iV).toRingHom (v ⊗ₜ[K₆] (1 : W₆)))
  let A : (TG.obj NG).obj LG ≅ (TG.obj (He.obj NS)).obj LG := (TG.mapIso eN).app LG
  let B : (TG.obj (He.obj NS)).obj LG ≅ (TG.obj (He.obj NS)).obj (He.obj LS) :=
    (TG.obj (He.obj NS)).mapIso eL
  let C : (TG.obj (He.obj NS)).obj (He.obj LS) ≅ He.obj (L.obj LS) := ringComparison.symm
  let P : He.obj (L.obj (Fe.obj (He.obj LS))) ≅ (TG.obj (He.obj NS)).obj (He.obj LS) :=
    flatScalarExtensionTorCancellationIso.{max jv jw jb,max jv jb jw,max jk jb jv jw jt} G S NS (He.obj LS) q
  let μ₀ : (TG.obj NG).obj LG ⟶ (TG.obj NG).obj LG := (TG.obj NG).map μG
  let μ₁ : (TG.obj (He.obj NS)).obj LG ⟶ (TG.obj (He.obj NS)).obj LG := (TG.obj (He.obj NS)).map μG
  let μ₂ : (TG.obj (He.obj NS)).obj (He.obj LS) ⟶ (TG.obj (He.obj NS)).obj (He.obj LS) :=
    (TG.obj (He.obj NS)).map (He.map μS)
  let μ₃ : He.obj (L.obj LS) ⟶ He.obj (L.obj LS) := He.map (L.map μS)
  let μP : He.obj (L.obj (Fe.obj (He.obj LS))) ⟶ He.obj (L.obj (Fe.obj (He.obj LS))) :=
    He.map (L.map (Fe.map (He.map μS)))
  let μB : H.obj (H₀.obj (L.obj LS)) ⟶ H.obj (H₀.obj (L.obj LS)) := H.map (H₀.map (L.map μS))
  have hA : μ₀ ≫ A.hom = A.hom ≫ μ₁ := (TG.mapIso eN).hom.naturality μG
  have heL : μG ≫ eL.hom = eL.hom ≫ He.map μS := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  have hB : μ₁ ≫ B.hom = B.hom ≫ μ₂ := by
    let F := TG.obj (He.obj NS)
    have h := congrArg (fun k : LG ⟶ He.obj LS => F.map k) heL
    rw [F.map_comp μG eL.hom, F.map_comp eL.hom (He.map μS)] at h
    exact h
  have hP : μ₂ ≫ P.inv = P.inv ≫ μP :=
    flatScalarExtensionTorCancellationIso_inv_naturality_resolved.{max jv jw jb,max jv jb jw,max jk jb jv jw jt}
      G S (He.map μS) NS q
  have hc : Fe.map (He.map μS) ≫ c.hom = c.hom ≫ μS := adj.counit.naturality μS
  have hC₂ : μP ≫ He.map (L.map c.hom) = He.map (L.map c.hom) ≫ μ₃ := by
    have h := congrArg (fun k : Fe.obj (He.obj LS) ⟶ LS => He.map (L.map k)) hc
    rw [L.map_comp (Fe.map (He.map μS)) c.hom, L.map_comp c.hom μS,
      He.map_comp (L.map (Fe.map (He.map μS))) (L.map c.hom), He.map_comp (L.map c.hom) (L.map μS)] at h
    exact h
  have hC : μ₂ ≫ C.hom = C.hom ≫ μ₃ := by
    change μ₂ ≫ (P.inv ≫ He.map (L.map c.hom)) = (P.inv ≫ He.map (L.map c.hom)) ≫ μ₃
    calc
      _ = P.inv ≫ μP ≫ He.map (L.map c.hom) := by
        simpa only [Category.assoc] using congrArg (fun k => k ≫ He.map (L.map c.hom)) hP
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun k => P.inv ≫ k) hC₂
  have hchain : μ₀ ≫ (A.hom ≫ B.hom ≫ C.hom) = (A.hom ≫ B.hom ≫ C.hom) ≫ μ₃ := by
    calc
      _ = A.hom ≫ μ₁ ≫ B.hom ≫ C.hom := by
        simpa only [Category.assoc] using congrArg (fun k => k ≫ B.hom ≫ C.hom) hA
      _ = A.hom ≫ B.hom ≫ μ₂ ≫ C.hom := by
        simpa only [Category.assoc] using congrArg (fun k => A.hom ≫ k ≫ C.hom) hB
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun k => A.hom ≫ B.hom ≫ k) hC
  have hHG : HG.map μ₀ ≫ HG.map (A.hom ≫ B.hom ≫ C.hom) =
      HG.map (A.hom ≫ B.hom ≫ C.hom) ≫ HG.map μ₃ := by
    have h := congrArg (fun k => HG.map k) hchain
    rw [HG.map_comp μ₀ (A.hom ≫ B.hom ≫ C.hom), HG.map_comp (A.hom ≫ B.hom ≫ C.hom) μ₃] at h
    exact h
  have hrho : HG.map μ₃ ≫ rho.hom = rho.hom ≫ μB := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  let E : HG.obj ((TG.obj NG).obj LG) ≅ H.obj (H₀.obj (L.obj LS)) :=
    originalIntrinsicStandardTorIso.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q
  have h : HG.map μ₀ ≫ E.hom = E.hom ≫ μB := by
    change HG.map μ₀ ≫ (HG.map (A.hom ≫ B.hom ≫ C.hom) ≫ rho.hom) =
      (HG.map (A.hom ≫ B.hom ≫ C.hom) ≫ rho.hom) ≫ μB
    calc
      _ = HG.map (A.hom ≫ B.hom ≫ C.hom) ≫ HG.map μ₃ ≫ rho.hom := by
        simpa only [Category.assoc] using congrArg (fun k => k ≫ rho.hom) hHG
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun k => HG.map (A.hom ≫ B.hom ≫ C.hom) ≫ k) hrho
  change E.hom.hom ((HG.map μ₀).hom z) = μB.hom (E.hom.hom z)
  exact congrArg (fun k : HG.obj ((TG.obj NG).obj LG) ⟶ H.obj (H₀.obj (L.obj LS)) => k.hom z) h


/-- The actual intrinsic graph rearrangement preserves original W
multiplication on the genuine original coefficient in every native degree. -/
theorem originalIntrinsicStandardTorIso_right_mul (q : ℕ) (w : W₆)
    (z : originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q) :
    (originalIntrinsicStandardTorIso.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q).hom
      (originalIntrinsicAmbientRightOperator.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q w z) =
      originalStandardAmbientRightOperator.{jk,jv,jb,jw,jv,jw,jt} K₆ V₆ B₆ W₆ V₆ W₆
        (intrinsicStandardLeftSupport K₆ B₆ V₆ a) (intrinsicStandardRightSupport K₆ B₆ W₆ b) q w
          ((originalIntrinsicStandardTorIso.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q).hom z) := by
  let : Algebra B₆ ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆) := Algebra.TensorProduct.rightAlgebra
  let : Algebra B₆ (V₆ ⊗[K₆] B₆) := Algebra.TensorProduct.rightAlgebra
  let : MonoidalCategoryStruct (ModuleCat.{max jk jb jv jw jt} B₆) :=
    tensorStructure.{jb,max jk jb jv jw jt}
  let : MonoidalCategoryStruct (ModuleCat.{max jk jb jv jw jt} (V₆ ⊗[K₆] B₆)) :=
    tensorStructure.{max jv jb,max jk jb jv jw jt}
  let : MonoidalCategoryStruct (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] B₆) ⊗[K₆] W₆)) :=
    tensorStructure.{max jv jb jw,max jk jb jv jw jt}
  let : MonoidalCategoryStruct (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆)) :=
    tensorStructure.{max jv jw jb,max jk jb jv jw jt}
  let : MonoidalCategory (ModuleCat.{max jk jb jv jw jt} B₆) :=
    monoidalCategory.{jb,max jk jb jv jw jt}
  let : MonoidalCategory (ModuleCat.{max jk jb jv jw jt} (V₆ ⊗[K₆] B₆)) :=
    monoidalCategory.{max jv jb,max jk jb jv jw jt}
  let : MonoidalCategory (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] B₆) ⊗[K₆] W₆)) :=
    monoidalCategory.{max jv jb jw,max jk jb jv jw jt}
  let : MonoidalCategory (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆)) :=
    monoidalCategory.{max jv jw jb,max jk jb jv jw jt}
  let : MonoidalPreadditive (ModuleCat.{max jk jb jv jw jt} B₆) :=
    monoidalPreadditive.{jb,max jk jb jv jw jt}
  let : MonoidalPreadditive (ModuleCat.{max jk jb jv jw jt} (V₆ ⊗[K₆] B₆)) :=
    monoidalPreadditive.{max jv jb,max jk jb jv jw jt}
  let : MonoidalPreadditive (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] B₆) ⊗[K₆] W₆)) :=
    monoidalPreadditive.{max jv jb jw,max jk jb jv jw jt}
  let : MonoidalPreadditive (ModuleCat.{max jk jb jv jw jt} ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆)) :=
    monoidalPreadditive.{max jv jw jb,max jk jb jv jw jt}
  let G := (V₆ ⊗[K₆] W₆) ⊗[K₆] B₆
  let S₀ := V₆ ⊗[K₆] B₆
  let S := S₀ ⊗[K₆] W₆
  let D := V₆ ⊗[K₆] W₆
  let e := intrinsicToStandardAmbientEquiv K₆ B₆ V₆ W₆
  let He := restrictScalars.{max jk jb jv jw jt,max jv jw jb,max jv jb jw} e.toRingHom
  let HG := restrictScalars.{max jk jb jv jw jt,jb,max jv jw jb} (algebraMap B₆ G)
  let H₀ := restrictScalars.{max jk jb jv jw jt,max jv jb,max jv jb jw} (algebraMap S₀ S)
  let H := restrictScalars.{max jk jb jv jw jt,jb,max jv jb} (algebraMap B₆ S₀)
  let iV := intrinsicStandardLeftSupport K₆ B₆ V₆ a
  let iW := intrinsicStandardRightSupport K₆ B₆ W₆ b
  let NS : ModuleCat.{max jk jb jv jw jt} S :=
    originalRingCoefficient.{max jv jb jw,max jv jw,max jk jb jv jw jt} _ _
      (originalAmbientRightMap K₆ V₆ B₆ W₆ W₆ iW).toRingHom
  let LS : ModuleCat.{max jk jb jv jw jt} S :=
    originalRingCoefficient.{max jv jb jw,max jv jw,max jk jb jv jw jt} _ _
      (originalAmbientLeftMap K₆ V₆ B₆ W₆ V₆ iV).toRingHom
  let NG : ModuleCat.{max jk jb jv jw jt} G :=
    originalRingCoefficient.{max jv jw jb,max jv jw,max jk jb jv jw jt} _ _
      (intrinsicGraphRightEvaluation K₆ B₆ V₆ W₆ b).toRingHom
  let LG : ModuleCat.{max jk jb jv jw jt} G :=
    originalRingCoefficient.{max jv jw jb,max jv jw,max jk jb jv jw jt} _ _
      (intrinsicGraphLeftEvaluation K₆ B₆ V₆ W₆ a).toRingHom
  let eN : NG ≅ He.obj NS :=
    restrictScalarsComp'App e.toRingHom
      (originalAmbientRightMap K₆ V₆ B₆ W₆ W₆ iW).toRingHom
      (intrinsicGraphRightEvaluation K₆ B₆ V₆ W₆ b).toRingHom
      (congrArg AlgHom.toRingHom (intrinsicGraphRightEvaluation_comp_rearrangement K₆ B₆ V₆ W₆ b))
      (ModuleCat.of D (ULift.{max jk jb jv jw jt} D))
  let eL : LG ≅ He.obj LS :=
    restrictScalarsComp'App e.toRingHom
      (originalAmbientLeftMap K₆ V₆ B₆ W₆ V₆ iV).toRingHom
      (intrinsicGraphLeftEvaluation K₆ B₆ V₆ W₆ a).toRingHom
      (congrArg AlgHom.toRingHom (intrinsicGraphLeftEvaluation_comp_rearrangement K₆ B₆ V₆ W₆ a))
      (ModuleCat.of D (ULift.{max jk jb jv jw jt} D))
  let Tₛ := ((Tor (ModuleCat.{max jk jb jv jw jt} S) q).obj NS).obj LS
  let ringComparison : He.obj Tₛ ≅
      ((Tor (ModuleCat.{max jk jb jv jw jt} G) q).obj (He.obj NS)).obj (He.obj LS) := by
    let : Algebra G S := e.toRingHom.toAlgebra
    let : Module.Flat G S := RingHom.Flat.of_bijective e.bijective
    let adj := extendRestrictScalarsAdj.{max jk jb jv jw jt,max jv jw jb,max jv jb jw} e.toRingHom
    let : He.IsEquivalence := restrictScalars_isEquivalence_of_ringEquiv e.toRingEquiv
    let c : (extendScalars.{max jv jw jb,max jv jb jw,max jk jb jv jw jt} e.toRingHom).obj
        (He.obj LS) ≅ LS := asIso (adj.counit.app LS)
    exact (He.mapIso (((Tor (ModuleCat.{max jk jb jv jw jt} S) q).obj NS).mapIso c)).symm ≪≫
      flatScalarExtensionTorCancellationIso.{max jv jw jb,max jv jb jw,max jk jb jv jw jt}
        G S NS (He.obj LS) q
  let changeAmbient : ((Tor (ModuleCat.{max jk jb jv jw jt} G) q).obj NG).obj LG ≅ He.obj Tₛ :=
    ((Tor (ModuleCat.{max jk jb jv jw jt} G) q).mapIso eN).app LG ≪≫
      ((Tor (ModuleCat.{max jk jb jv jw jt} G) q).obj (He.obj NS)).mapIso eL ≪≫
        ringComparison.symm
  have hB : (algebraMap S₀ S).comp (algebraMap B₆ S₀) = e.toRingHom.comp (algebraMap B₆ G) := by
    symm
    exact congrArg AlgHom.toRingHom (intrinsicToStandardAmbientEquiv_comp_includeRight K₆ B₆ V₆ W₆)
  let rho : HG.obj (He.obj Tₛ) ≅ H.obj (H₀.obj Tₛ) :=
    (restrictScalarsComp'App (algebraMap B₆ G) e.toRingHom
      ((algebraMap S₀ S).comp (algebraMap B₆ S₀)) hB Tₛ).symm ≪≫
      restrictScalarsComp'App (algebraMap B₆ S₀) (algebraMap S₀ S)
        ((algebraMap S₀ S).comp (algebraMap B₆ S₀)) rfl Tₛ
  let : Algebra G S := e.toRingHom.toAlgebra
  let : Module.Flat G S := RingHom.Flat.of_bijective e.bijective
  let : He.IsEquivalence := restrictScalars_isEquivalence_of_ringEquiv e.toRingEquiv
  let Fe := extendScalars.{max jv jw jb,max jv jb jw,max jk jb jv jw jt} e.toRingHom
  let adj := extendRestrictScalarsAdj.{max jk jb jv jw jt,max jv jw jb,max jv jb jw} e.toRingHom
  let c : Fe.obj (He.obj LS) ≅ LS := asIso (adj.counit.app LS)
  let TG := Tor (ModuleCat.{max jk jb jv jw jt} G) q
  let TS := Tor (ModuleCat.{max jk jb jv jw jt} S) q
  let L := TS.obj NS
  let μG : NG ⟶ NG := ModuleCat.ofHom (X := NG) (Y := NG)
    (originalRingCoefficientMul.{max jv jw jb,max jv jw,max jk jb jv jw jt} G D
      (intrinsicGraphRightEvaluation K₆ B₆ V₆ W₆ b).toRingHom ((1 : V₆) ⊗ₜ[K₆] w))
  let μS : NS ⟶ NS := ModuleCat.ofHom (X := NS) (Y := NS)
    (originalRingCoefficientMul.{max jv jb jw,max jv jw,max jk jb jv jw jt} S D
      (originalAmbientRightMap K₆ V₆ B₆ W₆ W₆ iW).toRingHom ((1 : V₆) ⊗ₜ[K₆] w))
  let A : (TG.obj NG).obj LG ≅ (TG.obj (He.obj NS)).obj LG := (TG.mapIso eN).app LG
  let B : (TG.obj (He.obj NS)).obj LG ≅ (TG.obj (He.obj NS)).obj (He.obj LS) :=
    (TG.obj (He.obj NS)).mapIso eL
  let C : (TG.obj (He.obj NS)).obj (He.obj LS) ≅ He.obj (L.obj LS) := ringComparison.symm
  let P : He.obj (L.obj (Fe.obj (He.obj LS))) ≅ (TG.obj (He.obj NS)).obj (He.obj LS) :=
    flatScalarExtensionTorCancellationIso.{max jv jw jb,max jv jb jw,max jk jb jv jw jt} G S NS (He.obj LS) q
  let μ₀ : (TG.obj NG).obj LG ⟶ (TG.obj NG).obj LG := (TG.map μG).app LG
  let μ₁ : (TG.obj (He.obj NS)).obj LG ⟶ (TG.obj (He.obj NS)).obj LG := (TG.map (He.map μS)).app LG
  let μ₂ : (TG.obj (He.obj NS)).obj (He.obj LS) ⟶ (TG.obj (He.obj NS)).obj (He.obj LS) :=
    (TG.map (He.map μS)).app (He.obj LS)
  let μ₃ : He.obj (L.obj LS) ⟶ He.obj (L.obj LS) := He.map ((TS.map μS).app LS)
  let μP : He.obj (L.obj (Fe.obj (He.obj LS))) ⟶ He.obj (L.obj (Fe.obj (He.obj LS))) :=
    He.map ((TS.map μS).app (Fe.obj (He.obj LS)))
  let μB : H.obj (H₀.obj (L.obj LS)) ⟶ H.obj (H₀.obj (L.obj LS)) := H.map (H₀.map ((TS.map μS).app LS))
  have heN : μG ≫ eN.hom = eN.hom ≫ He.map μS := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  have hA : μ₀ ≫ A.hom = A.hom ≫ μ₁ := by
    let F : ModuleCat.{max jk jb jv jw jt} G ⥤ ModuleCat.{max jk jb jv jw jt} G := (Functor.flip TG).obj LG
    have h := congrArg (fun k : NG ⟶ He.obj NS => F.map k) heN
    rw [F.map_comp μG eN.hom, F.map_comp eN.hom (He.map μS)] at h
    exact h
  have hB : μ₁ ≫ B.hom = B.hom ≫ μ₂ := ((TG.map (He.map μS)).naturality eL.hom).symm
  have hP : μ₂ ≫ P.inv = P.inv ≫ μP :=
    flatScalarExtensionTorCancellationIso_inv_naturality_coefficient.{max jv jw jb,max jv jb jw,max jk jb jv jw jt}
      G S μS (He.obj LS) q
  have hC₂ : μP ≫ He.map (L.map c.hom) = He.map (L.map c.hom) ≫ μ₃ := by
    have h := congrArg (fun k : L.obj (Fe.obj (He.obj LS)) ⟶ L.obj LS => He.map k)
      ((TS.map μS).naturality c.hom).symm
    rw [He.map_comp ((TS.map μS).app (Fe.obj (He.obj LS))) (L.map c.hom),
      He.map_comp (L.map c.hom) ((TS.map μS).app LS)] at h
    exact h
  have hC : μ₂ ≫ C.hom = C.hom ≫ μ₃ := by
    change μ₂ ≫ (P.inv ≫ He.map (L.map c.hom)) = (P.inv ≫ He.map (L.map c.hom)) ≫ μ₃
    calc
      _ = P.inv ≫ μP ≫ He.map (L.map c.hom) := by
        simpa only [Category.assoc] using congrArg (fun k => k ≫ He.map (L.map c.hom)) hP
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun k => P.inv ≫ k) hC₂
  have hchain : μ₀ ≫ (A.hom ≫ B.hom ≫ C.hom) = (A.hom ≫ B.hom ≫ C.hom) ≫ μ₃ := by
    calc
      _ = A.hom ≫ μ₁ ≫ B.hom ≫ C.hom := by
        simpa only [Category.assoc] using congrArg (fun k => k ≫ B.hom ≫ C.hom) hA
      _ = A.hom ≫ B.hom ≫ μ₂ ≫ C.hom := by
        simpa only [Category.assoc] using congrArg (fun k => A.hom ≫ k ≫ C.hom) hB
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun k => A.hom ≫ B.hom ≫ k) hC
  have hHG : HG.map μ₀ ≫ HG.map (A.hom ≫ B.hom ≫ C.hom) =
      HG.map (A.hom ≫ B.hom ≫ C.hom) ≫ HG.map μ₃ := by
    have h := congrArg (fun k => HG.map k) hchain
    rw [HG.map_comp μ₀ (A.hom ≫ B.hom ≫ C.hom), HG.map_comp (A.hom ≫ B.hom ≫ C.hom) μ₃] at h
    exact h
  have hrho : HG.map μ₃ ≫ rho.hom = rho.hom ≫ μB := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  let E : HG.obj ((TG.obj NG).obj LG) ≅ H.obj (H₀.obj (L.obj LS)) :=
    originalIntrinsicStandardTorIso.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q
  have h : HG.map μ₀ ≫ E.hom = E.hom ≫ μB := by
    change HG.map μ₀ ≫ (HG.map (A.hom ≫ B.hom ≫ C.hom) ≫ rho.hom) =
      (HG.map (A.hom ≫ B.hom ≫ C.hom) ≫ rho.hom) ≫ μB
    calc
      _ = HG.map (A.hom ≫ B.hom ≫ C.hom) ≫ HG.map μ₃ ≫ rho.hom := by
        simpa only [Category.assoc] using congrArg (fun k => k ≫ rho.hom) hHG
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun k => HG.map (A.hom ≫ B.hom ≫ C.hom) ≫ k) hrho
  change E.hom.hom ((HG.map μ₀).hom z) = μB.hom (E.hom.hom z)
  exact congrArg (fun k : HG.obj ((TG.obj NG).obj LG) ⟶ H.obj (H₀.obj (L.obj LS)) => k.hom z) h

/-- Both genuine intrinsic adjoining cancellations retain the original
intrinsic graph ambient and both actual graph evaluations, and reach the
same original ordered middle-ring native Tor in every degree. -/
def originalIntrinsicAmbientTorIso [Module.Flat K₆ V₆] [Module.Flat K₆ W₆] (q : ℕ) :
    letI : Algebra B₆ V₆ := a.toRingHom.toAlgebra
    letI : Algebra B₆ W₆ := b.toRingHom.toAlgebra
    (originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q) ≅
      (originalMiddleTor.{jb,jv,jw,max jk jt} B₆ V₆ W₆ q) := by
  letI : Algebra B₆ V₆ := a.toRingHom.toAlgebra
  letI : Algebra B₆ W₆ := b.toRingHom.toAlgebra
  letI : Algebra B₆ ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆) := Algebra.TensorProduct.rightAlgebra
  letI : MonoidalCategoryStruct (ModuleCat.{max jk jb jv jw jt} B₆) := tensorStructure.{jb,max jk jb jv jw jt}
  letI : MonoidalCategory (ModuleCat.{max jk jb jv jw jt} B₆) := monoidalCategory.{jb,max jk jb jv jw jt}
  letI : MonoidalPreadditive (ModuleCat.{max jk jb jv jw jt} B₆) := monoidalPreadditive.{jb,max jk jb jv jw jt}
  let iV := intrinsicStandardLeftSupport K₆ B₆ V₆ a
  let iW := intrinsicStandardRightSupport K₆ B₆ W₆ b
  let VB₀ := originalRingCoefficient.{jb,jv,max jk jb jv jw jt} _ _
    (originalMiddleLeftMap K₆ V₆ B₆ V₆ iV).toRingHom
  let WB₀ := originalRingCoefficient.{jb,jw,max jk jb jv jw jt} _ _
    (originalMiddleRightMap K₆ B₆ W₆ W₆ iW).toRingHom
  let VB := originalRingCoefficient.{jb,jv,max jk jb jv jw jt} _ _ a.toRingHom
  let WB := originalRingCoefficient.{jb,jw,max jk jb jv jw jt} _ _ b.toRingHom
  let eV : VB₀ ≅ VB := (restrictScalarsCongr
    (congrArg AlgHom.toRingHom (intrinsicStandardMiddleLeftMap K₆ B₆ V₆ a))).app
      (ModuleCat.of V₆ (ULift.{max jk jb jv jw jt} V₆))
  let eW : WB₀ ≅ WB := (restrictScalarsCongr
    (congrArg AlgHom.toRingHom (intrinsicStandardMiddleRightMap K₆ B₆ W₆ b))).app
      (ModuleCat.of W₆ (ULift.{max jk jb jv jw jt} W₆))
  let TB := Tor (ModuleCat.{max jk jb jv jw jt} B₆) q
  exact originalIntrinsicStandardTorIso.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q ≪≫
    originalStandardAmbientTorIso.{jk,jv,jb,jw,jv,jw,jt} K₆ V₆ B₆ W₆ V₆ W₆ iV iW q ≪≫
      (TB.mapIso eV).app WB₀ ≪≫ (TB.obj VB).mapIso eW

/-- The full original intrinsic comparison preserves actual V
multiplication through the rearrangement, both flat adjoining reductions,
and the original coefficient maps, in every native degree. -/
theorem originalIntrinsicAmbientTorIso_left_mul [Module.Flat K₆ V₆] [Module.Flat K₆ W₆]
    (q : ℕ) (v : V₆)
    (z : originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q) :
    letI : Algebra B₆ V₆ := a.toRingHom.toAlgebra
    letI : Algebra B₆ W₆ := b.toRingHom.toAlgebra
    (originalIntrinsicAmbientTorIso.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q).hom
      (originalIntrinsicAmbientLeftOperator.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q v z) =
      originalMiddleTorLeftEndMap.{jb,jv,jw,max jk jt} B₆ V₆ W₆ q v
        ((originalIntrinsicAmbientTorIso.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q).hom z) := by
  let : Algebra B₆ V₆ := a.toRingHom.toAlgebra
  let : Algebra B₆ W₆ := b.toRingHom.toAlgebra
  let : Algebra B₆ ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆) := Algebra.TensorProduct.rightAlgebra
  let : MonoidalCategoryStruct (ModuleCat.{max jk jb jv jw jt} B₆) := tensorStructure.{jb,max jk jb jv jw jt}
  let : MonoidalCategory (ModuleCat.{max jk jb jv jw jt} B₆) := monoidalCategory.{jb,max jk jb jv jw jt}
  let : MonoidalPreadditive (ModuleCat.{max jk jb jv jw jt} B₆) := monoidalPreadditive.{jb,max jk jb jv jw jt}
  let iV := intrinsicStandardLeftSupport K₆ B₆ V₆ a
  let iW := intrinsicStandardRightSupport K₆ B₆ W₆ b
  let VB₀ := originalRingCoefficient.{jb,jv,max jk jb jv jw jt} _ _
    (originalMiddleLeftMap K₆ V₆ B₆ V₆ iV).toRingHom
  let WB₀ := originalRingCoefficient.{jb,jw,max jk jb jv jw jt} _ _
    (originalMiddleRightMap K₆ B₆ W₆ W₆ iW).toRingHom
  let VB := originalRingCoefficient.{jb,jv,max jk jb jv jw jt} _ _ a.toRingHom
  let WB := originalRingCoefficient.{jb,jw,max jk jb jv jw jt} _ _ b.toRingHom
  let eV : VB₀ ≅ VB := (restrictScalarsCongr
    (congrArg AlgHom.toRingHom (intrinsicStandardMiddleLeftMap K₆ B₆ V₆ a))).app
      (ModuleCat.of V₆ (ULift.{max jk jb jv jw jt} V₆))
  let eW : WB₀ ≅ WB := (restrictScalarsCongr
    (congrArg AlgHom.toRingHom (intrinsicStandardMiddleRightMap K₆ B₆ W₆ b))).app
      (ModuleCat.of W₆ (ULift.{max jk jb jv jw jt} W₆))
  let TB := Tor (ModuleCat.{max jk jb jv jw jt} B₆) q
  let XG := originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q
  let XS := originalStandardAmbientTorModule.{jk,jv,jb,jw,jv,jw,jt} K₆ V₆ B₆ W₆ V₆ W₆ iV iW q
  let R : XG ≅ XS := originalIntrinsicStandardTorIso.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q
  let S : XS ≅ (TB.obj VB₀).obj WB₀ :=
    originalStandardAmbientTorIso.{jk,jv,jb,jw,jv,jw,jt} K₆ V₆ B₆ W₆ V₆ W₆ iV iW q
  let A : (TB.obj VB₀).obj WB₀ ≅ (TB.obj VB).obj WB₀ := (TB.mapIso eV).app WB₀
  let B : (TB.obj VB).obj WB₀ ≅ (TB.obj VB).obj WB := (TB.obj VB).mapIso eW
  let μG : XG ⟶ XG := ModuleCat.ofHom (X := XG) (Y := XG)
    (originalIntrinsicAmbientLeftOperator.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q v)
  let μS : XS ⟶ XS := ModuleCat.ofHom (X := XS) (Y := XS)
    (originalStandardAmbientLeftOperator.{jk,jv,jb,jw,jv,jw,jt} K₆ V₆ B₆ W₆ V₆ W₆ iV iW q v)
  let μ₀ : VB₀ ⟶ VB₀ := ModuleCat.ofHom (X := VB₀) (Y := VB₀)
    (originalRingCoefficientMul.{jb,jv,max jk jb jv jw jt} B₆ V₆
      (originalMiddleLeftMap K₆ V₆ B₆ V₆ iV).toRingHom v)
  let μ : VB ⟶ VB := ModuleCat.ofHom (X := VB) (Y := VB)
    (originalRingCoefficientMul.{jb,jv,max jk jb jv jw jt} B₆ V₆ a.toRingHom v)
  let μT₀ : (TB.obj VB₀).obj WB₀ ⟶ (TB.obj VB₀).obj WB₀ := (TB.map μ₀).app WB₀
  let μT₁ : (TB.obj VB).obj WB₀ ⟶ (TB.obj VB).obj WB₀ := (TB.map μ).app WB₀
  let μT : (TB.obj VB).obj WB ⟶ (TB.obj VB).obj WB := (TB.map μ).app WB
  have hR : μG ≫ R.hom = R.hom ≫ μS := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact originalIntrinsicStandardTorIso_left_mul.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q v x
  have hS : μS ≫ S.hom = S.hom ≫ μT₀ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact originalStandardAmbientTorIso_left_mul.{jk,jv,jb,jw,jv,jw,jt}
      K₆ V₆ B₆ W₆ V₆ W₆ iV iW q v x
  have heV : μ₀ ≫ eV.hom = eV.hom ≫ μ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  have hA : μT₀ ≫ A.hom = A.hom ≫ μT₁ := by
    let F : ModuleCat.{max jk jb jv jw jt} B₆ ⥤ ModuleCat.{max jk jb jv jw jt} B₆ := (Functor.flip TB).obj WB₀
    have h := congrArg (fun k : VB₀ ⟶ VB => F.map k) heV
    rw [F.map_comp μ₀ eV.hom, F.map_comp eV.hom μ] at h
    exact h
  have hB : μT₁ ≫ B.hom = B.hom ≫ μT := ((TB.map μ).naturality eW.hom).symm
  let E : XG ≅ (TB.obj VB).obj WB := originalIntrinsicAmbientTorIso.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q
  have h : μG ≫ E.hom = E.hom ≫ μT := by
    change μG ≫ (R.hom ≫ S.hom ≫ A.hom ≫ B.hom) = (R.hom ≫ S.hom ≫ A.hom ≫ B.hom) ≫ μT
    calc
      _ = R.hom ≫ μS ≫ S.hom ≫ A.hom ≫ B.hom := by
        simpa only [Category.assoc] using congrArg (fun k => k ≫ S.hom ≫ A.hom ≫ B.hom) hR
      _ = R.hom ≫ S.hom ≫ μT₀ ≫ A.hom ≫ B.hom := by
        simpa only [Category.assoc] using congrArg (fun k => R.hom ≫ k ≫ A.hom ≫ B.hom) hS
      _ = R.hom ≫ S.hom ≫ A.hom ≫ μT₁ ≫ B.hom := by
        simpa only [Category.assoc] using congrArg (fun k => R.hom ≫ S.hom ≫ k ≫ B.hom) hA
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun k => R.hom ≫ S.hom ≫ A.hom ≫ k) hB
  change E.hom.hom (μG.hom z) = μT.hom (E.hom.hom z)
  exact congrArg (fun k : XG ⟶ (TB.obj VB).obj WB => k.hom z) h

/-- The full original intrinsic comparison preserves actual W
multiplication through the rearrangement, both flat adjoining reductions,
and the original coefficient maps, in every native degree. -/
theorem originalIntrinsicAmbientTorIso_right_mul [Module.Flat K₆ V₆] [Module.Flat K₆ W₆]
    (q : ℕ) (w : W₆)
    (z : originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q) :
    letI : Algebra B₆ V₆ := a.toRingHom.toAlgebra
    letI : Algebra B₆ W₆ := b.toRingHom.toAlgebra
    (originalIntrinsicAmbientTorIso.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q).hom
      (originalIntrinsicAmbientRightOperator.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q w z) =
      originalMiddleTorRightEndMap.{jb,jv,jw,max jk jt} B₆ V₆ W₆ q w
        ((originalIntrinsicAmbientTorIso.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q).hom z) := by
  let : Algebra B₆ V₆ := a.toRingHom.toAlgebra
  let : Algebra B₆ W₆ := b.toRingHom.toAlgebra
  let : Algebra B₆ ((V₆ ⊗[K₆] W₆) ⊗[K₆] B₆) := Algebra.TensorProduct.rightAlgebra
  let : MonoidalCategoryStruct (ModuleCat.{max jk jb jv jw jt} B₆) := tensorStructure.{jb,max jk jb jv jw jt}
  let : MonoidalCategory (ModuleCat.{max jk jb jv jw jt} B₆) := monoidalCategory.{jb,max jk jb jv jw jt}
  let : MonoidalPreadditive (ModuleCat.{max jk jb jv jw jt} B₆) := monoidalPreadditive.{jb,max jk jb jv jw jt}
  let iV := intrinsicStandardLeftSupport K₆ B₆ V₆ a
  let iW := intrinsicStandardRightSupport K₆ B₆ W₆ b
  let VB₀ := originalRingCoefficient.{jb,jv,max jk jb jv jw jt} _ _
    (originalMiddleLeftMap K₆ V₆ B₆ V₆ iV).toRingHom
  let WB₀ := originalRingCoefficient.{jb,jw,max jk jb jv jw jt} _ _
    (originalMiddleRightMap K₆ B₆ W₆ W₆ iW).toRingHom
  let VB := originalRingCoefficient.{jb,jv,max jk jb jv jw jt} _ _ a.toRingHom
  let WB := originalRingCoefficient.{jb,jw,max jk jb jv jw jt} _ _ b.toRingHom
  let eV : VB₀ ≅ VB := (restrictScalarsCongr
    (congrArg AlgHom.toRingHom (intrinsicStandardMiddleLeftMap K₆ B₆ V₆ a))).app
      (ModuleCat.of V₆ (ULift.{max jk jb jv jw jt} V₆))
  let eW : WB₀ ≅ WB := (restrictScalarsCongr
    (congrArg AlgHom.toRingHom (intrinsicStandardMiddleRightMap K₆ B₆ W₆ b))).app
      (ModuleCat.of W₆ (ULift.{max jk jb jv jw jt} W₆))
  let TB := Tor (ModuleCat.{max jk jb jv jw jt} B₆) q
  let XG := originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q
  let XS := originalStandardAmbientTorModule.{jk,jv,jb,jw,jv,jw,jt} K₆ V₆ B₆ W₆ V₆ W₆ iV iW q
  let R : XG ≅ XS := originalIntrinsicStandardTorIso.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q
  let S : XS ≅ (TB.obj VB₀).obj WB₀ :=
    originalStandardAmbientTorIso.{jk,jv,jb,jw,jv,jw,jt} K₆ V₆ B₆ W₆ V₆ W₆ iV iW q
  let A : (TB.obj VB₀).obj WB₀ ≅ (TB.obj VB).obj WB₀ := (TB.mapIso eV).app WB₀
  let B : (TB.obj VB).obj WB₀ ≅ (TB.obj VB).obj WB := (TB.obj VB).mapIso eW
  let μG : XG ⟶ XG := ModuleCat.ofHom (X := XG) (Y := XG)
    (originalIntrinsicAmbientRightOperator.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q w)
  let μS : XS ⟶ XS := ModuleCat.ofHom (X := XS) (Y := XS)
    (originalStandardAmbientRightOperator.{jk,jv,jb,jw,jv,jw,jt} K₆ V₆ B₆ W₆ V₆ W₆ iV iW q w)
  let μ₀ : WB₀ ⟶ WB₀ := ModuleCat.ofHom (X := WB₀) (Y := WB₀)
    (originalRingCoefficientMul.{jb,jw,max jk jb jv jw jt} B₆ W₆
      (originalMiddleRightMap K₆ B₆ W₆ W₆ iW).toRingHom w)
  let μ : WB ⟶ WB := ModuleCat.ofHom (X := WB) (Y := WB)
    (originalRingCoefficientMul.{jb,jw,max jk jb jv jw jt} B₆ W₆ b.toRingHom w)
  let μT₀ : (TB.obj VB₀).obj WB₀ ⟶ (TB.obj VB₀).obj WB₀ := (TB.obj VB₀).map μ₀
  let μT₁ : (TB.obj VB).obj WB₀ ⟶ (TB.obj VB).obj WB₀ := (TB.obj VB).map μ₀
  let μT : (TB.obj VB).obj WB ⟶ (TB.obj VB).obj WB := (TB.obj VB).map μ
  have hR : μG ≫ R.hom = R.hom ≫ μS := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact originalIntrinsicStandardTorIso_right_mul.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q w x
  have hS : μS ≫ S.hom = S.hom ≫ μT₀ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact originalStandardAmbientTorIso_right_mul.{jk,jv,jb,jw,jv,jw,jt}
      K₆ V₆ B₆ W₆ V₆ W₆ iV iW q w x
  have hA : μT₀ ≫ A.hom = A.hom ≫ μT₁ := (TB.mapIso eV).hom.naturality μ₀
  have heW : μ₀ ≫ eW.hom = eW.hom ≫ μ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  have hB : μT₁ ≫ B.hom = B.hom ≫ μT := by
    let F := TB.obj VB
    have h := congrArg (fun k : WB₀ ⟶ WB => F.map k) heW
    rw [F.map_comp μ₀ eW.hom, F.map_comp eW.hom μ] at h
    exact h
  let E : XG ≅ (TB.obj VB).obj WB := originalIntrinsicAmbientTorIso.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q
  have h : μG ≫ E.hom = E.hom ≫ μT := by
    change μG ≫ (R.hom ≫ S.hom ≫ A.hom ≫ B.hom) = (R.hom ≫ S.hom ≫ A.hom ≫ B.hom) ≫ μT
    calc
      _ = R.hom ≫ μS ≫ S.hom ≫ A.hom ≫ B.hom := by
        simpa only [Category.assoc] using congrArg (fun k => k ≫ S.hom ≫ A.hom ≫ B.hom) hR
      _ = R.hom ≫ S.hom ≫ μT₀ ≫ A.hom ≫ B.hom := by
        simpa only [Category.assoc] using congrArg (fun k => R.hom ≫ k ≫ A.hom ≫ B.hom) hS
      _ = R.hom ≫ S.hom ≫ A.hom ≫ μT₁ ≫ B.hom := by
        simpa only [Category.assoc] using congrArg (fun k => R.hom ≫ S.hom ≫ k ≫ B.hom) hA
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun k => R.hom ≫ S.hom ≫ A.hom ≫ k) hB
  change E.hom.hom (μG.hom z) = μT.hom (E.hom.hom z)
  exact congrArg (fun k : XG ⟶ (TB.obj VB).obj WB => k.hom z) h

/-- The real original support algebra acts through the actual
comparison and its already derived native support representation. -/
def originalIntrinsicAmbientTensorEndMap [Module.Flat K₆ V₆] [Module.Flat K₆ W₆] (q : ℕ) :
    letI : Algebra B₆ V₆ := a.toRingHom.toAlgebra
    letI : Algebra B₆ W₆ := b.toRingHom.toAlgebra
    (V₆ ⊗[B₆] W₆) →ₐ[B₆] Module.End B₆ (originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q) := by
  letI : Algebra B₆ V₆ := a.toRingHom.toAlgebra
  letI : Algebra B₆ W₆ := b.toRingHom.toAlgebra
  let E : (originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q) ≅ (originalMiddleTor.{jb,jv,jw,max jk jt} B₆ V₆ W₆ q) := originalIntrinsicAmbientTorIso.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q
  exact (E.symm.toLinearEquiv.conjAlgEquiv B₆).toAlgHom.comp (originalMiddleTorTensorEndMap.{jb,jv,jw,max jk jt} B₆ V₆ W₆ q)

/-- The derived ambient support operator uses the literal original
forward and inverse comparison maps. -/
theorem originalIntrinsicAmbientTensorEndMap_apply [Module.Flat K₆ V₆] [Module.Flat K₆ W₆] (q : ℕ) (t :
    letI : Algebra B₆ V₆ := a.toRingHom.toAlgebra
    letI : Algebra B₆ W₆ := b.toRingHom.toAlgebra
    (V₆ ⊗[B₆] W₆)) (z : originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q) :
    letI : Algebra B₆ V₆ := a.toRingHom.toAlgebra
    letI : Algebra B₆ W₆ := b.toRingHom.toAlgebra
    originalIntrinsicAmbientTensorEndMap.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q t z = (originalIntrinsicAmbientTorIso.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q).inv
      (originalMiddleTorTensorEndMap.{jb,jv,jw,max jk jt} B₆ V₆ W₆ q t ((originalIntrinsicAmbientTorIso.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q).hom z)) := by
  rfl

/-- The actual intrinsic support action and comparison are constructed
together from the earned native comparison and the stock additive transport.
The action is derived from the genuine commuting middle-ring Tor operators. -/
def originalIntrinsicAmbientTensorTorData [Module.Flat K₆ V₆] [Module.Flat K₆ W₆]
    (q : ℕ) :
    letI : Algebra B₆ V₆ := a.toRingHom.toAlgebra
    letI : Algebra B₆ W₆ := b.toRingHom.toAlgebra
    letI : Module (V₆ ⊗[B₆] W₆) (originalMiddleTor.{jb,jv,jw,max jk jt} B₆ V₆ W₆ q) :=
      originalMiddleTorTensorModule.{jb,jv,jw,max jk jt} B₆ V₆ W₆ q
    Σ (action : Module (V₆ ⊗[B₆] W₆)
      (originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q)),
      letI := action
      (originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q) ≃ₗ[V₆ ⊗[B₆] W₆]
        (originalMiddleTor.{jb,jv,jw,max jk jt} B₆ V₆ W₆ q) := by
  letI : Algebra B₆ V₆ := a.toRingHom.toAlgebra
  letI : Algebra B₆ W₆ := b.toRingHom.toAlgebra
  letI : Module (V₆ ⊗[B₆] W₆) (originalMiddleTor.{jb,jv,jw,max jk jt} B₆ V₆ W₆ q) :=
    originalMiddleTorTensorModule.{jb,jv,jw,max jk jt} B₆ V₆ W₆ q
  let E : (originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q) ≅
      (originalMiddleTor.{jb,jv,jw,max jk jt} B₆ V₆ W₆ q) :=
    originalIntrinsicAmbientTorIso.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q
  let e : (originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q) ≃+
      (originalMiddleTor.{jb,jv,jw,max jk jt} B₆ V₆ W₆ q) := E.toLinearEquiv.toAddEquiv
  exact ⟨e.module (V₆ ⊗[B₆] W₆), e.linearEquiv (V₆ ⊗[B₆] W₆)⟩

/-- The real balanced original support action on this actual ambient
native Tor. Its factor operators are the literal original multiplication
maps proved compatible with the original native comparison above. -/
abbrev originalIntrinsicAmbientTensorModule [Module.Flat K₆ V₆] [Module.Flat K₆ W₆] (q : ℕ) :
    letI : Algebra B₆ V₆ := a.toRingHom.toAlgebra
    letI : Algebra B₆ W₆ := b.toRingHom.toAlgebra
    Module (V₆ ⊗[B₆] W₆) (originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q) := by
  letI : Algebra B₆ V₆ := a.toRingHom.toAlgebra
  letI : Algebra B₆ W₆ := b.toRingHom.toAlgebra
  exact (originalIntrinsicAmbientTensorTorData.{jk,jb,jv,jw,jt}
    K₆ B₆ V₆ W₆ a b q).1

/-- The actual original ambient comparison is linear over the real
support algebra T = V ⊗[B] W, retaining every original native Tor degree. -/
def originalIntrinsicAmbientTensorTorEquiv [Module.Flat K₆ V₆] [Module.Flat K₆ W₆] (q : ℕ) :
    letI : Algebra B₆ V₆ := a.toRingHom.toAlgebra
    letI : Algebra B₆ W₆ := b.toRingHom.toAlgebra
    letI : Module (V₆ ⊗[B₆] W₆) (originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q) := originalIntrinsicAmbientTensorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q
    letI : Module (V₆ ⊗[B₆] W₆) (originalMiddleTor.{jb,jv,jw,max jk jt} B₆ V₆ W₆ q) := originalMiddleTorTensorModule.{jb,jv,jw,max jk jt} B₆ V₆ W₆ q
    (originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q) ≃ₗ[(V₆ ⊗[B₆] W₆)] (originalMiddleTor.{jb,jv,jw,max jk jt} B₆ V₆ W₆ q) := by
  letI : Algebra B₆ V₆ := a.toRingHom.toAlgebra
  letI : Algebra B₆ W₆ := b.toRingHom.toAlgebra
  exact (originalIntrinsicAmbientTensorTorData.{jk,jb,jv,jw,jt}
    K₆ B₆ V₆ W₆ a b q).2

/-- The tensor-linear upgrade has exactly the original comparison map. -/
theorem originalIntrinsicAmbientTensorTorEquiv_apply [Module.Flat K₆ V₆] [Module.Flat K₆ W₆] (q : ℕ) (z : originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q) :
    letI : Algebra B₆ V₆ := a.toRingHom.toAlgebra
    letI : Algebra B₆ W₆ := b.toRingHom.toAlgebra
    (originalIntrinsicAmbientTensorTorEquiv.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q) z = (originalIntrinsicAmbientTorIso.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q).hom z := by
  rfl

/-- The inverse tensor-linear upgrade has exactly the original inverse
comparison map, with all original carrier coordinates retained. -/
theorem originalIntrinsicAmbientTensorTorEquiv_symm_apply [Module.Flat K₆ V₆] [Module.Flat K₆ W₆] (q : ℕ) (z :
    letI : Algebra B₆ V₆ := a.toRingHom.toAlgebra
    letI : Algebra B₆ W₆ := b.toRingHom.toAlgebra
    originalMiddleTor.{jb,jv,jw,max jk jt} B₆ V₆ W₆ q) :
    letI : Algebra B₆ V₆ := a.toRingHom.toAlgebra
    letI : Algebra B₆ W₆ := b.toRingHom.toAlgebra
    (originalIntrinsicAmbientTensorTorEquiv.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q).symm z = (originalIntrinsicAmbientTorIso.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q).inv z := by
  rfl
/-- Every pure original support tensor acts by the two genuine original
coefficient multiplication operators on the original ambient native Tor. -/
theorem originalIntrinsicAmbientTensorModule_tmul [Module.Flat K₆ V₆] [Module.Flat K₆ W₆]
    (q : ℕ) (v : V₆) (w : W₆) (z : originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q) :
    letI : Algebra B₆ V₆ := a.toRingHom.toAlgebra
    letI : Algebra B₆ W₆ := b.toRingHom.toAlgebra
    letI : Module (V₆ ⊗[B₆] W₆) (originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q) := originalIntrinsicAmbientTensorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q
    (v ⊗ₜ[B₆] w) • z = originalIntrinsicAmbientLeftOperator.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q v (originalIntrinsicAmbientRightOperator.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q w z) := by
  let : Algebra B₆ V₆ := a.toRingHom.toAlgebra
  let : Algebra B₆ W₆ := b.toRingHom.toAlgebra
  let : Module (V₆ ⊗[B₆] W₆) (originalMiddleTor.{jb,jv,jw,max jk jt} B₆ V₆ W₆ q) := originalMiddleTorTensorModule.{jb,jv,jw,max jk jt} B₆ V₆ W₆ q
  let E : (originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q) ≅ (originalMiddleTor.{jb,jv,jw,max jk jt} B₆ V₆ W₆ q) := originalIntrinsicAmbientTorIso.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q
  have hv := originalIntrinsicAmbientTorIso_left_mul.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q v
    (originalIntrinsicAmbientRightOperator.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q w z)
  have hw := originalIntrinsicAmbientTorIso_right_mul.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q w z
  have hright := hv.trans (congrArg
    (fun y => originalMiddleTorLeftEndMap.{jb,jv,jw,max jk jt} B₆ V₆ W₆ q v y) hw)
  have he := originalMiddleTorTensorModule_tmul.{jb,jv,jw,max jk jt} B₆ V₆ W₆ q v w (E.hom z)
  exact transferredModule_smul_eq E.toLinearEquiv.toAddEquiv (v ⊗ₜ[B₆] w) z
    (originalIntrinsicAmbientLeftOperator.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q v
      (originalIntrinsicAmbientRightOperator.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q w z))
    (hright.trans he.symm)


/-- Pure intrinsic support tensors act through the genuine original
coefficient multiplication maps in the endomorphism-valued representation. -/
theorem originalIntrinsicAmbientTensorEndMap_tmul [Module.Flat K₆ V₆] [Module.Flat K₆ W₆]
    (q : ℕ) (v : V₆) (w : W₆)
    (z : originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q) :
    letI : Algebra B₆ V₆ := a.toRingHom.toAlgebra
    letI : Algebra B₆ W₆ := b.toRingHom.toAlgebra
    originalIntrinsicAmbientTensorEndMap.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q (v ⊗ₜ[B₆] w) z =
      originalIntrinsicAmbientLeftOperator.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q v
        (originalIntrinsicAmbientRightOperator.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q w z) := by
  let : Algebra B₆ V₆ := a.toRingHom.toAlgebra
  let : Algebra B₆ W₆ := b.toRingHom.toAlgebra
  let E : (originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q) ≅
      (originalMiddleTor.{jb,jv,jw,max jk jt} B₆ V₆ W₆ q) :=
    originalIntrinsicAmbientTorIso.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q
  have hv := originalIntrinsicAmbientTorIso_left_mul.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q v
    (originalIntrinsicAmbientRightOperator.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q w z)
  have hw := originalIntrinsicAmbientTorIso_right_mul.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q w z
  have hvw := hv.trans (congrArg
    (fun x => originalMiddleTorLeftEndMap.{jb,jv,jw,max jk jt} B₆ V₆ W₆ q v x) hw)
  have ht := originalMiddleTorTensorEndMap_tmul.{jb,jv,jw,max jk jt} B₆ V₆ W₆ q v w (E.hom z)
  exact transferredConj_eq E.toLinearEquiv
    (originalMiddleTorTensorEndMap.{jb,jv,jw,max jk jt} B₆ V₆ W₆ q (v ⊗ₜ[B₆] w)) z
    (originalIntrinsicAmbientLeftOperator.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q v
      (originalIntrinsicAmbientRightOperator.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q w z))
    (hvw.trans ht.symm)

/-- The intrinsic balanced endomorphism representation is exactly the
actual stock-transported support action in every original native Tor degree. -/
theorem originalIntrinsicAmbientTensorEndMap_smul [Module.Flat K₆ V₆] [Module.Flat K₆ W₆]
    (q : ℕ) (t :
      letI : Algebra B₆ V₆ := a.toRingHom.toAlgebra
      letI : Algebra B₆ W₆ := b.toRingHom.toAlgebra
      V₆ ⊗[B₆] W₆)
    (z : originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q) :
    letI : Algebra B₆ V₆ := a.toRingHom.toAlgebra
    letI : Algebra B₆ W₆ := b.toRingHom.toAlgebra
    letI : Module (V₆ ⊗[B₆] W₆) (originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q) :=
      originalIntrinsicAmbientTensorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q
    originalIntrinsicAmbientTensorEndMap.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q t z = t • z := by
  let : Algebra B₆ V₆ := a.toRingHom.toAlgebra
  let : Algebra B₆ W₆ := b.toRingHom.toAlgebra
  let : Module (V₆ ⊗[B₆] W₆) (originalIntrinsicAmbientTorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q) :=
    originalIntrinsicAmbientTensorModule.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q
  induction t using TensorProduct.inductionOn with
  | tmul v w =>
    exact (originalIntrinsicAmbientTensorEndMap_tmul.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q v w z).trans
      (originalIntrinsicAmbientTensorModule_tmul.{jk,jb,jv,jw,jt} K₆ B₆ V₆ W₆ a b q v w z).symm
  | add t₁ t₂ h₁ h₂ => simp only [_root_.map_add, LinearMap.add_apply, add_smul, h₁, h₂]


end IntrinsicNativeComparison


section FieldNativeTensorComparison

universe fku fau fbu fcu fvu fwu fmu

variable (Kf : Type fku) (Af : Type fau) (Bf : Type fbu) (Cf : Type fcu)
  (Vf : Type fvu) (Wf : Type fwu)
  [Field Kf] [CommRing Af] [CommRing Bf] [CommRing Cf] [CommRing Vf] [CommRing Wf]
  [Algebra Kf Af] [Algebra Kf Bf] [Algebra Kf Cf] [Algebra Kf Vf] [Algebra Kf Wf]
  (iV : Af ⊗[Kf] Bf →ₐ[Kf] Vf) (iW : Bf ⊗[Kf] Cf →ₐ[Kf] Wf)

/-- Over any original field, standard and intrinsic ambient native Tor
are equivalent over the actual support algebra V ⊗[B] W, by their earned
comparisons with the same ordered Tor_B(V,W). All four adjoining factors
are flat over the original field; no B-flatness or finiteness is assumed.
The common module universe remains arbitrary and includes the actual
standard and intrinsic ambient ring universes. -/
def fieldTensorAmbientTorEquiv (q : ℕ) :
    letI : Algebra Bf Vf := (originalMiddleLeftMap Kf Af Bf Vf iV).toRingHom.toAlgebra
    letI : Algebra Bf Wf := (originalMiddleRightMap Kf Bf Cf Wf iW).toRingHom.toAlgebra
    letI : Module (Vf ⊗[Bf] Wf) (originalStandardAmbientTorModule.{fku,fau,fbu,fcu,fvu,fwu,fmu} Kf Af Bf Cf Vf Wf iV iW q) :=
      originalStandardAmbientTensorModule.{fku,fau,fbu,fcu,fvu,fwu,fmu} Kf Af Bf Cf Vf Wf iV iW q
    letI : Module (Vf ⊗[Bf] Wf) (originalIntrinsicAmbientTorModule.{fku,fbu,fvu,fwu,max fau fcu fmu} Kf Bf Vf Wf
      (originalMiddleLeftMap Kf Af Bf Vf iV) (originalMiddleRightMap Kf Bf Cf Wf iW) q) :=
      originalIntrinsicAmbientTensorModule.{fku,fbu,fvu,fwu,max fau fcu fmu} Kf Bf Vf Wf
        (originalMiddleLeftMap Kf Af Bf Vf iV) (originalMiddleRightMap Kf Bf Cf Wf iW) q
    (originalStandardAmbientTorModule.{fku,fau,fbu,fcu,fvu,fwu,fmu} Kf Af Bf Cf Vf Wf iV iW q) ≃ₗ[Vf ⊗[Bf] Wf]
      (originalIntrinsicAmbientTorModule.{fku,fbu,fvu,fwu,max fau fcu fmu} Kf Bf Vf Wf
        (originalMiddleLeftMap Kf Af Bf Vf iV) (originalMiddleRightMap Kf Bf Cf Wf iW) q) := by
  letI : Algebra Bf Vf := (originalMiddleLeftMap Kf Af Bf Vf iV).toRingHom.toAlgebra
  letI : Algebra Bf Wf := (originalMiddleRightMap Kf Bf Cf Wf iW).toRingHom.toAlgebra
  letI : Module (Vf ⊗[Bf] Wf) (originalStandardAmbientTorModule.{fku,fau,fbu,fcu,fvu,fwu,fmu} Kf Af Bf Cf Vf Wf iV iW q) :=
    originalStandardAmbientTensorModule.{fku,fau,fbu,fcu,fvu,fwu,fmu} Kf Af Bf Cf Vf Wf iV iW q
  letI : Module (Vf ⊗[Bf] Wf) (originalIntrinsicAmbientTorModule.{fku,fbu,fvu,fwu,max fau fcu fmu} Kf Bf Vf Wf
      (originalMiddleLeftMap Kf Af Bf Vf iV) (originalMiddleRightMap Kf Bf Cf Wf iW) q) :=
    originalIntrinsicAmbientTensorModule.{fku,fbu,fvu,fwu,max fau fcu fmu} Kf Bf Vf Wf
      (originalMiddleLeftMap Kf Af Bf Vf iV) (originalMiddleRightMap Kf Bf Cf Wf iW) q
  letI : Module (Vf ⊗[Bf] Wf) (originalMiddleTor.{fbu,fvu,fwu,max fku fau fcu fmu} Bf Vf Wf q) :=
    originalMiddleTorTensorModule.{fbu,fvu,fwu,max fku fau fcu fmu} Bf Vf Wf q
  let ES : (originalStandardAmbientTorModule.{fku,fau,fbu,fcu,fvu,fwu,fmu} Kf Af Bf Cf Vf Wf iV iW q) ≃ₗ[Vf ⊗[Bf] Wf]
      (originalMiddleTor.{fbu,fvu,fwu,max fku fau fcu fmu} Bf Vf Wf q) :=
    originalStandardAmbientTensorTorEquiv.{fku,fau,fbu,fcu,fvu,fwu,fmu} Kf Af Bf Cf Vf Wf iV iW q
  let EG : (originalIntrinsicAmbientTorModule.{fku,fbu,fvu,fwu,max fau fcu fmu} Kf Bf Vf Wf
      (originalMiddleLeftMap Kf Af Bf Vf iV) (originalMiddleRightMap Kf Bf Cf Wf iW) q) ≃ₗ[Vf ⊗[Bf] Wf]
      (originalMiddleTor.{fbu,fvu,fwu,max fku fau fcu fmu} Bf Vf Wf q) :=
    originalIntrinsicAmbientTensorTorEquiv.{fku,fbu,fvu,fwu,max fau fcu fmu} Kf Bf Vf Wf
      (originalMiddleLeftMap Kf Af Bf Vf iV) (originalMiddleRightMap Kf Bf Cf Wf iW) q
  exact ES.trans EG.symm

end FieldNativeTensorComparison

end ModuleCat.UniverseTensor
