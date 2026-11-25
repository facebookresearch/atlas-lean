/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.FieldTensorTorComparison
public import Mathlib.RingTheory.TensorProduct.Maps
public import MathlibExt.Algebra.Category.ModuleCat.LocalizationUnderSurjection
public import MathlibExt.Algebra.Category.ModuleCat.FlatScalarExtensionTorBaseChangeUniverse

/-!
# Native field-tensor Tor localization, support, and length

The original coefficient actions identify the actual native ambient actions
with restriction along the standard and intrinsic support maps. Genuine Tor
localization then compares native Tor over both ambient local rings with the
actual T-prime localization of ordered middle Tor. The standard comparison
requires surjective support maps. Lengths include infinity, and the finite
Euler statement retains explicit finite-length and eventual-zero hypotheses.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory
open scoped TensorProduct ModuleCat.UniverseTensor

namespace ModuleCat.UniverseTensor

universe k r v w
variable (K : Type k) (B : Type r) (V : Type v) (W : Type w)
  [CommRing K] [CommRing B] [CommRing V] [CommRing W]
  [Algebra K B] [Algebra K V] [Algebra K W]
  (a : B →ₐ[K] V) (b : B →ₐ[K] W)

/-- The stock scalar-balancing quotient from the original K tensor to the B tensor. -/
def balancedSupportMap :
    letI : Algebra B V := a.toRingHom.toAlgebra
    letI : Algebra B W := b.toRingHom.toAlgebra
    letI : IsScalarTower K B V := IsScalarTower.of_algHom a
    letI : IsScalarTower K B W := IsScalarTower.of_algHom b
    V ⊗[K] W →ₐ[K] V ⊗[B] W := by
  letI : Algebra B V := a.toRingHom.toAlgebra
  letI : Algebra B W := b.toRingHom.toAlgebra
  letI : IsScalarTower K B V := IsScalarTower.of_algHom a
  letI : IsScalarTower K B W := IsScalarTower.of_algHom b
  exact Algebra.TensorProduct.mapOfCompatibleSMul B K K V W

/-- The actual intrinsic graph ambient maps to its original tensor support quotient. -/
def intrinsicSupportMap :
    letI : Algebra B V := a.toRingHom.toAlgebra
    letI : Algebra B W := b.toRingHom.toAlgebra
    letI : IsScalarTower K B V := IsScalarTower.of_algHom a
    letI : IsScalarTower K B W := IsScalarTower.of_algHom b
    ((V ⊗[K] W) ⊗[K] B) →ₐ[K] V ⊗[B] W := by
  letI : Algebra B V := a.toRingHom.toAlgebra
  letI : Algebra B W := b.toRingHom.toAlgebra
  letI : IsScalarTower K B V := IsScalarTower.of_algHom a
  letI : IsScalarTower K B W := IsScalarTower.of_algHom b
  let q := balancedSupportMap K B V W a b
  exact Algebra.TensorProduct.lift q
    ((q.comp (Algebra.TensorProduct.includeLeft (R := K) (A := V) (B := W))).comp a)
    (fun _ _ => Commute.all _ _)

/-- The canonical intrinsic support map keeps both original factors and the middle scalar. -/
theorem intrinsicSupportMap_tmul (x : V) (y : W) (c : B) :
    letI : Algebra B V := a.toRingHom.toAlgebra
    letI : Algebra B W := b.toRingHom.toAlgebra
    letI : IsScalarTower K B V := IsScalarTower.of_algHom a
    letI : IsScalarTower K B W := IsScalarTower.of_algHom b
    intrinsicSupportMap K B V W a b ((x ⊗ₜ[K] y) ⊗ₜ[K] c) =
      (x * a c) ⊗ₜ[B] y := by
  let : Algebra B V := a.toRingHom.toAlgebra
  let : Algebra B W := b.toRingHom.toAlgebra
  let : IsScalarTower K B V := IsScalarTower.of_algHom a
  let : IsScalarTower K B W := IsScalarTower.of_algHom b
  change (x ⊗ₜ[B] y) * (a c ⊗ₜ[B] (1 : W)) = (x * a c) ⊗ₜ[B] y
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

/-- Every actual balanced support tensor has an intrinsic ambient preimage. -/
theorem intrinsicSupportMap_surjective :
    letI : Algebra B V := a.toRingHom.toAlgebra
    letI : Algebra B W := b.toRingHom.toAlgebra
    letI : IsScalarTower K B V := IsScalarTower.of_algHom a
    letI : IsScalarTower K B W := IsScalarTower.of_algHom b
    Function.Surjective (intrinsicSupportMap K B V W a b) := by
  let : Algebra B V := a.toRingHom.toAlgebra
  let : Algebra B W := b.toRingHom.toAlgebra
  let : IsScalarTower K B V := IsScalarTower.of_algHom a
  let : IsScalarTower K B W := IsScalarTower.of_algHom b
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    refine ⟨(x ⊗ₜ[K] y) ⊗ₜ[K] (1 : B), ?_⟩
    rw [intrinsicSupportMap_tmul, _root_.map_one, mul_one]
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨x, hx⟩ := h₁
    obtain ⟨y, hy⟩ := h₂
    exact ⟨x + y, by rw [_root_.map_add, hx, hy]⟩

section StandardAmbient

universe sa sc

variable (A : Type sa) (C : Type sc) [CommRing A] [CommRing C] [Algebra K A] [Algebra K C]
  (iV : A ⊗[K] B →ₐ[K] V) (iW : B ⊗[K] C →ₐ[K] W)

/-- The actual standard triple tensor ambient maps to the original balanced support tensor. -/
def standardSupportMap :
    letI : Algebra B V := (originalMiddleLeftMap K A B V iV).toRingHom.toAlgebra
    letI : Algebra B W := (originalMiddleRightMap K B C W iW).toRingHom.toAlgebra
    letI : IsScalarTower K B V := IsScalarTower.of_algHom (originalMiddleLeftMap K A B V iV)
    letI : IsScalarTower K B W := IsScalarTower.of_algHom (originalMiddleRightMap K B C W iW)
    ((A ⊗[K] B) ⊗[K] C) →ₐ[K] V ⊗[B] W := by
  letI : Algebra B V := (originalMiddleLeftMap K A B V iV).toRingHom.toAlgebra
  letI : Algebra B W := (originalMiddleRightMap K B C W iW).toRingHom.toAlgebra
  letI : IsScalarTower K B V := IsScalarTower.of_algHom (originalMiddleLeftMap K A B V iV)
  letI : IsScalarTower K B W := IsScalarTower.of_algHom (originalMiddleRightMap K B C W iW)
  let q := balancedSupportMap K B V W
    (originalMiddleLeftMap K A B V iV) (originalMiddleRightMap K B C W iW)
  exact q.comp (Algebra.TensorProduct.map iV
    (iW.comp (Algebra.TensorProduct.includeRight (R := K) (A := B) (B := C))))

/-- The original standard support map has its literal three-factor value. -/
theorem standardSupportMap_tmul (x : A) (y : B) (z : C) :
    letI : Algebra B V := (originalMiddleLeftMap K A B V iV).toRingHom.toAlgebra
    letI : Algebra B W := (originalMiddleRightMap K B C W iW).toRingHom.toAlgebra
    letI : IsScalarTower K B V := IsScalarTower.of_algHom (originalMiddleLeftMap K A B V iV)
    letI : IsScalarTower K B W := IsScalarTower.of_algHom (originalMiddleRightMap K B C W iW)
    standardSupportMap K B V W A C iV iW ((x ⊗ₜ[K] y) ⊗ₜ[K] z) =
      iV (x ⊗ₜ[K] y) ⊗ₜ[B] iW ((1 : B) ⊗ₜ[K] z) := by
  let : Algebra B V := (originalMiddleLeftMap K A B V iV).toRingHom.toAlgebra
  let : Algebra B W := (originalMiddleRightMap K B C W iW).toRingHom.toAlgebra
  let : IsScalarTower K B V := IsScalarTower.of_algHom (originalMiddleLeftMap K A B V iV)
  let : IsScalarTower K B W := IsScalarTower.of_algHom (originalMiddleRightMap K B C W iW)
  rfl

/-- Genuine quotient support maps give a surjective map from the original
standard tensor ambient, without coefficient flatness or finiteness. -/
theorem standardSupportMap_surjective
    (hV : Function.Surjective iV) (hW : Function.Surjective iW) :
    letI : Algebra B V := (originalMiddleLeftMap K A B V iV).toRingHom.toAlgebra
    letI : Algebra B W := (originalMiddleRightMap K B C W iW).toRingHom.toAlgebra
    letI : IsScalarTower K B V := IsScalarTower.of_algHom (originalMiddleLeftMap K A B V iV)
    letI : IsScalarTower K B W := IsScalarTower.of_algHom (originalMiddleRightMap K B C W iW)
    Function.Surjective (standardSupportMap K B V W A C iV iW) := by
  let : Algebra B V := (originalMiddleLeftMap K A B V iV).toRingHom.toAlgebra
  let : Algebra B W := (originalMiddleRightMap K B C W iW).toRingHom.toAlgebra
  let : IsScalarTower K B V := IsScalarTower.of_algHom (originalMiddleLeftMap K A B V iV)
  let : IsScalarTower K B W := IsScalarTower.of_algHom (originalMiddleRightMap K B C W iW)
  have liftPair (x : A ⊗[K] B) (y : B ⊗[K] C) :
      ∃ z, standardSupportMap K B V W A C iV iW z = iV x ⊗ₜ[B] iW y := by
    induction y using TensorProduct.inductionOn with
    | tmul d c =>
      refine ⟨(x * ((1 : A) ⊗ₜ[K] d)) ⊗ₜ[K] c, ?_⟩
      change iV (x * ((1 : A) ⊗ₜ[K] d)) ⊗ₜ[B] iW ((1 : B) ⊗ₜ[K] c) =
        iV x ⊗ₜ[B] iW (d ⊗ₜ[K] c)
      rw [_root_.map_mul]
      have hw : iW (d ⊗ₜ[K] c) = d • iW ((1 : B) ⊗ₜ[K] c) := by
        change iW (d ⊗ₜ[K] c) = iW (d ⊗ₜ[K] (1 : C)) * iW ((1 : B) ⊗ₜ[K] c)
        rw [← _root_.map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hw, mul_comm (iV x)]
      change (d • iV x) ⊗ₜ[B] iW ((1 : B) ⊗ₜ[K] c) = _
      exact TensorProduct.smul_tmul (R := B) d (iV x) (iW ((1 : B) ⊗ₜ[K] c))
    | add y₁ y₂ h₁ h₂ =>
      obtain ⟨z₁, hz₁⟩ := h₁
      obtain ⟨z₂, hz₂⟩ := h₂
      exact ⟨z₁ + z₂, by simp only [_root_.map_add, TensorProduct.tmul_add, hz₁, hz₂]⟩
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul v w =>
    obtain ⟨x, hx⟩ := hV v
    obtain ⟨y, hy⟩ := hW w
    simpa only [hx, hy] using liftPair x y
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨z₁, hz₁⟩ := h₁
    obtain ⟨z₂, hz₂⟩ := h₂
    exact ⟨z₁ + z₂, by rw [_root_.map_add, hz₁, hz₂]⟩

end StandardAmbient

section StandardNative

universe au cu mu

variable (A : Type au) (C : Type cu) [CommRing A] [CommRing C]
  [Algebra K A] [Algebra K C]
  (iV : A ⊗[K] B →ₐ[K] V) (iW : B ⊗[K] C →ₐ[K] W)

/-- The original standard Tor before restriction of its ambient scalars. -/
abbrev standardAmbientNativeTor (q : ℕ) :
    ModuleCat.{max k au r cu v w mu} ((A ⊗[K] B) ⊗[K] C) := by
  letI : MonoidalCategoryStruct
      (ModuleCat.{max k au r cu v w mu} ((A ⊗[K] B) ⊗[K] C)) :=
    tensorStructure.{max au r cu, max k au r cu v w mu}
  letI : MonoidalCategory
      (ModuleCat.{max k au r cu v w mu} ((A ⊗[K] B) ⊗[K] C)) :=
    monoidalCategory.{max au r cu, max k au r cu v w mu}
  letI : MonoidalPreadditive
      (ModuleCat.{max k au r cu v w mu} ((A ⊗[K] B) ⊗[K] C)) :=
    monoidalPreadditive.{max au r cu, max k au r cu v w mu}
  exact ((Tor (ModuleCat.{max k au r cu v w mu} ((A ⊗[K] B) ⊗[K] C)) q).obj
    (originalRingCoefficient.{max au r cu, max au w, max k au r cu v w mu} _ _
      (originalAmbientRightMap K A B C W iW).toRingHom)).obj
        (originalRingCoefficient.{max au r cu, max v cu, max k au r cu v w mu} _ _
          (originalAmbientLeftMap K A B C V iV).toRingHom)

/-- Resolved coefficient multiplication by `iV x` is multiplication by
the actual ambient scalar `x ⊗ 1` on the original native Tor. -/
theorem standardAmbientLeftOperator_scalar (q : ℕ) (x : A ⊗[K] B)
    (z : standardAmbientNativeTor.{k, r, v, w, au, cu, mu} K B V W A C iV iW q) :
    originalStandardAmbientLeftOperator.{k, au, r, cu, v, w, mu}
      K A B C V W iV iW q (iV x) z = (x ⊗ₜ[K] (1 : C)) • z := by
  let : Algebra B (A ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
  let : Algebra ((A ⊗[K] B) ⊗[K] C) (V ⊗[K] C) :=
    (originalAmbientLeftMap K A B C V iV).toRingHom.toAlgebra
  let : MonoidalCategoryStruct
      (ModuleCat.{max k au r cu v w mu} ((A ⊗[K] B) ⊗[K] C)) :=
    tensorStructure.{max au r cu, max k au r cu v w mu}
  let : MonoidalCategory
      (ModuleCat.{max k au r cu v w mu} ((A ⊗[K] B) ⊗[K] C)) :=
    monoidalCategory.{max au r cu, max k au r cu v w mu}
  let : MonoidalPreadditive
      (ModuleCat.{max k au r cu v w mu} ((A ⊗[K] B) ⊗[K] C)) :=
    monoidalPreadditive.{max au r cu, max k au r cu v w mu}
  let NS := originalRingCoefficient.{max au r cu, max au w, max k au r cu v w mu} _ _
    (originalAmbientRightMap K A B C W iW).toRingHom
  let LS := originalRingCoefficient.{max au r cu, max v cu, max k au r cu v w mu} _ _
    (originalAmbientLeftMap K A B C V iV).toRingHom
  exact congrArg (fun e => e z)
    ((nativeTorSecondEndAlgHom.{max au r cu, max k au r cu v w mu}
      ((A ⊗[K] B) ⊗[K] C) NS LS q).commutes (x ⊗ₜ[K] (1 : C)))

/-- First coefficient multiplication by `iW (1 ⊗ c)` is multiplication
by the actual ambient scalar `1 ⊗ c` on the original native Tor. -/
theorem standardAmbientRightOperator_scalar (q : ℕ) (c : C)
    (z : standardAmbientNativeTor.{k, r, v, w, au, cu, mu} K B V W A C iV iW q) :
    originalStandardAmbientRightOperator.{k, au, r, cu, v, w, mu}
      K A B C V W iV iW q (iW ((1 : B) ⊗ₜ[K] c)) z =
        ((1 : A ⊗[K] B) ⊗ₜ[K] c) • z := by
  let : Algebra B (A ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
  let : Algebra ((A ⊗[K] B) ⊗[K] C) (A ⊗[K] W) :=
    (originalAmbientRightMap K A B C W iW).toRingHom.toAlgebra
  let : MonoidalCategoryStruct
      (ModuleCat.{max k au r cu v w mu} ((A ⊗[K] B) ⊗[K] C)) :=
    tensorStructure.{max au r cu, max k au r cu v w mu}
  let : MonoidalCategory
      (ModuleCat.{max k au r cu v w mu} ((A ⊗[K] B) ⊗[K] C)) :=
    monoidalCategory.{max au r cu, max k au r cu v w mu}
  let : MonoidalPreadditive
      (ModuleCat.{max k au r cu v w mu} ((A ⊗[K] B) ⊗[K] C)) :=
    monoidalPreadditive.{max au r cu, max k au r cu v w mu}
  let NS := originalRingCoefficient.{max au r cu, max au w, max k au r cu v w mu} _ _
    (originalAmbientRightMap K A B C W iW).toRingHom
  let LS := originalRingCoefficient.{max au r cu, max v cu, max k au r cu v w mu} _ _
    (originalAmbientLeftMap K A B C V iV).toRingHom
  exact congrArg (fun e => e z)
    ((nativeTorFirstEndAlgHom.{max au r cu, max k au r cu v w mu}
      ((A ⊗[K] B) ⊗[K] C) NS LS q).commutes ((1 : A ⊗[K] B) ⊗ₜ[K] c))

/-- The native ambient action is the restriction of the earned balanced
support action. This identity is derived from the actual coefficient maps. -/
theorem standardAmbientNativeTor_smul [Module.Flat K A] [Module.Flat K C]
    (q : ℕ) (s : (A ⊗[K] B) ⊗[K] C)
    (z : standardAmbientNativeTor.{k, r, v, w, au, cu, mu} K B V W A C iV iW q) :
    letI : Algebra B V := (originalMiddleLeftMap K A B V iV).toRingHom.toAlgebra
    letI : Algebra B W := (originalMiddleRightMap K B C W iW).toRingHom.toAlgebra
    letI : Module (V ⊗[B] W)
        (standardAmbientNativeTor.{k, r, v, w, au, cu, mu} K B V W A C iV iW q) :=
      originalStandardAmbientTensorModule.{k, au, r, cu, v, w, mu} K A B C V W iV iW q
    s • z = standardSupportMap K B V W A C iV iW s • z := by
  let : Algebra B V := (originalMiddleLeftMap K A B V iV).toRingHom.toAlgebra
  let : Algebra B W := (originalMiddleRightMap K B C W iW).toRingHom.toAlgebra
  let : Module (V ⊗[B] W)
      (standardAmbientNativeTor.{k, r, v, w, au, cu, mu} K B V W A C iV iW q) :=
    originalStandardAmbientTensorModule.{k, au, r, cu, v, w, mu} K A B C V W iV iW q
  induction s using TensorProduct.inductionOn with
  | tmul x c =>
    change (x ⊗ₜ[K] c) • z = (iV x ⊗ₜ[B] iW ((1 : B) ⊗ₜ[K] c)) • z
    let z' : standardAmbientNativeTor.{k, r, v, w, au, cu, mu}
        K B V W A C iV iW q :=
      originalStandardAmbientRightOperator.{k, au, r, cu, v, w, mu}
        K A B C V W iV iW q (iW ((1 : B) ⊗ₜ[K] c)) z
    have hl : originalStandardAmbientLeftOperator.{k, au, r, cu, v, w, mu}
        K A B C V W iV iW q (iV x) z' = (x ⊗ₜ[K] (1 : C)) • z' :=
      standardAmbientLeftOperator_scalar.{k, r, v, w, au, cu, mu}
        K B V W A C iV iW q x z'
    have hr : z' = ((1 : A ⊗[K] B) ⊗ₜ[K] c) • z :=
      standardAmbientRightOperator_scalar.{k, r, v, w, au, cu, mu}
        K B V W A C iV iW q c z
    have ht : (iV x ⊗ₜ[B] iW ((1 : B) ⊗ₜ[K] c)) • z =
        originalStandardAmbientLeftOperator.{k, au, r, cu, v, w, mu}
          K A B C V W iV iW q (iV x) z' :=
      originalStandardAmbientTensorModule_tmul.{k, au, r, cu, v, w, mu}
        K A B C V W iV iW q (iV x) (iW ((1 : B) ⊗ₜ[K] c)) z
    have hm : (x ⊗ₜ[K] c) • z =
        (x ⊗ₜ[K] (1 : C)) • (((1 : A ⊗[K] B) ⊗ₜ[K] c) • z) := by
      rw [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    exact hm.trans ((congrArg
      (fun y : standardAmbientNativeTor.{k, r, v, w, au, cu, mu}
        K B V W A C iV iW q => (x ⊗ₜ[K] (1 : C)) • y) hr).symm.trans
          (hl.symm.trans ht.symm))
  | add s₁ s₂ h₁ h₂ => simp only [_root_.map_add, add_smul, h₁, h₂]

/-- The identity on the original native carrier identifies its actual
ambient module with restriction of the earned support module. -/
def standardAmbientSupportRestrictionIso [Module.Flat K A] [Module.Flat K C] (q : ℕ) :
    letI : Algebra B V := (originalMiddleLeftMap K A B V iV).toRingHom.toAlgebra
    letI : Algebra B W := (originalMiddleRightMap K B C W iW).toRingHom.toAlgebra
    letI : Module (V ⊗[B] W)
        (standardAmbientNativeTor.{k, r, v, w, au, cu, mu} K B V W A C iV iW q) :=
      originalStandardAmbientTensorModule.{k, au, r, cu, v, w, mu} K A B C V W iV iW q
    standardAmbientNativeTor.{k, r, v, w, au, cu, mu} K B V W A C iV iW q ≅
      (restrictScalars (standardSupportMap K B V W A C iV iW).toRingHom).obj
        (ModuleCat.of (V ⊗[B] W)
          (standardAmbientNativeTor.{k, r, v, w, au, cu, mu} K B V W A C iV iW q)) := by
  letI : Algebra B V := (originalMiddleLeftMap K A B V iV).toRingHom.toAlgebra
  letI : Algebra B W := (originalMiddleRightMap K B C W iW).toRingHom.toAlgebra
  letI : Module (V ⊗[B] W)
      (standardAmbientNativeTor.{k, r, v, w, au, cu, mu} K B V W A C iV iW q) :=
    originalStandardAmbientTensorModule.{k, au, r, cu, v, w, mu} K A B C V W iV iW q
  let X := standardAmbientNativeTor.{k, r, v, w, au, cu, mu} K B V W A C iV iW q
  let Y := (restrictScalars (standardSupportMap K B V W A C iV iW).toRingHom).obj
    (ModuleCat.of (V ⊗[B] W) X)
  let f : X ⟶ Y := ConcreteCategory.ofHom
    { toFun := fun z => z
      map_add' := fun _ _ => rfl
      map_smul' := fun s z => standardAmbientNativeTor_smul.{k, r, v, w, au, cu, mu}
        K B V W A C iV iW q s z }
  let g : Y ⟶ X := ConcreteCategory.ofHom
    { toFun := fun z => z
      map_add' := fun _ _ => rfl
      map_smul' := fun s z => (standardAmbientNativeTor_smul.{k, r, v, w, au, cu, mu}
        K B V W A C iV iW q s z).symm }
  exact { hom := f, inv := g, hom_inv_id := by ext z; rfl, inv_hom_id := by ext z; rfl }

end StandardNative

section IntrinsicNative

universe im

/-- The original intrinsic graph Tor before restriction of ambient scalars. -/
abbrev intrinsicAmbientNativeTor (q : ℕ) :
    ModuleCat.{max k r v w im} ((V ⊗[K] W) ⊗[K] B) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max k r v w im} ((V ⊗[K] W) ⊗[K] B)) :=
    tensorStructure.{max v w r, max k r v w im}
  letI : MonoidalCategory (ModuleCat.{max k r v w im} ((V ⊗[K] W) ⊗[K] B)) :=
    monoidalCategory.{max v w r, max k r v w im}
  letI : MonoidalPreadditive (ModuleCat.{max k r v w im} ((V ⊗[K] W) ⊗[K] B)) :=
    monoidalPreadditive.{max v w r, max k r v w im}
  exact ((Tor (ModuleCat.{max k r v w im} ((V ⊗[K] W) ⊗[K] B)) q).obj
    (originalRingCoefficient.{max v w r, max v w, max k r v w im} _ _
      (intrinsicGraphRightEvaluation K B V W b).toRingHom)).obj
        (originalRingCoefficient.{max v w r, max v w, max k r v w im} _ _
          (intrinsicGraphLeftEvaluation K B V W a).toRingHom)

/-- The actual V multiplication operator is native multiplication by its
ambient tensor inclusion. -/
theorem intrinsicAmbientLeftOperator_scalar (q : ℕ) (x : V)
    (z : intrinsicAmbientNativeTor.{k, r, v, w, im} K B V W a b q) :
    originalIntrinsicAmbientLeftOperator.{k, r, v, w, im} K B V W a b q x z =
      ((x ⊗ₜ[K] (1 : W)) ⊗ₜ[K] (1 : B)) • z := by
  let : Algebra B ((V ⊗[K] W) ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
  let : MonoidalCategoryStruct (ModuleCat.{max k r v w im} ((V ⊗[K] W) ⊗[K] B)) :=
    tensorStructure.{max v w r, max k r v w im}
  let : MonoidalCategory (ModuleCat.{max k r v w im} ((V ⊗[K] W) ⊗[K] B)) :=
    monoidalCategory.{max v w r, max k r v w im}
  let : MonoidalPreadditive (ModuleCat.{max k r v w im} ((V ⊗[K] W) ⊗[K] B)) :=
    monoidalPreadditive.{max v w r, max k r v w im}
  let G := (V ⊗[K] W) ⊗[K] B
  let D := V ⊗[K] W
  let NG := originalRingCoefficient.{max v w r, max v w, max k r v w im} G D
    (intrinsicGraphRightEvaluation K B V W b).toRingHom
  let LG := originalRingCoefficient.{max v w r, max v w, max k r v w im} G D
    (intrinsicGraphLeftEvaluation K B V W a).toRingHom
  let g := (x ⊗ₜ[K] (1 : W)) ⊗ₜ[K] (1 : B)
  have hc := (nativeTorSecondEndAlgHom.{max v w r, max k r v w im} G NG LG q).commutes g
  change nativeTorSecondEndAlgHom.{max v w r, max k r v w im} G NG LG q
      (originalRingCoefficientMul.{max v w r, max v w, max k r v w im} G D
        (intrinsicGraphLeftEvaluation K B V W a).toRingHom
        (intrinsicGraphLeftEvaluation K B V W a g)) =
    algebraMap G (Module.End G (intrinsicAmbientNativeTor.{k, r, v, w, im} K B V W a b q)) g at hc
  have he : intrinsicGraphLeftEvaluation K B V W a g = x ⊗ₜ[K] (1 : W) := by
    change (x ⊗ₜ[K] (1 : W)) * (a 1 ⊗ₜ[K] (1 : W)) = _
    rw [_root_.map_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [he] at hc
  exact congrArg (fun e => e z) hc

/-- The actual W multiplication operator is native multiplication by its
ambient tensor inclusion. -/
theorem intrinsicAmbientRightOperator_scalar (q : ℕ) (y : W)
    (z : intrinsicAmbientNativeTor.{k, r, v, w, im} K B V W a b q) :
    originalIntrinsicAmbientRightOperator.{k, r, v, w, im} K B V W a b q y z =
      (((1 : V) ⊗ₜ[K] y) ⊗ₜ[K] (1 : B)) • z := by
  let : Algebra B ((V ⊗[K] W) ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
  let : MonoidalCategoryStruct (ModuleCat.{max k r v w im} ((V ⊗[K] W) ⊗[K] B)) :=
    tensorStructure.{max v w r, max k r v w im}
  let : MonoidalCategory (ModuleCat.{max k r v w im} ((V ⊗[K] W) ⊗[K] B)) :=
    monoidalCategory.{max v w r, max k r v w im}
  let : MonoidalPreadditive (ModuleCat.{max k r v w im} ((V ⊗[K] W) ⊗[K] B)) :=
    monoidalPreadditive.{max v w r, max k r v w im}
  let G := (V ⊗[K] W) ⊗[K] B
  let D := V ⊗[K] W
  let NG := originalRingCoefficient.{max v w r, max v w, max k r v w im} G D
    (intrinsicGraphRightEvaluation K B V W b).toRingHom
  let LG := originalRingCoefficient.{max v w r, max v w, max k r v w im} G D
    (intrinsicGraphLeftEvaluation K B V W a).toRingHom
  let g := ((1 : V) ⊗ₜ[K] y) ⊗ₜ[K] (1 : B)
  have hc := (nativeTorFirstEndAlgHom.{max v w r, max k r v w im} G NG LG q).commutes g
  change nativeTorFirstEndAlgHom.{max v w r, max k r v w im} G NG LG q
      (originalRingCoefficientMul.{max v w r, max v w, max k r v w im} G D
        (intrinsicGraphRightEvaluation K B V W b).toRingHom
        (intrinsicGraphRightEvaluation K B V W b g)) =
    algebraMap G (Module.End G (intrinsicAmbientNativeTor.{k, r, v, w, im} K B V W a b q)) g at hc
  have he : intrinsicGraphRightEvaluation K B V W b g = (1 : V) ⊗ₜ[K] y := by
    change ((1 : V) ⊗ₜ[K] y) * ((1 : V) ⊗ₜ[K] b 1) = _
    simp only [_root_.map_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [he] at hc
  exact congrArg (fun e => e z) hc

/-- The native middle scalar agrees with its actual V image on Tor,
by the original resolved graph coefficient's scalar map. -/
theorem intrinsicAmbientMiddle_scalar (q : ℕ) (c : B)
    (z : intrinsicAmbientNativeTor.{k, r, v, w, im} K B V W a b q) :
    ((1 : V ⊗[K] W) ⊗ₜ[K] c) • z =
      ((a c ⊗ₜ[K] (1 : W)) ⊗ₜ[K] (1 : B)) • z := by
  let : Algebra B ((V ⊗[K] W) ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
  let : MonoidalCategoryStruct (ModuleCat.{max k r v w im} ((V ⊗[K] W) ⊗[K] B)) :=
    tensorStructure.{max v w r, max k r v w im}
  let : MonoidalCategory (ModuleCat.{max k r v w im} ((V ⊗[K] W) ⊗[K] B)) :=
    monoidalCategory.{max v w r, max k r v w im}
  let : MonoidalPreadditive (ModuleCat.{max k r v w im} ((V ⊗[K] W) ⊗[K] B)) :=
    monoidalPreadditive.{max v w r, max k r v w im}
  let G := (V ⊗[K] W) ⊗[K] B
  let D := V ⊗[K] W
  let NG := originalRingCoefficient.{max v w r, max v w, max k r v w im} G D
    (intrinsicGraphRightEvaluation K B V W b).toRingHom
  let LG := originalRingCoefficient.{max v w r, max v w, max k r v w im} G D
    (intrinsicGraphLeftEvaluation K B V W a).toRingHom
  let g := (1 : D) ⊗ₜ[K] c
  have hc := (nativeTorSecondEndAlgHom.{max v w r, max k r v w im} G NG LG q).commutes g
  change nativeTorSecondEndAlgHom.{max v w r, max k r v w im} G NG LG q
      (originalRingCoefficientMul.{max v w r, max v w, max k r v w im} G D
        (intrinsicGraphLeftEvaluation K B V W a).toRingHom
        (intrinsicGraphLeftEvaluation K B V W a g)) =
    algebraMap G (Module.End G (intrinsicAmbientNativeTor.{k, r, v, w, im} K B V W a b q)) g at hc
  have he : intrinsicGraphLeftEvaluation K B V W a g = a c ⊗ₜ[K] (1 : W) := by
    change (1 : D) * (a c ⊗ₜ[K] (1 : W)) = _
    exact one_mul _
  rw [he] at hc
  have hs : originalIntrinsicAmbientLeftOperator.{k, r, v, w, im} K B V W a b q (a c) z =
      g • z := congrArg (fun e => e z) hc
  exact hs.symm.trans
    (intrinsicAmbientLeftOperator_scalar.{k, r, v, w, im} K B V W a b q (a c) z)

/-- The genuine native graph ambient action is restriction of the earned
balanced support action, including the original middle-ring scalar. -/
theorem intrinsicAmbientNativeTor_smul [Module.Flat K V] [Module.Flat K W]
    (q : ℕ) (g : (V ⊗[K] W) ⊗[K] B)
    (z : intrinsicAmbientNativeTor.{k, r, v, w, im} K B V W a b q) :
    letI : Algebra B V := a.toRingHom.toAlgebra
    letI : Algebra B W := b.toRingHom.toAlgebra
    letI : Module (V ⊗[B] W)
        (intrinsicAmbientNativeTor.{k, r, v, w, im} K B V W a b q) :=
      originalIntrinsicAmbientTensorModule.{k, r, v, w, im} K B V W a b q
    g • z = intrinsicSupportMap K B V W a b g • z := by
  let : Algebra B V := a.toRingHom.toAlgebra
  let : Algebra B W := b.toRingHom.toAlgebra
  let : Module (V ⊗[B] W)
      (intrinsicAmbientNativeTor.{k, r, v, w, im} K B V W a b q) :=
    originalIntrinsicAmbientTensorModule.{k, r, v, w, im} K B V W a b q
  induction g using TensorProduct.inductionOn with
  | tmul d c =>
    induction d using TensorProduct.inductionOn with
    | tmul x y =>
      rw [intrinsicSupportMap_tmul]
      let z' : intrinsicAmbientNativeTor.{k, r, v, w, im} K B V W a b q :=
        originalIntrinsicAmbientRightOperator.{k, r, v, w, im} K B V W a b q y z
      have hl : originalIntrinsicAmbientLeftOperator.{k, r, v, w, im}
          K B V W a b q (x * a c) z' =
          (((x * a c) ⊗ₜ[K] (1 : W)) ⊗ₜ[K] (1 : B)) • z' :=
        intrinsicAmbientLeftOperator_scalar.{k, r, v, w, im} K B V W a b q (x * a c) z'
      have hr : z' = (((1 : V) ⊗ₜ[K] y) ⊗ₜ[K] (1 : B)) • z :=
        intrinsicAmbientRightOperator_scalar.{k, r, v, w, im} K B V W a b q y z
      have ht : ((x * a c) ⊗ₜ[B] y) • z =
          originalIntrinsicAmbientLeftOperator.{k, r, v, w, im} K B V W a b q (x * a c) z' :=
        originalIntrinsicAmbientTensorModule_tmul.{k, r, v, w, im}
          K B V W a b q (x * a c) y z
      have hm : ((x ⊗ₜ[K] y) ⊗ₜ[K] c) • z =
          (((x * a c) ⊗ₜ[K] (1 : W)) ⊗ₜ[K] (1 : B)) •
            ((((1 : V) ⊗ₜ[K] y) ⊗ₜ[K] (1 : B)) • z) := by
        calc
          _ = ((x ⊗ₜ[K] y) ⊗ₜ[K] (1 : B)) •
              (((1 : V ⊗[K] W) ⊗ₜ[K] c) • z) := by
            rw [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
          _ = ((x ⊗ₜ[K] y) ⊗ₜ[K] (1 : B)) •
              (((a c ⊗ₜ[K] (1 : W)) ⊗ₜ[K] (1 : B)) • z) :=
            congrArg (fun zz : intrinsicAmbientNativeTor.{k, r, v, w, im}
                K B V W a b q => ((x ⊗ₜ[K] y) ⊗ₜ[K] (1 : B)) • zz)
              (intrinsicAmbientMiddle_scalar.{k, r, v, w, im} K B V W a b q c z)
          _ = _ := by
            simp only [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      exact hm.trans ((congrArg
        (fun zz : intrinsicAmbientNativeTor.{k, r, v, w, im} K B V W a b q =>
          (((x * a c) ⊗ₜ[K] (1 : W)) ⊗ₜ[K] (1 : B)) • zz) hr).symm.trans
            (hl.symm.trans ht.symm))
    | add d₁ d₂ h₁ h₂ =>
      simp only [TensorProduct.add_tmul, _root_.map_add, add_smul, h₁, h₂]
  | add g₁ g₂ h₁ h₂ => simp only [_root_.map_add, add_smul, h₁, h₂]

/-- The actual native G action and the earned T action form a scalar
tower along the canonical graph support map. -/
theorem intrinsicAmbientNativeTor_scalarTower [Module.Flat K V] [Module.Flat K W] (q : ℕ) :
    letI : Algebra B V := a.toRingHom.toAlgebra
    letI : Algebra B W := b.toRingHom.toAlgebra
    letI : Algebra ((V ⊗[K] W) ⊗[K] B) (V ⊗[B] W) :=
      (intrinsicSupportMap K B V W a b).toRingHom.toAlgebra
    letI : Module (V ⊗[B] W)
        (intrinsicAmbientNativeTor.{k, r, v, w, im} K B V W a b q) :=
      originalIntrinsicAmbientTensorModule.{k, r, v, w, im} K B V W a b q
    IsScalarTower ((V ⊗[K] W) ⊗[K] B) (V ⊗[B] W)
      (intrinsicAmbientNativeTor.{k, r, v, w, im} K B V W a b q) := by
  let : Algebra B V := a.toRingHom.toAlgebra
  let : Algebra B W := b.toRingHom.toAlgebra
  let : Algebra ((V ⊗[K] W) ⊗[K] B) (V ⊗[B] W) :=
    (intrinsicSupportMap K B V W a b).toRingHom.toAlgebra
  let : Module (V ⊗[B] W)
      (intrinsicAmbientNativeTor.{k, r, v, w, im} K B V W a b q) :=
    originalIntrinsicAmbientTensorModule.{k, r, v, w, im} K B V W a b q
  apply IsScalarTower.of_algebraMap_smul
  intro g z
  exact (intrinsicAmbientNativeTor_smul.{k, r, v, w, im} K B V W a b q g z).symm

end IntrinsicNative

section StandardPrimeLocal

universe pa pc pm

variable (A : Type pa) (C : Type pc) [CommRing A] [CommRing C]
  [Algebra K A] [Algebra K C]
  (iV : A ⊗[K] B →ₐ[K] V) (iW : B ⊗[K] C →ₐ[K] W)

/-- The actual standard native Tor over the inverse-image local ring,
with both original ambient coefficients localized. -/
abbrev standardAmbientTorAtPrime (p :
    letI : Algebra B V := (originalMiddleLeftMap K A B V iV).toRingHom.toAlgebra
    letI : Algebra B W := (originalMiddleRightMap K B C W iW).toRingHom.toAlgebra
    PrimeSpectrum (V ⊗[B] W)) (q : ℕ) :
    letI : Algebra B V := (originalMiddleLeftMap K A B V iV).toRingHom.toAlgebra
    letI : Algebra B W := (originalMiddleRightMap K B C W iW).toRingHom.toAlgebra
    ModuleCat.{max k pa r pc v w pm}
      (Localization.AtPrime (p.asIdeal.comap
        (standardSupportMap K B V W A C iV iW).toRingHom)) := by
  letI : Algebra B V := (originalMiddleLeftMap K A B V iV).toRingHom.toAlgebra
  letI : Algebra B W := (originalMiddleRightMap K B C W iW).toRingHom.toAlgebra
  exact nativeTorAtPrime.{max pa r pc, max k pa r pc v w pm}
    ((A ⊗[K] B) ⊗[K] C)
    (p.asIdeal.comap (standardSupportMap K B V W A C iV iW).toRingHom)
    (originalRingCoefficient.{max pa r pc, max pa w, max k pa r pc v w pm} _ _
      (originalAmbientRightMap K A B C W iW).toRingHom)
    (originalRingCoefficient.{max pa r pc, max v pc, max k pa r pc v w pm} _ _
      (originalAmbientLeftMap K A B C V iV).toRingHom) q

/-- The actual standard native scalar tower along its support map. -/
theorem standardAmbientNativeTor_scalarTower [Module.Flat K A] [Module.Flat K C] (q : ℕ) :
    letI : Algebra B V := (originalMiddleLeftMap K A B V iV).toRingHom.toAlgebra
    letI : Algebra B W := (originalMiddleRightMap K B C W iW).toRingHom.toAlgebra
    letI : Algebra ((A ⊗[K] B) ⊗[K] C) (V ⊗[B] W) :=
      (standardSupportMap K B V W A C iV iW).toRingHom.toAlgebra
    letI : Module (V ⊗[B] W)
        (standardAmbientNativeTor.{k, r, v, w, pa, pc, pm} K B V W A C iV iW q) :=
      originalStandardAmbientTensorModule.{k, pa, r, pc, v, w, pm} K A B C V W iV iW q
    IsScalarTower ((A ⊗[K] B) ⊗[K] C) (V ⊗[B] W)
      (standardAmbientNativeTor.{k, r, v, w, pa, pc, pm} K B V W A C iV iW q) := by
  let : Algebra B V := (originalMiddleLeftMap K A B V iV).toRingHom.toAlgebra
  let : Algebra B W := (originalMiddleRightMap K B C W iW).toRingHom.toAlgebra
  let : Algebra ((A ⊗[K] B) ⊗[K] C) (V ⊗[B] W) :=
    (standardSupportMap K B V W A C iV iW).toRingHom.toAlgebra
  let : Module (V ⊗[B] W)
      (standardAmbientNativeTor.{k, r, v, w, pa, pc, pm} K B V W A C iV iW q) :=
    originalStandardAmbientTensorModule.{k, pa, r, pc, v, w, pm} K A B C V W iV iW q
  apply IsScalarTower.of_algebraMap_smul
  intro s z
  exact (standardAmbientNativeTor_smul.{k, r, v, w, pa, pc, pm}
    K B V W A C iV iW q s z).symm

/-- At every actual support prime, the standard local native Tor has the
literal length of the corresponding T-localized ordered middle Tor.
Surjectivity of both support maps is required. Infinite length is allowed. -/
theorem standardAmbientTorAtPrime_length [Module.Flat K A] [Module.Flat K C]
    (hV : Function.Surjective iV) (hW : Function.Surjective iW) (p :
      letI : Algebra B V := (originalMiddleLeftMap K A B V iV).toRingHom.toAlgebra
      letI : Algebra B W := (originalMiddleRightMap K B C W iW).toRingHom.toAlgebra
      PrimeSpectrum (V ⊗[B] W)) (q : ℕ) :
    letI : Algebra B V := (originalMiddleLeftMap K A B V iV).toRingHom.toAlgebra
    letI : Algebra B W := (originalMiddleRightMap K B C W iW).toRingHom.toAlgebra
    letI : Module (V ⊗[B] W) (originalMiddleTor.{r, v, w, max k pa pc pm} B V W q) :=
      originalMiddleTorTensorModule.{r, v, w, max k pa pc pm} B V W q
    Module.length
        (Localization.AtPrime (p.asIdeal.comap
          (standardSupportMap K B V W A C iV iW).toRingHom))
        (standardAmbientTorAtPrime.{k, r, v, w, pa, pc, pm} K B V W A C iV iW p q) =
      Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal
          (originalMiddleTor.{r, v, w, max k pa pc pm} B V W q)) := by
  let : Algebra B V := (originalMiddleLeftMap K A B V iV).toRingHom.toAlgebra
  let : Algebra B W := (originalMiddleRightMap K B C W iW).toRingHom.toAlgebra
  let S := (A ⊗[K] B) ⊗[K] C
  let f := (standardSupportMap K B V W A C iV iW).toRingHom
  let : Algebra S (V ⊗[B] W) := f.toAlgebra
  let X : ModuleCat.{max k pa r pc v w pm} S :=
    standardAmbientNativeTor.{k, r, v, w, pa, pc, pm} K B V W A C iV iW q
  let : Module (V ⊗[B] W) X :=
    originalStandardAmbientTensorModule.{k, pa, r, pc, v, w, pm} K A B C V W iV iW q
  have : IsScalarTower S (V ⊗[B] W) X :=
    standardAmbientNativeTor_scalarTower.{k, r, v, w, pa, pc, pm} K B V W A C iV iW q
  let XB := originalMiddleTor.{r, v, w, max k pa pc pm} B V W q
  let : Module (V ⊗[B] W) XB := originalMiddleTorTensorModule.{r, v, w, max k pa pc pm} B V W q
  let NS := originalRingCoefficient.{max pa r pc, max pa w, max k pa r pc v w pm} _ _
    (originalAmbientRightMap K A B C W iW).toRingHom
  let LS := originalRingCoefficient.{max pa r pc, max v pc, max k pa r pc v w pm} _ _
    (originalAmbientLeftMap K A B C V iV).toRingHom
  have e₀ : ModuleCat.of (Localization.AtPrime (p.asIdeal.comap f))
        (LocalizedModule.AtPrime (p.asIdeal.comap f) X) ≅
      standardAmbientTorAtPrime.{k, r, v, w, pa, pc, pm} K B V W A C iV iW p q :=
    localizedNativeTorIso.{max pa r pc, max k pa r pc v w pm} S (p.asIdeal.comap f) NS LS q
  have hloc := localizedModuleLengthOfSurjective
    (standardSupportMap_surjective K B V W A C iV iW hV hW) p.asIdeal X
  let E : X ≃ₗ[V ⊗[B] W] XB :=
    originalStandardAmbientTensorTorEquiv.{k, pa, r, pc, v, w, pm} K A B C V W iV iW q
  let e : LocalizedModule.AtPrime p.asIdeal X ≃ₗ[Localization.AtPrime p.asIdeal]
      LocalizedModule.AtPrime p.asIdeal XB :=
    IsLocalizedModule.mapEquiv p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl X)
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl XB) (Localization.AtPrime p.asIdeal) E
  exact e₀.toLinearEquiv.length_eq.symm.trans (hloc.trans e.length_eq)

/-- The actual native standard support is the inverse-image-prime image
of the support of ordered middle Tor, for genuine support quotients. -/
theorem standardAmbientNativeTor_support [Module.Flat K A] [Module.Flat K C]
    (hV : Function.Surjective iV) (hW : Function.Surjective iW) (q : ℕ) :
    letI : Algebra B V := (originalMiddleLeftMap K A B V iV).toRingHom.toAlgebra
    letI : Algebra B W := (originalMiddleRightMap K B C W iW).toRingHom.toAlgebra
    letI : Module (V ⊗[B] W) (originalMiddleTor.{r, v, w, max k pa pc pm} B V W q) :=
      originalMiddleTorTensorModule.{r, v, w, max k pa pc pm} B V W q
    Module.support ((A ⊗[K] B) ⊗[K] C)
        (standardAmbientNativeTor.{k, r, v, w, pa, pc, pm} K B V W A C iV iW q) =
      PrimeSpectrum.comap (standardSupportMap K B V W A C iV iW).toRingHom ''
        Module.support (V ⊗[B] W) (originalMiddleTor.{r, v, w, max k pa pc pm} B V W q) := by
  let : Algebra B V := (originalMiddleLeftMap K A B V iV).toRingHom.toAlgebra
  let : Algebra B W := (originalMiddleRightMap K B C W iW).toRingHom.toAlgebra
  let S := (A ⊗[K] B) ⊗[K] C
  let f := (standardSupportMap K B V W A C iV iW).toRingHom
  let : Algebra S (V ⊗[B] W) := f.toAlgebra
  let X : ModuleCat.{max k pa r pc v w pm} S :=
    standardAmbientNativeTor.{k, r, v, w, pa, pc, pm} K B V W A C iV iW q
  let : Module (V ⊗[B] W) X :=
    originalStandardAmbientTensorModule.{k, pa, r, pc, v, w, pm} K A B C V W iV iW q
  have : IsScalarTower S (V ⊗[B] W) X :=
    standardAmbientNativeTor_scalarTower.{k, r, v, w, pa, pc, pm} K B V W A C iV iW q
  let XB := originalMiddleTor.{r, v, w, max k pa pc pm} B V W q
  let : Module (V ⊗[B] W) XB := originalMiddleTorTensorModule.{r, v, w, max k pa pc pm} B V W q
  let E : X ≃ₗ[V ⊗[B] W] XB :=
    originalStandardAmbientTensorTorEquiv.{k, pa, r, pc, v, w, pm} K A B C V W iV iW q
  exact (Module.support_eq_image_of_surjective
    (standardSupportMap_surjective K B V W A C iV iW hV hW) X).trans
      (congrArg (Set.image (PrimeSpectrum.comap f)) E.support_eq)

end StandardPrimeLocal

section IntrinsicPrimeLocal

universe ip

/-- Native local Tor of the two actual graph coefficients over the
inverse-image local ring of the intrinsic ambient. -/
abbrev intrinsicAmbientTorAtPrime (p :
    letI : Algebra B V := a.toRingHom.toAlgebra
    letI : Algebra B W := b.toRingHom.toAlgebra
    PrimeSpectrum (V ⊗[B] W)) (q : ℕ) :
    letI : Algebra B V := a.toRingHom.toAlgebra
    letI : Algebra B W := b.toRingHom.toAlgebra
    ModuleCat.{max k r v w ip}
      (Localization.AtPrime (p.asIdeal.comap (intrinsicSupportMap K B V W a b).toRingHom)) := by
  letI : Algebra B V := a.toRingHom.toAlgebra
  letI : Algebra B W := b.toRingHom.toAlgebra
  exact nativeTorAtPrime.{max v w r, max k r v w ip} ((V ⊗[K] W) ⊗[K] B)
    (p.asIdeal.comap (intrinsicSupportMap K B V W a b).toRingHom)
    (originalRingCoefficient.{max v w r, max v w, max k r v w ip} _ _
      (intrinsicGraphRightEvaluation K B V W b).toRingHom)
    (originalRingCoefficient.{max v w r, max v w, max k r v w ip} _ _
      (intrinsicGraphLeftEvaluation K B V W a).toRingHom) q

/-- The intrinsic local native Tor has the literal T-local middle-Tor
length. The graph support quotient is always surjective. -/
theorem intrinsicAmbientTorAtPrime_length [Module.Flat K V] [Module.Flat K W] (p :
    letI : Algebra B V := a.toRingHom.toAlgebra
    letI : Algebra B W := b.toRingHom.toAlgebra
    PrimeSpectrum (V ⊗[B] W)) (q : ℕ) :
    letI : Algebra B V := a.toRingHom.toAlgebra
    letI : Algebra B W := b.toRingHom.toAlgebra
    letI : Module (V ⊗[B] W) (originalMiddleTor.{r, v, w, max k ip} B V W q) :=
      originalMiddleTorTensorModule.{r, v, w, max k ip} B V W q
    Module.length
        (Localization.AtPrime (p.asIdeal.comap (intrinsicSupportMap K B V W a b).toRingHom))
        (intrinsicAmbientTorAtPrime.{k, r, v, w, ip} K B V W a b p q) =
      Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal (originalMiddleTor.{r, v, w, max k ip} B V W q)) := by
  let : Algebra B V := a.toRingHom.toAlgebra
  let : Algebra B W := b.toRingHom.toAlgebra
  let G := (V ⊗[K] W) ⊗[K] B
  let f := (intrinsicSupportMap K B V W a b).toRingHom
  let : Algebra G (V ⊗[B] W) := f.toAlgebra
  let X : ModuleCat.{max k r v w ip} G :=
    intrinsicAmbientNativeTor.{k, r, v, w, ip} K B V W a b q
  let : Module (V ⊗[B] W) X := originalIntrinsicAmbientTensorModule.{k, r, v, w, ip} K B V W a b q
  have : IsScalarTower G (V ⊗[B] W) X :=
    intrinsicAmbientNativeTor_scalarTower.{k, r, v, w, ip} K B V W a b q
  let XB := originalMiddleTor.{r, v, w, max k ip} B V W q
  let : Module (V ⊗[B] W) XB := originalMiddleTorTensorModule.{r, v, w, max k ip} B V W q
  let NG := originalRingCoefficient.{max v w r, max v w, max k r v w ip} _ _
    (intrinsicGraphRightEvaluation K B V W b).toRingHom
  let LG := originalRingCoefficient.{max v w r, max v w, max k r v w ip} _ _
    (intrinsicGraphLeftEvaluation K B V W a).toRingHom
  have e₀ : ModuleCat.of (Localization.AtPrime (p.asIdeal.comap f))
        (LocalizedModule.AtPrime (p.asIdeal.comap f) X) ≅
      intrinsicAmbientTorAtPrime.{k, r, v, w, ip} K B V W a b p q :=
    localizedNativeTorIso.{max v w r, max k r v w ip} G (p.asIdeal.comap f) NG LG q
  have hloc := localizedModuleLengthOfSurjective
    (intrinsicSupportMap_surjective K B V W a b) p.asIdeal X
  let E : X ≃ₗ[V ⊗[B] W] XB :=
    originalIntrinsicAmbientTensorTorEquiv.{k, r, v, w, ip} K B V W a b q
  let e : LocalizedModule.AtPrime p.asIdeal X ≃ₗ[Localization.AtPrime p.asIdeal]
      LocalizedModule.AtPrime p.asIdeal XB :=
    IsLocalizedModule.mapEquiv p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl X)
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl XB) (Localization.AtPrime p.asIdeal) E
  exact e₀.toLinearEquiv.length_eq.symm.trans (hloc.trans e.length_eq)

/-- The native intrinsic graph support is the prime image of the actual
support of ordered middle Tor, without additional quotient hypotheses. -/
theorem intrinsicAmbientNativeTor_support [Module.Flat K V] [Module.Flat K W] (q : ℕ) :
    letI : Algebra B V := a.toRingHom.toAlgebra
    letI : Algebra B W := b.toRingHom.toAlgebra
    letI : Module (V ⊗[B] W) (originalMiddleTor.{r, v, w, max k ip} B V W q) :=
      originalMiddleTorTensorModule.{r, v, w, max k ip} B V W q
    Module.support ((V ⊗[K] W) ⊗[K] B)
        (intrinsicAmbientNativeTor.{k, r, v, w, ip} K B V W a b q) =
      PrimeSpectrum.comap (intrinsicSupportMap K B V W a b).toRingHom ''
        Module.support (V ⊗[B] W) (originalMiddleTor.{r, v, w, max k ip} B V W q) := by
  let : Algebra B V := a.toRingHom.toAlgebra
  let : Algebra B W := b.toRingHom.toAlgebra
  let G := (V ⊗[K] W) ⊗[K] B
  let f := (intrinsicSupportMap K B V W a b).toRingHom
  let : Algebra G (V ⊗[B] W) := f.toAlgebra
  let X : ModuleCat.{max k r v w ip} G :=
    intrinsicAmbientNativeTor.{k, r, v, w, ip} K B V W a b q
  let : Module (V ⊗[B] W) X := originalIntrinsicAmbientTensorModule.{k, r, v, w, ip} K B V W a b q
  have : IsScalarTower G (V ⊗[B] W) X :=
    intrinsicAmbientNativeTor_scalarTower.{k, r, v, w, ip} K B V W a b q
  let XB := originalMiddleTor.{r, v, w, max k ip} B V W q
  let : Module (V ⊗[B] W) XB := originalMiddleTorTensorModule.{r, v, w, max k ip} B V W q
  let E : X ≃ₗ[V ⊗[B] W] XB :=
    originalIntrinsicAmbientTensorTorEquiv.{k, r, v, w, ip} K B V W a b q
  exact (Module.support_eq_image_of_surjective
    (intrinsicSupportMap_surjective K B V W a b) X).trans
      (congrArg (Set.image (PrimeSpectrum.comap f)) E.support_eq)

end IntrinsicPrimeLocal

section FieldComparison

universe fk fa fb fc fv fw fm

variable (KF : Type fk) (AF : Type fa) (BF : Type fb) (CF : Type fc)
  (VF : Type fv) (WF : Type fw) [Field KF] [CommRing AF] [CommRing BF] [CommRing CF]
  [CommRing VF] [CommRing WF] [Algebra KF AF] [Algebra KF BF] [Algebra KF CF]
  [Algebra KF VF] [Algebra KF WF]
  (iV : AF ⊗[KF] BF →ₐ[KF] VF) (iW : BF ⊗[KF] CF →ₐ[KF] WF)
  (hV : Function.Surjective iV) (hW : Function.Surjective iW)
  (p :
    letI : Algebra BF VF := (originalMiddleLeftMap KF AF BF VF iV).toRingHom.toAlgebra
    letI : Algebra BF WF := (originalMiddleRightMap KF BF CF WF iW).toRingHom.toAlgebra
    PrimeSpectrum (VF ⊗[BF] WF))

include hV hW

/-- Over the original field, native Tor over both actual ambient local
rings has the same literal composition length. Genuine quotient support
maps are needed on the standard side. All degrees and universes are retained. -/
theorem fieldTensorTorAtPrime_length_eq (q : ℕ) :
    letI : Algebra BF VF := (originalMiddleLeftMap KF AF BF VF iV).toRingHom.toAlgebra
    letI : Algebra BF WF := (originalMiddleRightMap KF BF CF WF iW).toRingHom.toAlgebra
    let Sp := Localization.AtPrime
      (p.asIdeal.comap (standardSupportMap KF BF VF WF AF CF iV iW).toRingHom)
    let Gu := Localization.AtPrime
      (p.asIdeal.comap (intrinsicSupportMap KF BF VF WF
        (originalMiddleLeftMap KF AF BF VF iV)
        (originalMiddleRightMap KF BF CF WF iW)).toRingHom)
    let YS (j : ℕ) := standardAmbientTorAtPrime.{fk, fb, fv, fw, fa, fc, fm}
      KF BF VF WF AF CF iV iW p j
    let YG (j : ℕ) := intrinsicAmbientTorAtPrime.{fk, fb, fv, fw, max fa fc fm}
      KF BF VF WF (originalMiddleLeftMap KF AF BF VF iV)
        (originalMiddleRightMap KF BF CF WF iW) p j
    Module.length Sp (YS q) = Module.length Gu (YG q) := by
  let : Algebra BF VF := (originalMiddleLeftMap KF AF BF VF iV).toRingHom.toAlgebra
  let : Algebra BF WF := (originalMiddleRightMap KF BF CF WF iW).toRingHom.toAlgebra
  let : Module (VF ⊗[BF] WF)
      (originalMiddleTor.{fb, fv, fw, max fk fa fc fm} BF VF WF q) :=
    originalMiddleTorTensorModule.{fb, fv, fw, max fk fa fc fm} BF VF WF q
  have hs := standardAmbientTorAtPrime_length.{fk, fb, fv, fw, fa, fc, fm}
    KF BF VF WF AF CF iV iW hV hW p q
  have hg := intrinsicAmbientTorAtPrime_length.{fk, fb, fv, fw, max fa fc fm}
    KF BF VF WF (originalMiddleLeftMap KF AF BF VF iV)
      (originalMiddleRightMap KF BF CF WF iW) p q
  exact hs.trans hg.symm

/-- Honest finite-length and eventual-zero data for the standard native
local Tor transport to the intrinsic native local Tor. Their finite
alternating integer sums agree at the supplied cutoff. -/
theorem fieldTensorTorAtPrime_finiteEuler (cutoff : ℕ)
    (hfinite :
      let : Algebra BF VF := (originalMiddleLeftMap KF AF BF VF iV).toRingHom.toAlgebra
      let : Algebra BF WF := (originalMiddleRightMap KF BF CF WF iW).toRingHom.toAlgebra
      let Sp := Localization.AtPrime
        (p.asIdeal.comap (standardSupportMap KF BF VF WF AF CF iV iW).toRingHom)
      let YS (j : ℕ) := standardAmbientTorAtPrime.{fk, fb, fv, fw, fa, fc, fm}
        KF BF VF WF AF CF iV iW p j
      ∀ j < cutoff, Module.length Sp (YS j) ≠ ⊤)
    (hvanishes :
      let : Algebra BF VF := (originalMiddleLeftMap KF AF BF VF iV).toRingHom.toAlgebra
      let : Algebra BF WF := (originalMiddleRightMap KF BF CF WF iW).toRingHom.toAlgebra
      let YS (j : ℕ) := standardAmbientTorAtPrime.{fk, fb, fv, fw, fa, fc, fm}
        KF BF VF WF AF CF iV iW p j
      ∀ j, cutoff ≤ j → Subsingleton (YS j)) :
    letI : Algebra BF VF := (originalMiddleLeftMap KF AF BF VF iV).toRingHom.toAlgebra
    letI : Algebra BF WF := (originalMiddleRightMap KF BF CF WF iW).toRingHom.toAlgebra
    let Sp := Localization.AtPrime
      (p.asIdeal.comap (standardSupportMap KF BF VF WF AF CF iV iW).toRingHom)
    let Gu := Localization.AtPrime
      (p.asIdeal.comap (intrinsicSupportMap KF BF VF WF
        (originalMiddleLeftMap KF AF BF VF iV)
        (originalMiddleRightMap KF BF CF WF iW)).toRingHom)
    let YS (j : ℕ) := standardAmbientTorAtPrime.{fk, fb, fv, fw, fa, fc, fm}
      KF BF VF WF AF CF iV iW p j
    let YG (j : ℕ) := intrinsicAmbientTorAtPrime.{fk, fb, fv, fw, max fa fc fm}
      KF BF VF WF (originalMiddleLeftMap KF AF BF VF iV)
        (originalMiddleRightMap KF BF CF WF iW) p j
    (∀ j < cutoff, Module.length Gu (YG j) ≠ ⊤) ∧
      (∀ j, cutoff ≤ j → Subsingleton (YG j)) ∧
      (∑ j ∈ Finset.range cutoff, (-1 : ℤ) ^ j * (Module.length Sp (YS j)).toNat) =
        ∑ j ∈ Finset.range cutoff, (-1 : ℤ) ^ j * (Module.length Gu (YG j)).toNat := by
  let : Algebra BF VF := (originalMiddleLeftMap KF AF BF VF iV).toRingHom.toAlgebra
  let : Algebra BF WF := (originalMiddleRightMap KF BF CF WF iW).toRingHom.toAlgebra
  let Sp := Localization.AtPrime
    (p.asIdeal.comap (standardSupportMap KF BF VF WF AF CF iV iW).toRingHom)
  let Gu := Localization.AtPrime
    (p.asIdeal.comap (intrinsicSupportMap KF BF VF WF
      (originalMiddleLeftMap KF AF BF VF iV)
      (originalMiddleRightMap KF BF CF WF iW)).toRingHom)
  let YS (j : ℕ) := standardAmbientTorAtPrime.{fk, fb, fv, fw, fa, fc, fm}
    KF BF VF WF AF CF iV iW p j
  let YG (j : ℕ) := intrinsicAmbientTorAtPrime.{fk, fb, fv, fw, max fa fc fm}
    KF BF VF WF (originalMiddleLeftMap KF AF BF VF iV)
      (originalMiddleRightMap KF BF CF WF iW) p j
  have hlength (j : ℕ) : Module.length Sp (YS j) = Module.length Gu (YG j) :=
    fieldTensorTorAtPrime_length_eq.{fk, fa, fb, fc, fv, fw, fm}
      KF AF BF CF VF WF iV iW hV hW p j
  refine ⟨fun j hj => ?_, (fun j hj => ?_), ?_⟩
  · rw [← hlength j]
    exact hfinite j hj
  · apply (Module.length_eq_zero_iff (R := Gu)).mp
    rw [← hlength j]
    exact (Module.length_eq_zero_iff (R := Sp)).mpr (hvanishes j hj)
  · apply Finset.sum_congr rfl
    intro j _
    rw [hlength j]

end FieldComparison

end ModuleCat.UniverseTensor
