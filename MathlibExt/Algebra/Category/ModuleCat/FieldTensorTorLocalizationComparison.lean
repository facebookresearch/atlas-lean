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
# Graph ambient Tor, support primes and localized module lengths

Let K be a commutative ring and B,V,W commutative K-algebras with maps
a:B→V,b:B→W. Put T=V⊗[B]W and G=(V⊗[K]W)⊗[K]B.
The intrinsic support map is
σ_G((x⊗y)⊗c)=(x a(c))⊗_B y; it is always surjective.

For commutative K-algebras A,C and maps
i_V:A⊗[K]B→V, i_W:B⊗[K]C→W, use their induced B-actions
and S=(A⊗[K]B)⊗[K]C. The standard support map is
σ_S((x⊗y)⊗z)=i_V(x⊗y)⊗_B i_W(1⊗z).
It is surjective when both i_V and i_W are surjective.

Flat adjoining factors identify ambient Tor with ordered Tor_B(V,W)
over T. Localizing at a support prime p gives equality of the
ambient-local and T_p-local module lengths. The intrinsic comparison
requires V,W flat over K; the standard one requires A,C flat over K
and surjectivity for its support and length results.
Lengths may be infinite. Over a field, the finite Euler comparison
separately assumes finite standard lengths below a cutoff and zero
standard local Tor at and above it, then transfers both properties
and the finite alternating integer sum.
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

/-- For commutative K-algebras B,V,W and maps a:B→V,b:B→W,
the support quotient V⊗[K]W→V⊗[B]W sends x⊗y to x⊗_B y.
It imposes the balancing relation from the two B-actions. -/
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

/-- For G=(V⊗[K]W)⊗[K]B and T=V⊗[B]W through a,b,
the intrinsic support map σ_G:G→T is induced by the
K-tensor balancing quotient and the middle B-action.
All rings are commutative K-algebras. -/
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

/-- For x∈V,y∈W,c∈B, the intrinsic support map satisfies
σ_G((x⊗y)⊗c)=(x*a(c))⊗_B y.
The B-action on V is induced by a and that on W by b. -/
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

/-- For K-algebra maps a:B→V,b:B→W between commutative rings,
σ_G:(V⊗[K]W)⊗[K]B→V⊗[B]W is surjective.
A pure support class x⊗_B y has preimage (x⊗_K y)⊗1_B. -/
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

/-- For i_V:A⊗[K]B→V and i_W:B⊗[K]C→W, the standard
support map σ_S:S→T uses S=(A⊗[K]B)⊗[K]C and T=V⊗[B]W.
The B-actions are i_V(1⊗−) and i_W(−⊗1). -/
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

/-- For x∈A,y∈B,z∈C, the standard support map satisfies
σ_S((x⊗y)⊗z)=i_V(x⊗y)⊗_B i_W(1_B⊗z).
The displayed coefficient order agrees with the induced
B-actions on V and W. -/
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

/-- For commutative K-algebra maps i_V:A⊗K B→V and
i_W:B⊗K C→W, if both maps are surjective, then
σ_S:(A⊗K B)⊗K C→V⊗B W is surjective.
No coefficient flatness is needed for this quotient property. -/
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

/-- For S=(A⊗K B)⊗K C, the ambient Tor is Tor_q^S
of the right coefficient A⊗K W first and the left coefficient
V⊗K C second, using their ambient evaluation maps.
Its carrier height is max(k,au,r,cu,v,w,mu). -/
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

/-- For x∈A⊗K B, the V-support operator given by i_V(x)
on standard ambient Tor equals multiplication by x⊗1_C
in the ambient ring S. This identifies the coefficient
multiplication with the existing S-module action. -/
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

/-- For c∈C, the W-support operator given by i_W(1_B⊗c)
on standard ambient Tor equals multiplication by
1_(A⊗B)⊗c in S=(A⊗K B)⊗K C. -/
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

/-- If A,C are flat over K, the standard ambient Tor
carries its canonical T=V⊗B W action.
For s∈S and z in that Tor module, the ambient scalar
action satisfies s•z=σ_S(s)•_T z. -/
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

/-- If A,C are flat over K, the identity on the standard
ambient Tor carrier gives an S-linear isomorphism to
its T-support module restricted along σ_S:S→T.
The two scalar actions agree. -/
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

/-- For G=(V⊗K W)⊗K B and maps a:B→V,b:B→W,
intrinsic ambient Tor is Tor_q^G of the right graph
coefficient followed by the left graph coefficient.
Both carriers are V⊗K W with their respective G-actions,
at height max(k,r,v,w,im). -/
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

/-- For x∈V, the intrinsic V-multiplication operator
on ambient Tor equals multiplication by
(x⊗1_W)⊗1_B in G=(V⊗K W)⊗K B.
This is an equality before any flatness comparison. -/
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

/-- For y∈W, the intrinsic W-multiplication operator
on ambient Tor equals multiplication by
(1_V⊗y)⊗1_B in the intrinsic ambient ring G. -/
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

/-- For c∈B, the intrinsic ambient Tor scalar action satisfies
(1_(V⊗W)⊗c)•z=((a(c)⊗1_W)⊗1_B)•z.
The equality uses the graph coefficient action induced by a. -/
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

/-- If V,W are flat over K, the intrinsic ambient Tor
carries its canonical T=V⊗B W action, and
g•z=σ_G(g)•_T z for g∈G.
The maps a,b specify the B-actions on the two coefficients. -/
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

/-- If V,W are flat over K, the G-action on intrinsic
ambient Tor and the canonical T-action are compatible
through σ_G:G→T. They give the scalar tower G→T acting
on the same Tor carrier. -/
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

/-- For p∈Spec(T) and S=(A⊗K B)⊗K C, put q_S=σ_S⁻¹(p).
The local standard ambient Tor is Tor_q^(S_(q_S)) of
the two original ambient coefficients localized at q_S,
in the same order. Its carrier height includes every
ring, coefficient and chosen additional world. -/
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

/-- If A,C are flat over K, the standard ambient Tor
has compatible actions of S and T through σ_S:S→T.
This is the scalar tower of its ambient module action
and its canonical balanced support action. -/
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

/-- Assume A,C flat over K and i_V,i_W surjective.
For p∈Spec(T) and q≥0,
length_(S_(σ_S⁻¹p))(Tor_std,p,q)=
length_(T_p)((Tor_q^B(V,W))_p).
The coefficient maps determine the B-actions, and both
finite and infinite module lengths are allowed. -/
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

/-- Assume A,C flat over K and i_V,i_W surjective.
For every q≥0, the support of standard ambient Tor in Spec(S)
is the image of Supp_T(Tor_q^B(V,W)) under
Spec(T)→Spec(S), p↦σ_S⁻¹(p).
This is an image under the prime pullback map. -/
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

/-- For p∈Spec(T), T=V⊗B W, put q_G=σ_G⁻¹(p).
The intrinsic local object is Tor_q^(G_(q_G)) of the
localized right and left graph coefficients in that order.
Here G=(V⊗K W)⊗K B and the B-actions come from a,b. -/
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

/-- If V,W are flat over K, then for p∈Spec(T) and q≥0,
length_(G_(σ_G⁻¹p))(Tor_intrinsic,p,q)=
length_(T_p)((Tor_q^B(V,W))_p).
The intrinsic support map is always surjective,
and infinite lengths are included. -/
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

/-- If V,W are flat over K, the support of intrinsic
ambient Tor in Spec(G) is the image of
Supp_T(Tor_q^B(V,W)) under p↦σ_G⁻¹(p).
No extra surjectivity hypothesis is needed for σ_G. -/
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

/-- For a field K, surjective coefficient maps
i_V:A⊗K B→V and i_W:B⊗K C→W, and p∈Spec(T),
the standard and intrinsic local ambient Tor have equal
module length in every degree q≥0.
The two local rings are S_(σ_S⁻¹p) and G_(σ_G⁻¹p),
and the common carrier height is max(k,a,b,c,v,w,m). -/
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

/-- In the field case with i_V,i_W surjective and p∈Spec(T),
assume standard local Tor has finite length for every j<cutoff
and is zero for every j≥cutoff.
Then intrinsic local Tor has the same two properties, and
the integer sums ∑_(j<cutoff)(−1)^j length(Tor_std,j)
and ∑_(j<cutoff)(−1)^j length(Tor_intrinsic,j) agree.
The finite-length and cutoff hypotheses are explicit premises. -/
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
