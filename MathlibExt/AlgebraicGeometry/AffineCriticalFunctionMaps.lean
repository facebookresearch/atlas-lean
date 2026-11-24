/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AffineCriticalFunctions

/-!
# Fixed maps between affine critical-function subquotients

An actual algebra map carrying I into J induces the universal
differential map and the actual quotient map on critical function
classes. The maps are completed from native Kähler functoriality and
ideal operations. An ambient refinement cannot carry a freely supplied
map of S_X⁰ classes.

Reference: Joyce, arXiv:1304.4508v3, Theorem 2.1(ii), equation 2.3.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AffineCriticalFunctionMaps

open MathlibExt.AlgebraicGeometry.AffineCriticalFunctions

universe u

variable {k P Q : Type u} [CommRing k] [CommRing P] [CommRing Q]
  [Algebra k P] [Algebra k Q]

/-- The native Kähler differential map of the specified algebra map. -/
def differential (φ : P →ₐ[k] Q) : Ω[P⁄k] →ₗ[k] Ω[Q⁄k] := by
  letI : Algebra P Q := φ.toAlgebra
  letI : IsScalarTower k P Q := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  exact (KaehlerDifferential.map k k P Q).restrictScalars k

@[simp]
theorem differential_D (φ : P →ₐ[k] Q) (f : P) :
    differential φ (KaehlerDifferential.D k P f) = KaehlerDifferential.D k Q (φ f) := by
  let : Algebra P Q := φ.toAlgebra
  let : IsScalarTower k P Q := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  exact KaehlerDifferential.map_D k k P Q f

/-- The scalar compatibility fixes the base-changing differential map. -/
theorem differential_smul (φ : P →ₐ[k] Q) (a : P) (w : Ω[P⁄k]) :
    differential φ (a • w) = φ a • differential φ w := by
  let : Algebra P Q := φ.toAlgebra
  let : IsScalarTower k P Q := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  exact (KaehlerDifferential.map k k P Q).map_smul a w

/-- Ideal-preserving maps carry the actual I Ω into J Ω. -/
theorem differential_ideal (φ : P →ₐ[k] Q) {I : Ideal P} {J : Ideal Q}
    (h : I.map φ.toRingHom ≤ J) {w : Ω[P⁄k]}
    (hw : w ∈ idealDifferentials k P I) :
    differential φ w ∈ idealDifferentials k Q J := by
  exact Submodule.smul_induction_on hw
    (fun a ha w _ => by
      rw [differential_smul]
      exact Submodule.smul_mem_smul (h (Ideal.mem_map_of_mem φ.toRingHom ha))
        (Submodule.mem_top))
    (fun x y hx hy => by rw [map_add]; exact Submodule.add_mem _ hx hy)

/-- The computed coefficient-linear map of actual zero-critical numerators. -/
def numeratorMap (φ : P →ₐ[k] Q) {I : Ideal P} {J : Ideal Q}
    (h : I.map φ.toRingHom ≤ J) :
    zeroCriticalFunctions k P I →ₗ[k] zeroCriticalFunctions k Q J where
  toFun f := ⟨φ f, mem_zeroCriticalFunctions.mpr ⟨by
    rw [← differential_D]
    exact differential_ideal φ h ((mem_zeroCriticalFunctions).mp f.property).1,
    Ideal.radical_mono h (Ideal.map_radical_le φ.toRingHom
      (Ideal.mem_map_of_mem φ.toRingHom ((mem_zeroCriticalFunctions).mp f.property).2))⟩⟩
  map_add' f g := Subtype.ext (φ.map_add f g)
  map_smul' a f := Subtype.ext (φ.toLinearMap.map_smul a f)

/-- The actual quotient relations are preserved by the algebra map. -/
theorem numeratorMap_square (φ : P →ₐ[k] Q) {I : Ideal P} {J : Ideal Q}
    (h : I.map φ.toRingHom ≤ J) :
    zeroSquareDenominator k P I ≤
      (zeroSquareDenominator k Q J).comap (numeratorMap φ h) := by
  intro f hf
  change (φ f : Q) ∈ J ^ 2
  have hm : (φ f : Q) ∈ (I ^ 2).map φ.toRingHom :=
    Ideal.mem_map_of_mem φ.toRingHom hf
  rw [Ideal.map_pow] at hm
  exact (pow_le_pow_left' h 2) hm

/-- The literal quotient map of critical function classes. -/
def localZeroMap (φ : P →ₐ[k] Q) {I : Ideal P} {J : Ideal Q}
    (h : I.map φ.toRingHom ≤ J) :
    localZeroCriticalModule k P I →ₗ[k] localZeroCriticalModule k Q J :=
  Submodule.mapQ (zeroSquareDenominator k P I) (zeroSquareDenominator k Q J)
    (numeratorMap φ h) (numeratorMap_square φ h)

/-- The quotient map is fixed on every representative by the actual algebra map. -/
theorem localZeroMap_class (φ : P →ₐ[k] Q) {I : Ideal P} {J : Ideal Q}
    (h : I.map φ.toRingHom ≤ J) (f : P)
    (hd : KaehlerDifferential.D k P f ∈ idealDifferentials k P I)
    (hr : f ∈ I.radical) :
    localZeroMap φ h (criticalClass I f hd hr) =
      criticalClass J (φ f)
        (by rw [← differential_D]; exact differential_ideal φ h hd)
        (Ideal.radical_mono h (Ideal.map_radical_le φ.toRingHom
          (Ideal.mem_map_of_mem φ.toRingHom hr))) := by
  rfl

end MathlibExt.AlgebraicGeometry.AffineCriticalFunctionMaps
