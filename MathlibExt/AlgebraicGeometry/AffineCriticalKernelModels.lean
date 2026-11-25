/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AffineCriticalFunctionMaps
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Critical-function kernels and their reduction maps

The derivative is a coefficient-linear map from the actual quotient by
I squared to the quotient of native Kähler differentials by I Ω. The
critical module is compared with its literal kernel. Reduction is the
actual quotient by the radical of I. These constructions apply to every
coefficient algebra, without choosing polynomial coordinates.

Reference: Joyce, arXiv:1304.4508v3, Theorem 2.1, equations (2.2)--(2.5).
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AffineCriticalKernelModels

open MathlibExt.AlgebraicGeometry.AffineCriticalFunctions
open MathlibExt.AlgebraicGeometry.AffineCriticalFunctionMaps

variable {k P : Type} [CommRing k] [CommRing P] [Algebra k P]

/-- The actual coefficient-module quotient O/I². -/
abbrev FunctionQuotient (I : Ideal P) := P ⧸ (I ^ 2).restrictScalars k

/-- The actual coefficient-module quotient Ω/IΩ. -/
abbrev DifferentialQuotient (I : Ideal P) :=
  Ω[P⁄k] ⧸ (idealDifferentials k P I).restrictScalars k

/-- The $k$-linear map $P/I^2 \to \Omega_{P/k}/I\,\Omega_{P/k}$ sending the class of $f$ to the
class of $df$, induced by the universal derivation $d : P \to \Omega_{P/k}$ (well defined since
$d(I^2) \subseteq I\,\Omega_{P/k}$). It is $k$-linear, and in general not $P$-linear. -/
def quotientDifferential (I : Ideal P) :
    FunctionQuotient (k := k) I →ₗ[k] DifferentialQuotient (k := k) I :=
  ((I ^ 2).restrictScalars k).liftQ
    (((idealDifferentials k P I).restrictScalars k).mkQ.comp
      (KaehlerDifferential.D k P).toLinearMap) (by
    intro f hf
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      ((square_le_zeroCriticalFunctions I hf).1))

/-- The kernel in the exact sequence (2.2). -/
abbrev CriticalKernel (I : Ideal P) :=
  LinearMap.ker (quotientDifferential (k := k) I)

/-- The literal map from the critical-function subquotient to O/I². -/
def criticalInclusion (I : Ideal P) :
    localCriticalModule k P I →ₗ[k] FunctionQuotient (k := k) I :=
  (squareDenominator k P I).liftQ
    (((I ^ 2).restrictScalars k).mkQ.comp (criticalFunctions k P I).subtype) (by
    intro f hf
    exact (Submodule.Quotient.mk_eq_zero _).mpr hf)

/-- The reduction target O/Irad retains the actual radical quotient. -/
abbrev ReducedFunctions (I : Ideal P) := P ⧸ I.radical.restrictScalars k

/-- The reduction map on critical-function classes. -/
def criticalReduction (I : Ideal P) :
    localCriticalModule k P I →ₗ[k] ReducedFunctions (k := k) I :=
  (squareDenominator k P I).liftQ
    ((I.radical.restrictScalars k).mkQ.comp (criticalFunctions k P I).subtype) (by
    intro f hf
    change (f : P) ∈ I ^ 2 at hf
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (square_le_zeroCriticalFunctions (k := k) I hf).2)

/-- The zero-on-reduction critical kernel in (2.5). -/
abbrev ZeroCriticalKernel (I : Ideal P) :=
  LinearMap.ker (criticalReduction (k := k) I)

@[simp]
theorem quotientDifferential_class (I : Ideal P) (f : P) :
    quotientDifferential (k := k) I (((I ^ 2).restrictScalars k).mkQ f) =
      ((idealDifferentials k P I).restrictScalars k).mkQ
        (KaehlerDifferential.D k P f) := rfl

@[simp]
theorem criticalReduction_class (I : Ideal P) (f : criticalFunctions k P I) :
    criticalReduction (k := k) I ((squareDenominator k P I).mkQ f) =
      (I.radical.restrictScalars k).mkQ f := rfl

section Maps

variable {Q : Type} [CommRing Q] [Algebra k Q]

/-- Actual algebra maps induce the map on the full critical numerator. -/
def numeratorMap (φ : P →ₐ[k] Q) {I : Ideal P} {J : Ideal Q}
    (h : I.map φ.toRingHom ≤ J) :
    criticalFunctions k P I →ₗ[k] criticalFunctions k Q J where
  toFun f := ⟨φ f, by
    rw [mem_criticalFunctions, ← differential_D]
    exact differential_ideal φ h f.property⟩
  map_add' f g := Subtype.ext (φ.map_add f g)
  map_smul' a f := Subtype.ext (φ.toLinearMap.map_smul a f)

theorem numeratorMap_square (φ : P →ₐ[k] Q) {I : Ideal P} {J : Ideal Q}
    (h : I.map φ.toRingHom ≤ J) :
    squareDenominator k P I ≤
      (squareDenominator k Q J).comap (numeratorMap φ h) := by
  intro f hf
  change (φ f : Q) ∈ J ^ 2
  have hm : (φ f : Q) ∈ (I ^ 2).map φ.toRingHom :=
    Ideal.mem_map_of_mem φ.toRingHom hf
  rw [Ideal.map_pow] at hm
  exact (pow_le_pow_left' h 2) hm

/-- The class map is fixed by the original algebra map on all representatives. -/
def localMap (φ : P →ₐ[k] Q) {I : Ideal P} {J : Ideal Q}
    (h : I.map φ.toRingHom ≤ J) :
    localCriticalModule k P I →ₗ[k] localCriticalModule k Q J :=
  Submodule.mapQ (squareDenominator k P I) (squareDenominator k Q J)
    (numeratorMap φ h) (numeratorMap_square φ h)

theorem localMap_class (φ : P →ₐ[k] Q) {I : Ideal P} {J : Ideal Q}
    (h : I.map φ.toRingHom ≤ J) (f : criticalFunctions k P I) :
    localMap φ h ((squareDenominator k P I).mkQ f) =
      (squareDenominator k Q J).mkQ (numeratorMap φ h f) := rfl

end Maps

end MathlibExt.AlgebraicGeometry.AffineCriticalKernelModels
