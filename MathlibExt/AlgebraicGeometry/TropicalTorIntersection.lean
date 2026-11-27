/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.TropicalCycleIntersections
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Actual local Tor coefficients of tropical intersections

Components are minimal primes over the actual sum of the two ideals in the
ambient quotient ring. The modules are their actual local quotient modules.
The coefficient is the alternating sum of native Tor lengths, cut off at the
least actual vanishing bound. Degree zero is constructed from Mathlib's
derived-to-tensor map and its two-quotient tensor equivalence.

References: Osserman--Payne, 1007.1314v3, section 2.5, Theorem 5.1.1 and
Corollary 5.1.3; Fulton, *Intersection Theory*, sections 7.1 and 8.2.
Native Tor: Kim Morrison (2021), quotient tensor: Mathlib contributors,
length: Mathlib contributors, depth: Nailin Guan (2025), all Apache 2.0 at
56a005855ea17e0b0958f73ec801ae140b0a1679. Ordinary Tor balancing and
local intersection results are source integration from AxiomMath/Stacks
c496df0d9beea9deaeabcea8492605f9a0a2313b, RingTheory/Tor and Chow,
Apache 2.0; they are not new tropical comparison assumptions.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.TropicalTorIntersection

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct BigOperators

variable (R : Type) [CommRing R]

def torModule (I J : Ideal R) (q : ℕ) : ModuleCat R :=
  ((Tor (ModuleCat R) q).obj (ModuleCat.of R (R ⧸ I))).obj (ModuleCat.of R (R ⧸ J))

/-- This is the native tensor-quotient map, including its multiplication normalization. -/
def tensorIntersectionEquiv (I J : Ideal R) :
    (R ⧸ I) ⊗[R] (R ⧸ J) ≃ₗ[R] R ⧸ (I ⊔ J) :=
  (Ideal.quotMapEquivTensorQuot (R ⧸ I) (I := J)).symm.restrictScalars R |>.trans
    (DoubleQuot.quotQuotEquivQuotSupₐ R I J).toLinearEquiv

def torZeroIso (I J : Ideal R) :
    torModule R I J 0 ≅ ModuleCat.of R (R ⧸ (I ⊔ J)) :=
  (((tensoringLeft (ModuleCat R)).obj (ModuleCat.of R (R ⧸ I))).leftDerivedZeroIsoSelf.app
    (ModuleCat.of R (R ⧸ J))) ≪≫ (tensorIntersectionEquiv R I J).toModuleIso

structure FiniteTor (I J : Ideal R) : Prop where
  finite_length : ∀ q, Module.length R (torModule R I J q) ≠ ⊤
  bounded : ∃ b : ℕ, ∀ q, b < q → IsZero (torModule R I J q)

def torCoefficient {I J : Ideal R} (F : FiniteTor R I J) : ℤ := by
  classical
  exact ∑ q ∈ Finset.range (Nat.find F.bounded + 1),
    (-1 : ℤ) ^ q * (Module.length R (torModule R I J q)).toNat

def schemeCoefficient (I J : Ideal R) : ℕ∞ := Module.length R (R ⧸ (I ⊔ J))

def HigherTorZero (I J : Ideal R) : Prop :=
  ∀ q : ℕ, 0 < q → IsZero (torModule R I J q)

theorem torLength_zero {I J : Ideal R} {q : ℕ} (h : IsZero (torModule R I J q)) :
    Module.length R (torModule R I J q) = 0 :=
  Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp h)

theorem coefficient_of_higherTor_zero {I J : Ideal R} (F : FiniteTor R I J)
    (h : HigherTorZero R I J) :
    torCoefficient R F = (schemeCoefficient R I J).toNat := by
  classical
  have hlen : Module.length R (torModule R I J 0) = Module.length R (R ⧸ (I ⊔ J)) :=
    (torZeroIso R I J).toLinearEquiv.length_eq
  unfold torCoefficient
  rw [Finset.sum_eq_single 0]
  · simp [hlen, schemeCoefficient]
  · intro q _ hq
    simp [torLength_zero R (h q (Nat.pos_of_ne_zero hq))]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (Nat.zero_lt_succ _)))

variable (K : Type) [Field K] (n : ℕ)

abbrev CoordinateRing := ValuativeTropicalization.CoordinateRing K n

structure AmbientIdeals where
  ambient : Ideal (CoordinateRing K n)
  [ambient_prime : ambient.IsPrime]
  left : Ideal (CoordinateRing K n)
  right : Ideal (CoordinateRing K n)
  left_in_ambient : ambient ≤ left
  right_in_ambient : ambient ≤ right

attribute [instance] AmbientIdeals.ambient_prime

namespace AmbientIdeals

variable {K n} (P : AmbientIdeals K n)

abbrev ambientRing := CoordinateRing K n ⧸ P.ambient

def leftIdeal : Ideal P.ambientRing := P.left.map (Ideal.Quotient.mk P.ambient)
def rightIdeal : Ideal P.ambientRing := P.right.map (Ideal.Quotient.mk P.ambient)
def intersectionIdeal : Ideal P.ambientRing := P.leftIdeal ⊔ P.rightIdeal

abbrev Component := P.intersectionIdeal.minimalPrimes

variable (Z : P.Component)

instance componentPrime : Z.val.IsPrime := Z.property.isPrime

def componentPoint : PrimeSpectrum P.ambientRing := ⟨Z.val, inferInstance⟩

abbrev LocalRing := Localization.AtPrime Z.val

instance localCommRing : CommRing (P.LocalRing Z) := inferInstance

instance localRing : Ring (P.LocalRing Z) := (localCommRing P Z).toRing

instance localQuotient : HasQuotient (P.LocalRing Z) (Ideal (P.LocalRing Z)) :=
  @Ideal.instHasQuotient (P.LocalRing Z) (localRing P Z)

def localLeft : Ideal (P.LocalRing Z) :=
  P.leftIdeal.map (algebraMap P.ambientRing (P.LocalRing Z))
def localRight : Ideal (P.LocalRing Z) :=
  P.rightIdeal.map (algebraMap P.ambientRing (P.LocalRing Z))

abbrev LocalTor := FiniteTor (P.LocalRing Z) (P.localLeft Z) (P.localRight Z)

def componentCoefficient (F : P.LocalTor Z) : ℤ := torCoefficient (P.LocalRing Z) F

def componentSchemeCoefficient : ℕ∞ :=
  schemeCoefficient (P.LocalRing Z) (P.localLeft Z) (P.localRight Z)

/-- Depth equals the Krull dimension of the actual local quotient ring. -/
def CohenMacaulayLeft : Prop :=
  (IsLocalRing.depth (ModuleCat.of (P.LocalRing Z)
    ((P.LocalRing Z) ⧸ (P.localLeft Z))) : WithBot ℕ∞) =
      ringKrullDim ((P.LocalRing Z) ⧸ (P.localLeft Z))

def CohenMacaulayRight : Prop :=
  (IsLocalRing.depth (ModuleCat.of (P.LocalRing Z)
    ((P.LocalRing Z) ⧸ (P.localRight Z))) : WithBot ℕ∞) =
      ringKrullDim ((P.LocalRing Z) ⧸ (P.localRight Z))

end AmbientIdeals

end MathlibExt.AlgebraicGeometry.TropicalTorIntersection
