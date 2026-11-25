/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.RingTheory.Smooth.Basic

/-!
# Actual affine critical-function subquotients

For a closed presentation with ideal I, the critical-function numerator
is the inverse image of I Ω under the universal differential. Its
quotient by I² and its zero-on-reduction subquotient are k-modules, not
modules over the ambient algebra. Denominators are taken inside the
numerators; this implements the subquotient without assuming a chosen
quotient realization or a d-critical gluing theorem.

Critical loci use the ideal of the actual df coordinates in an actual
Kähler basis. The local Hessian is the iterated coordinate derivation.
The canonical reduction uses the radical of the zero ideal sheaf of the
native critical scheme.

Reference: Joyce, arXiv:1304.4508v3, Theorem 2.1, Definition 2.5 and
§2.4. The Hessian-normalized transition uses one half of the normal
Hessian, as in Proposition 2.25; it is a separate interface from this
local algebraic construction.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AffineCriticalFunctions

open CategoryTheory _root_.AlgebraicGeometry Module
open scoped TensorProduct

universe u

variable (k P : Type u) [CommRing k] [CommRing P] [Algebra k P]

/-- The literal ideal multiple I Ω inside the native differential module. -/
def idealDifferentials (I : Ideal P) : Submodule P Ω[P⁄k] :=
  I • (⊤ : Submodule P Ω[P⁄k])

/-- Functions whose universal differential vanishes modulo I Ω. -/
def criticalFunctions (I : Ideal P) : Submodule k P :=
  ((idealDifferentials k P I).restrictScalars k).comap
    (KaehlerDifferential.D k P).toLinearMap

/-- Critical functions which vanish on the reduced closed subscheme. -/
def zeroCriticalFunctions (I : Ideal P) : Submodule k P :=
  criticalFunctions k P I ⊓ I.radical.restrictScalars k

/-- The actual I² denominator inside the critical-function numerator. -/
def squareDenominator (I : Ideal P) : Submodule k (criticalFunctions k P I) :=
  ((I ^ 2).restrictScalars k).comap (criticalFunctions k P I).subtype

/-- The actual I² denominator inside the zero-on-reduction numerator. -/
def zeroSquareDenominator (I : Ideal P) : Submodule k (zeroCriticalFunctions k P I) :=
  ((I ^ 2).restrictScalars k).comap (zeroCriticalFunctions k P I).subtype

/-- The local S_X subquotient, with its actual coefficient-module structure. -/
abbrev localCriticalModule (I : Ideal P) :=
  (criticalFunctions k P I) ⧸ squareDenominator k P I

/-- The local S_X⁰ subquotient. No ambient-algebra module structure is asserted. -/
abbrev localZeroCriticalModule (I : Ideal P) :=
  (zeroCriticalFunctions k P I) ⧸ zeroSquareDenominator k P I

variable {k P}

@[simp]
theorem mem_criticalFunctions {I : Ideal P} {f : P} :
    f ∈ criticalFunctions k P I ↔
      KaehlerDifferential.D k P f ∈ idealDifferentials k P I := Iff.rfl

@[simp]
theorem mem_zeroCriticalFunctions {I : Ideal P} {f : P} :
    f ∈ zeroCriticalFunctions k P I ↔
      KaehlerDifferential.D k P f ∈ idealDifferentials k P I ∧ f ∈ I.radical := Iff.rfl

/-- I² lies in the numerator: the differential of a product of two
elements of I lies in I Ω, and I² vanishes on the reduction. Thus the
subquotient denominator is the full I², rather than a smaller relation. -/
theorem square_le_zeroCriticalFunctions (I : Ideal P) :
    (I ^ 2).restrictScalars k ≤ zeroCriticalFunctions k P I := by
  intro f hf
  apply mem_zeroCriticalFunctions.mpr
  constructor
  · change f ∈ I ^ 2 at hf
    rw [pow_two] at hf
    exact Submodule.mul_induction_on hf
      (fun a ha b hb => by
        rw [Derivation.leibniz]
        exact Submodule.add_mem _
          (Submodule.smul_mem_smul ha (Submodule.mem_top))
          (Submodule.smul_mem_smul hb (Submodule.mem_top)))
      (fun a b ha hb => by rw [map_add]; exact Submodule.add_mem _ ha hb)
  · exact Ideal.le_radical (Ideal.pow_le_self (by decide) hf)

/-- The actual class of a function satisfying the two local conditions. -/
def criticalClass (I : Ideal P) (f : P)
    (hd : KaehlerDifferential.D k P f ∈ idealDifferentials k P I)
    (hr : f ∈ I.radical) : localZeroCriticalModule k P I :=
  (zeroSquareDenominator k P I).mkQ ⟨f, hd, hr⟩

/-- A local function represents zero precisely when it lies in I². -/
theorem criticalClass_eq_zero_iff (I : Ideal P) (f : P)
    (hd : KaehlerDifferential.D k P f ∈ idealDifferentials k P I)
    (hr : f ∈ I.radical) :
    criticalClass I f hd hr = 0 ↔ f ∈ I ^ 2 := by
  change (zeroSquareDenominator k P I).mkQ
    (⟨f, (mem_zeroCriticalFunctions).mpr ⟨hd, hr⟩⟩ : zeroCriticalFunctions k P I) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl

/-- Coordinate functions whose universal differentials form an actual
finite basis. This keeps the generators needed for critical ideals and
Jacobian/Hessian comparisons. -/
structure DifferentialCoordinates (k P : Type u)
    [CommRing k] [CommRing P] [Algebra k P] (n : ℕ) where
  coordinate : Fin n → P
  basis : Basis (Fin n) P Ω[P⁄k]
  basis_eq : ∀ i, basis i = KaehlerDifferential.D k P (coordinate i)

/-- The native coordinate derivation induced by the universal differential. -/
def coordinateDerivation {n : ℕ} (E : DifferentialCoordinates k P n) (i : Fin n) :
    Derivation k P P :=
  (E.basis.coord i).compDer (KaehlerDifferential.D k P)

/-- The ideal of the actual section df in the specified differential basis. -/
def criticalIdeal {n : ℕ} (E : DifferentialCoordinates k P n) (f : P) : Ideal P :=
  Ideal.span (Set.range fun i : Fin n => coordinateDerivation E i f)

/-- The native affine critical locus, retaining its nilpotent structure. -/
def criticalScheme {n : ℕ} (E : DifferentialCoordinates k P n) (f : P) : Scheme.{u} :=
  Spec (CommRingCat.of (P ⧸ criticalIdeal E f))

/-- The literal reduced critical scheme from the native radical-zero ideal sheaf. -/
def reducedCriticalScheme {n : ℕ} (E : DifferentialCoordinates k P n) (f : P) : Scheme.{u} :=
  ((⊥ : (criticalScheme E f).IdealSheafData).radical).subscheme

/-- The native closed immersion of the reduction into the critical scheme. -/
def reductionMap {n : ℕ} (E : DifferentialCoordinates k P n) (f : P) :
    reducedCriticalScheme E f ⟶ criticalScheme E f :=
  ((⊥ : (criticalScheme E f).IdealSheafData).radical).subschemeι

/-- The actual coordinate Hessian before restriction to the critical locus. -/
def hessian {n : ℕ} (E : DifferentialCoordinates k P n) (f : P) : Matrix (Fin n) (Fin n) P :=
  fun i j => coordinateDerivation E i (coordinateDerivation E j f)

end MathlibExt.AlgebraicGeometry.AffineCriticalFunctions
