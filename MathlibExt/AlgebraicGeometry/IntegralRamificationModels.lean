/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.RepresentationTheory.Invariants

/-!
# Actual lower ramification groups on integral closures

The integer ring is the actual integral closure of the given discrete
valuation ring in its finite Galois extension. Integral automorphisms are
fixed by the original field automorphisms. The i-th lower group is the
kernel of their action on S / m_S^(i+1), with every quotient value fixed
by the literal reduction map.

Swan is the finite lower-group sum of the actual invariant-space
codimensions weighted by |G_i|/|G_0|. No numerical conductor or arbitrary
filtration is provided. Construction, eventual triviality and integrality
are separate source proof requests.

Reference: Serre, Local Fields, Chapter IV, Sections 1--2;
Saito, arXiv:1510.03018v4, Section 1.3.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.IntegralRamificationModels

open scoped BigOperators

variable (R K L : Type) [CommRing R] [domainR : IsDomain R]
  [dvrR : IsDiscreteValuationRing R]
  [Field K] [Field L] [Algebra R K] [fractionRK : IsFractionRing R K]
  [Algebra K L] [Algebra R L] [towerRKL : IsScalarTower R K L]
  [finiteKL : FiniteDimensional K L] [galoisKL : IsGalois K L]

abbrev Integers := integralClosure R L

include domainR dvrR fractionRK towerRKL finiteKL galoisKL in
/-- The action on the fixed actual integral closure, with its original field values. -/
structure IntegralAction where
  action : Gal(L/K) →* (Integers R L ≃+* Integers R L)
  normalized : ∀ (g : Gal(L/K)) (x : Integers R L),
    (action g x).val = g x.val

variable [IsDiscreteValuationRing (Integers R L)]

def ramificationIdeal (i : ℕ) : Ideal (Integers R L) :=
  (IsLocalRing.maximalIdeal (Integers R L)) ^ (i + 1)

abbrev RamificationQuotient (i : ℕ) := Integers R L ⧸ ramificationIdeal R L i

/-- Quotient actions are fixed on every actual integral element. -/
structure QuotientActions (A : IntegralAction R K L) where
  action : ∀ i : ℕ, Gal(L/K) →*
    (RamificationQuotient R L i ≃+* RamificationQuotient R L i)
  normalized : ∀ (i : ℕ) (g : Gal(L/K)) (x : Integers R L),
    action i g (Ideal.Quotient.mk (ramificationIdeal R L i) x) =
      Ideal.Quotient.mk (ramificationIdeal R L i) (A.action g x)

/-- The actual lower ramification subgroup, including inertia at i=0. -/
def lowerGroup {A : IntegralAction R K L} (Q : QuotientActions R K L A) (i : ℕ) :
    Subgroup Gal(L/K) := (Q.action i).ker

/-- A finite cut records eventual triviality of those exact groups. -/
structure FiniteCut {A : IntegralAction R K L} (Q : QuotientActions R K L A) where
  bound : ℕ
  trivial : ∀ i : ℕ, bound ≤ i → lowerGroup R K L Q i = ⊥

variable {κ V : Type*} [Field κ] [AddCommGroup V] [Module κ V]
  [finiteV : Module.Finite κ V]
  (ρ : Gal(L/K) →* Module.End κ V)

include finiteV in
/-- The codimension of the vectors fixed by `H`: the invariants of the restricted
representation. -/
def fixedCodimension (H : Subgroup Gal(L/K)) : ℕ :=
  Module.finrank κ V - Module.finrank κ (Representation.invariants (ρ.comp H.subtype))

include finiteV in
/-- The source Swan sum, preserving every positive lower ramification term. -/
def swan {A : IntegralAction R K L} (Q : QuotientActions R K L A)
    (N : FiniteCut R K L Q) : ℚ :=
  ∑ j ∈ Finset.range N.bound,
    (Nat.card (lowerGroup R K L Q (j + 1)) : ℚ) /
      (Nat.card (lowerGroup R K L Q 0) : ℚ) *
        (fixedCodimension K L ρ (lowerGroup R K L Q (j + 1)) : ℚ)

end MathlibExt.AlgebraicGeometry.IntegralRamificationModels
