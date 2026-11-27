/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.IsGaloisGroup.IntegrallyClosed
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.GCDMonoid.Nat

/-- Consumer with the original binders: the fixed ring of a Galois group
action on an integrally closed domain is integrally closed. -/
example (G : Type*) [Group G] {A B : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
    [MulSemiringAction G B] [IsGaloisGroup G A B] [IsIntegrallyClosed B] :
    IsIntegrallyClosed A :=
  IsGaloisGroup.isIntegrallyClosed_of_isIntegrallyClosed (A := A) (B := B) G

/-- The same consumer in a higher universe for the acting group. -/
example (G : Type 1) [Group G] {A B : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
    [MulSemiringAction G B] [IsGaloisGroup G A B] [IsIntegrallyClosed B] :
    IsIntegrallyClosed A :=
  IsGaloisGroup.isIntegrallyClosed_of_isIntegrallyClosed (A := A) (B := B) G

/-- The general form needs no Galois-group structure: an action that commutes
with `A` and whose fixed elements come from `A` is enough. -/
example (G : Type*) [Group G] {A B : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
    [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
    [IsIntegrallyClosed B] : IsIntegrallyClosed A :=
  Algebra.IsInvariant.isIntegrallyClosed_of_isIntegrallyClosed (A := A) (B := B) G

/-- The trivial action of a two-element group on `ℤ`, which is not faithful. -/
private instance trivialAction : MulSemiringAction (Multiplicative (ZMod 2)) ℤ where
  smul _ n := n
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

/-- Every integer is fixed by the trivial action and comes from `ℤ`, so `ℤ` is the
invariant ring. -/
private instance : Algebra.IsInvariant ℤ ℤ (Multiplicative (ZMod 2)) :=
  ⟨fun b _ => ⟨b, rfl⟩⟩

/-- The trivial action is not faithful, so it carries no Galois-group structure,
yet the general form applies to it. -/
example : ¬ IsGaloisGroup (Multiplicative (ZMod 2)) ℤ ℤ ∧ IsIntegrallyClosed ℤ :=
  ⟨fun h => absurd (h.faithful.eq_of_smul_eq_smul (m₁ := .ofAdd 1) (m₂ := 1) fun _ => rfl)
      (by decide),
    Algebra.IsInvariant.isIntegrallyClosed_of_isIntegrallyClosed (A := ℤ) (B := ℤ)
      (Multiplicative (ZMod 2))⟩
