/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.AdicCompletion.RestrictScalars

@[expose] public section

universe u₁ u₂

/-- Consumer with the original binders: the restriction-of-scalars
equivalence of adic completions. -/
example {A : Type u₁} [CommRing A] (B : Type u₂) [CommRing B] [Algebra A B]
    (𝔭 : Ideal A) :
    Nonempty (AdicCompletion (𝔭.map (algebraMap A B)) B ≃ₗ[A]
      AdicCompletion 𝔭 B) :=
  ⟨AdicCompletion.restrictScalarsEquiv B 𝔭⟩

/-- Unfolding characterization: the equivalence sends the canonical image
of `b` to the canonical image of `b`, and its inverse does the same. -/
example {A : Type u₁} [CommRing A] (B : Type u₂) [CommRing B] [Algebra A B]
    (𝔭 : Ideal A) (b : B) :
    AdicCompletion.restrictScalarsEquiv B 𝔭
        (AdicCompletion.of (𝔭.map (algebraMap A B)) B b) =
      AdicCompletion.of 𝔭 B b ∧
    (AdicCompletion.restrictScalarsEquiv B 𝔭).symm
        (AdicCompletion.of 𝔭 B b) =
      AdicCompletion.of (𝔭.map (algebraMap A B)) B b :=
  ⟨AdicCompletion.restrictScalarsEquiv_of B 𝔭 b,
    AdicCompletion.restrictScalarsEquiv_symm_of B 𝔭 b⟩

/-- Nontrivial instance: for the `(2)`-adic completion along `ℤ → ℤ[X]`,
the element `X + 3` has the same image on both sides, checked levelwise. -/
example (b : Polynomial ℤ) (n : ℕ) :
    (AdicCompletion.restrictScalarsEquiv (Polynomial ℤ) (Ideal.span {(2 : ℤ)})
      (AdicCompletion.of
        ((Ideal.span {(2 : ℤ)}).map (algebraMap ℤ (Polynomial ℤ)))
        (Polynomial ℤ) b)).val n =
      (AdicCompletion.of (Ideal.span {(2 : ℤ)}) (Polynomial ℤ) b).val n :=
  congrFun (congrArg Subtype.val
    (AdicCompletion.restrictScalarsEquiv_of (Polynomial ℤ)
      (Ideal.span {(2 : ℤ)}) b)) n
