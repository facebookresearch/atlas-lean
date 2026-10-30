/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.ZMod
public import MathlibExt.Algebra.Polynomial.SeparableExpand

/-!
# Tests for irreducible polynomials as expansions of separable irreducibles

These examples exercise the three public theorems of
`MathlibExt.Algebra.Polynomial.SeparableExpand` (Corollary 4.5 of ATLAS
`NumberTheoryI`): existence and uniqueness generically, and the combined
statement on `X` over `ℚ` (characteristic zero) and over `ZMod 2`
(positive characteristic), where the unique expansion is the trivial one.
-/

@[expose] public section

open Polynomial

variable {K : Type*} [Field K]

/-- The existence theorem applies generically. -/
example {f : K[X]} (hf : Irreducible f) :
    ∃ (n : ℕ) (g : K[X]),
      Irreducible g ∧ g.Separable ∧
        expand K ((ringChar K) ^ n) g = f :=
  exists_irreducible_separable_expand_eq hf

/-- The uniqueness theorem applies generically. -/
example {f : K[X]} (hf : Irreducible f) {n₁ n₂ : ℕ} {g₁ g₂ : K[X]}
    (h₁ : Irreducible g₁ ∧ g₁.Separable ∧
      expand K ((ringChar K) ^ n₁) g₁ = f)
    (h₂ : Irreducible g₂ ∧ g₂.Separable ∧
      expand K ((ringChar K) ^ n₂) g₂ = f) :
    n₁ = n₂ ∧ g₁ = g₂ :=
  unique_irreducible_separable_expand_eq hf h₁ h₂

/-- Over `ℚ`, the unique expansion of `X` is the trivial one. -/
example :
    ∃ (n : ℕ) (g : ℚ[X]),
      (Irreducible g ∧ g.Separable ∧
        expand ℚ ((ringChar ℚ) ^ n) g = X) ∧
        ∀ (n' : ℕ) (g' : ℚ[X]),
          Irreducible g' ∧ g'.Separable ∧
            expand ℚ ((ringChar ℚ) ^ n') g' = X →
              n' = n ∧ g' = g := by
  obtain ⟨n, g, hg, huniq⟩ :=
    exists_unique_irreducible_separable_expand_eq (f := (X : ℚ[X]))
      irreducible_X
  refine ⟨n, g, hg, huniq⟩

/-- Over `ℚ`, the unique expansion of `X - 1` is the trivial one. -/
example :
    ∃ (n : ℕ) (g : ℚ[X]),
      (Irreducible g ∧ g.Separable ∧
        expand ℚ ((ringChar ℚ) ^ n) g = X - C 1) ∧
        ∀ (n' : ℕ) (g' : ℚ[X]),
          Irreducible g' ∧ g'.Separable ∧
            expand ℚ ((ringChar ℚ) ^ n') g' = X - C 1 →
              n' = n ∧ g' = g :=
  exists_unique_irreducible_separable_expand_eq (irreducible_X_sub_C 1)

/-- Over `ZMod 2`, the unique expansion of `X` is the trivial one. -/
example :
    ∃ (n : ℕ) (g : (ZMod 2)[X]),
      (Irreducible g ∧ g.Separable ∧
        expand (ZMod 2) ((ringChar (ZMod 2)) ^ n) g = X) ∧
        ∀ (n' : ℕ) (g' : (ZMod 2)[X]),
          Irreducible g' ∧ g'.Separable ∧
            expand (ZMod 2) ((ringChar (ZMod 2)) ^ n') g' = X →
              n' = n ∧ g' = g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, g, hg, huniq⟩ :=
    exists_unique_irreducible_separable_expand_eq
      (f := (X : (ZMod 2)[X]))
      (irreducible_X : Irreducible (X : (ZMod 2)[X]))
  refine ⟨n, g, hg, huniq⟩
