/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Subpolynomial decay of minimum sign-matrix condition numbers
-/
module

public import MathlibExt.LinearAlgebra.Matrix.SignConditionNumber
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Data.EReal.Basic
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix

@[expose] public section

open Asymptotics Filter

namespace Matrix.SignConditionNumber

/-- A nonnegative sequence grows slower than every positive power. -/
def IsSubpolynomial (f : ℕ → NNReal) : Prop :=
  ∀ ε : ℝ, 0 < ε → IsLittleO atTop (fun n : ℕ => (f n : ℝ))
    (fun n : ℕ => Real.rpow (n : ℝ) ε)

/-- One fixed subpolynomial sequence gives the exact equality at every
positive order. -/
def IsAdmissibleExponent (α : ℝ) : Prop :=
  ∃ f : ℕ → NNReal, IsSubpolynomial f ∧
    ∀ (n : ℕ) (hn : 0 < n), minimumConditionNumber ⟨n, hn⟩ =
      1 + (f n : ENNReal) / ENNReal.ofReal (Real.rpow (n : ℝ) α)

/-- Supremal admissible exponent, without assuming that a maximum is attained. -/
noncomputable def decayExponent : EReal :=
  sSup ((fun α : ℝ => (α : EReal)) '' {α : ℝ | IsAdmissibleExponent α})

/-- Canonical Hadamard existence at every order divisible by four. -/
def HadamardHypothesis : Prop :=
  ∀ n : ℕ, n % 4 = 0 → ∃ M : Matrix (Fin n) (Fin n) ℤ, Matrix.IsHadamard M

/-- A real symmetric conference matrix of nontrivial order, with zero diagonal,
sign off-diagonal entries, and the exact Gram equation. -/
def IsSymmetricConference {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  2 ≤ n ∧ C.transpose = C ∧ (∀ i, C i i = 0) ∧
    (∀ i j, i ≠ j → C i j = 1 ∨ C i j = -1) ∧
    C * C.transpose = ((n : ℝ) - 1) • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- Adding the identity to an actual conference matrix gives an actual sign matrix. -/
theorem IsSymmetricConference.exists_realize_add_one {n : ℕ}
    {C : Matrix (Fin n) (Fin n) ℝ} (hC : IsSymmetricConference C) :
    ∃ A : SignMatrix n, A.realize = C + 1 := by
  apply (exists_realize_iff (C + 1)).mpr
  intro i j
  by_cases hij : i = j
  · subst j
    exact Or.inl (by simp [hC.2.2.1 i])
  · simpa [Matrix.add_apply, Matrix.one_apply, hij] using hC.2.2.2.1 i j hij

end Matrix.SignConditionNumber
