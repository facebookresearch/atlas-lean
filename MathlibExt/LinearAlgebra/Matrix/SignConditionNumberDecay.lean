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

/-- **Subpolynomial sequences.** A sequence $f \colon \mathbb{N} \to [0, \infty)$ is subpolynomial
when for every real $\varepsilon > 0$ we have $f(n) = o(n^{\varepsilon})$ as $n \to \infty$. -/
def IsSubpolynomial (f : ℕ → NNReal) : Prop :=
  ∀ ε : ℝ, 0 < ε → IsLittleO atTop (fun n : ℕ => (f n : ℝ))
    (fun n : ℕ => Real.rpow (n : ℝ) ε)

/-- **Admissible decay exponents.** A real number $\alpha$ is an admissible exponent when there is a
subpolynomial sequence $f \colon \mathbb{N} \to [0, \infty)$ such that for every positive integer
$n$ the minimum condition number $\kappa_n$ of the real $n \times n$ sign matrices satisfies
$\kappa_n = 1 + f(n) / n^{\alpha}$, as an equality in $[0, \infty]$. -/
def IsAdmissibleExponent (α : ℝ) : Prop :=
  ∃ f : ℕ → NNReal, IsSubpolynomial f ∧
    ∀ (n : ℕ) (hn : 0 < n), minimumConditionNumber ⟨n, hn⟩ =
      1 + (f n : ENNReal) / ENNReal.ofReal (Real.rpow (n : ℝ) α)

/-- **Decay exponent of minimum sign-matrix condition numbers.** The decay exponent is the
supremum, taken in the extended reals $[-\infty, \infty]$, of the set of admissible exponents
$\alpha \in \mathbb{R}$.

The supremum need not be attained; it is $-\infty$ when no exponent is admissible. -/
noncomputable def decayExponent : EReal :=
  sSup ((fun α : ℝ => (α : EReal)) '' {α : ℝ | IsAdmissibleExponent α})

/-- **Hadamard hypothesis.** The Hadamard hypothesis is the proposition that for every natural
number $n$ divisible by $4$ there is an $n \times n$ Hadamard matrix with integer entries, that is,
an integer matrix $H$ with all entries $\pm 1$ such that
$H H^{\mathsf{T}} = H^{\mathsf{T}} H = n I$.

This is the Hadamard conjecture, stated as a proposition to be used as a hypothesis. -/
def HadamardHypothesis : Prop :=
  ∀ n : ℕ, n % 4 = 0 → ∃ M : Matrix (Fin n) (Fin n) ℤ, Matrix.IsHadamard M

/-- **Symmetric conference matrices.** A real $n \times n$ matrix $C$ is a symmetric conference
matrix when $n \ge 2$, $C^{\mathsf{T}} = C$, every diagonal entry of $C$ is $0$, every off-diagonal
entry of $C$ is $1$ or $-1$, and $C C^{\mathsf{T}} = (n - 1) I$, where $I$ is the identity
matrix. -/
def IsSymmetricConference {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  2 ≤ n ∧ C.transpose = C ∧ (∀ i, C i i = 0) ∧
    (∀ i j, i ≠ j → C i j = 1 ∨ C i j = -1) ∧
    C * C.transpose = ((n : ℝ) - 1) • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- **Adding the identity to a symmetric conference matrix gives a sign matrix.** If $C$ is a real
$n \times n$ symmetric conference matrix and $I$ is the $n \times n$ identity matrix, then there is
a Boolean $n \times n$ matrix whose realization as a real sign matrix equals $C + I$. -/
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
