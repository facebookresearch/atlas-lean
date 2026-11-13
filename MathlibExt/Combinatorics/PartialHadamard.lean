/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.Combinatorics.PartialHadamard

open Filter Topology

/-!
# Partial Hadamard counting and the leading-term exponent

Sign matrices with pairwise orthogonal rows (encoded by `Fin 2`
entries), their count `N_{n,t}`, the de Launey--Levin leading term
`A_{n,4t}`, and the infimum of exponents at which `N ~ A` holds
uniformly.

Source: Optimization Problems, record 23c, "Asymptotic counting
exponent for partial Hadamard matrices", frozen at
teorth/optimizationproblems commit
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`; `constants/23c.md` SHA-256
`e8db544df42e4d8cc3de97b9dc9b0e0dba2d01b37d78442cfd5c615e5c2e6d99`.

Scope note (partial): the catalogue's `C_{23c}` allows arbitrary
corrected asymptotic formulas below the cubic scale, which is not a
precise predicate. This file formalizes the precise leading-term
specialization whose exact threshold the source records as `3`;
`leadingTermExponent` is not asserted to equal `C_{23c}`.
-/

/-- **Sign of a bit.** The sign of a bit $b \in \{0, 1\}$ is the integer $\sigma(b)$ given by
$\sigma(0) = -1$ and $\sigma(1) = 1$. -/
def signVal (b : Fin 2) : ℤ := if b = 0 then -1 else 1

/-- **Partial Hadamard matrices.** Read a bit $b \in \{0, 1\}$ as the sign $\sigma(b)$, where
$\sigma(0) = -1$ and $\sigma(1) = 1$. An $n \times t$ matrix $M$ with entries in $\{0, 1\}$ is a
partial Hadamard matrix when its rows are pairwise orthogonal as sign vectors: for all distinct
rows $i \ne i'$, $\sum_{j < t} \sigma(M_{ij}) \sigma(M_{i'j}) = 0$. -/
def IsPartialHadamard {n t : ℕ} (M : Fin n → Fin t → Fin 2) : Prop :=
  ∀ i i' : Fin n, i ≠ i' →
    ∑ j : Fin t, signVal (M i j) * signVal (M i' j) = 0

noncomputable instance {n t : ℕ} : DecidablePred (IsPartialHadamard (n := n) (t := t)) :=
  fun _ => Classical.propDecidable _

noncomputable instance {n t : ℕ} :
    Fintype { M : Fin n → Fin t → Fin 2 // IsPartialHadamard M } :=
  Subtype.fintype _

/-- **Number of partial Hadamard matrices.** For natural numbers $n$ and $t$, $N_{n,t}$ is the
number of $n \times t$ partial Hadamard matrices, that is, of $n \times t$ matrices with entries in
$\{0, 1\}$ whose rows are pairwise orthogonal when each entry $0$ is read as the sign $-1$ and
each entry $1$ as the sign $1$. -/
noncomputable def partialHadamardCount (n t : ℕ) : ℕ :=
  Fintype.card { M : Fin n → Fin t → Fin 2 // IsPartialHadamard M }

theorem partialHadamardCount_le (n t : ℕ) :
    partialHadamardCount n t ≤ 2 ^ (n * t) := by
  refine (Fintype.card_subtype_le _).trans_eq ?_
  simp only [Fintype.card_fun, Fintype.card_fin]
  rw [← pow_mul, Nat.mul_comm]

/-- **Width-zero partial Hadamard count.** For every natural number $n$, the number $N_{n,0}$ of
$n \times 0$ partial Hadamard matrices is $1$: the orthogonality conditions are empty sums, so the
empty matrix is the only one. -/
theorem partialHadamardCount_zero_width (n : ℕ) :
    partialHadamardCount n 0 = 1 := by
  rw [partialHadamardCount, Fintype.card_eq_one_iff]
  refine ⟨⟨0, fun i i' _ => by simp⟩, ?_⟩
  rintro ⟨M, -⟩
  apply Subtype.ext
  funext i j
  exact j.elim0

/-- **De Launey–Levin leading term.** For natural numbers $n$ and $t$, the de Launey–Levin leading
term is the real number $A_{n,4t} = 2^{4nt + (n-1)^2} (8\pi t)^{-n(n-1)/4}$, where the power of
$8\pi t$ is the real power function and $n - 1$ in the exponent of $2$ is truncated subtraction of
natural numbers, so that $(n-1)^2 = 0$ when $n = 0$. -/
noncomputable def leadingTerm (n t : ℕ) : ℝ :=
  (2 : ℝ) ^ (4 * n * t + (n - 1) ^ 2) *
    (8 * Real.pi * t) ^ (-((n * (n - 1) : ℝ) / 4))

theorem leadingTerm_pos {n t : ℕ} (ht : 0 < t) : 0 < leadingTerm n t := by
  rw [leadingTerm]
  positivity

/-- **Admissible exponents for the partial Hadamard leading term.** For natural numbers $n$ and
$m$, let $N_{n,m}$ be the number of $n \times m$ partial Hadamard matrices, and for natural
numbers $n$ and $t$ let $A_{n,4t} = 2^{4nt + (n-1)^2} (8\pi t)^{-n(n-1)/4}$ be the de
Launey–Levin leading term. A real number $\alpha$ is admissible for the leading term when, for
all sequences $(n_k)$ and $(t_k)$ of natural numbers with $n_k \ge 2$ for every $k$ and
$t_k / n_k^{\alpha} \to \infty$ as $k \to \infty$, the ratio $N_{n_k, 4t_k} / A_{n_k, 4t_k}$
tends to $1$.

The catalogue constant $C_{23c}$ also allows corrected asymptotic formulas below the cubic scale;
this predicate is its precise leading-term specialization, whose exact threshold the source
records as $3$. -/
def IsLeadingAdmissible (α : ℝ) : Prop :=
  ∀ (n t : ℕ → ℕ), (∀ k : ℕ, 2 ≤ n k) →
    Tendsto (fun k : ℕ => (t k : ℝ) / (n k : ℝ) ^ α) atTop atTop →
    Tendsto (fun k : ℕ =>
      (partialHadamardCount (n k) (4 * t k) : ℝ) / leadingTerm (n k) (t k))
      atTop (nhds 1)

/-- **Leading-term counting exponent for partial Hadamard matrices.** For natural numbers $n$
and $m$, let $N_{n,m}$ be the number of $n \times m$ partial Hadamard matrices, and for natural
numbers $n$ and $t$ let $A_{n,4t} = 2^{4nt + (n-1)^2} (8\pi t)^{-n(n-1)/4}$ be the de
Launey–Levin leading term. Call a real number $\alpha$ admissible when
$N_{n_k, 4t_k} / A_{n_k, 4t_k} \to 1$ along all sequences $(n_k)$ and $(t_k)$ of natural numbers
with $n_k \ge 2$ for every $k$ and $t_k / n_k^{\alpha} \to \infty$. The leading-term counting
exponent is the infimum of the admissible $\alpha \ge 1$, and is $0$ if there is no such $\alpha$.

This exponent is not asserted to equal the catalogue constant $C_{23c}$, which also permits
corrected asymptotic formulas. -/
noncomputable def leadingTermExponent : ℝ :=
  sInf { α : ℝ | 1 ≤ α ∧ IsLeadingAdmissible α }

end MathlibExt.Combinatorics.PartialHadamard
