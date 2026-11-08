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

/-- The `±1` value encoded by a bit. -/
def signVal (b : Fin 2) : ℤ := if b = 0 then -1 else 1

/-- An `n × t` sign matrix has pairwise orthogonal rows. Sign matrices
are encoded by `Fin 2` entries to keep the type finite. -/
def IsPartialHadamard {n t : ℕ} (M : Fin n → Fin t → Fin 2) : Prop :=
  ∀ i i' : Fin n, i ≠ i' →
    ∑ j : Fin t, signVal (M i j) * signVal (M i' j) = 0

noncomputable instance {n t : ℕ} : DecidablePred (IsPartialHadamard (n := n) (t := t)) :=
  fun _ => Classical.propDecidable _

noncomputable instance {n t : ℕ} :
    Fintype { M : Fin n → Fin t → Fin 2 // IsPartialHadamard M } :=
  Subtype.fintype _

/-- `N_{n,t}`: the number of `n × t` partial Hadamard matrices. -/
noncomputable def partialHadamardCount (n t : ℕ) : ℕ :=
  Fintype.card { M : Fin n → Fin t → Fin 2 // IsPartialHadamard M }

theorem partialHadamardCount_le (n t : ℕ) :
    partialHadamardCount n t ≤ 2 ^ (n * t) := by
  refine (Fintype.card_subtype_le _).trans_eq ?_
  simp only [Fintype.card_fun, Fintype.card_fin]
  rw [← pow_mul, Nat.mul_comm]

/-- At width zero the empty row conditions are vacuous, leaving exactly
the empty matrix. -/
theorem partialHadamardCount_zero_width (n : ℕ) :
    partialHadamardCount n 0 = 1 := by
  rw [partialHadamardCount, Fintype.card_eq_one_iff]
  refine ⟨⟨0, fun i i' _ => by simp⟩, ?_⟩
  rintro ⟨M, -⟩
  apply Subtype.ext
  funext i j
  exact j.elim0

/-- The de Launey--Levin leading term
`A_{n,4t} = 2^{4nt + (n-1)^2} (8πt)^{-n(n-1)/4}` as a real number
(the subtracted exponent is formed in `ℕ` before casting). -/
noncomputable def leadingTerm (n t : ℕ) : ℝ :=
  (2 : ℝ) ^ (4 * n * t + (n - 1) ^ 2) *
    (8 * Real.pi * t) ^ (-((n * (n - 1) : ℝ) / 4))

theorem leadingTerm_pos {n t : ℕ} (ht : 0 < t) : 0 < leadingTerm n t := by
  rw [leadingTerm]
  positivity

/-- Exponent `α` is admissible for the leading term when, along every
sequence of row counts `n ≥ 2` and quarter-widths `t` with
`t / n ^ α → ∞`, the count is asymptotic to the leading term. The
catalogue's `C_{23c}` allows unspecified corrected formulas below the
cubic scale; this predicate is its precise leading-term specialization,
whose exact threshold the source records as `3`. -/
def IsLeadingAdmissible (α : ℝ) : Prop :=
  ∀ (n t : ℕ → ℕ), (∀ k : ℕ, 2 ≤ n k) →
    Tendsto (fun k : ℕ => (t k : ℝ) / (n k : ℝ) ^ α) atTop atTop →
    Tendsto (fun k : ℕ =>
      (partialHadamardCount (n k) (4 * t k) : ℝ) / leadingTerm (n k) (t k))
      atTop (nhds 1)

/-- The leading-term counting exponent: the infimum of admissible
exponents `α ≥ 1`, totalized by real `sInf`. This is not asserted to
equal the catalogue's `C_{23c}`, which permits corrected asymptotic
formulas; see the module scope note in the repository copy. -/
noncomputable def leadingTermExponent : ℝ :=
  sInf { α : ℝ | 1 ≤ α ∧ IsLeadingAdmissible α }

end MathlibExt.Combinatorics.PartialHadamard
