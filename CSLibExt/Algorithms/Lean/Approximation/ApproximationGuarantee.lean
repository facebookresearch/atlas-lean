/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Classes
public import Mathlib.Algebra.BigOperators.Expect

/-!
# Approximation algorithms and approximation ratios

Following Williamson and Shmoys, *The Design of Approximation Algorithms* (2011),
§1.1, Definition 1.1, we use an upper bound on the cost for minimization and a
lower bound on the value for maximization. We include exact optimization at
ratio `1`. For the expected-value variant (cf. Theorems 1.17 and 5.1), we use
the finite random tape of `Cslib.Complexity.Classes.BPP`, but require feasibility
on every tape and average the objective rather than counting successes.

We reuse `Cslib.Complexity.Classes.OptProblem` as data for either direction:
instances and solutions are bitstrings, values are nonnegative rationals, and
the feasible set is nonempty and finite by the length bound. Comparing with
every feasible value is therefore equivalent to comparing with the attained
optimum. This formulation also works when the optimum is zero. Ratios may be
real; they and the objective comparisons are specifications, not operations
performed by the solver. No `IsNPO` hypothesis is imposed here: certification of
a solver is separate from polynomial-time evaluation of the problem data.

`Cslib.Complexity.Classes.IsPTAS` already expresses a maximization scheme for
NPO problems using `ApproxAt` and unary precision. The bridge below compares
its fixed-precision guarantee to the deterministic maximization predicate at
positive rational thresholds (`k ≥ 2` for the PTAS schedule `1 - 1/k`).
-/

@[expose] public section

namespace CSLibExt.Algorithms.Approximation

open Cslib.Complexity.Classes (OptProblem ApproxAt)
open MetaMathlibExt.ComplexityTheory (IsPolyTime)
open scoped BigOperators

/-- A deterministic `α`-approximation for minimization runs in polynomial time, returns a
feasible solution on every instance, and has cost at most `α` times the minimum cost.
Here `1 ≤ α`. -/
def IsMinApproximation (P : OptProblem) (A : List Bool → List Bool) (α : ℝ) : Prop :=
  IsPolyTime A ∧ 1 ≤ α ∧ ∀ x, P.feas x (A x) = true ∧
    ∀ s, P.feas x s = true → (P.val x (A x) : ℝ) ≤ α * (P.val x s : ℝ)

/-- A deterministic `α`-approximation for maximization runs in polynomial time, returns a
feasible solution on every instance, and has value at least `α` times the maximum value.
Here `0 < α ≤ 1`. -/
def IsMaxApproximation (P : OptProblem) (A : List Bool → List Bool) (α : ℝ) : Prop :=
  IsPolyTime A ∧ 0 < α ∧ α ≤ 1 ∧ ∀ x, P.feas x (A x) = true ∧
    ∀ s, P.feas x s = true → α * (P.val x s : ℝ) ≤ (P.val x (A x) : ℝ)

/-- The expected value of `A` on `x` with `m` independent fair bits: the uniform average over
all tapes, counting each tape separately even if some outputs coincide. When `m = 0` the
only tape is empty. This average is a specification, not a polynomial-time computation. -/
def expectedValue (P : OptProblem) (A : List Bool × List Bool → List Bool)
    (x : List Bool) (m : ℕ) : ℚ :=
  𝔼 r : Fin m → Bool, P.val x (A (x, List.ofFn r))

/-- A randomized `α`-approximation for minimization uses `p.eval x.length` independent fair
bits on instance `x`. Its solver is polynomial time on the encoded pair of the instance and
tape, is feasible on every such tape, and has expected cost at most `α` times the minimum cost.
The polynomial tape length bounds the cost of generating the bits as well. Here `1 ≤ α`. -/
def IsRandomizedMinApproximation (P : OptProblem) (p : Polynomial ℕ)
    (A : List Bool × List Bool → List Bool) (α : ℝ) : Prop :=
  IsPolyTime A ∧ 1 ≤ α ∧ ∀ x,
    (∀ r : Fin (p.eval x.length) → Bool, P.feas x (A (x, List.ofFn r)) = true) ∧
    ∀ s, P.feas x s = true → (expectedValue P A x (p.eval x.length) : ℝ) ≤ α * (P.val x s : ℝ)

/-- A randomized `α`-approximation for maximization uses `p.eval x.length` independent fair
bits on instance `x`. Its solver is polynomial time on the encoded pair of the instance and
tape, is feasible on every such tape, and has expected value at least `α` times the maximum value.
The polynomial tape length bounds the cost of generating the bits as well. Here `0 < α ≤ 1`. -/
def IsRandomizedMaxApproximation (P : OptProblem) (p : Polynomial ℕ)
    (A : List Bool × List Bool → List Bool) (α : ℝ) : Prop :=
  IsPolyTime A ∧ 0 < α ∧ α ≤ 1 ∧ ∀ x,
    (∀ r : Fin (p.eval x.length) → Bool, P.feas x (A (x, List.ofFn r)) = true) ∧
    ∀ s, P.feas x s = true → α * (P.val x s : ℝ) ≤ (expectedValue P A x (p.eval x.length) : ℝ)

/-- A positive maximization threshold `α` and the reciprocal factor `α⁻¹` give the same
comparison for a deterministic value or an expected value, including when `opt = 0`.
Only the approximation parameter is inverted, never the optimum. -/
theorem maxThreshold_iff_factor {α : ℝ} (hα : 0 < α) (opt value : ℝ) :
    (α ≤ 1 ∧ α * opt ≤ value) ↔ (1 ≤ α⁻¹ ∧ opt / α⁻¹ ≤ value) := by
  rw [one_le_inv₀ hα, div_inv_eq_mul, mul_comm opt α]

/-- At a fixed unary precision and a positive rational threshold at most `1`, `ApproxAt`
characterizes the deterministic maximization guarantee for the specialized solver, given
its polynomial-time witness. The canonical `ApproxAt` also allows the zero threshold. -/
theorem approxAt_iff_isMaxApproximation {P : OptProblem} {A : List Bool × List Bool → List Bool}
    {k : ℕ} {α : ℚ} (hA : IsPolyTime (fun x => A (x, List.replicate k true)))
    (hpos : 0 < α) (hle : α ≤ 1) :
    ApproxAt P A k α ↔ IsMaxApproximation P (fun x => A (x, List.replicate k true)) (α : ℝ) := by
  constructor
  · intro h
    refine ⟨hA, by exact_mod_cast hpos, by exact_mod_cast hle, fun x => ⟨?_, ?_⟩⟩
    · obtain ⟨s, hs⟩ := P.feas_nonempty x
      exact (h x s hs).2
    · intro s hs
      exact_mod_cast (h x s hs).1
  · intro h x s hs
    refine ⟨?_, (h.2.2.2 x).1⟩
    exact_mod_cast (h.2.2.2 x).2 s hs

end CSLibExt.Algorithms.Approximation
