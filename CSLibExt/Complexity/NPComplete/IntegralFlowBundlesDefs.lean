/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTEGRAL FLOW WITH BUNDLES: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND36] INTEGRAL FLOW WITH
BUNDLES;
S. Sahni, "Computationally related problems", SIAM Journal on Computing 3 (1974),
262-279, doi:10.1137/0203021 (Problem N(iv), Theorem 2.2).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Fintype.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntegralFlowBundles

/-- An instance: vertex count `n` (vertices `0, ..., n - 1`), the arcs `(u, v)`, `s`, `t`, the
bundles `(I_j, c_j)` (a list of arcs and its capacity), and the requirement `R`. -/
abbrev IntegralFlowBundlesInstance :=
  ℕ × List (ℕ × ℕ) × ℕ × ℕ × List (List (ℕ × ℕ) × ℕ) × ℕ

/-- Well-formedness of an instance: the arcs describe a directed graph on `0, ..., n - 1`
(endpoints in range, no self-loops, no repeated arcs), `s` and `t` are vertices, every bundle
consists of arcs and has a positive capacity, the bundles cover the arcs
(`⋃_j I_j = A`), and the requirement `R` is positive. -/
def WellFormed (i : IntegralFlowBundlesInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ a ∈ i.2.1, a.1 < i.1 ∧ a.2 < i.1 ∧ a.1 ≠ a.2) ∧
    i.2.2.1 < i.1 ∧ i.2.2.2.1 < i.1 ∧
    (∀ b ∈ i.2.2.2.2.1, (∀ a ∈ b.1, a ∈ i.2.1) ∧ 0 < b.2) ∧
    (∀ a ∈ i.2.1, ∃ b ∈ i.2.2.2.2.1, a ∈ b.1) ∧
    0 < i.2.2.2.2.2

/-- The flow `∑_{a ∈ I} f(a)` on the arcs of the bundle `I`. -/
def bundleFlow {n : ℕ} (I : List (ℕ × ℕ)) (f : Fin n → Fin n → ℕ) : ℕ :=
  ∑ e ∈ Finset.univ.filter (fun e : Fin n × Fin n => ((e.1 : ℕ), (e.2 : ℕ)) ∈ I), f e.1 e.2

/-- There is an integral flow `f` on the arcs, with flow at most `c_j` on each bundle `I_j`,
conserved at every vertex other than `s` and `t`, whose net flow into `t` is at least `R`. -/
def IntegralFlowBundlesFeasible (i : IntegralFlowBundlesInstance) : Prop :=
  ∃ (hs : i.2.2.1 < i.1) (ht : i.2.2.2.1 < i.1) (f : Fin i.1 → Fin i.1 → ℕ),
    (∀ u v : Fin i.1, ((u : ℕ), (v : ℕ)) ∉ i.2.1 → f u v = 0) ∧
      (∀ b ∈ i.2.2.2.2.1, bundleFlow b.1 f ≤ b.2) ∧
      (∀ v : Fin i.1, v ≠ ⟨i.2.2.1, hs⟩ → v ≠ ⟨i.2.2.2.1, ht⟩ →
        ∑ u, f u v = ∑ w, f v w) ∧
      (i.2.2.2.2.2 : ℤ) ≤ (∑ u, (f u ⟨i.2.2.2.1, ht⟩ : ℤ)) - ∑ w, (f ⟨i.2.2.2.1, ht⟩ w : ℤ)

open Classical in
/-- INTEGRAL FLOW WITH BUNDLES as a decision problem over bitstrings. -/
noncomputable def integralFlowBundlesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntegralFlowBundlesInstance) x with
  | some i => decide (WellFormed i ∧ IntegralFlowBundlesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IntegralFlowBundles
