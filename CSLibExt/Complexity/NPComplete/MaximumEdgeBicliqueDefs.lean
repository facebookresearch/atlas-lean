/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM EDGE BICLIQUE: definitions

Source:
R. Peeters, "The maximum edge biclique problem is NP-complete", Discrete Applied Mathematics
131(3) (2003), 651-654, doi:10.1016/S0166-218X(03)00333-0;
N. Gillis and F. Glineur, "Nonnegative factorization and the maximum edge biclique problem",
arXiv:0810.4225 (2008), Section 3.1 (the problem as stated here; its decision version "has been
shown to be NP-complete" by Peeters).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumEdgeBiclique

/-- An instance: the side sizes `p = |V₁|` and `q = |V₂|`, the edges `(a, b)` with `a < p` and
`b < q`, and the bound `K`. -/
abbrev MaximumEdgeBicliqueInstance := ℕ × ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: the edges are distinct pairs `(a, b)` with `a < p` and
`b < q`, and `K` is positive. -/
def WellFormed (i : MaximumEdgeBicliqueInstance) : Prop :=
  i.2.2.1.Nodup ∧ (∀ e ∈ i.2.2.1, e.1 < i.1 ∧ e.2 < i.2.1) ∧ 0 < i.2.2.2

/-- Some `A ⊆ V₁` and `B ⊆ V₂` with every pair of `A × B` an edge have `|A| · |B| ≥ K`. -/
def MaximumEdgeBicliqueFeasible (i : MaximumEdgeBicliqueInstance) : Prop :=
  ∃ (A : Finset (Fin i.1)) (B : Finset (Fin i.2.1)),
    (∀ a ∈ A, ∀ b ∈ B, ((a : ℕ), (b : ℕ)) ∈ i.2.2.1) ∧ i.2.2.2 ≤ A.card * B.card

open Classical in
/-- MAXIMUM EDGE BICLIQUE as a decision problem over bitstrings. -/
noncomputable def maximumEdgeBicliqueDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumEdgeBicliqueInstance) x with
  | some i => decide (WellFormed i ∧ MaximumEdgeBicliqueFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaximumEdgeBiclique
