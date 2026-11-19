/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Coprime automorphisms centralizing the centralizer of an element (Kourovka Notebook Problem 4.23)

Kourovka Notebook, Archive of Solved Problems, Problem 4.23 (G. Glauberman): let `G` be a finite
simple group, `τ` some element of prime order, and `α` an automorphism of `G` whose order is coprime
to `|G|`. Suppose `α` centralizes `C_G(τ)`. Is `α = 1`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Simple

@[expose] public section

namespace MathlibExt.GroupTheory.CoprimeAutomorphismCentralizerKourovka4Problem23Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.23 (G.
Glauberman). UnsolvedMath record UM-00700233 (`KOU-4.23`), dataset ulamai/UnsolvedMath v1.8.0.

Simple is Mathlib's `IsSimpleGroup`; `α` centralizes `C_G(τ)` when it fixes every element commuting
with `τ`. The refutation is one explicit configuration in the Suzuki group `Sz(8)` of order `29120`;
checking it needs the structure of `Sz(8)` and its field automorphism, not a decision procedure on a
small object.
-/

/-- Kourovka 4.23 (G. Glauberman): let `G` be a finite simple group, `τ ∈ G` an element of prime
order and `α` an automorphism of `G` whose order is coprime to `|G|`. If `α` centralizes
`C_G(τ)` (fixes each element commuting with `τ`), then `α = 1`. -/
def coprimeAutomorphismCentralizingCentralizerTrivial : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (τ : G) (α : MulAut G), IsSimpleGroup G →
    (orderOf τ).Prime → Nat.Coprime (orderOf α) (Nat.card G) →
    (∀ g : G, g * τ = τ * g → α g = g) → α = 1

/--
Resolved false: the Kourovka Archive answers 4.23 "Not always", with the example `G = Sz(8)`, `|τ| =
5`, `|α| = 3` (Podufalov, 1975): an automorphism of order `3`, coprime to `|Sz(8)| = 29120`,
centralizing `C_G(τ)` for an element `τ` of order `5`. Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 4.23 (G. Glauberman); resolution: N. D. Podufalov,
letter of 3 September 1975, recorded in the Kourovka Archive, Kourovka Archive of Solved Problems,
Problem 4.23: Not always; for example, G = Sz(8), |τ| = 5, |α| = 3,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted coprimeAutomorphismCentralizingCentralizerTrivial_refuted :
    ¬ coprimeAutomorphismCentralizingCentralizerTrivial

end MathlibExt.GroupTheory.CoprimeAutomorphismCentralizerKourovka4Problem23Wanted
