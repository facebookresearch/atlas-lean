/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Highly transitive groups as homeomorphisms of ℚ (Kourovka Notebook Problem 5.40)

Kourovka Notebook, Archive of Solved Problems, Problem 5.40 (P. M. Neumann): let G be a countable
group acting on a set Ω, k-fold transitively for every finite k, with no non-trivial permutations of
finite support; can Ω be identified with the rational line ℚ so that G becomes a group of
autohomeomorphisms?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

@[expose] public section

namespace MathlibExt.GroupTheory.HighlyTransitiveRationalsHomeomorphismsKourovka5Problem40Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.40 (P. M.
Neumann). UnsolvedMath record UM-00700322 (`KOU-5.40`), dataset ulamai/UnsolvedMath v1.8.0.

`G` acts faithfully (a group of permutations of `Ω`); `k`-fold transitivity is Mathlib's
`MulAction.IsMultiplyPretransitive`. `Ω` is required to be infinite: if `Ω` has at most one point,
the trivial group satisfies all hypotheses and `Ω` cannot be identified with `ℚ`, while for finite
`Ω` with at least two points the hypotheses cannot hold (high transitivity forces a transposition).
The identification is a bijection `e : Ω ≃ ℚ` under which every element of `G` acts continuously
(its inverse is the action of `g⁻¹`).
-/

/-- Kourovka 5.40 (P. M. Neumann): if a countable group `G` acts faithfully on an infinite set `Ω`,
`k`-transitively for every finite `k`, and no non-trivial element moves only finitely many points,
then `Ω` can be identified with the rational line `ℚ` so that every element of `G` acts as a
homeomorphism of `ℚ`. -/
def highlyTransitiveActsByHomeomorphismsOfRationals : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (Ω : Type) [MulAction G Ω] [FaithfulSMul G Ω],
    Infinite Ω → (∀ k : ℕ, MulAction.IsMultiplyPretransitive G Ω k) →
    (∀ g : G, g ≠ 1 → {ω : Ω | g • ω ≠ ω}.Infinite) →
      ∃ e : Ω ≃ ℚ, ∀ g : G, Continuous fun q : ℚ => e (g • e.symm q)

/--
Resolved false: the Kourovka Archive answers 5.40 "Not always", citing Mekler, Groups embeddable in
the autohomeomorphisms of Q (J. London Math. Soc. (2) 33 (1986), 49-58). Source: E. I. Khukhro and
V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.40 (P. M. Neumann); resolution: A.
H. Mekler, Groups embeddable in the autohomeomorphisms of Q, J. London Math. Soc. (2) 33 (1986),
49-58, Kourovka Archive, Problem 5.40: Not always (Mekler), https://doi.org/10.1112/jlms/s2-33.1.49.
-/
public theorem_wanted highlyTransitiveActsByHomeomorphismsOfRationals_refuted :
    ¬ highlyTransitiveActsByHomeomorphismsOfRationals

end MathlibExt.GroupTheory.HighlyTransitiveRationalsHomeomorphismsKourovka5Problem40Wanted
