/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Soluble groups with a splitting automorphism of prime order (Kourovka Notebook Problem 1.10)

Kourovka Notebook, Archive of Solved Problems, Problem 1.10 (Yu. M. Gorchakov): an automorphism `φ`
of a group `G` is splitting if `g g^φ ⋯ g^(φ^(n-1)) = 1` for every `g ∈ G`, where `n` is the order
of `φ`. Is a soluble group admitting a regular splitting automorphism of prime order necessarily
nilpotent?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.SplittingAutomorphismSolubleNilpotentKourovka1Problem10Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.10 (Yu. M.
Gorchakov). UnsolvedMath record UM-00700008 (`KOU-1.10`), dataset ulamai/UnsolvedMath v1.8.0.

Automorphisms are elements of `MulAut G`; `φ` has prime order `p` (`orderOf φ = p`), so the
splitting product has `p` factors `(φ ^ i) g`, `i < p`. Regular means fixed-point-free: `φ g = g`
only for `g = 1`. Soluble is `Group.IsSolvable` (finite derived length) and nilpotent is
`Group.IsNilpotent`; `G` may be infinite. The second target drops the regularity condition, as the
Archive records.
-/

/-- The automorphism `φ` is splitting with respect to `p`: `g · φ(g) · φ²(g) ⋯ φ^(p-1)(g) = 1` for
every `g` (Kourovka 1.10 takes `p` to be the order of `φ`). -/
def IsSplitting {G : Type} [Group G] (φ : MulAut G) (p : ℕ) : Prop :=
  ∀ g : G, ((List.range p).map fun i => (φ ^ i) g).prod = 1

/-- Kourovka 1.10 (Yu. M. Gorchakov): a soluble group admitting a regular (fixed-point-free)
splitting automorphism of prime order is nilpotent. -/
def regularSplittingAutSolubleNilpotent : Prop :=
  ∀ (G : Type) [Group G] (p : ℕ) (φ : MulAut G), p.Prime → orderOf φ = p → IsSplitting φ p →
    (∀ g : G, φ g = g → g = 1) → Group.IsSolvable G → Group.IsNilpotent G

/-- Kourovka 1.10 without the regularity condition: a soluble group admitting a splitting
automorphism of prime order is nilpotent. -/
def splittingAutSolubleNilpotent : Prop :=
  ∀ (G : Type) [Group G] (p : ℕ) (φ : MulAut G), p.Prime → orderOf φ = p → IsSplitting φ p →
    Group.IsSolvable G → Group.IsNilpotent G

/--
Resolved true: the Kourovka Archive answers 1.10 "Yes, it is" (Khukhro 1978): a soluble group with a
regular splitting automorphism of prime order is nilpotent. Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 1.10 (Yu. M. Gorchakov); resolution: E. I. Khukhro,
Algebra and Logic 17 (1978), 402-406; E. I. Khukhro, Algebra and Logic 19 (1980), 77-84, Kourovka
Archive, Problem 1.10 (yes, and even without the regularity condition).
-/
public theorem_wanted regularSplittingAutSolubleNilpotent_holds :
    regularSplittingAutSolubleNilpotent

/--
Resolved true: the Kourovka Archive adds that the answer is yes "even without the regularity
condition on the automorphism" (Khukhro 1980): a soluble group with a splitting automorphism of
prime order is nilpotent. This implies the first target. Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 1.10 (Yu. M. Gorchakov); resolution: E. I. Khukhro,
Algebra and Logic 17 (1978), 402-406; E. I. Khukhro, Algebra and Logic 19 (1980), 77-84, Kourovka
Archive, Problem 1.10 (yes, and even without the regularity condition).
-/
public theorem_wanted splittingAutSolubleNilpotent_holds : splittingAutSolubleNilpotent

end MathlibExt.GroupTheory.SplittingAutomorphismSolubleNilpotentKourovka1Problem10Wanted
