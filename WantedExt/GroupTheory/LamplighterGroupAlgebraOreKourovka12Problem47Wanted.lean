/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Ore condition for group algebras of lamplighter groups (Kourovka Notebook Problem 12.47)

Kourovka Notebook, Archive of Solved Problems, Problem 12.47 (P. A. Linnell): let `k` be a field,
`p` a prime and `G = ℤₚ ≀ ℤ`. Does `kG` have a classical quotient ring, i.e. do the
non-zero-divisors of `kG` form an Ore set?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.SemidirectProduct

@[expose] public section

namespace MathlibExt.GroupTheory.LamplighterGroupAlgebraOreKourovka12Problem47Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.47 (P. A.
Linnell). UnsolvedMath record UM-00700866 (`KOU-12.47`), dataset ulamai/UnsolvedMath v1.8.0.

`ℤₚ ≀ ℤ` is the semidirect product of `⨁_{i ∈ ℤ} ℤ/p` (finitely supported functions) by `ℤ` acting
by the shift. Having a classical (right) ring of quotients is the right Ore condition for the
non-zero-divisors, as in Definition 1 of Linnell, Lück and Schick; for group algebras the left and
right conditions are equivalent. The target is stated for some field and some prime (the strongest
true form, existential when refuted, as in WantedExt/Sources/UnsolvedMath.md), so its refutation
asserts that `k[ℤₚ ≀ ℤ]` is not Ore for every field `k` and every prime `p`: stronger than the
source's negative answer, which needs one pair, and what Theorem 3 of Linnell, Lück and Schick
proves.
-/

/-- The shift `f ↦ f(· - 1)` of the base group `⊕_{i ∈ ℤ} ℤ/p`. -/
noncomputable def shift (p : ℕ) : MulAut (Multiplicative (ℤ →₀ ZMod p)) :=
  AddEquiv.toMultiplicative (Finsupp.domCongr (Equiv.addRight (1 : ℤ)))

/-- The wreath product `ℤ/p ≀ ℤ = (⊕_{i ∈ ℤ} ℤ/p) ⋊ ℤ`, with `ℤ` acting by the shift. -/
abbrev Lamplighter (p : ℕ) : Type :=
  Multiplicative (ℤ →₀ ZMod p) ⋊[zpowersHom (MulAut (Multiplicative (ℤ →₀ ZMod p))) (shift p)]
    Multiplicative ℤ

/-- `s` is a non-zero-divisor: neither a left nor a right zero divisor. -/
def IsNonZeroDivisor {R : Type*} [Ring R] (s : R) : Prop :=
  (∀ z : R, z * s = 0 → z = 0) ∧ ∀ z : R, s * z = 0 → z = 0

/-- `R` satisfies the (right) Ore condition for its non-zero-divisors, i.e. has a classical
right ring of quotients: for `s, t` with `s` a non-zero-divisor there are `x, y` with `x` a
non-zero-divisor and `s y = t x`. For group algebras the left and right conditions agree. -/
def IsOreRing (R : Type*) [Ring R] : Prop :=
  ∀ s t : R, IsNonZeroDivisor s → ∃ x y : R, IsNonZeroDivisor x ∧ s * y = t * x

/-- Kourovka 12.47 (P. A. Linnell), stated for some field `k` and some prime `p`: the group
algebra `k[ℤ/p ≀ ℤ]` has a classical ring of quotients. -/
def lamplighterGroupAlgebraOre : Prop :=
  ∃ (k : Type) (_ : Field k) (p : ℕ), p.Prime ∧ IsOreRing (MonoidAlgebra k (Lamplighter p))

/--
Resolved false: Linnell, Lück and Schick (Theorem 3, with W. Dicks's argument) prove that `kG` is
not an Ore ring for every field `k` and every group `G` containing `H ≀ ℤ` with `H ≠ 1` finite, in
particular for `G = ℤₚ ≀ ℤ` and every prime `p`; the Kourovka Archive answers 12.47 "No, it does
not". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.47
(P. A. Linnell); resolution: P. A. Linnell, W. Lück and T. Schick, The Ore condition, affiliated
operators, and the lamplighter group, in: High-dimensional manifold topology (Trieste, 2001), World
Scientific, 2003, 315-321, Theorem 3: kG is not an Ore ring for every field k and every group G
containing H ≀ ℤ with H ≠ 1 finite; Kourovka Archive, Problem 12.47,
http://him-lueck.uni-bonn.de/data/lamplighter.pdf.
-/
public theorem_wanted lamplighterGroupAlgebraOre_refuted : ¬ lamplighterGroupAlgebraOre

end MathlibExt.GroupTheory.LamplighterGroupAlgebraOreKourovka12Problem47Wanted
