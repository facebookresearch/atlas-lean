/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Group-ring powers in fields with a finite automorphism group (Kourovka Notebook Problem 11.79)

Kourovka Notebook, Archive of Solved Problems, Problem 11.79 (K. N. Ponomarëv): let `G` be a finite
group of automorphisms of an infinite field `F` of characteristic `p`; integral powers and the
action of `G` define an action of `ℤG` on `Fˣ`. Does every subfield of `F` that contains the images
of all elements of `F` under a fixed element of `ℤG \ pℤG` contain infinitely many `G`-invariant
elements?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Ring.Aut

@[expose] public section

namespace MathlibExt.GroupTheory.FieldAutomorphismGroupRingKourovka11Problem79Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.79 (K. N.
Ponomarëv). UnsolvedMath record UM-00700771 (`KOU-11.79`), dataset ulamai/UnsolvedMath v1.8.0.

`G` is a finite subgroup of `RingAut F` and `ξ ∈ ℤG` a finitely supported function `G → ℤ`, acting
by `x ^ ξ = ∏_g (g x) ^ (ξ g)` on nonzero `x`; `ξ ∉ pℤG` means some coefficient is not divisible by
`p`. The characteristic is a prime `p`: in characteristic 0 every subfield contains `ℚ`, which is
infinite and fixed by `G`, so the statement would be trivial.
-/

/-- Kourovka 11.79 (K. N. Ponomarëv): let `G` be a finite group of automorphisms of an infinite
field `F` of prime characteristic `p`, acting with integral powers on `Fˣ` through the group ring:
`x ^ ξ = ∏_g (g x) ^ (ξ g)` for `ξ = ∑_g ξ g · g ∈ ℤG`. If `ξ ∉ pℤG` and a subfield `K` of `F`
contains `x ^ ξ` for every `x ≠ 0`, then `K` contains infinitely many `G`-invariant elements. -/
def subfieldContainsInfinitelyManyInvariants : Prop :=
  ∀ (p : ℕ) (F : Type) [Field F] [CharP F p], p.Prime → Infinite F →
    ∀ G : Subgroup (RingAut F), (G : Set (RingAut F)).Finite →
    ∀ ξ : G →₀ ℤ, (¬ ∀ g : G, (p : ℤ) ∣ ξ g) →
    ∀ K : Subfield F, (∀ x : F, x ≠ 0 → (ξ.prod fun g n => ((g : RingAut F) x) ^ n) ∈ K) →
      {y : F | y ∈ K ∧ ∀ g ∈ G, g y = y}.Infinite

/--
Resolved true: the Kourovka Archive answers 11.79 "Yes" (Ponomarëv): a subfield of an infinite field
of characteristic `p` containing all `x ^ ξ`, for a finite automorphism group `G` and `ξ ∈ ℤG \
pℤG`, contains infinitely many `G`-invariant elements. Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 11.79 (K. N. Ponomarëv); resolution: K. N. Ponomarëv,
Siberian Math. J. 33 (1992), 1094-1099, Kourovka Archive, Problem 11.79: "Yes",
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted subfieldContainsInfinitelyManyInvariants_holds :
    subfieldContainsInfinitelyManyInvariants

end MathlibExt.GroupTheory.FieldAutomorphismGroupRingKourovka11Problem79Wanted
