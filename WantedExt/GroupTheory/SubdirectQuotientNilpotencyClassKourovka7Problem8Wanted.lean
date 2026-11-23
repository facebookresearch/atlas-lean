/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Nilpotency class of quotients of subdirect products (Kourovka Notebook Problem 7.8)

Kourovka Notebook, Archive of Solved Problems, Problem 7.8 (Yu. M. Gorchakov): suppose that `H` is a
normal subgroup of a group `G`, where `H` and `G` are subdirect products of the same `n` groups `G₁,
…, Gₙ`. Does the nilpotency class of `G / H` increase with `n`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.SubdirectQuotientNilpotencyClassKourovka7Problem8Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 7.8 (Yu. M.
Gorchakov). UnsolvedMath record UM-00700414 (`KOU-7.8`), dataset ulamai/UnsolvedMath v1.8.0.

A subdirect product of `G₁, …, Gₙ` is a subgroup of `∏ i, Gᵢ` projecting onto every factor. Such a
quotient `G / H` is always nilpotent; "increases with `n`" is read as unbounded: for every `c` there
are `n`, `Gᵢ` and `H ⊴ G` with `G / H` of nilpotency class at least `c`.
-/

/-- Kourovka 7.8 (Yu. M. Gorchakov): the nilpotency class of `G / H`, where `H ⊴ G` are subdirect
products of the same `n` groups `G₁, …, Gₙ` (subgroups of `∏ i, Gᵢ` projecting onto every factor),
grows with `n`: for every `c` there are such `n`, `Gᵢ`, `G` and `H` with `G / H` nilpotent of class
at least `c`. -/
def subdirectQuotientClassUnbounded : Prop :=
  ∀ c : ℕ, ∃ (n : ℕ) (Gi : Fin n → Type) (_ : ∀ i, Group (Gi i))
    (G H : Subgroup ((i : Fin n) → Gi i)) (_ : H ≤ G) (_ : (H.subgroupOf G).Normal),
    (∀ i, Function.Surjective fun g : G => (g : (j : Fin n) → Gi j) i) ∧
    (∀ i, Function.Surjective fun h : H => (h : (j : Fin n) → Gi j) i) ∧
    ∃ _ : Group.IsNilpotent (G ⧸ H.subgroupOf G), c ≤ Group.nilpotencyClass (G ⧸ H.subgroupOf G)

/--
Resolved true: the Kourovka Archive answers 7.8 "Yes, it does", citing Khukhro (1982): the
nilpotency class of `G / H` is not bounded independently of `n`. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 7.8 (Yu. M. Gorchakov); resolution:
E. I. Khukhro, On nilpotent subdirect products, Sibirsk. Mat. Zh. 23, no. 6 (1982), 178-180
(Russian), Zbl 0515.20023, Kourovka Archive, Problem 7.8: Yes, it does (Khukhro),
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted subdirectQuotientClassUnbounded_holds : subdirectQuotientClassUnbounded

end MathlibExt.GroupTheory.SubdirectQuotientNilpotencyClassKourovka7Problem8Wanted
