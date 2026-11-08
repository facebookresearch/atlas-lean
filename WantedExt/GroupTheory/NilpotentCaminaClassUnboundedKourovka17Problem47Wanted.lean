/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Nilpotency class of nilpotent Camina-type groups (Kourovka Notebook Problem 17.47)

Kourovka Notebook, Problem 17.47 (S. H. Ghate, A. S. Muktibodh): let `G` be a nilpotent group in
which every coset `x[G, G]` for `x ∉ [G, G]` coincides with the conjugacy class `x^G`. Is there a
bound for the nilpotency class of `G`? (If `G` is finite, its class is at most 3 (R. Dark, C.
Scoppola).)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.NilpotentCaminaClassUnboundedKourovka17Problem47Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 17.47 (S. H. Ghate, A. S. Muktibodh).
UnsolvedMath record UM-00701349 (`KOU-17.47`), dataset ulamai/UnsolvedMath v1.8.0.

`[G, G]` is `commutator G` and the class is `Group.nilpotencyClass`; groups are taken in `Type`.
-/

/-- Kourovka 17.47 (S. H. Ghate, A. S. Muktibodh): there is a bound `c` on the nilpotency class of
the nilpotent groups `G` in which every coset `x[G, G]` with `x ∉ [G, G]` equals the conjugacy
class `x^G`. -/
def nilpotentCaminaClassBounded : Prop :=
  ∃ c : ℕ, ∀ (G : Type) [Group G], Group.IsNilpotent G →
    (∀ x : G, x ∉ commutator G →
      ∀ y : G, (∃ z ∈ commutator G, y = x * z) ↔ ∃ g : G, y = g * x * g⁻¹) →
    Group.nilpotencyClass G ≤ c

/--
Resolved false: Ionin and Semidetnov (Answer 4.2) construct, for every integer `c ≥ 2`, a nilpotent
group of class exactly `c` in which `x^G = x[G, G]` for every `x ∉ [G, G]`. The Kourovka Notebook
(21st issue) answers 17.47 "No, there is no such bound". Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Problem 17.47 (S. H. Ghate, A. S. Muktibodh); resolution: V. Ionin and A. Semidetnov, On
some more problems from the Kourovka Notebook, preprint, arXiv:2608.29219 (2026; solutions found
with the assistance of large language models and checked by the authors, per its abstract), Answer
4.2 (for every integer c ≥ 2 there exists a nilpotent Camina group of class exactly c); the Kourovka
Notebook (21st issue) marks 17.47 solved (No, there is no such bound),
https://arxiv.org/abs/2608.29219.
-/
public theorem_wanted nilpotentCaminaClassBounded_refuted : ¬ nilpotentCaminaClassBounded

end MathlibExt.GroupTheory.NilpotentCaminaClassUnboundedKourovka17Problem47Wanted
