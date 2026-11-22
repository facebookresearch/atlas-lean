/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Recognition of alternating groups by their element orders (Kourovka Notebook Problem 16.107)

Kourovka Notebook, Archive of Solved Problems, Problem 16.107 (W. J. Shi): is it true that almost
every alternating group `Aₙ` is uniquely determined in the class of finite groups by its set of
element orders, i.e. that `h(π_e(Aₙ)) = 1` for all large enough `n`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.SpecificGroups.Alternating

@[expose] public section

namespace MathlibExt.GroupTheory.AlternatingGroupSpectrumRecognitionKourovka16Problem107Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.107 (W. J.
Shi). UnsolvedMath record UM-00701298 (`KOU-16.107`), dataset ulamai/UnsolvedMath v1.8.0.

`Aₙ` is Mathlib's `alternatingGroup (Fin n)` and the spectrum is the set of element orders; "almost
every" means "for all sufficiently large `n`", as the problem states.
-/

/-- The spectrum `π_e(G)`: the set of orders of elements of `G`. -/
def elementOrders (G : Type*) [Group G] : Set ℕ :=
  Set.range (orderOf : G → ℕ)

/-- Kourovka 16.107 (W. J. Shi): for all large `n`, every finite group with the same set of element
orders as `Aₙ` is isomorphic to `Aₙ`, i.e. `h(π_e(Aₙ)) = 1`. -/
def alternatingGroupRecognizableBySpectrum : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : Type) [Group G] [Finite G],
    elementOrders G = elementOrders (alternatingGroup (Fin n)) →
      Nonempty (G ≃* alternatingGroup (Fin n))

/--
Resolved true: the Kourovka Archive answers 16.107 "Yes, it is" (Gorshkov): for all large `n`, every
finite group with the same element orders as `Aₙ` is isomorphic to `Aₙ`. Source: E. I. Khukhro and
V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.107 (W. J. Shi); resolution: I. B.
Gorshkov, Recognizability of alternating groups by spectrum, Algebra and Logic 52 (2013), no. 1,
41-45, arXiv:1302.4825, abstract (the simple alternating groups Aₙ are recognizable by spectrum for
n ≠ 6, 10); Kourovka Archive, Problem 16.107 (answer: Yes, it is), https://arxiv.org/abs/1302.4825.
-/
public theorem_wanted alternatingGroupRecognizableBySpectrum_holds :
    alternatingGroupRecognizableBySpectrum

end MathlibExt.GroupTheory.AlternatingGroupSpectrumRecognitionKourovka16Problem107Wanted
