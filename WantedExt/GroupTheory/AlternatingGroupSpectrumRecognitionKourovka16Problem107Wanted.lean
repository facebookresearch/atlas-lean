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

/-- **Spectrum of a group.** The spectrum $\pi_e(G)$ of a group $G$ is the set of orders of the
elements of $G$, where an element of infinite order is assigned order $0$. -/
def elementOrders (G : Type*) [Group G] : Set ℕ :=
  Set.range (orderOf : G → ℕ)

/-- **Kourovka Problem 16.107 on recognition of alternating groups by spectrum.** This proposition
asserts that there is a natural number $N$ such that for every $n \ge N$, every finite group $G$
with the same spectrum (set of element orders) as the alternating group $A_n$ is isomorphic to
$A_n$. -/
def alternatingGroupRecognizableBySpectrum : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : Type) [Group G] [Finite G],
    elementOrders G = elementOrders (alternatingGroup (Fin n)) →
      Nonempty (G ≃* alternatingGroup (Fin n))

/--
**Large alternating groups are recognizable by spectrum.** There is a natural number $N$ such that
for every $n \ge N$, every finite group $G$ whose set of element orders equals that of the
alternating group $A_n$ is isomorphic to $A_n$.

Source: E. I. Khukhro and
V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.107 (W. J. Shi); resolution: I. B.
Gorshkov, Recognizability of alternating groups by spectrum, Algebra and Logic 52 (2013), no. 1,
41-45, arXiv:1302.4825, abstract (the simple alternating groups Aₙ are recognizable by spectrum for
n ≠ 6, 10); Kourovka Archive, Problem 16.107 (answer: Yes, it is), https://arxiv.org/abs/1302.4825.
-/
public theorem_wanted alternatingGroupRecognizableBySpectrum_holds :
    alternatingGroupRecognizableBySpectrum

end MathlibExt.GroupTheory.AlternatingGroupSpectrumRecognitionKourovka16Problem107Wanted
