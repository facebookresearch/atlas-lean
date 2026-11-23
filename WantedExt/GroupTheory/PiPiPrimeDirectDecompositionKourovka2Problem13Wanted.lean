/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Direct decompositions of periodic groups into π- and π'-parts (Kourovka Notebook Problem 2.13)

Kourovka Notebook, Archive of Solved Problems, Problem 2.13 (S. G. Ivanov): let `G` be a periodic
group in which every `π`-element commutes with every `π'`-element. Does `G` decompose into the
direct product of a maximal `π`-subgroup and a maximal `π'`-subgroup?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Torsion

@[expose] public section

namespace MathlibExt.GroupTheory.PiPiPrimeDirectDecompositionKourovka2Problem13Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.13 (S. G.
Ivanov). UnsolvedMath record UM-00700090 (`KOU-2.13`), dataset ulamai/UnsolvedMath v1.8.0.

`π` is any set of primes (a `Set ℕ`; its non-primes play no role) and `π'` the primes outside `π`; a
`π`-element is an element of finite order whose prime divisors lie in `π`. The direct decomposition
is internal: `P ⊓ Q = ⊥`, `P ⊔ Q = ⊤` and `P`, `Q` commute elementwise.
-/

/-- `g` is a `π`-element for a set `π` of primes: `g` has finite order and every prime divisor of
its order lies in `π`. -/
def IsPiElement (π : Set ℕ) {G : Type*} [Group G] (g : G) : Prop :=
  0 < orderOf g ∧ ∀ p : ℕ, p.Prime → p ∣ orderOf g → p ∈ π

/-- `H` is a maximal `π`-subgroup: all its elements are `π`-elements and no larger subgroup has this
property. -/
def IsMaximalPiSubgroup (π : Set ℕ) {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  (∀ g ∈ H, IsPiElement π g) ∧ ∀ K : Subgroup G, (∀ g ∈ K, IsPiElement π g) → H ≤ K → K = H

/-- Kourovka 2.13 (S. G. Ivanov): for every set `π` of primes, a periodic group `G` in which every
`π`-element commutes with every `π'`-element is the (internal) direct product of a maximal
`π`-subgroup and a maximal `π'`-subgroup (`π'` = the primes outside `π`). -/
def piPiPrimeDirectDecomposition : Prop :=
  ∀ (π : Set ℕ) (G : Type) [Group G], IsMulTorsion G →
    (∀ x y : G, IsPiElement π x → IsPiElement πᶜ y → x * y = y * x) →
    ∃ P Q : Subgroup G, IsMaximalPiSubgroup π P ∧ IsMaximalPiSubgroup πᶜ Q ∧ P ⊓ Q = ⊥ ∧
      P ⊔ Q = ⊤ ∧ ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x

/--
Resolved false: the Kourovka Archive answers 2.13 "Not always": Merzlyakov's counterexample is a
quotient `A / ⟨d^{p^k}⟩` of Adian's torsion-free central extension of the free Burnside group of odd
exponent `n ≥ 4381`, with `π = {p}`, `p` coprime to `n`. Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 2.13 (S. G. Ivanov); resolution: Yu. I. Merzlyakov
(1973), using S. I. Adian, On some torsion-free groups, Math. USSR-Izv. 5 (1971), 475-484, Kourovka
Archive, Problem 2.13: Not always; with Adian's torsion-free central extension A(m, n) of the free
Burnside group B(m, n), n ≥ 4381 odd, G = A / ⟨d^{p^k}⟩ is a counterexample for π = {p} and some k,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted piPiPrimeDirectDecomposition_refuted : ¬ piPiPrimeDirectDecomposition

end MathlibExt.GroupTheory.PiPiPrimeDirectDecompositionKourovka2Problem13Wanted
