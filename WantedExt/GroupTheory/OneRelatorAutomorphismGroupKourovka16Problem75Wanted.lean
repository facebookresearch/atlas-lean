/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# One-relator groups as automorphism groups (Kourovka Notebook Problem 16.75)

Kourovka Notebook, Archive of Solved Problems, Problem 16.75 (M. V. Neshchadim): can a non-abelian
one-relator group be the group of all automorphisms of some group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PresentedGroup

@[expose] public section

namespace MathlibExt.GroupTheory.OneRelatorAutomorphismGroupKourovka16Problem75Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.75 (M. V.
Neshchadim). UnsolvedMath record UM-00701267 (`KOU-16.75`), dataset ulamai/UnsolvedMath v1.8.0.

A one-relator group is `⟨x₀, …, x_{n-1} | r⟩` for some `n` and `r ∈ Fₙ` (`PresentedGroup {r}`);
being the automorphism group of `H` means being isomorphic to `MulAut H` for a group `H` in `Type`.
-/

/-- Kourovka 16.75 (M. V. Neshchadim): some non-abelian one-relator group
`⟨x₀, …, x_{n-1} | r⟩` is isomorphic to the automorphism group of some group. -/
def oneRelatorGroupIsAutomorphismGroup : Prop :=
  ∃ (n : ℕ) (r : FreeGroup (Fin n)),
    (∃ a b : PresentedGroup ({r} : Set (FreeGroup (Fin n))), a * b ≠ b * a) ∧
    ∃ (H : Type) (_ : Group H),
      Nonempty (PresentedGroup ({r} : Set (FreeGroup (Fin n))) ≃* MulAut H)

/--
Resolved true: the Kourovka Archive answers 16.75 "Yes, it can" (Churkin): Collins proved that for
integers `r, s` with `gcd(r, s) = 1`, `|r| ≠ |s|` and `r - s` even, the one-relator group `G = ⟨a, b
| a⁻¹ b^r a = b^s⟩` is isomorphic to `Aut(Aut(G))`, so `G` is the automorphism group of `H =
Aut(G)`. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.75
(M. V. Neshchadim); resolution: D. J. Collins, Proc. London Math. Soc. (3) 36 (1978), no. 3,
480-493; V. A. Churkin, letter of 5 April 2006, as recorded in the Kourovka Archive, Kourovka
Archive, Problem 16.75 (Yes, it can: for integers r, s with gcd(r, s) = 1, |r| ≠ |s| and r - s even,
G = ⟨a, b | a⁻¹ b^r a = b^s⟩ is isomorphic to Aut(Aut(G)), Collins).
-/
public theorem_wanted oneRelatorGroupIsAutomorphismGroup_holds : oneRelatorGroupIsAutomorphismGroup

end MathlibExt.GroupTheory.OneRelatorAutomorphismGroupKourovka16Problem75Wanted
