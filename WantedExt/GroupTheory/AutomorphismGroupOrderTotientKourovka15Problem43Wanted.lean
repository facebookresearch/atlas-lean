/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Orders of automorphism groups versus Euler's function (Kourovka Notebook Problem 15.43)

Kourovka Notebook, Archive of Solved Problems, Problem 15.43 (M. Deaconescu): let `G` be a finite
group of order `n`. (a) Is it true that `|Aut G| ≥ φ(n)`, where `φ` is Euler's function? (b) Is `G`
cyclic if `|Aut G| = φ(n)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Totient

@[expose] public section

namespace MathlibExt.GroupTheory.AutomorphismGroupOrderTotientKourovka15Problem43Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.43 (M.
Deaconescu). UnsolvedMath record UM-00701131 (`KOU-15.43`), dataset ulamai/UnsolvedMath v1.8.0.

`Aut G` is `MulAut G` and `φ` is `Nat.totient`; both parts are stated for all finite groups in
`Type`.
-/

/-- Kourovka 15.43(a) (M. Deaconescu): every finite group `G` satisfies `|Aut G| ≥ φ(|G|)`. -/
def totientLeAutOrder : Prop :=
  ∀ (G : Type) [Group G] [Finite G], (Nat.card G).totient ≤ Nat.card (MulAut G)

/-- Kourovka 15.43(b) (M. Deaconescu): every finite group `G` with `|Aut G| = φ(|G|)` is cyclic. -/
def autOrderEqTotientImpliesCyclic : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card (MulAut G) = (Nat.card G).totient → IsCyclic G

/--
Resolved false: the Kourovka Archive answers 15.43(a) negatively (Bray and Wilson): some finite
groups have `|Aut G| < φ(|G|)`, and the ratio `|Aut G| / φ(|G|)` can be made arbitrarily small.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.43 (M.
Deaconescu); resolution: J. N. Bray and R. A. Wilson, On the orders of automorphism groups of finite
groups, Bull. London Math. Soc. 37 (2005), no. 3, 381-385, main results (groups with |Aut G| <
φ(|G|), infinitely many non-cyclic groups with |Aut G| = φ(|G|), and |Aut G|/φ(|G|) arbitrarily
small); Kourovka Archive, Problem 15.43 (both answers negative),
https://webspace.maths.qmul.ac.uk/j.n.bray/web/Publ/AutG/.
-/
public theorem_wanted totientLeAutOrder_refuted : ¬ totientLeAutOrder

/--
Resolved false: the Kourovka Archive answers 15.43(b) negatively: Bray and Wilson construct
infinitely many non-cyclic finite groups with `|Aut G| = φ(|G|)`. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.43 (M. Deaconescu); resolution: J.
N. Bray and R. A. Wilson, On the orders of automorphism groups of finite groups, Bull. London Math.
Soc. 37 (2005), no. 3, 381-385, main results (groups with |Aut G| < φ(|G|), infinitely many
non-cyclic groups with |Aut G| = φ(|G|), and |Aut G|/φ(|G|) arbitrarily small); Kourovka Archive,
Problem 15.43 (both answers negative), https://webspace.maths.qmul.ac.uk/j.n.bray/web/Publ/AutG/.
-/
public theorem_wanted autOrderEqTotientImpliesCyclic_refuted : ¬ autOrderEqTotientImpliesCyclic

end MathlibExt.GroupTheory.AutomorphismGroupOrderTotientKourovka15Problem43Wanted
