/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Orders of `p`-groups and of their automorphism groups (Kourovka Notebook Problem 12.77)

Kourovka Notebook, Archive of Solved Problems, Problem 12.77 (well-known problem; A. I. Starostin):
does the order (if it is greater than `p²`) of a finite non-cyclic `p`-group divide the order of its
automorphism group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup

@[expose] public section

namespace MathlibExt.GroupTheory.PGroupOrderDividesAutKourovka12Problem77Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.77
(well-known problem; A. I. Starostin). UnsolvedMath record UM-00700895 (`KOU-12.77`), dataset
ulamai/UnsolvedMath v1.8.0.

`Aut(P)` is `MulAut P`. The target is stated for some prime `p` (the strongest true form,
existential when refuted, as in WantedExt/Sources/UnsolvedMath.md), so its refutation asserts a
counterexample for every prime: stronger than the source's negative answer, which needs one prime,
and what González-Sánchez and Jaikin-Zapirain prove (a family for each prime `p`).
-/

/-- Kourovka 12.77 (A. I. Starostin; well-known problem), stated for some prime `p`: the order of
every finite non-cyclic `p`-group of order greater than `p²` divides the order of its
automorphism group. -/
def pGroupOrderDividesAutOrder : Prop :=
  ∃ p : ℕ, p.Prime ∧ ∀ (P : Type) [Group P] [Finite P], IsPGroup p P → ¬ IsCyclic P →
    p ^ 2 < Nat.card P → Nat.card P ∣ Nat.card (MulAut P)

/--
Resolved false: González-Sánchez and Jaikin-Zapirain construct, for each prime `p`, finite
`p`-groups `Gᵢ` with `|Aut(Gᵢ)| / |Gᵢ| → 0`; they are non-abelian (hence non-cyclic, of order
greater than `p²`) and eventually `|Aut(Gᵢ)| < |Gᵢ|`, so `|Gᵢ| ∤ |Aut(Gᵢ)|`. The Kourovka Archive
answers 12.77 "No, not always". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 12.77 (well-known problem; A. I. Starostin); resolution: J. González-Sánchez and
A. Jaikin-Zapirain, Finite p-groups with small automorphism group, Forum Math. Sigma 3 (2015), Paper
No. e7, main theorem (abstract): for each prime p, finite p-groups G_i with |Aut(G_i)|/|G_i| → 0;
Kourovka Archive, Problem 12.77.
-/
public theorem_wanted pGroupOrderDividesAutOrder_refuted : ¬ pGroupOrderDividesAutOrder

end MathlibExt.GroupTheory.PGroupOrderDividesAutKourovka12Problem77Wanted
