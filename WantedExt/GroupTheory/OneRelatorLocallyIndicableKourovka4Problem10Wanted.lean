/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Torsion-free one-relator groups are locally indicable (Kourovka Notebook Problem 4.10)

Kourovka Notebook, Archive of Solved Problems, Problem 4.10 (G. Baumslag): a group `G` is called
locally indicable if every non-trivial finitely generated subgroup of `G` has an infinite cyclic
factor group. Is every torsion-free one-relator group locally indicable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace MathlibExt.GroupTheory.OneRelatorLocallyIndicableKourovka4Problem10Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.10 (G.
Baumslag). UnsolvedMath record UM-00700221 (`KOU-4.10`), dataset ulamai/UnsolvedMath v1.8.0.

A one-relator group is `⟨x₁, …, xₙ | r⟩ = F_n / ⟨⟨r⟩⟩` with finitely many generators. An infinite
cyclic factor group of `H` is a surjection `H → ℤ` (`Multiplicative ℤ`). Torsion-free is written `∀
g, g ≠ 1 → ¬ IsOfFinOrder g`.
-/

/-- `G` is locally indicable: every non-trivial finitely generated subgroup has an infinite cyclic
quotient (maps onto `ℤ`). -/
def IsLocallyIndicable (G : Type*) [Group G] : Prop :=
  ∀ H : Subgroup G, H.FG → H ≠ ⊥ → ∃ f : H →* Multiplicative ℤ, Function.Surjective f

/-- Kourovka 4.10 (G. Baumslag): every torsion-free one-relator group
`⟨x₁, …, xₙ | r⟩ = F_n / ⟨⟨r⟩⟩` is locally indicable. -/
def torsionFreeOneRelatorLocallyIndicable : Prop :=
  ∀ (n : ℕ) (r : FreeGroup (Fin n)),
    (∀ g : FreeGroup (Fin n) ⧸ Subgroup.normalClosure {r}, g ≠ 1 → ¬ IsOfFinOrder g) →
    IsLocallyIndicable (FreeGroup (Fin n) ⧸ Subgroup.normalClosure {r})

/--
Resolved true: Brodskiĭ proved that every torsion-free one-relator group is locally indicable; the
Kourovka Archive answers 4.10 "Yes, it is". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 4.10 (G. Baumslag); resolution: S. D. Brodskiĭ, Dep. no. 2214-80, VINITI,
Moscow, 1980 (Russian); S. D. Brodskiĭ, Equations over groups, and groups with one defining
relation, Siberian Math. J. 25 (1984), 235-251, the 1984 paper gives the proofs; its zbMATH review
(Zbl 0579.20020) states that every torsion-free one-relator group is locally indicable; Kourovka
Archive of Solved Problems, Problem 4.10: Yes, it is, https://doi.org/10.1007/BF00971461.
-/
public theorem_wanted torsionFreeOneRelatorLocallyIndicable_holds :
    torsionFreeOneRelatorLocallyIndicable

end MathlibExt.GroupTheory.OneRelatorLocallyIndicableKourovka4Problem10Wanted
