/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SQ-universal and simple amalgamated free products (Kourovka Notebook Problem 4.45)

Kourovka Notebook, Archive of Solved Problems, Problem 4.45 (P. M. Neumann): let `G` be a free
product amalgamating proper subgroups `H` and `K` of `A` and `B`, respectively. a) Suppose that `H`,
`K` are finite and `|A : H| > 2`, `|B : K| ≥ 2`. Is `G` SQ-universal? b) Suppose that `A`, `B`, `H`,
`K` are free groups of finite ranks. Can `G` be simple?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PushoutI
public import Mathlib.GroupTheory.Subgroup.Simple
public import WantedExt.GroupTheory.SQUniversalShared

@[expose] public section

namespace MathlibExt.GroupTheory.AmalgamatedProductSQUniversalSimpleKourovka4Problem45Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.45 (P. M.
Neumann). UnsolvedMath record UM-00700252 (`KOU-4.45`), dataset ulamai/UnsolvedMath v1.8.0.

The two factors are a family `G : Fin 2 → Type`, `A = G 0`, `B = G 1`, with `H = φ₀(C) ≤ A` and `K =
φ₁(C) ≤ B` for injective homomorphisms `φᵢ` from a common group `C`; the amalgamated free product is
Mathlib's pushout `Monoid.PushoutI φ`. In a) `A` and `B` are countable (SQ-universality is defined
for countable groups, as in 4.39) and `C` is finite; `|A : H| > 2` is `H ≠ A` and `|A : H| ≠ 2`, and
`|B : K| ≥ 2` is `K ≠ B`, so infinite indices (where Mathlib's `Subgroup.index` is `0`) are
included. SQ-universality is the batch's shared `SQUniversalShared.IsSQUniversal`. In b) the factors
are free of finite ranks `r₀`, `r₁`, the amalgamated subgroup is free of finite rank `c`, and both
amalgamated subgroups are proper.
-/

open MathlibExt.GroupTheory.SQUniversalShared

/-- Kourovka 4.45(a) (P. M. Neumann): let `G` be the free product of the countable groups
`A = G₀`, `B = G₁` amalgamating proper finite subgroups `H ≅ K` (`H = φ₀(C) ≤ A`,
`K = φ₁(C) ≤ B` for injective `φᵢ` from a finite group `C`; the amalgamated product is Mathlib's
pushout `Monoid.PushoutI φ`) with `|A : H| > 2` and `|B : K| ≥ 2` (indices may be infinite). Then
`G` is SQ-universal. -/
def finiteAmalgamSQUniversal : Prop :=
  ∀ (G : Fin 2 → Type) [∀ i, Group (G i)] [∀ i, Countable (G i)] (C : Type) [Group C] [Finite C]
    (φ : ∀ i, C →* G i), (∀ i, Function.Injective (φ i)) → (∀ i, (φ i).range ≠ ⊤) →
    (φ 0).range.index ≠ 2 → IsSQUniversal (Monoid.PushoutI φ)

/-- Kourovka 4.45(b) (P. M. Neumann): a free product `A *_H B` of free groups `A = F_{r₀}`,
`B = F_{r₁}` of finite rank amalgamating proper subgroups `H ≅ K` that are free of finite rank
(`H = φ₀(F_c)`, `K = φ₁(F_c)` for injective `φᵢ`; Mathlib's pushout `Monoid.PushoutI φ`) can be
simple. -/
def existsSimpleAmalgamOfFreeGroups : Prop :=
  ∃ (r : Fin 2 → ℕ) (c : ℕ) (φ : ∀ i, FreeGroup (Fin c) →* FreeGroup (Fin (r i))),
    (∀ i, Function.Injective (φ i)) ∧ (∀ i, (φ i).range ≠ ⊤) ∧ IsSimpleGroup (Monoid.PushoutI φ)

/--
Resolved true: Lossov proves that a free product of countable groups `A`, `B` amalgamating finite
proper subgroups `H`, `K` with `|A : H| > 2` and `|B : K| ≥ 2` is SQ-universal; the Kourovka Archive
answers 4.45(a) "Yes, it is". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 4.45 (P. M. Neumann); resolution: K. I. Lossov, SQ-universality of free products
with amalgamated finite subgroups, Siberian Math. J. 27 (1986), no. 6, 890-899; M. Burger and S.
Mozes, Lattices in product of trees, Publ. Math. IHÉS 92 (2000), 151-194, Lossov's main theorem (O.
V. Belegradek's zbMATH review, Zbl 0611.20021: `A *_C B` with `C` finite, `|A : C| ≥ 2`, `|B : C| ≥
3` is SQ-universal, answering P. M. Neumann's question); Burger-Mozes, Introduction and Theorem
5.5(5) (their simple groups are amalgams `F *_E F` of finitely generated free groups over a subgroup
of finite index, answering Problem 4.45); Kourovka Archive of Solved Problems, Problem 4.45: a) Yes,
it is; b) Yes, it can (but if one of the indices |A : H|, |B : K| is infinite, then no, it cannot),
https://doi.org/10.1007/BF00970007.
-/
public theorem_wanted finiteAmalgamSQUniversal_holds : finiteAmalgamSQUniversal

/--
Resolved true: Burger and Mozes construct simple amalgamated free products `A *_H B` of free groups
of finite rank over a common subgroup that is free of finite rank and proper in both factors (DOI
10.1007/BF02698916); the Kourovka Archive answers 4.45(b) "Yes, it can" and adds that if one of the
indices `|A : H|`, `|B : K|` is infinite the product cannot be simple (Ivanov and Schupp). Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.45 (P. M. Neumann);
resolution: K. I. Lossov, SQ-universality of free products with amalgamated finite subgroups,
Siberian Math. J. 27 (1986), no. 6, 890-899; M. Burger and S. Mozes, Lattices in product of trees,
Publ. Math. IHÉS 92 (2000), 151-194, Lossov's main theorem (O. V. Belegradek's zbMATH review, Zbl
0611.20021: `A *_C B` with `C` finite, `|A : C| ≥ 2`, `|B : C| ≥ 3` is SQ-universal, answering P. M.
Neumann's question); Burger-Mozes, Introduction and Theorem 5.5(5) (their simple groups are amalgams
`F *_E F` of finitely generated free groups over a subgroup of finite index, answering Problem
4.45); Kourovka Archive of Solved Problems, Problem 4.45: a) Yes, it is; b) Yes, it can (but if one
of the indices |A : H|, |B : K| is infinite, then no, it cannot),
https://doi.org/10.1007/BF00970007.
-/
public theorem_wanted existsSimpleAmalgamOfFreeGroups_holds : existsSimpleAmalgamOfFreeGroups

end MathlibExt.GroupTheory.AmalgamatedProductSQUniversalSimpleKourovka4Problem45Wanted
