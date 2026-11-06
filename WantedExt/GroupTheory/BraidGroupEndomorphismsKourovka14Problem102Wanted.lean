/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Endomorphisms and quotients of braid groups (Kourovka Notebook Problem 14.102)

Kourovka Notebook, Problem 14.102 (V. Lin; V. Shpilrain), for the braid group `Bₙ`, `n > 4`: (a)
does `Bₙ` have non-trivial non-injective endomorphisms with non-cyclic images? (b) is every
non-trivial endomorphism of `[Bₙ, Bₙ]` an automorphism? (c) (Archive of Solved Problems) does `Bₙ`
have proper non-abelian torsion-free quotients?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.PresentedGroup

@[expose] public section

namespace MathlibExt.GroupTheory.BraidGroupEndomorphismsKourovka14Problem102Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.102 (V. Lin; V. Shpilrain); part (c) in
the Archive of Solved Problems. UnsolvedMath record UM-00701086 (`KOU-14.102`), dataset
ulamai/UnsolvedMath v1.8.0.

`Bₙ` is given by Artin's presentation, as in `BraidConjugacyProblemKourovka1Problem11Wanted`. (a) is
stated for some `n > 4` and refuted, so the refutation covers every `n > 4`; a non-cyclic image is
automatically non-trivial. (b) and (c) are stated for every `n > 4`. A proper quotient is `Bₙ / N`
with `N ≠ 1`; torsion-free means no nontrivial element of finite order.
-/

open FreeGroup

/-- Artin's relators for the braid group on `n` strands, in the free group on the generators
`σ₀, …, σ_{n-2}` (indexed by `Fin (n - 1)`): `σᵢ σⱼ = σⱼ σᵢ` when `j ≥ i + 2`, and
`σᵢ σᵢ₊₁ σᵢ = σᵢ₊₁ σᵢ σᵢ₊₁`. -/
def braidRelators (n : ℕ) : Set (FreeGroup (Fin (n - 1))) :=
  {r | ∃ i j : Fin (n - 1),
    (i.val + 2 ≤ j.val ∧ r = of i * of j * (of i)⁻¹ * (of j)⁻¹) ∨
    (i.val + 1 = j.val ∧ r = of i * of j * of i * (of j * of i * of j)⁻¹)}

/-- The braid group `Bₙ` on `n` strands, by Artin's presentation. -/
abbrev BraidGroup (n : ℕ) : Type := PresentedGroup (braidRelators n)

/-- **Kourovka Problem 14.102(a): non-injective braid endomorphisms with non-cyclic image.** The
statement that for some $n > 4$ the braid group $B_n$ on $n$ strands has a non-injective
endomorphism whose image is not cyclic (in particular not trivial). Posed by V. Lin and
V. Shpilrain. -/
def braidNonInjectiveNoncyclicEndomorphism : Prop :=
  ∃ n : ℕ, 4 < n ∧ ∃ φ : BraidGroup n →* BraidGroup n, ¬ Function.Injective φ ∧
    ¬ IsCyclic φ.range

/-- **Kourovka Problem 14.102(b): endomorphisms of the braid commutator subgroup.** The statement
that for every $n > 4$, every endomorphism of the commutator subgroup $[B_n, B_n]$ of the braid
group $B_n$ on $n$ strands other than the trivial endomorphism is bijective, that is, an
automorphism. Posed by V. Lin and V. Shpilrain. -/
def braidCommutatorEndomorphismAutomorphism : Prop :=
  ∀ n : ℕ, 4 < n → ∀ φ : commutator (BraidGroup n) →* commutator (BraidGroup n), φ ≠ 1 →
    Function.Bijective φ

/-- **Kourovka Problem 14.102(c): torsion-free quotients of braid groups.** The statement that for
every $n > 4$, the braid group $B_n$ on $n$ strands has a nontrivial normal subgroup $N$ such that
the quotient $B_n / N$ is non-abelian and torsion-free (no element other than the identity has
finite order). Posed by V. Lin and V. Shpilrain. -/
def braidTorsionFreeNonabelianProperQuotient : Prop :=
  ∀ n : ℕ, 4 < n → ∃ (N : Subgroup (BraidGroup n)) (_ : N.Normal), N ≠ ⊥ ∧
    (∃ x y : BraidGroup n ⧸ N, x * y ≠ y * x) ∧
    ∀ x : BraidGroup n ⧸ N, x ≠ 1 → ¬ IsOfFinOrder x

/--
**Non-injective endomorphisms of braid groups on five or more strands have cyclic image.** The
answer to Kourovka Problem 14.102(a) is negative: there is no $n > 4$ for which the braid group
$B_n$ on $n$ strands has a non-injective endomorphism whose image is not cyclic. Equivalently, for
every $n \ge 5$, every non-injective endomorphism of $B_n$ has cyclic image.

This was proved by Castel for $n \ge 6$ and by Chen, Kordek and Margalit for $n = 5$; the Kourovka
Notebook (21st issue) answers 14.102(a) "No".

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.102 (V. Lin; V. Shpilrain);
part (c) in the Archive of Solved Problems; resolution: (a) F. Castel, Geometric representations of
the braid groups, Astérisque 378 (2016) (n ≥ 6), and L. Chen, K. Kordek and D. Margalit,
Homomorphisms between braid groups, arXiv:1910.00712 (n = 5); (b) S. Orevkov, Ann. Fac. Sci.
Toulouse Math. 33 (2024), no. 1, 105-121, extending K. Kordek and D. Margalit, Bull. London Math.
Soc. 54 (2022), 95-111 (n ≥ 7); (c) P. Linnell and T. Schick, J. Amer. Math. Soc. 20 (2007), no. 4,
1003-1051, the Kourovka Notebook (21st issue) marks 14.102(a), (b) solved (for n ≥ 5 every
non-injective endomorphism of B_n has cyclic image; every non-trivial endomorphism of [B_n, B_n] is
an automorphism); Kourovka Archive, Problem 14.102(c) (Yes), https://arxiv.org/abs/1910.00712.
-/
public theorem_wanted braidNonInjectiveNoncyclicEndomorphism_refuted :
    ¬ braidNonInjectiveNoncyclicEndomorphism

/--
**Nontrivial endomorphisms of the braid commutator subgroup on five or more strands are
automorphisms.** For every $n > 4$, every endomorphism of the commutator subgroup $[B_n, B_n]$ of
the braid group $B_n$ on $n$ strands other than the trivial endomorphism is bijective, that is, an
automorphism.

This was proved by Kordek and Margalit for $n \ge 7$ and extended by Orevkov to all $n \ge 5$; the
Kourovka Notebook (21st issue) answers 14.102(b) "Yes".

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory:
The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.102 (V. Lin; V. Shpilrain);
part (c) in the Archive of Solved Problems; resolution: (a) F. Castel, Geometric representations of
the braid groups, Astérisque 378 (2016) (n ≥ 6), and L. Chen, K. Kordek and D. Margalit,
Homomorphisms between braid groups, arXiv:1910.00712 (n = 5); (b) S. Orevkov, Ann. Fac. Sci.
Toulouse Math. 33 (2024), no. 1, 105-121, extending K. Kordek and D. Margalit, Bull. London Math.
Soc. 54 (2022), 95-111 (n ≥ 7); (c) P. Linnell and T. Schick, J. Amer. Math. Soc. 20 (2007), no. 4,
1003-1051, the Kourovka Notebook (21st issue) marks 14.102(a), (b) solved (for n ≥ 5 every
non-injective endomorphism of B_n has cyclic image; every non-trivial endomorphism of [B_n, B_n] is
an automorphism); Kourovka Archive, Problem 14.102(c) (Yes), https://arxiv.org/abs/1910.00712.
-/
public theorem_wanted braidCommutatorEndomorphismAutomorphism_holds :
    braidCommutatorEndomorphismAutomorphism

/--
**Braid groups on five or more strands have proper non-abelian torsion-free quotients.** For
every $n > 4$, the braid group $B_n$ on $n$ strands has a nontrivial normal subgroup $N$ such that
the quotient $B_n / N$ is non-abelian and torsion-free (no element other than the identity has
finite order).

The Kourovka Archive answers 14.102(c) "Yes, it does", citing Linnell and Schick (every braid group
is residually torsion-free nilpotent-by-finite); Humphries had constructed such quotients for
$n < 7$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.102 (V. Lin; V.
Shpilrain); part (c) in the Archive of Solved Problems; resolution: (a) F. Castel, Geometric
representations of the braid groups, Astérisque 378 (2016) (n ≥ 6), and L. Chen, K. Kordek and D.
Margalit, Homomorphisms between braid groups, arXiv:1910.00712 (n = 5); (b) S. Orevkov, Ann. Fac.
Sci. Toulouse Math. 33 (2024), no. 1, 105-121, extending K. Kordek and D. Margalit, Bull. London
Math. Soc. 54 (2022), 95-111 (n ≥ 7); (c) P. Linnell and T. Schick, J. Amer. Math. Soc. 20 (2007),
no. 4, 1003-1051, the Kourovka Notebook (21st issue) marks 14.102(a), (b) solved (for n ≥ 5 every
non-injective endomorphism of B_n has cyclic image; every non-trivial endomorphism of [B_n, B_n] is
an automorphism); Kourovka Archive, Problem 14.102(c) (Yes), https://arxiv.org/abs/1910.00712.
-/
public theorem_wanted braidTorsionFreeNonabelianProperQuotient_holds :
    braidTorsionFreeNonabelianProperQuotient

end MathlibExt.GroupTheory.BraidGroupEndomorphismsKourovka14Problem102Wanted
