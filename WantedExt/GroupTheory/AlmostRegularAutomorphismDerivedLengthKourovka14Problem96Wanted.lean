/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Almost regular automorphisms of `p`-groups and derived length (Kourovka Notebook Problem 14.96)

Kourovka Notebook, Archive of Solved Problems, Problem 14.96 (E. I. Khukhro): if a finite `p`-group
`P` admits an automorphism of order `pⁿ` having exactly `pᵐ` fixed points, does `P` have a subgroup
of index bounded in terms of `p`, `n` and `m` which is soluble of derived length bounded in terms of
`m`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.AlmostRegularAutomorphismDerivedLengthKourovka14Problem96Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.96 (E. I.
Khukhro). UnsolvedMath record UM-00701080 (`KOU-14.96`), dataset ulamai/UnsolvedMath v1.8.0.

"Bounded in terms of" is made explicit by functions `f(p, n, m)` and `g(m)` chosen before `P`, so
the derived-length bound depends on `m` only. Derived length at most `g(m)` is `derivedSeries H (g
m) = ⊥`; the fixed points of `φ` are the `x` with `φ x = x`.
-/

/-- **Bounded-index subgroups of bounded derived length (Kourovka 14.96).** The proposition that
there are functions $f \colon \mathbb{N}^3 \to \mathbb{N}$ and $g \colon \mathbb{N} \to \mathbb{N}$
such that for every prime $p$, all natural numbers $n$ and $m$, every finite $p$-group $P$ and
every automorphism $\varphi$ of $P$ of order $p^n$ with exactly $p^m$ fixed points, $P$ has a
subgroup of index at most $f(p, n, m)$ that is soluble of derived length at most $g(m)$.

This is the question posed by E. I. Khukhro as Kourovka Problem 14.96. -/
def boundedIndexSubgroupOfBoundedDerivedLength : Prop :=
  ∃ (f : ℕ → ℕ → ℕ → ℕ) (g : ℕ → ℕ), ∀ p n m : ℕ, p.Prime →
    ∀ (P : Type) [Group P] [Finite P], IsPGroup p P →
      ∀ φ : MulAut P, orderOf φ = p ^ n → Nat.card {x : P // φ x = x} = p ^ m →
        ∃ H : Subgroup P, H.index ≤ f p n m ∧ derivedSeries H (g m) = ⊥

/--
**Almost regular automorphisms of finite $p$-groups and derived length (Kourovka 14.96).** There
are functions $f \colon \mathbb{N}^3 \to \mathbb{N}$ and $g \colon \mathbb{N} \to \mathbb{N}$ such
that for every prime $p$, all natural numbers $n$ and $m$, every finite $p$-group $P$ and every
automorphism $\varphi$ of $P$ of order $p^n$ with exactly $p^m$ fixed points, $P$ has a subgroup
of index at most $f(p, n, m)$ that is soluble of derived length at most $g(m)$. So Khukhro's
question of Kourovka Problem 14.96 has a positive answer.

This was proved by Jaikin-Zapirain.

Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.96 (E. I. Khukhro); resolution: A.
Jaikin-Zapirain, On almost regular automorphisms of finite p-groups, Adv. Math. 153 (2000), no. 2,
391-402, main theorem (a subgroup of (p, n, m)-bounded index and m-bounded derived length); Kourovka
Archive, Problem 14.96 (answer: Yes, it is true).
-/
public theorem_wanted boundedIndexSubgroupOfBoundedDerivedLength_holds :
    boundedIndexSubgroupOfBoundedDerivedLength

end MathlibExt.GroupTheory.AlmostRegularAutomorphismDerivedLengthKourovka14Problem96Wanted
