/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# p-groups with an almost regular automorphism (Kourovka Notebook Problem 8.81)

Kourovka Notebook, Archive of Solved Problems, Problem 8.81 (B. Hartley): let `G` be a finite
`p`-group admitting an automorphism `α` of prime order `q` with `|C_G(α)| ≤ n`. a) If `p = q`, then
does `G` have a nilpotent subgroup of class at most `2` and index bounded by a function of `n`? b)
If `p ≠ q`, then does `G` have a nilpotent subgroup of class bounded by a function of `q` and index
bounded by a function of `n` (and, possibly, `q`)?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.AlmostRegularAutomorphismPGroupKourovka8Problem81Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.81 (B.
Hartley). UnsolvedMath record UM-00700529 (`KOU-8.81`), dataset ulamai/UnsolvedMath v1.8.0.

Groups are finite types; `α : MulAut G` has order `q` (`orderOf α`), and `C_G(α)` is the set of
fixed points. "Nilpotent of class at most `c`" is `Subgroup.upperCentralSeries H c = ⊤`. A bound "by
a function of `n`" is a function `f : ℕ → ℕ` independent of the group, the automorphism and the
prime; in (a), `|C_G(α)| ≥ p` for a non-trivial `G`, so allowing `f` to depend on `p` as well would
not change the question. One target per part.
-/

/-- Kourovka 8.81(a) (B. Hartley): there is a function `f` such that every finite `p`-group `G` with
an automorphism `α` of order `p` having at most `n` fixed points has a subgroup of nilpotency class
at most `2` and index at most `f n`. -/
def classTwoSubgroupBoundedIndex : Prop :=
  ∃ f : ℕ → ℕ, ∀ p : ℕ, p.Prime → ∀ (G : Type) [Group G] [Finite G], IsPGroup p G →
    ∀ α : MulAut G, orderOf α = p → ∀ n : ℕ, Nat.card {g : G // α g = g} ≤ n →
      ∃ H : Subgroup G, Subgroup.upperCentralSeries H 2 = ⊤ ∧ H.index ≤ f n

/-- Kourovka 8.81(b) (B. Hartley): there are functions `c` and `f` such that, for primes `p ≠ q`,
every finite `p`-group `G` with an automorphism `α` of order `q` having at most `n` fixed points has
a subgroup of nilpotency class at most `c q` and index at most `f n q`. -/
def boundedClassSubgroupBoundedIndex : Prop :=
  ∃ (c : ℕ → ℕ) (f : ℕ → ℕ → ℕ), ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
    ∀ (G : Type) [Group G] [Finite G], IsPGroup p G → ∀ α : MulAut G, orderOf α = q →
      ∀ n : ℕ, Nat.card {g : G // α g = g} ≤ n →
        ∃ H : Subgroup G, Subgroup.upperCentralSeries H (c q) = ⊤ ∧ H.index ≤ f n q

/--
Resolved false: the Kourovka Archive answers 8.81(a) "Not necessarily", citing Khukhro (Math. Notes
38, 1985), who shows (zbMATH review Zbl 0598.20024) that there are no function `k(p, m)` and
constant `c` such that every finite metabelian `p`-group with an automorphism of order `p` having
`p^m` fixed points has a subgroup of index at most `k(p, m)` and class at most `c`; in particular no
function `f` bounds by `f(n)` the index of a subgroup of class at most `2` when there are at most
`n` fixed points. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory:
The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem
8.81 (B. Hartley); resolution: (a) E. I. Khukhro, Finite p-groups admitting an automorphism of order
p with a small number of fixed points, Math. Notes 38 (1985), 867-870,
https://doi.org/10.1007/BF01157528; (b) E. I. Khukhro, Lie rings and Lie groups admitting an almost
regular automorphism of prime order, Math. USSR-Sb. 71 (1992), 51-63, (a) zbMATH review Zbl
0598.20024: there are no function k(p, m) and constant c such that every finite metabelian p-group
with an automorphism of order p having p^m fixed points has a subgroup of index at most k(p, m) and
class at most c, which solves 8.81(a) in the negative; (b) abstract: a nilpotent periodic group with
an automorphism of prime order p having m fixed points has a nilpotent subgroup of index bounded in
terms of m and p and of class bounded in terms of p, a positive answer to Hartley's Question 8.81b;
Kourovka Archive of Solved Problems, Problem 8.81: a) Not necessarily; b) Yes, it does,
https://doi.org/10.1070/SM1992v071n01ABEH001390.
-/
public theorem_wanted classTwoSubgroupBoundedIndex_refuted : ¬ classTwoSubgroupBoundedIndex

/--
Resolved true: Khukhro (Math. USSR-Sb. 71, 1992) proves that a nilpotent periodic group with an
automorphism of prime order `q` having `m` fixed points has a nilpotent subgroup of index bounded in
terms of `m` and `q` and of class bounded in terms of `q`, which the abstract states is a positive
answer to 8.81(b); the Kourovka Archive answers "Yes, it does". Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.81 (B. Hartley); resolution: (a) E.
I. Khukhro, Finite p-groups admitting an automorphism of order p with a small number of fixed
points, Math. Notes 38 (1985), 867-870, https://doi.org/10.1007/BF01157528; (b) E. I. Khukhro, Lie
rings and Lie groups admitting an almost regular automorphism of prime order, Math. USSR-Sb. 71
(1992), 51-63, (a) zbMATH review Zbl 0598.20024: there are no function k(p, m) and constant c such
that every finite metabelian p-group with an automorphism of order p having p^m fixed points has a
subgroup of index at most k(p, m) and class at most c, which solves 8.81(a) in the negative; (b)
abstract: a nilpotent periodic group with an automorphism of prime order p having m fixed points has
a nilpotent subgroup of index bounded in terms of m and p and of class bounded in terms of p, a
positive answer to Hartley's Question 8.81b; Kourovka Archive of Solved Problems, Problem 8.81: a)
Not necessarily; b) Yes, it does, https://doi.org/10.1070/SM1992v071n01ABEH001390.
-/
public theorem_wanted boundedClassSubgroupBoundedIndex_holds : boundedClassSubgroupBoundedIndex

end MathlibExt.GroupTheory.AlmostRegularAutomorphismPGroupKourovka8Problem81Wanted
