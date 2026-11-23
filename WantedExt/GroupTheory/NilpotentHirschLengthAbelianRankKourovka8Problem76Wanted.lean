/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hirsch length versus ranks of abelian subgroups (Kourovka Notebook Problem 8.76)

Kourovka Notebook, Archive of Solved Problems, Problem 8.76 (John S. Wilson): give a realistic upper
bound for the torsion-free rank of a finitely generated nilpotent group in terms of the ranks of its
abelian subgroups. More precisely, let `f(n)` be the largest integer `h` such that there is a
finitely generated nilpotent group of torsion-free rank `h` all of whose abelian subgroups have
torsion-free rank at most `n`. It is easy to see that `f(n) ≤ n(n + 1)/2`. Describe the behaviour of
`f(n)` for large `n`. Is `f(n)` bounded below by a quadratic in `n`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Order.Filter.AtTopBot.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.NilpotentHirschLengthAbelianRankKourovka8Problem76Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.76 (John S.
Wilson). UnsolvedMath record UM-00700524 (`KOU-8.76`), dataset ulamai/UnsolvedMath v1.8.0.

Only the yes/no question is formalized; the request to describe the behaviour of `f(n)` is
open-ended. The torsion-free rank of an abelian group is the largest number of independent elements,
so "every abelian subgroup has torsion-free rank at most `n`" says that any `n + 1` pairwise
commuting elements are dependent (`AbelianSubgroupsRankLE`). The torsion-free rank (Hirsch length)
of a finitely generated nilpotent group is the number of infinite factors in a cyclic series (`1 =
G₀ ⊴ G₁ ⊴ ⋯ ⊴ Gₘ = G`, `Gᵢ₊₁ = Gᵢ⟨gᵢ⟩`), the same for every such series (`HirschLengthGE`). "Bounded
below by a quadratic" is stated as `f(n) ≥ c n²` for some `c > 0` and all large `n`, which is
equivalent to `f(n) ≥ q(n)` for all `n` for a quadratic `q` with positive leading coefficient;
`f(n)` is not used as a function, the target asserts the witnessing groups.
-/

/-- Every abelian subgroup of `G` has torsion-free rank at most `n`: any `n + 1` pairwise commuting
elements `x₀, …, xₙ` are dependent, `x₀^{m₀} ⋯ xₙ^{mₙ} = 1` for some non-zero `m : Fin (n + 1) → ℤ`
(pairwise commuting elements generate an abelian subgroup, and the torsion-free rank of an abelian
group is the largest number of independent elements). -/
def AbelianSubgroupsRankLE (G : Type*) [Group G] (n : ℕ) : Prop :=
  ∀ x : Fin (n + 1) → G, (∀ i j, Commute (x i) (x j)) →
    ∃ m : Fin (n + 1) → ℤ, m ≠ 0 ∧ (List.ofFn fun i => x i ^ m i).prod = 1

/-- `G` has torsion-free rank (Hirsch length) at least `h`: it has a cyclic series
`1 = G₀ ≤ G₁ ≤ ⋯ ≤ Gₘ = G`, each `Gᵢ` normal in `Gᵢ₊₁ = Gᵢ ⊔ ⟨gᵢ⟩`, with at least `h` infinite
factors (`Gᵢ` of infinite index in `Gᵢ₊₁`). For a polycyclic group, e.g. a finitely generated
nilpotent group, every cyclic series has the same number of infinite factors, the Hirsch length. -/
def HirschLengthGE (G : Type*) [Group G] (h : ℕ) : Prop :=
  ∃ (m : ℕ) (s : ℕ → Subgroup G) (g : ℕ → G), s 0 = ⊥ ∧ s m = ⊤ ∧
    (∀ i < m, ((s i).subgroupOf (s (i + 1))).Normal ∧ s (i + 1) = s i ⊔ Subgroup.zpowers (g i)) ∧
    ∃ t : Finset ℕ, t ⊆ Finset.range m ∧ h ≤ t.card ∧ ∀ i ∈ t, (s i).relIndex (s (i + 1)) = 0

/-- Kourovka 8.76 (J. S. Wilson), the quadratic lower bound: let `f(n)` be the largest torsion-free
rank of a finitely generated nilpotent group all of whose abelian subgroups have torsion-free rank
at most `n`. Then `f(n)` is bounded below by a quadratic in `n`: there is `c > 0` such that for all
large `n` some finitely generated nilpotent group with abelian subgroups of torsion-free rank at
most `n` has torsion-free rank at least `c n²`. -/
def nilpotentHirschLengthQuadraticLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in Filter.atTop, ∃ (G : Type) (_ : Group G), Group.FG G ∧
    Group.IsNilpotent G ∧ AbelianSubgroupsRankLE G n ∧
      ∃ h : ℕ, c * (n : ℝ) ^ 2 ≤ h ∧ HirschLengthGE G h

/--
Resolved true: the Kourovka Archive answers the question of 8.76 "Yes, it is", citing Milenteva, who
proves `f(n) ≥ (n² - 4)/8 + n` (zbMATH review Zbl 1057.20027): `f(n)` is bounded below by a
quadratic in `n`, i.e. for some `c > 0` and all large `n` there are finitely generated nilpotent
groups whose abelian subgroups have torsion-free rank at most `n` and whose torsion-free rank is at
least `c n²`. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.76
(John S. Wilson); resolution: M. V. Milenteva, On the torsion-free ranks of finitely generated
nilpotent groups and of their abelian subgroups, J. Group Theory 7 (2004), no. 3, 403-408, main
theorem as stated in the zbMATH review Zbl 1057.20027 (A. I. Budkin): f(n) ≥ (n² - 4)/8 + n;
Kourovka Archive of Solved Problems, Problem 8.76: Yes, it is,
https://doi.org/10.1515/jgth.2004.015.
-/
public theorem_wanted nilpotentHirschLengthQuadraticLowerBound_holds :
    nilpotentHirschLengthQuadraticLowerBound

end MathlibExt.GroupTheory.NilpotentHirschLengthAbelianRankKourovka8Problem76Wanted
