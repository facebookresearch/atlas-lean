/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Test rank of relatively free groups and abelian varieties (Kourovka Notebook Problem 16.87)

Kourovka Notebook, Problem 16.87 (E. I. Timoshenko): let `𝔐` be a variety of groups and `G_r` a free
`r`-generator group in `𝔐`. A subset `S ⊆ G_r` is a test set if every endomorphism of `G_r`
identical on `S` is an automorphism; the minimum of the cardinalities of test sets is the test rank
of `G_r`. Suppose that the test rank of `G_r` is `r` for every `r ≥ 1`. a) Is it true that `𝔐` is an
abelian variety? b) Suppose that `𝔐` is not a periodic variety. Is it true that `𝔐` is the variety
of all abelian groups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.TestRankNonabelianVarietyKourovka16Problem87Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 16.87 (E. I. Timoshenko). UnsolvedMath
record UM-00701278 (`KOU-16.87`), dataset ulamai/UnsolvedMath v1.8.0.

A variety is given by a set of laws `W ⊆ FreeGroup ℕ`; a group lies in it when every law takes the
value `1` under every substitution. `G_r` is `Fᵣ` modulo its verbal subgroup, the normal closure of
all values of the laws in `Fᵣ`. The test rank is the minimum of `Set.encard` over test sets. The
variety is abelian when all its groups are abelian, periodic when some exponent `n > 0` holds in all
its groups, and equal to the variety of all abelian groups when its groups are exactly the abelian
groups (groups taken in `Type`). One target per part.
-/

/-- A group `G` satisfies the laws `W ⊆ FreeGroup ℕ`: every law takes the value `1` under every
substitution of elements of `G` for the variables. The variety defined by `W` is the class of
these groups. -/
def SatisfiesLaws (W : Set (FreeGroup ℕ)) (G : Type*) [Group G] : Prop :=
  ∀ w ∈ W, ∀ φ : FreeGroup ℕ →* G, φ w = 1

/-- The verbal subgroup of `FreeGroup (Fin r)` for the laws `W`: the normal closure of all values
`φ w` of laws under homomorphisms `φ : FreeGroup ℕ →* FreeGroup (Fin r)`. -/
abbrev verbalSubgroup (W : Set (FreeGroup ℕ)) (r : ℕ) : Subgroup (FreeGroup (Fin r)) :=
  Subgroup.normalClosure {x | ∃ w ∈ W, ∃ φ : FreeGroup ℕ →* FreeGroup (Fin r), φ w = x}

/-- The free `r`-generator group `G_r` of the variety defined by `W`. -/
abbrev RelativelyFreeGroup (W : Set (FreeGroup ℕ)) (r : ℕ) : Type :=
  FreeGroup (Fin r) ⧸ verbalSubgroup W r

/-- A test set of `G`: every endomorphism of `G` that is the identity on `S` is an automorphism. -/
def IsTestSet {G : Type*} [Group G] (S : Set G) : Prop :=
  ∀ f : G →* G, (∀ s ∈ S, f s = s) → Function.Bijective f

/-- `G` has test rank `r`: the minimum of the cardinalities of the test sets of `G` is `r`. -/
def HasTestRank (G : Type*) [Group G] (r : ℕ) : Prop :=
  (∃ S : Set G, IsTestSet S ∧ S.encard = r) ∧ ∀ S : Set G, IsTestSet S → (r : ℕ∞) ≤ S.encard

/-- Kourovka 16.87(a) (E. I. Timoshenko): if the free `r`-generator group of a variety has test
rank `r` for every `r ≥ 1`, then the variety is abelian. -/
def testRankVarietyAbelian : Prop :=
  ∀ W : Set (FreeGroup ℕ), (∀ r : ℕ, 1 ≤ r → HasTestRank (RelativelyFreeGroup W r) r) →
    ∀ (G : Type) [Group G], SatisfiesLaws W G → ∀ a b : G, a * b = b * a

/-- Kourovka 16.87(b) (E. I. Timoshenko): if, moreover, the variety is not periodic (no exponent
`n > 0` holds in all its groups), then it is the variety of all abelian groups. -/
def testRankNonperiodicVarietyAllAbelian : Prop :=
  ∀ W : Set (FreeGroup ℕ), (∀ r : ℕ, 1 ≤ r → HasTestRank (RelativelyFreeGroup W r) r) →
    (¬ ∃ n : ℕ, 0 < n ∧ ∀ (G : Type) [Group G], SatisfiesLaws W G → ∀ g : G, g ^ n = 1) →
      ∀ (G : Type) [Group G], (SatisfiesLaws W G ↔ ∀ a b : G, a * b = b * a)

/--
Resolved false: Kinyon and Urban (Section 3.23, Proposition 3.9) show that for a prime `p` the free
groups of every rank `r ≥ 1` in the variety defined by `[[x, y], z] = 1` and `[x, y]^p = 1` have
test rank `r`, while the variety is not abelian since it contains `UT₃(𝔽_p)`. The Kourovka Notebook
(21st issue) answers 16.87(a) "No" (AI solution confirmed by E. I. Timoshenko). Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Problem 16.87 (E. I. Timoshenko); resolution: M. Kinyon and J.
Urban (with Codex gpt-6-astra), Results on problems from the Kourovka Notebook, preprint, version 4
(19 September 2026), Section 3.23 (Problem 16.87): the variety M_p defined by [[x, y], z] = 1 and
[x, y]^p = 1 (p prime) is nonabelian (it contains UT_3(F_p)) and nonperiodic (it contains Z), and
Proposition 3.9 shows that its free group of rank r has test rank r for every r ≥ 1; the Kourovka
Notebook (21st issue) marks 16.87 solved (a), b) No, it is not true in both cases; AI solution
confirmed by E. I. Timoshenko),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka-mathematics.pdf.
-/
public theorem_wanted testRankVarietyAbelian_refuted : ¬ testRankVarietyAbelian

/--
Resolved false: the same variety (`[[x, y], z] = 1`, `[x, y]^p = 1`, `p` prime) is not periodic
since it contains `ℤ`, its free groups of every rank `r ≥ 1` have test rank `r` (Kinyon-Urban,
Proposition 3.9), and it is not the variety of all abelian groups since it contains the non-abelian
group `UT₃(𝔽_p)`. The Kourovka Notebook (21st issue) answers 16.87(b) "No" (AI solution confirmed by
E. I. Timoshenko). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 16.87 (E. I.
Timoshenko); resolution: M. Kinyon and J. Urban (with Codex gpt-6-astra), Results on problems from
the Kourovka Notebook, preprint, version 4 (19 September 2026), Section 3.23 (Problem 16.87): the
variety M_p defined by [[x, y], z] = 1 and [x, y]^p = 1 (p prime) is nonabelian (it contains
UT_3(F_p)) and nonperiodic (it contains Z), and Proposition 3.9 shows that its free group of rank r
has test rank r for every r ≥ 1; the Kourovka Notebook (21st issue) marks 16.87 solved (a), b) No,
it is not true in both cases; AI solution confirmed by E. I. Timoshenko),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka-mathematics.pdf.
-/
public theorem_wanted testRankNonperiodicVarietyAllAbelian_refuted :
    ¬ testRankNonperiodicVarietyAllAbelian

end MathlibExt.GroupTheory.TestRankNonabelianVarietyKourovka16Problem87Wanted
