/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Group.WordMetric
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Growth of a finitely generated group

The *growth function* of a group `G` with respect to a generating family `P : Group.Generators G ι`
counts, for each radius `n`, the number of group elements whose word length is at most `n`, i.e. the
cardinality of the ball of radius `n` in the word metric induced by `P`. A group has *polynomial
growth* (with respect to `P`) if this count is bounded by a polynomial in `n`.

## Main definitions

* `Group.Generators.growth`: the growth function `γ_P(n) = |{g : G | wordLength g ≤ n}|` of the
  generating family `P`, defined as the `Nat.card` of the word ball of radius `n`.
* `Group.Generators.HasPolynomialGrowth`: the predicate that `P` has polynomial growth, i.e. there
  are `C d : ℕ` with `γ_P(n) ≤ C * (n + 1) ^ d` for all `n`.

## Main results

* `Group.Generators.growth_zero`: the ball of radius `0` contains only the identity, so
  `γ_P(0) = 1`.
* `Group.Generators.growth_le_card`: the growth function is bounded by the order of the group.
* `Group.Generators.hasPolynomialGrowth_of_finite`: every generating family of a finite group has
  polynomial growth (indeed, bounded growth of degree `0`).

## Implementation notes

* Growth is defined thinly over the word-length API `Group.Generators.wordLength`
  (`Mathlib.Geometry.Group.WordMetric`); it does not re-derive word length.
* `growth` uses `Nat.card`, which is the honest cardinality when the ball is finite (the case of a
  finitely generated group with a finite generating set) and takes the junk value `0` when the ball
  is infinite. The lemmas that need genuine cardinalities are stated under a `[Finite _]` hypothesis.
* `HasPolynomialGrowth` requires every word ball to be finite: `growth` uses `Nat.card`, which
  is the junk value `0` on an infinite subtype, so without finiteness an infinite group with
  the all-elements generating family would spuriously satisfy the bound. For a finite
  generating family (`[Finite ι]`) balls are finite in the intended applications; the
  predicate records the requirement explicitly rather than hiding it in `Nat.card`.
* `HasPolynomialGrowth` is defined *per generating family* `P`. The large-scale growth type is a
  quasi-isometry invariant and hence independent of the finite generating set, but proving this
  requires the bi-Lipschitz comparison of word metrics for different generating sets, which is not
  available cheaply here; we therefore do not state generating-set independence.
* The bound uses `(n + 1) ^ d` rather than `n ^ d` so that the `n = 0` boundary (`γ_P(0) = 1`) is
  covered by the same inequality.

## References

* [M. Gromov, *Groups of polynomial growth and expanding maps*][Gromov1981]

## Tags

group growth, growth function, polynomial growth, word metric, geometric group theory
-/

@[expose] public section

namespace Group.Generators

variable {G ι : Type*} [Group G] (P : Group.Generators G ι)

/-- **Growth function of a generating family.** Let $P$ be a generating family of a group $G$.
The growth function $\gamma_P$ of $P$ assigns to each natural number $n$ the number of elements
$g \in G$ whose word length with respect to $P$ is at most $n$, that is, the cardinality of the
ball of radius $n$ in the word metric of $P$; when this ball is infinite, $\gamma_P(n)$ is taken
to be $0$. -/
noncomputable def growth (n : ℕ) : ℕ := Nat.card {g : G // P.wordLength g ≤ n}

/-- **Polynomial growth.** Let $P$ be a generating family of a group $G$, with growth function
$\gamma_P$. Then $P$ has polynomial growth if, for every natural number $n$, the ball of radius
$n$ (the set of elements of $G$ of word length at most $n$ with respect to $P$) is finite, and
there are natural numbers $C$ and $d$ such that $\gamma_P(n) \le C (n + 1)^d$ for every
natural number $n$. -/
def HasPolynomialGrowth : Prop :=
  (∀ n, Finite {g : G // P.wordLength g ≤ n}) ∧
    ∃ C d : ℕ, ∀ n, P.growth n ≤ C * (n + 1) ^ d

/-- **The growth function at radius zero.** For every generating family $P$ of a group $G$, the
growth function of $P$ takes the value $1$ at $0$: the ball of radius $0$ consists of the identity
element alone. -/
lemma growth_zero : P.growth 0 = 1 := by
  show Nat.card {g : G // P.wordLength g ≤ 0} = 1
  refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨1, by simp⟩⟩⟩
  rw [P.wordLength_eq_zero_iff.mp (Nat.le_zero.mp a.2),
    P.wordLength_eq_zero_iff.mp (Nat.le_zero.mp b.2)]

/-- **The growth function of a finite group is positive.** For every generating family $P$ of a
finite group $G$ and every natural number $n$, the growth function of $P$ is positive at $n$: the
ball of radius $n$ contains the identity. -/
lemma growth_pos [Finite G] (n : ℕ) : 0 < P.growth n := by
  show 0 < Nat.card {g : G // P.wordLength g ≤ n}
  have : Nonempty {g : G // P.wordLength g ≤ n} :=
    ⟨⟨1, by rw [P.wordLength_one]; exact Nat.zero_le n⟩⟩
  exact Nat.card_pos

/-- **The growth function is bounded by the order of the group.** For every generating family $P$
of a finite group $G$ and every natural number $n$, the value of the growth function of $P$ at $n$
is at most the order of $G$, since every ball is a subset of $G$. -/
lemma growth_le_card [Finite G] (n : ℕ) : P.growth n ≤ Nat.card G := by
  show Nat.card {g : G // P.wordLength g ≤ n} ≤ Nat.card G
  exact Finite.card_subtype_le _

/-- **Finite groups have polynomial growth.** Every generating family of a finite group has
polynomial growth: its growth function is bounded by the order of the group, a polynomial of
degree $0$. -/
theorem hasPolynomialGrowth_of_finite [Finite G] : P.HasPolynomialGrowth := by
  refine ⟨fun _ => inferInstance, Nat.card G, 0, fun n => ?_⟩
  simpa using P.growth_le_card n

lemma growth_pos_of_finite (hfin : ∀ n, Finite {g : G // P.wordLength g ≤ n}) (n : ℕ) :
    0 < P.growth n := by
  haveI := hfin n
  show 0 < Nat.card {g : G // P.wordLength g ≤ n}
  have : Nonempty {g : G // P.wordLength g ≤ n} :=
    ⟨⟨1, by rw [P.wordLength_one]; exact Nat.zero_le n⟩⟩
  exact Nat.card_pos

/-- **Polynomial growth makes the growth function positive.** If a generating family $P$ of a
group $G$ has polynomial growth, then the growth function of $P$ is positive at every natural
number $n$. -/
lemma HasPolynomialGrowth.growth_pos (h : P.HasPolynomialGrowth) (n : ℕ) : 0 < P.growth n :=
  P.growth_pos_of_finite h.1 n

end Group.Generators
