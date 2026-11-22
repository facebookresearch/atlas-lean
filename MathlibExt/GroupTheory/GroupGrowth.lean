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
* `HasPolynomialGrowth` is defined *per generating family* `P`. Independence of the finite
  generating set is proved in `MathlibExt.GroupTheory.GroupGrowthGenerators`
  (`Group.Generators.hasPolynomialGrowth_iff`), from the bi-Lipschitz comparison of word lengths
  in `MathlibExt.GroupTheory.WordMetricComparison`.
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

/-- The growth function of the generating family `P`: the number of elements of `G` whose word
length with respect to `P` is at most `n`, i.e. the cardinality of the word ball of radius `n`. -/
noncomputable def growth (n : ℕ) : ℕ := Nat.card {g : G // P.wordLength g ≤ n}

/-- `P` has *polynomial growth* if its growth function is bounded by a polynomial: there exist
`C d : ℕ` such that the ball of radius `n` has at most `C * (n + 1) ^ d` elements for every `n`. -/
def HasPolynomialGrowth : Prop :=
  (∀ n, Finite {g : G // P.wordLength g ≤ n}) ∧
    ∃ C d : ℕ, ∀ n, P.growth n ≤ C * (n + 1) ^ d

/-- The ball of radius `0` is exactly `{1}`, so the growth function starts at `1`. -/
lemma growth_zero : P.growth 0 = 1 := by
  show Nat.card {g : G // P.wordLength g ≤ 0} = 1
  refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨1, by simp⟩⟩⟩
  rw [P.wordLength_eq_zero_iff.mp (Nat.le_zero.mp a.2),
    P.wordLength_eq_zero_iff.mp (Nat.le_zero.mp b.2)]

/-- Over a finite group every ball is nonempty (it contains the identity), so the growth function
is positive. -/
lemma growth_pos [Finite G] (n : ℕ) : 0 < P.growth n := by
  show 0 < Nat.card {g : G // P.wordLength g ≤ n}
  have : Nonempty {g : G // P.wordLength g ≤ n} :=
    ⟨⟨1, by rw [P.wordLength_one]; exact Nat.zero_le n⟩⟩
  exact Nat.card_pos

/-- The growth function is bounded by the order of the group, since every ball is a subset of `G`. -/
lemma growth_le_card [Finite G] (n : ℕ) : P.growth n ≤ Nat.card G := by
  show Nat.card {g : G // P.wordLength g ≤ n} ≤ Nat.card G
  exact Finite.card_subtype_le _

/-- Every generating family of a finite group has polynomial growth: the growth function is bounded
by the (constant) order of the group, i.e. by a polynomial of degree `0`. -/
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

/-- Polynomial growth implies positive growth at every radius. -/
lemma HasPolynomialGrowth.growth_pos (h : P.HasPolynomialGrowth) (n : ℕ) : 0 < P.growth n :=
  P.growth_pos_of_finite h.1 n

end Group.Generators
