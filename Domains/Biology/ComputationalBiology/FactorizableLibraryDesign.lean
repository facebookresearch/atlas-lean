/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Finset.NAry
public import Mathlib.Order.Interval.Finset.Fin

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Factorizable sequence libraries and the reverse kernel trick

A **factorizable library** over an alphabet `α` is built from a set `X` of prefixes of length
`Lp` and a set `Y` of suffixes of length `Ls`: its members are the concatenations `Fin.append x y`
of a prefix `x ∈ X` with a suffix `y ∈ Y`, so that `#X * #Y` sequences of length `Lp + Ls` come
from `#X + #Y` synthesised segments (`card_factorizableLibrary`).

Let `f` score single sequences. If `f` factorizes through feature maps `φp` and `φs` of the two
segments into a real inner-product space, `f (Fin.append x y) = ⟪φp x, φs y⟫_ℝ`, then the total
score of the library is one inner product of two running sums,

  `∑ z ∈ factorizableLibrary X Y, f z = ⟪∑ x ∈ X, φp x, ∑ y ∈ Y, φs y⟫_ℝ`,

which is `sum_factorizableLibrary_eq_inner`, the **reverse kernel trick** of Dai et al. (2022):
the kernel trick replaces an inner product of features by a kernel evaluation, and this replaces
an expensive function of a concatenation by an inner product of cheap segment features. Keeping
the two sums, replacing one prefix or one suffix changes the total score by a single inner
product (`sum_factorizableLibrary_replace_prefix`, `sum_factorizableLibrary_replace_suffix`),
rather than by re-scoring the `#Y` members built on a replaced prefix, or the `#X` members built
on a replaced suffix.

Over a finite alphabet, a pairwise (Potts) score `f z = ∑ i, h i (z i) + ∑ i < j, J i j (z i)
(z j)` factorizes in this way with features of dimension `Ls * card α + 2`
(`exists_features_of_pairwise`): one coordinate for each suffix position `l` and letter `b`,
carrying the couplings `∑ k, J k (Lp + l) (x k) b` on the prefix side and the indicator
`if y l = b then 1 else 0` on the suffix side, and two coordinates carrying the prefix-only and
the suffix-only parts of the score, each paired with the constant `1`.

## Conventions

* Sequences of length `n` over the alphabet `α` are tuples `Fin n → α`, and the concatenation of
  a prefix with a suffix is `Fin.append`: position `i` of the prefix becomes position
  `Fin.castAdd Ls i` and position `i` of the suffix becomes position `Fin.natAdd Lp i`.
* The feature maps take values in a real inner-product space `V`; the finite-dimensional
  construction of `exists_features_of_pairwise` uses `EuclideanSpace ℝ (Fin (Ls * card α + 2))`.
* A pairwise score has a field `h i` at each position and a coupling `J i j` for each ordered
  pair of positions `i < j`; `J i j` for `j ≤ i` is never read.

## Main definitions

* `factorizableLibrary X Y`: the factorizable library with prefixes `X` and suffixes `Y`, the
  finite set of concatenations `Fin.append x y`.

## Main results

* `card_factorizableLibrary`: the library has `#X * #Y` members.
* `sum_factorizableLibrary`: the total score of the library is the double sum over prefixes and
  suffixes, as distinct pairs give distinct members.
* `sum_factorizableLibrary_eq_inner`: the reverse kernel trick, the total score of the library as
  one inner product of the sum of the prefix features with the sum of the suffix features.
* `sum_factorizableLibrary_replace_prefix`, `sum_factorizableLibrary_replace_suffix`: replacing
  one prefix, or one suffix, changes the total score by one inner product.
* `exists_features_of_pairwise`: a pairwise (Potts) score over a finite alphabet has such feature
  maps, of dimension `Ls * card α + 2`.

## References

* Z. Dai, S. D. Saksena, G. Horny, C. Banholzer, S. Ewert, D. K. Gifford, "Ultra-high-diversity
  factorizable libraries for efficient therapeutic discovery", Genome Research 32 (2022),
  1787–1794, <https://doi.org/10.1101/gr.276593.122>, Methods: "Preliminaries", "SAPS generates
  factorizable libraries" and "The reverse kernel trick allows for efficient library score
  evaluation".
-/

@[expose] public section

open scoped InnerProductSpace

namespace Domains.Biology.ComputationalBiology.FactorizableLibraryDesign

variable {α : Type*} [DecidableEq α] {Lp Ls : ℕ}
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The **factorizable library** with prefixes `X` and suffixes `Y`: the set of all
concatenations `Fin.append x y` of a prefix `x ∈ X` of length `Lp` with a suffix `y ∈ Y` of
length `Ls`. Synthesising the `#X + #Y` segments gives the `#X * #Y` sequences of the library
(`card_factorizableLibrary`).

A score `f` of single sequences that factorizes through features of the two segments,
`f (Fin.append x y) = ⟪φp x, φs y⟫_ℝ`, makes the total score of the library one inner product of
two running sums (`sum_factorizableLibrary_eq_inner`), so that replacing one prefix or one suffix
costs one vector update and one inner product
(`sum_factorizableLibrary_replace_prefix`, `sum_factorizableLibrary_replace_suffix`). -/
def factorizableLibrary (X : Finset (Fin Lp → α)) (Y : Finset (Fin Ls → α)) :
    Finset (Fin (Lp + Ls) → α) :=
  Finset.image₂ Fin.append X Y

variable {X : Finset (Fin Lp → α)} {Y : Finset (Fin Ls → α)}

/-- The members of a factorizable library are exactly the concatenations of one of its prefixes
with one of its suffixes. -/
@[simp]
theorem mem_factorizableLibrary {z : Fin (Lp + Ls) → α} :
    z ∈ factorizableLibrary X Y ↔ ∃ x ∈ X, ∃ y ∈ Y, Fin.append x y = z :=
  Finset.mem_image₂

omit [DecidableEq α] in
private theorem append_injective2 :
    Function.Injective2 (Fin.append : (Fin Lp → α) → (Fin Ls → α) → Fin (Lp + Ls) → α) := by
  intro x₁ x₂ y₁ y₂ hxy
  have h := (Fin.appendEquiv (α := α) Lp Ls).injective (a₁ := (x₁, y₁)) (a₂ := (x₂, y₂)) hxy
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- A factorizable library has `#X * #Y` members: distinct prefixes or distinct suffixes give
distinct sequences, so the `#X + #Y` synthesised segments yield `#X * #Y` library members. -/
theorem card_factorizableLibrary (X : Finset (Fin Lp → α)) (Y : Finset (Fin Ls → α)) :
    (factorizableLibrary X Y).card = X.card * Y.card :=
  Finset.card_image₂ append_injective2 X Y

/-- The total score of a factorizable library is the double sum of the score over prefixes and
suffixes: each pair of a prefix and a suffix contributes its concatenation once. -/
theorem sum_factorizableLibrary {M : Type*} [AddCommMonoid M] (f : (Fin (Lp + Ls) → α) → M)
    (X : Finset (Fin Lp → α)) (Y : Finset (Fin Ls → α)) :
    ∑ z ∈ factorizableLibrary X Y, f z = ∑ x ∈ X, ∑ y ∈ Y, f (Fin.append x y) := by
  rw [factorizableLibrary, ← Finset.image_uncurry_product, Finset.sum_image, Finset.sum_product]
  · rfl
  · rintro ⟨x₁, y₁⟩ - ⟨x₂, y₂⟩ - hxy
    obtain ⟨hx, hy⟩ := append_injective2 hxy
    exact Prod.ext hx hy

/-- **The reverse kernel trick.** If the score `f` of a single sequence is the inner product of a
feature `φp x` of its prefix with a feature `φs y` of its suffix, then the total score of a
factorizable library is the inner product of the sum of the prefix features with the sum of the
suffix features:

  `∑ z ∈ factorizableLibrary X Y, f z = ⟪∑ x ∈ X, φp x, ∑ y ∈ Y, φs y⟫_ℝ`.

Evaluating the right-hand side costs `#X + #Y` feature evaluations and one inner product, instead
of the `#X * #Y` evaluations of `f` on the library. -/
theorem sum_factorizableLibrary_eq_inner {f : (Fin (Lp + Ls) → α) → ℝ}
    {φp : (Fin Lp → α) → V} {φs : (Fin Ls → α) → V}
    (hf : ∀ x y, f (Fin.append x y) = ⟪φp x, φs y⟫_ℝ)
    (X : Finset (Fin Lp → α)) (Y : Finset (Fin Ls → α)) :
    ∑ z ∈ factorizableLibrary X Y, f z = ⟪∑ x ∈ X, φp x, ∑ y ∈ Y, φs y⟫_ℝ := by
  rw [sum_factorizableLibrary, sum_inner]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [inner_sum]
  exact Finset.sum_congr rfl fun y _ => hf x y

/-- Replacing one prefix `x₀` of a factorizable library by a new prefix `x₁` changes the total
score by one inner product of the change `φp x₁ - φp x₀` of the prefix feature with the running
sum of the suffix features, whatever the `#Y` library members that change. -/
theorem sum_factorizableLibrary_replace_prefix {f : (Fin (Lp + Ls) → α) → ℝ}
    {φp : (Fin Lp → α) → V} {φs : (Fin Ls → α) → V}
    (hf : ∀ x y, f (Fin.append x y) = ⟪φp x, φs y⟫_ℝ)
    {x₀ x₁ : Fin Lp → α} (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∉ X) (Y : Finset (Fin Ls → α)) :
    ∑ z ∈ factorizableLibrary (insert x₁ (X.erase x₀)) Y, f z =
      (∑ z ∈ factorizableLibrary X Y, f z) + ⟪φp x₁ - φp x₀, ∑ y ∈ Y, φs y⟫_ℝ := by
  have hx₁' : x₁ ∉ X.erase x₀ := fun hmem => hx₁ (Finset.mem_of_mem_erase hmem)
  have hsum : ∑ x ∈ insert x₁ (X.erase x₀), φp x = (∑ x ∈ X, φp x) + (φp x₁ - φp x₀) := by
    rw [Finset.sum_insert hx₁', ← Finset.sum_erase_add X _ hx₀]
    abel
  rw [sum_factorizableLibrary_eq_inner hf, sum_factorizableLibrary_eq_inner hf, hsum,
    inner_add_left]

/-- Replacing one suffix `y₀` of a factorizable library by a new suffix `y₁` changes the total
score by one inner product of the running sum of the prefix features with the change
`φs y₁ - φs y₀` of the suffix feature, whatever the `#X` library members that change. -/
theorem sum_factorizableLibrary_replace_suffix {f : (Fin (Lp + Ls) → α) → ℝ}
    {φp : (Fin Lp → α) → V} {φs : (Fin Ls → α) → V}
    (hf : ∀ x y, f (Fin.append x y) = ⟪φp x, φs y⟫_ℝ)
    (X : Finset (Fin Lp → α)) {y₀ y₁ : Fin Ls → α} (hy₀ : y₀ ∈ Y) (hy₁ : y₁ ∉ Y) :
    ∑ z ∈ factorizableLibrary X (insert y₁ (Y.erase y₀)), f z =
      (∑ z ∈ factorizableLibrary X Y, f z) + ⟪∑ x ∈ X, φp x, φs y₁ - φs y₀⟫_ℝ := by
  have hy₁' : y₁ ∉ Y.erase y₀ := fun hmem => hy₁ (Finset.mem_of_mem_erase hmem)
  have hsum : ∑ y ∈ insert y₁ (Y.erase y₀), φs y = (∑ y ∈ Y, φs y) + (φs y₁ - φs y₀) := by
    rw [Finset.sum_insert hy₁', ← Finset.sum_erase_add Y _ hy₀]
    abel
  rw [sum_factorizableLibrary_eq_inner hf, sum_factorizableLibrary_eq_inner hf, hsum,
    inner_add_right]

/-! ### Pairwise (Potts) scores

A pairwise score of a concatenation splits into a part of the prefix alone, a part of the suffix
alone, and the couplings between a prefix position and a suffix position, which are linear in the
indicator of the suffix letter. This is the factorization through features of dimension
`Ls * card α + 2` that `exists_features_of_pairwise` states. -/

/-- A sum over the positions after `i` is a sum over all positions of a term that vanishes
except after `i`. -/
private theorem sum_Ioi_eq_sum_ite {n : ℕ} (g : Fin n → Fin n → ℝ) (i : Fin n) :
    ∑ j ∈ Finset.Ioi i, g i j = ∑ j, if i < j then g i j else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp

/-- A sum over the ordered pairs of positions of a concatenation splits into the pairs of two
prefix positions, the pairs of two suffix positions, and the pairs of a prefix position with a
suffix position, which are ordered that way round. -/
private theorem sum_Ioi_append_split (g : Fin (Lp + Ls) → Fin (Lp + Ls) → ℝ) :
    ∑ i, ∑ j ∈ Finset.Ioi i, g i j =
      (∑ k : Fin Lp, ∑ k' ∈ Finset.Ioi k, g (Fin.castAdd Ls k) (Fin.castAdd Ls k')) +
        (∑ l : Fin Ls, ∑ l' ∈ Finset.Ioi l, g (Fin.natAdd Lp l) (Fin.natAdd Lp l')) +
        ∑ l : Fin Ls, ∑ k : Fin Lp, g (Fin.castAdd Ls k) (Fin.natAdd Lp l) := by
  have hcc : ∀ k k' : Fin Lp, (Fin.castAdd Ls k < Fin.castAdd Ls k') ↔ k < k' := by
    intro k k'
    simp only [Fin.lt_def, Fin.val_castAdd]
  have hcn : ∀ (k : Fin Lp) (l : Fin Ls), Fin.castAdd Ls k < Fin.natAdd Lp l := by
    intro k l
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega
  have hnc : ∀ (l : Fin Ls) (k : Fin Lp), ¬Fin.natAdd Lp l < Fin.castAdd Ls k := by
    intro l k
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega
  have hnn : ∀ l l' : Fin Ls, (Fin.natAdd Lp l < Fin.natAdd Lp l') ↔ l < l' := by
    intro l l'
    simp only [Fin.lt_def, Fin.val_natAdd]
    omega
  have hall : ∑ i, ∑ j ∈ Finset.Ioi i, g i j = ∑ i, ∑ j, if i < j then g i j else 0 :=
    Finset.sum_congr rfl fun i _ => sum_Ioi_eq_sum_ite g i
  have hpre : (∑ k : Fin Lp, ∑ k' ∈ Finset.Ioi k, g (Fin.castAdd Ls k) (Fin.castAdd Ls k')) =
      ∑ k : Fin Lp, ∑ k' : Fin Lp,
        if k < k' then g (Fin.castAdd Ls k) (Fin.castAdd Ls k') else 0 :=
    Finset.sum_congr rfl fun k _ =>
      sum_Ioi_eq_sum_ite (fun i j => g (Fin.castAdd Ls i) (Fin.castAdd Ls j)) k
  have hsuf : (∑ l : Fin Ls, ∑ l' ∈ Finset.Ioi l, g (Fin.natAdd Lp l) (Fin.natAdd Lp l')) =
      ∑ l : Fin Ls, ∑ l' : Fin Ls,
        if l < l' then g (Fin.natAdd Lp l) (Fin.natAdd Lp l') else 0 :=
    Finset.sum_congr rfl fun l _ =>
      sum_Ioi_eq_sum_ite (fun i j => g (Fin.natAdd Lp i) (Fin.natAdd Lp j)) l
  rw [hall, hpre, hsuf, Fin.sum_univ_add]
  simp only [Fin.sum_univ_add, hcc, hcn, hnc, hnn, ite_true, ite_false, Finset.sum_const_zero,
    zero_add, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin Lp))) (t := (Finset.univ : Finset (Fin Ls)))]
  abel

/-- The prefix feature of a pairwise score: on the coordinate `Sum.inl (l, b)` of a suffix
position `l` and a letter `b`, the sum over the prefix positions `k` of the coupling
`J k (Lp + l) (x k) b`; on `Sum.inr true`, the part of the score that the prefix alone
contributes; and `1` on `Sum.inr false`, the coordinate that carries the suffix-only part. -/
private def pottsPrefixFeature (h : Fin (Lp + Ls) → α → ℝ)
    (J : Fin (Lp + Ls) → Fin (Lp + Ls) → α → α → ℝ) (x : Fin Lp → α) :
    (Fin Ls × α) ⊕ Bool → ℝ
  | .inl (l, b) => ∑ k : Fin Lp, J (Fin.castAdd Ls k) (Fin.natAdd Lp l) (x k) b
  | .inr true =>
      (∑ k : Fin Lp, h (Fin.castAdd Ls k) (x k)) +
        ∑ k : Fin Lp, ∑ k' ∈ Finset.Ioi k,
          J (Fin.castAdd Ls k) (Fin.castAdd Ls k') (x k) (x k')
  | .inr false => 1

/-- The suffix feature of a pairwise score: on the coordinate `Sum.inl (l, b)`, the indicator of
the letter `b` of the suffix at the position `l`; `1` on `Sum.inr true`, against the prefix-only
part of the score; and on `Sum.inr false`, the part of the score that the suffix alone
contributes. -/
private def pottsSuffixFeature (h : Fin (Lp + Ls) → α → ℝ)
    (J : Fin (Lp + Ls) → Fin (Lp + Ls) → α → α → ℝ) (y : Fin Ls → α) :
    (Fin Ls × α) ⊕ Bool → ℝ
  | .inl (l, b) => if y l = b then 1 else 0
  | .inr true => 1
  | .inr false =>
      (∑ l : Fin Ls, h (Fin.natAdd Lp l) (y l)) +
        ∑ l : Fin Ls, ∑ l' ∈ Finset.Ioi l,
          J (Fin.natAdd Lp l) (Fin.natAdd Lp l') (y l) (y l')

/-- The two features of a pairwise score have the score of the concatenation as their inner
product, coordinate by coordinate. -/
private theorem sum_pottsFeature_mul [Fintype α] (h : Fin (Lp + Ls) → α → ℝ)
    (J : Fin (Lp + Ls) → Fin (Lp + Ls) → α → α → ℝ) (x : Fin Lp → α) (y : Fin Ls → α) :
    ∑ j : (Fin Ls × α) ⊕ Bool, pottsPrefixFeature h J x j * pottsSuffixFeature h J y j =
      (∑ i, h i (Fin.append x y i)) +
        ∑ i, ∑ j ∈ Finset.Ioi i, J i j (Fin.append x y i) (Fin.append x y j) := by
  rw [Fin.sum_univ_add, sum_Ioi_append_split]
  simp only [Fin.append_left, Fin.append_right]
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [pottsPrefixFeature, pottsSuffixFeature, mul_one, one_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  abel

omit [DecidableEq α] in
/-- A **pairwise (Potts) score** over a finite alphabet factorizes through features of the prefix
and of the suffix of dimension `Ls * card α + 2`. If

  `f z = ∑ i, h i (z i) + ∑ i, ∑ j > i, J i j (z i) (z j)`,

with a field `h i` at each position and a coupling `J i j` for each pair of positions `i < j`,
then there are `φp` and `φs` with `f (Fin.append x y) = ⟪φp x, φs y⟫_ℝ`, so that the total score
of a factorizable library is one inner product (`sum_factorizableLibrary_eq_inner`).

The features are those of Dai et al. (2022): one coordinate for each suffix position `l` and
letter `b`, carrying the couplings `∑ k, J k (Lp + l) (x k) b` of the prefix with the letter `b`
at that position and, on the suffix side, the indicator of `y l = b`; and two coordinates
carrying the part of the score that the prefix alone contributes and the part that the suffix
alone contributes, each paired with the constant `1`. -/
theorem exists_features_of_pairwise [Fintype α] (h : Fin (Lp + Ls) → α → ℝ)
    (J : Fin (Lp + Ls) → Fin (Lp + Ls) → α → α → ℝ) (f : (Fin (Lp + Ls) → α) → ℝ)
    (hf : ∀ z, f z = (∑ i, h i (z i)) + ∑ i, ∑ j ∈ Finset.Ioi i, J i j (z i) (z j)) :
    ∃ φp : (Fin Lp → α) → EuclideanSpace ℝ (Fin (Ls * Fintype.card α + 2)),
      ∃ φs : (Fin Ls → α) → EuclideanSpace ℝ (Fin (Ls * Fintype.card α + 2)),
        ∀ x y, f (Fin.append x y) = ⟪φp x, φs y⟫_ℝ := by
  classical
  have hcard : Fintype.card ((Fin Ls × α) ⊕ Bool) = Ls * Fintype.card α + 2 := by simp
  let e : (Fin Ls × α) ⊕ Bool ≃ Fin (Ls * Fintype.card α + 2) := Fintype.equivFinOfCardEq hcard
  refine ⟨fun x => WithLp.toLp 2 fun i => pottsPrefixFeature h J x (e.symm i),
    fun y => WithLp.toLp 2 fun i => pottsSuffixFeature h J y (e.symm i), fun x y => ?_⟩
  rw [hf, ← sum_pottsFeature_mul h J x y, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [← Equiv.sum_comp e.symm fun j => pottsPrefixFeature h J x j * pottsSuffixFeature h J y j]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end Domains.Biology.ComputationalBiology.FactorizableLibraryDesign
