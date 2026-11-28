/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.ComputationalBiology.FactorizableLibraryDesign
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-! Tests for factorizable sequence libraries and the reverse kernel trick.

The alphabet is `Bool`, prefixes have length two and suffixes length one. The two prefixes
`![true, true]` and `![false, true]` and the two suffixes `![true]` and `![false]` give a library
of four sequences of length three, computed here from the definition.

The score is the rank-one score `f z = φp (prefix of z) * φs (suffix of z)` of the prefix feature
`φp x = (if x 0 then 2 else 3) + (if x 1 then 10 else 0)` and the suffix feature
`φs y = if y 0 then 5 else 7`, both real numbers, so that the inner-product space of the reverse
kernel trick is `ℝ` itself:

| prefix | `φp` | suffix | `φs` |
|---|---|---|---|
| `![true, true]` | `12` | `![true]` | `5` |
| `![false, true]` | `13` | `![false]` | `7` |
| `![false, false]` | `3` | | |

* ground truth by enumeration: the four library members score `12 * 5`, `12 * 7`, `13 * 5` and
  `13 * 7`, so the library scores `300`, which is the inner product `(12 + 13) * (5 + 7)` of the
  two running sums;
* replacing the prefix `![false, true]` by `![false, false]` takes the total to `180`, a change
  of `(3 - 13) * 12 = -120`, one inner product;
* a pairwise (Potts) score on one prefix position and one suffix position, with its features of
  dimension `card Bool + 2 = 4`;
* edge cases: a library with no prefix is empty, and the count and the membership test on the
  four-member library. -/

open Domains.Biology.ComputationalBiology.FactorizableLibraryDesign

open scoped InnerProductSpace

namespace DomainsTest.Biology.ComputationalBiology.FactorizableLibraryDesign

/-! ### A library of four sequences -/

/-- The two prefixes of the library. -/
def prefixes : Finset (Fin 2 → Bool) := {![true, true], ![false, true]}

/-- The two suffixes of the library. -/
def suffixes : Finset (Fin 1 → Bool) := {![true], ![false]}

/-- The four sequences of the library. -/
def members : Finset (Fin (2 + 1) → Bool) :=
  {![true, true, true], ![true, true, false], ![false, true, true], ![false, true, false]}

/-- The library of the two prefixes and the two suffixes, computed from the definition. -/
theorem factorizableLibrary_eq : factorizableLibrary prefixes suffixes = members := by
  decide

/-- The library has `2 * 2 = 4` members, from `2 + 2` synthesised segments. -/
example : (factorizableLibrary prefixes suffixes).card = 4 := by
  rw [card_factorizableLibrary]
  decide

/-- A sequence is in the library exactly when it is the concatenation of one of the prefixes with
one of the suffixes: `![false, true, false]` is, and `![true, false, true]` is not. -/
example : ![false, true, false] ∈ factorizableLibrary prefixes suffixes ∧
    ![true, false, true] ∉ factorizableLibrary prefixes suffixes := by
  decide

/-- A library with no prefix is empty. -/
example : factorizableLibrary (∅ : Finset (Fin 2 → Bool)) suffixes = ∅ := by
  decide

/-! ### The reverse kernel trick on a rank-one score -/

/-- The feature of a prefix. -/
def φp (x : Fin 2 → Bool) : ℝ := (if x 0 then 2 else 3) + (if x 1 then 10 else 0)

/-- The feature of a suffix. -/
def φs (y : Fin 1 → Bool) : ℝ := if y 0 then 5 else 7

/-- The score of a sequence: the product of the feature of its prefix with the feature of its
suffix, a rank-one score. -/
def score (z : Fin (2 + 1) → Bool) : ℝ :=
  φp (fun i => z (Fin.castAdd 1 i)) * φs (fun i => z (Fin.natAdd 2 i))

/-- The score factorizes through the two features: in `ℝ` the inner product is the product. -/
theorem score_append (x : Fin 2 → Bool) (y : Fin 1 → Bool) :
    score (Fin.append x y) = ⟪φp x, φs y⟫_ℝ := by
  simp [score, RCLike.inner_apply, mul_comm]

/-- Ground truth: the four members of the library score `12 * 5`, `12 * 7`, `13 * 5` and
`13 * 7`, so the library scores `300`. -/
theorem sum_score_eq : ∑ z ∈ factorizableLibrary prefixes suffixes, score z = 300 := by
  rw [factorizableLibrary_eq, members]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  norm_num [score, φp, φs]

/-- The same total from the reverse kernel trick, as one inner product of the two running sums.
-/
example : ∑ z ∈ factorizableLibrary prefixes suffixes, score z =
    ⟪∑ x ∈ prefixes, φp x, ∑ y ∈ suffixes, φs y⟫_ℝ :=
  sum_factorizableLibrary_eq_inner score_append _ _

/-- The running sums are `12 + 13 = 25` and `5 + 7 = 12`, and their inner product is the `300` of
the enumeration. -/
example : ⟪∑ x ∈ prefixes, φp x, ∑ y ∈ suffixes, φs y⟫_ℝ = 300 := by
  rw [prefixes, suffixes, Finset.sum_pair (by decide), Finset.sum_pair (by decide)]
  norm_num [φp, φs, RCLike.inner_apply]

/-! ### Replacing one prefix -/

/-- Replacing the prefix `![false, true]`, of feature `13`, by `![false, false]`, of feature `3`,
changes the total score by one inner product. -/
example : ∑ z ∈ factorizableLibrary
      (insert ![false, false] (prefixes.erase ![false, true])) suffixes, score z =
    (∑ z ∈ factorizableLibrary prefixes suffixes, score z) +
      ⟪φp ![false, false] - φp ![false, true], ∑ y ∈ suffixes, φs y⟫_ℝ :=
  sum_factorizableLibrary_replace_prefix score_append (by decide) (by decide) _

/-- That change is `(3 - 13) * 12 = -120`, taking the total from `300` to `180`. -/
example : ∑ z ∈ factorizableLibrary
    (insert ![false, false] (prefixes.erase ![false, true])) suffixes, score z = 180 := by
  rw [sum_factorizableLibrary_replace_prefix score_append (X := prefixes) (by decide) (by decide),
    sum_score_eq, suffixes, Finset.sum_pair (by decide)]
  norm_num [φp, φs, RCLike.inner_apply]

/-! ### A pairwise (Potts) score -/

/-- The fields of a pairwise score on one prefix position and one suffix position. -/
def field : Fin 2 → Bool → ℝ := ![fun b => if b then 1 else 2, fun b => if b then 4 else 8]

/-- The coupling of the two positions of the pairwise score. -/
def coupling : Fin 2 → Fin 2 → Bool → Bool → ℝ :=
  fun _ _ a b => if a = b then 3 else -3

/-- The pairwise score: the two fields and the coupling of the two positions. -/
def pairwiseScore (z : Fin 2 → Bool) : ℝ :=
  (∑ i, field i (z i)) + ∑ i, ∑ j ∈ Finset.Ioi i, coupling i j (z i) (z j)

/-- A pairwise score on a finite alphabet has features of dimension
`Ls * card Bool + 2 = 1 * 2 + 2 = 4`. -/
theorem exists_features_pairwiseScore : ∃ φp : (Fin 1 → Bool) → EuclideanSpace ℝ (Fin 4),
    ∃ φs : (Fin 1 → Bool) → EuclideanSpace ℝ (Fin 4),
      ∀ x y, pairwiseScore (Fin.append x y) = ⟪φp x, φs y⟫_ℝ :=
  exists_features_of_pairwise (Lp := 1) (Ls := 1) field coupling pairwiseScore fun _ => rfl

/-- For a pairwise score of three positions over a four-letter alphabet, split after the first
position, the features have dimension `2 * 4 + 2 = 10`. -/
example (h : Fin (1 + 2) → Fin 4 → ℝ) (J : Fin (1 + 2) → Fin (1 + 2) → Fin 4 → Fin 4 → ℝ)
    (f : (Fin (1 + 2) → Fin 4) → ℝ)
    (hf : ∀ z, f z = (∑ i, h i (z i)) + ∑ i, ∑ j ∈ Finset.Ioi i, J i j (z i) (z j)) :
    ∃ φp : (Fin 1 → Fin 4) → EuclideanSpace ℝ (Fin 10),
      ∃ φs : (Fin 2 → Fin 4) → EuclideanSpace ℝ (Fin 10),
        ∀ x y, f (Fin.append x y) = ⟪φp x, φs y⟫_ℝ :=
  exists_features_of_pairwise h J f hf

/-- The two sequences `![true, true]` and `![true, false]` score `1 + 4 + 3 = 8` and
`1 + 8 - 3 = 6`: the library of the one prefix `![true]` and the two suffixes scores `14`. -/
example : ∑ z ∈ factorizableLibrary {![true]} suffixes, pairwiseScore z = 14 := by
  rw [sum_factorizableLibrary, Finset.sum_singleton, suffixes, Finset.sum_pair (by decide),
    show Fin.append ![true] ![true] = ![true, true] from by decide,
    show Fin.append ![true] ![false] = ![true, false] from by decide]
  norm_num [pairwiseScore, field, coupling, Fin.sum_univ_two,
    show Finset.Ioi (0 : Fin 2) = {1} from by decide,
    show Finset.Ioi (1 : Fin 2) = ∅ from by decide]

/-- The features of that pairwise score give those two values as inner products, and the library
of the one prefix `![true]` and the two suffixes as one inner product of the running sums. -/
example : ∃ φp : (Fin 1 → Bool) → EuclideanSpace ℝ (Fin 4),
    ∃ φs : (Fin 1 → Bool) → EuclideanSpace ℝ (Fin 4),
      ⟪φp ![true], φs ![true]⟫_ℝ = 8 ∧ ⟪φp ![true], φs ![false]⟫_ℝ = 6 ∧
        ∑ z ∈ factorizableLibrary {![true]} suffixes, pairwiseScore z =
          ⟪∑ x ∈ {![true]}, φp x, ∑ y ∈ suffixes, φs y⟫_ℝ := by
  obtain ⟨φp, φs, hφ⟩ := exists_features_pairwiseScore
  refine ⟨φp, φs, ?_, ?_, sum_factorizableLibrary_eq_inner hφ _ _⟩
  · rw [← hφ, show Fin.append ![true] ![true] = ![true, true] from by decide]
    norm_num [pairwiseScore, field, coupling, Fin.sum_univ_two,
      show Finset.Ioi (0 : Fin 2) = {1} from by decide,
      show Finset.Ioi (1 : Fin 2) = ∅ from by decide]
  · rw [← hφ, show Fin.append ![true] ![false] = ![true, false] from by decide]
    norm_num [pairwiseScore, field, coupling, Fin.sum_univ_two,
      show Finset.Ioi (0 : Fin 2) = {1} from by decide,
      show Finset.Ioi (1 : Fin 2) = ∅ from by decide]

end DomainsTest.Biology.ComputationalBiology.FactorizableLibraryDesign
