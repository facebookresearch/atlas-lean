/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.RationalSimplicialHomologyShared
public import MathlibExt.Probability.ProbabilityMassFunction.Uniform
import Mathlib.Data.Finset.Powerset

/-!
# Face laws of a pure weighted simplicial complex

Let `K` be a finite pure simplicial complex of dimension `d`: it is closed under subsets, and
every face lies in a face with `d + 1` vertices. Give these top faces any full-support
probability law. When no weighting is specified, `PureWeightedComplex.uniform` gives the
uniform law on the top faces, provided that rank is nonempty.

A top face contains `choose (d + 1) k` subfaces of cardinality `k` for every natural `k`.
This count is zero above `d + 1`. For `0 ≤ k ≤ d + 1`, draw one top face and then choose
uniformly among its `k`-vertex subsets. The mass of a face `τ` is the sum of the masses of
the top faces containing `τ`, divided by `choose (d + 1) k`. These masses are positive
and sum to one at each such rank; they need not be equal even for a uniform top law.
At `k = 0` the sole outcome is the empty face (dimension `-1`); at `k = d + 1` the law
is the given top law.

Dinur and Kaufman, *High dimensional expanders imply agreement expanders*, ECCC TR17-089
(2017), §2.2, p. 15 and §3.1, pp. 16–17 describe the empty face and successive uniform
deletions. Here each rank law is constructed directly from the initial top face.
-/

@[expose] public section

namespace MathlibExt.Combinatorics

open RationalSimplicialHomologyShared
open scoped ENNReal

/-- A finite family `K` of finite sets of natural-number vertices, closed under subsets, in
which every face lies in a face of size `d + 1`. A weighting is a probability law on those
size-`d + 1` faces that gives strictly positive mass to every one of them. -/
structure PureWeightedComplex (K : Finset (Finset ℕ)) (d : ℕ) where
  /-- The family is closed under taking subsets. -/
  simplicial : IsSimplicialComplex K
  /-- Every member of `K` is contained in a member with exactly `d + 1` vertices. -/
  covers : ∀ τ ∈ K, ∃ σ : facesOfCard K (d + 1), τ ⊆ σ.val
  /-- The probability distribution on the members of `K` with `d + 1` vertices; it need
  not be uniform. -/
  topLaw : PMF (facesOfCard K (d + 1))
  /-- Every top face has strictly positive mass. -/
  top_pos : ∀ σ, 0 < topLaw σ

namespace PureWeightedComplex

variable {K : Finset (Finset ℕ)} {d k : ℕ}

/-- Equip a downward-closed finite family with the uniform top weighting when every face
extends to a face with `d + 1` vertices and that top rank is nonempty. This is the weighting
used when none is specified; it does not require the induced lower laws to be uniform. -/
noncomputable def uniform (hK : IsSimplicialComplex K)
    (hc : ∀ τ ∈ K, ∃ σ : facesOfCard K (d + 1), τ ⊆ σ.val)
    (hne : (facesOfCard K (d + 1)).Nonempty) : PureWeightedComplex K d := by
  letI : Nonempty ↥(facesOfCard K (d + 1)) := hne.to_subtype
  exact ⟨hK, hc, PMF.uniformFintype _, fun σ => by simp⟩

variable (X : PureWeightedComplex K d)

include X in
/-- In a pure weighted complex the facets are exactly the faces of cardinality `d + 1`. -/
theorem isFacet_iff {τ : Finset ℕ} : IsFacet K τ ↔ τ ∈ facesOfCard K (d + 1) := by
  constructor
  · intro ⟨hτ, hmax⟩
    obtain ⟨σ, hσ⟩ := X.covers τ hτ
    exact hmax σ.val (Finset.mem_filter.mp σ.property).1 hσ ▸ σ.property
  · intro hτ
    refine ⟨(Finset.mem_filter.mp hτ).1, fun γ hγ hsub => ?_⟩
    obtain ⟨σ, hσ⟩ := X.covers γ hγ
    apply Eq.symm <| Finset.eq_of_subset_of_card_le hsub ?_
    calc γ.card ≤ σ.val.card := Finset.card_le_card hσ
      _ = d + 1 := (Finset.mem_filter.mp σ.property).2
      _ = τ.card := (Finset.mem_filter.mp hτ).2.symm

/-- For a member `σ` of `K` with `d + 1` vertices, the members of `K` of size `k`
contained in `σ`, returned as elements of `facesOfCard K k`. If `K` is downward closed,
these are all the `k`-element subsets of `σ`. -/
def subfaces (σ : facesOfCard K (d + 1)) (k : ℕ) : Finset (facesOfCard K k) :=
  (σ.val.powersetCard k).subtype (· ∈ facesOfCard K k)

include X in
/-- For a top face of a pure weighted `d`-dimensional complex and any natural `k`, the
number of its `k`-vertex subfaces is `choose (d + 1) k`: downward closure retains every
`k`-element subset. The count is zero when `d + 1 < k`. -/
theorem card_subfaces (σ : facesOfCard K (d + 1)) :
    (subfaces σ k).card = (d + 1).choose k := by
  have hm := Finset.subtype_map_of_mem (p := fun τ => τ ∈ facesOfCard K k)
    (s := σ.val.powersetCard k) fun τ hτ => Finset.mem_filter.mpr
      ⟨X.simplicial _ (Finset.mem_filter.mp σ.property).1 τ (Finset.mem_powersetCard.mp hτ).1,
        (Finset.mem_powersetCard.mp hτ).2⟩
  simpa only [subfaces, Finset.card_map, Finset.card_powersetCard,
    (Finset.mem_filter.mp σ.property).2] using congrArg Finset.card hm

/-- Given a top face `σ` of a pure weighted `d`-dimensional complex and `0 ≤ k ≤ d + 1`,
the uniform law on the `choose (d + 1) k` subsets of `σ` with `k` vertices, viewed as a
probability law on the `k`-vertex faces of the complex. -/
noncomputable def subfaceLaw (hk : k ≤ d + 1) (σ : facesOfCard K (d + 1)) :
    PMF (facesOfCard K k) :=
  PMF.uniformFinset (subfaces σ k) (Finset.card_pos.mp ((X.card_subfaces σ).symm ▸
    Nat.choose_pos hk))

/-- For a pure weighted `d`-dimensional complex and `0 ≤ k ≤ d + 1`, the law on its
`k`-vertex faces obtained by drawing one top face from its given full-support law and then
choosing a uniform `k`-vertex subset of that face. -/
noncomputable def faceLaw (hk : k ≤ d + 1) : PMF (facesOfCard K k) :=
  X.topLaw.bind (X.subfaceLaw hk)

/-- For a `k`-vertex face `τ` of a pure weighted `d`-dimensional complex, with
`0 ≤ k ≤ d + 1`, its mass is the sum of the top-face probabilities over the faces containing
`τ`, divided by `choose (d + 1) k`. The divisor counts the `k`-subsets of each top face. -/
theorem faceLaw_apply (hk : k ≤ d + 1) (τ : facesOfCard K k) :
    X.faceLaw hk τ = (∑ σ : facesOfCard K (d + 1) with τ.val ⊆ σ.val, X.topLaw σ) /
      ((d + 1).choose k : ℝ≥0∞) := by
  classical
  rw [faceLaw, PMF.bind_apply, tsum_fintype, div_eq_mul_inv, Finset.sum_mul, Finset.sum_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hm : τ ∈ subfaces σ k ↔ τ.val ⊆ σ.val := by
    simp only [subfaces, Finset.mem_subtype, Finset.mem_powersetCard,
      (Finset.mem_filter.mp τ.property).2, and_true]
  simp only [subfaceLaw, PMF.uniformFinset_apply, X.card_subfaces, hm, mul_ite, mul_zero]

/-- For a `k`-vertex face `τ` of a pure weighted `d`-dimensional complex, with
`0 ≤ k ≤ d + 1`, its real probability is the sum of the real masses of all top faces
containing `τ`, divided by `choose (d + 1) k`. -/
theorem faceLaw_toReal (hk : k ≤ d + 1) (τ : facesOfCard K k) :
    (X.faceLaw hk τ).toReal =
      (∑ σ : facesOfCard K (d + 1) with τ.val ⊆ σ.val, (X.topLaw σ).toReal) /
        ((d + 1).choose k : ℝ) := by
  rw [X.faceLaw_apply, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_sum fun σ _ => X.topLaw.apply_ne_top σ]

/-- In a pure weighted `d`-dimensional complex, for each cardinality `0 ≤ k ≤ d + 1`,
the real probabilities of the `k`-vertex faces sum to one. -/
theorem sum_faceLaw_toReal (hk : k ≤ d + 1) :
    ∑ τ, (X.faceLaw hk τ).toReal = 1 := by
  have hsum := (X.faceLaw hk).tsum_coe
  rw [tsum_fintype] at hsum
  rw [← ENNReal.toReal_sum (fun τ _ => (X.faceLaw hk).apply_ne_top τ), hsum, ENNReal.toReal_one]

/-- In a pure weighted `d`-dimensional complex, every `k`-vertex face with
`0 ≤ k ≤ d + 1` has positive real probability: purity supplies a containing top face, and
full support gives that face positive mass. -/
theorem faceLaw_toReal_pos (hk : k ≤ d + 1) (τ : facesOfCard K k) :
    0 < (X.faceLaw hk τ).toReal := by
  obtain ⟨σ, hσ⟩ := X.covers τ.val (Finset.mem_filter.mp τ.property).1
  rw [X.faceLaw_toReal]
  apply div_pos _ (by exact_mod_cast Nat.choose_pos hk)
  exact Finset.sum_pos' (fun _ _ => ENNReal.toReal_nonneg)
    ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ⟩,
      ENNReal.toReal_pos (X.top_pos σ).ne' (X.topLaw.apply_ne_top σ)⟩

/-- The empty face, viewed as a member of rank zero. It exists by downward closure
because a probability law on the top faces has nonempty support. -/
def emptyFace : facesOfCard K 0 :=
  ⟨∅, by
    obtain ⟨σ, _⟩ := X.topLaw.support_nonempty
    exact Finset.mem_filter.mpr ⟨X.simplicial _ (Finset.mem_filter.mp σ.property).1 _
      (Finset.empty_subset _), Finset.card_empty⟩⟩

/-- At rank zero the law is the point mass at the empty face. -/
theorem faceLaw_zero : X.faceLaw (Nat.zero_le _) = PMF.pure X.emptyFace := by
  ext τ : 1
  have he : τ.val = ∅ := Finset.card_eq_zero.mp (Finset.mem_filter.mp τ.property).2
  have ht : τ = X.emptyFace := Subtype.ext he
  rw [X.faceLaw_apply, PMF.pure_apply, ite_eq_left ht, he]
  simpa only [Finset.empty_subset, Finset.filter_true, Nat.choose_zero_right,
    Nat.cast_one, div_one] using (tsum_fintype (fun σ => X.topLaw σ)).symm.trans X.topLaw.tsum_coe

/-- At the top rank the sampling construction recovers the original probability mass function. -/
theorem faceLaw_top : X.faceLaw (le_refl (d + 1)) = X.topLaw := by
  classical
  ext τ : 1
  have he (σ : facesOfCard K (d + 1)) : τ.val ⊆ σ.val ↔ σ = τ := by
    refine ⟨fun h => Subtype.ext (Finset.eq_of_subset_of_card_le h ?_).symm, ?_⟩
    · rw [(Finset.mem_filter.mp σ.property).2, (Finset.mem_filter.mp τ.property).2]
    · rintro rfl; exact Finset.Subset.rfl
  rw [X.faceLaw_apply, Finset.sum_filter]
  simp [he]

end PureWeightedComplex

end MathlibExt.Combinatorics
