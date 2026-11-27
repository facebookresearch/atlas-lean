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

Index faces by their cardinality. In `PureWeightedComplexOfRank K r`, `K` is a finite family
closed under subsets, every member of `K` lies in an `r`-vertex face, and the top law is an
arbitrary full-support probability distribution on those faces. If the weighting is
unspecified, `PureWeightedComplexOfRank.uniform` gives the uniform top law on a nonempty rank.

Each top face contains `r.choose k` subfaces with `k` vertices for every natural `k`, a count
of zero when `r < k`. For `0 ≤ k ≤ r`, draw one top face, then one of its `k`-vertex subsets
uniformly. A face's mass is the sum of the masses of its containing top faces divided by
`r.choose k`. The masses are positive and sum to one at each such rank; a uniform top law
need not induce a uniform lower law. The law at `k = 0` is the point mass at the empty face;
at `k = r` it is the given top law.

For natural dimension `d`, `PureWeightedComplex K d` means top cardinality `d + 1`.
Dinur and Kaufman, *High dimensional expanders imply agreement expanders*, ECCC TR17-089
(2017), §2.2, p. 15 and §3.1, pp. 16–17 describe the empty face and successive uniform
deletions in this setting. Here each rank law is constructed directly from the top law.
The cardinality formulation also covers the boundary case `r = 0`: the family `{∅}` can
carry a probability law, whereas the void family `∅` has no top face to sample.
-/

@[expose] public section

namespace MathlibExt.Combinatorics

open RationalSimplicialHomologyShared
open scoped ENNReal

/-- A finite family `K` of finite sets of natural-number vertices, closed under subsets, in
which every face lies in a face of size `r`. A weighting is a probability law on those
`r`-vertex faces that gives strictly positive mass to every one of them. The index `r` is a
cardinality and may be zero. -/
structure PureWeightedComplexOfRank (K : Finset (Finset ℕ)) (r : ℕ) where
  /-- The family is closed under taking every subset, including the empty subset. -/
  simplicial : IsSimplicialComplex K
  /-- Every member of `K` is contained in a member with exactly `r` vertices. -/
  covers : ∀ τ ∈ K, ∃ σ : facesOfCard K r, τ ⊆ σ.val
  /-- The probability distribution on the members of `K` with `r` vertices; it need
  not be uniform. -/
  topLaw : PMF (facesOfCard K r)
  /-- Every top face has strictly positive mass. -/
  top_pos : ∀ σ, 0 < topLaw σ

namespace PureWeightedComplexOfRank

variable {K : Finset (Finset ℕ)} {r k : ℕ}

/-- Equip a downward-closed finite family with the uniform top weighting when every face
extends to a face with `r` vertices and that rank is nonempty. This is the weighting
used when none is specified; it does not require the induced lower laws to be uniform. -/
noncomputable def uniform (hK : IsSimplicialComplex K)
    (hc : ∀ τ ∈ K, ∃ σ : facesOfCard K r, τ ⊆ σ.val)
    (hne : (facesOfCard K r).Nonempty) : PureWeightedComplexOfRank K r := by
  letI : Nonempty ↥(facesOfCard K r) := hne.to_subtype
  exact ⟨hK, hc, PMF.uniformFintype _, fun σ => by simp⟩

variable (X : PureWeightedComplexOfRank K r)

include X in
/-- In a pure weighted complex the facets are exactly the faces of cardinality `r`. -/
theorem isFacet_iff {τ : Finset ℕ} : IsFacet K τ ↔ τ ∈ facesOfCard K r := by
  constructor
  · intro ⟨hτ, hmax⟩
    obtain ⟨σ, hσ⟩ := X.covers τ hτ
    exact hmax σ.val (Finset.mem_filter.mp σ.property).1 hσ ▸ σ.property
  · intro hτ
    refine ⟨(Finset.mem_filter.mp hτ).1, fun γ hγ hsub => ?_⟩
    obtain ⟨σ, hσ⟩ := X.covers γ hγ
    apply Eq.symm <| Finset.eq_of_subset_of_card_le hsub ?_
    calc γ.card ≤ σ.val.card := Finset.card_le_card hσ
      _ = r := (Finset.mem_filter.mp σ.property).2
      _ = τ.card := (Finset.mem_filter.mp hτ).2.symm

/-- For a member `σ` of `K` with `r` vertices, the members of `K` of size `k`
contained in `σ`, returned as elements of `facesOfCard K k`. If `K` is downward closed,
these are all the `k`-element subsets of `σ`. -/
def subfaces (σ : facesOfCard K r) (k : ℕ) : Finset (facesOfCard K k) :=
  (σ.val.powersetCard k).subtype (· ∈ facesOfCard K k)

include X in
/-- For a top face of a pure weighted complex of top cardinality `r` and any natural `k`, the
number of its `k`-vertex subfaces is `r.choose k`: downward closure retains every
`k`-element subset. The count is zero when `r < k`. -/
theorem card_subfaces (σ : facesOfCard K r) :
    (subfaces σ k).card = r.choose k := by
  have hm := Finset.subtype_map_of_mem (p := fun τ => τ ∈ facesOfCard K k)
    (s := σ.val.powersetCard k) fun τ hτ => Finset.mem_filter.mpr
      ⟨X.simplicial _ (Finset.mem_filter.mp σ.property).1 τ (Finset.mem_powersetCard.mp hτ).1,
        (Finset.mem_powersetCard.mp hτ).2⟩
  simpa only [subfaces, Finset.card_map, Finset.card_powersetCard,
    (Finset.mem_filter.mp σ.property).2] using congrArg Finset.card hm

/-- Given a top face `σ` of a pure weighted complex of top cardinality `r` and `0 ≤ k ≤ r`,
the uniform law on the `r.choose k` subsets of `σ` with `k` vertices, viewed as a
probability law on the `k`-vertex faces of the complex. -/
noncomputable def subfaceLaw (hk : k ≤ r) (σ : facesOfCard K r) :
    PMF (facesOfCard K k) :=
  PMF.uniformFinset (subfaces σ k) (Finset.card_pos.mp ((X.card_subfaces σ).symm ▸
    Nat.choose_pos hk))

/-- For a pure weighted complex of top cardinality `r` and `0 ≤ k ≤ r`, the law on its
`k`-vertex faces obtained by drawing one top face from its given full-support law and then
choosing a uniform `k`-vertex subset of that face. -/
noncomputable def faceLaw (hk : k ≤ r) : PMF (facesOfCard K k) :=
  X.topLaw.bind (X.subfaceLaw hk)

/-- For a `k`-vertex face `τ` of a pure weighted complex of top cardinality `r`, with
`0 ≤ k ≤ r`, its mass is the sum of the top-face probabilities over the faces containing
`τ`, divided by `r.choose k`. The divisor counts the `k`-subsets of each top face. -/
theorem faceLaw_apply (hk : k ≤ r) (τ : facesOfCard K k) :
    X.faceLaw hk τ = (∑ σ : facesOfCard K r with τ.val ⊆ σ.val, X.topLaw σ) /
      (r.choose k : ℝ≥0∞) := by
  classical
  rw [faceLaw, PMF.bind_apply, tsum_fintype, div_eq_mul_inv, Finset.sum_mul, Finset.sum_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hm : τ ∈ subfaces σ k ↔ τ.val ⊆ σ.val := by
    simp only [subfaces, Finset.mem_subtype, Finset.mem_powersetCard,
      (Finset.mem_filter.mp τ.property).2, and_true]
  simp only [subfaceLaw, PMF.uniformFinset_apply, X.card_subfaces, hm, mul_ite, mul_zero]

/-- For a `k`-vertex face `τ` of a pure weighted complex of top cardinality `r`, with
`0 ≤ k ≤ r`, its real probability is the sum of the real masses of all top faces
containing `τ`, divided by `r.choose k`. -/
theorem faceLaw_toReal (hk : k ≤ r) (τ : facesOfCard K k) :
    (X.faceLaw hk τ).toReal =
      (∑ σ : facesOfCard K r with τ.val ⊆ σ.val, (X.topLaw σ).toReal) /
        (r.choose k : ℝ) := by
  rw [X.faceLaw_apply, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_sum fun σ _ => X.topLaw.apply_ne_top σ]

/-- In a pure weighted complex of top cardinality `r`, for each cardinality `0 ≤ k ≤ r`,
the real probabilities of the `k`-vertex faces sum to one. -/
theorem sum_faceLaw_toReal (hk : k ≤ r) :
    ∑ τ, (X.faceLaw hk τ).toReal = 1 := by
  have hsum := (X.faceLaw hk).tsum_coe
  rw [tsum_fintype] at hsum
  rw [← ENNReal.toReal_sum (fun τ _ => (X.faceLaw hk).apply_ne_top τ), hsum, ENNReal.toReal_one]

/-- In a pure weighted complex of top cardinality `r`, every `k`-vertex face with
`0 ≤ k ≤ r` has positive real probability: purity supplies a containing top face, and
full support gives that face positive mass. -/
theorem faceLaw_toReal_pos (hk : k ≤ r) (τ : facesOfCard K k) :
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

/-- For any top cardinality `r`, including zero, sampling a face of cardinality zero gives
the point mass at the empty face. -/
theorem faceLaw_zero : X.faceLaw (Nat.zero_le _) = PMF.pure X.emptyFace := by
  ext τ : 1
  have he : τ.val = ∅ := Finset.card_eq_zero.mp (Finset.mem_filter.mp τ.property).2
  have ht : τ = X.emptyFace := Subtype.ext he
  rw [X.faceLaw_apply, PMF.pure_apply, ite_eq_left ht, he]
  simpa only [Finset.empty_subset, Finset.filter_true, Nat.choose_zero_right,
    Nat.cast_one, div_one] using (tsum_fintype (fun σ => X.topLaw σ)).symm.trans X.topLaw.tsum_coe

/-- For any top cardinality `r`, including zero, sampling an `r`-vertex face recovers the
original probability mass function. -/
theorem faceLaw_top : X.faceLaw (le_refl r) = X.topLaw := by
  classical
  ext τ : 1
  have he (σ : facesOfCard K r) : τ.val ⊆ σ.val ↔ σ = τ := by
    refine ⟨fun h => Subtype.ext (Finset.eq_of_subset_of_card_le h ?_).symm, ?_⟩
    · rw [(Finset.mem_filter.mp σ.property).2, (Finset.mem_filter.mp τ.property).2]
    · rintro rfl; exact Finset.Subset.rfl
  rw [X.faceLaw_apply, Finset.sum_filter]
  simp [he]

/-- If the top cardinality is zero, the family consists of the empty face alone. Coverage
forces every face to be empty, and the top law ensures that the family has a face. -/
theorem family_eq_singleton_empty (Y : PureWeightedComplexOfRank K 0) : K = {∅} := by
  ext τ
  constructor
  · intro hτ
    obtain ⟨σ, h⟩ := Y.covers τ hτ
    have hσ : σ.val = ∅ := Finset.card_eq_zero.mp (Finset.mem_filter.mp σ.property).2
    exact Finset.mem_singleton.mpr (Finset.subset_empty.mp (hσ ▸ h))
  · intro hτ
    rw [Finset.mem_singleton.mp hτ]
    exact (Finset.mem_filter.mp Y.emptyFace.property).1

end PureWeightedComplexOfRank

/-- A pure weighted complex of natural dimension `d`, equivalently a pure weighted complex
of top cardinality `d + 1`. In particular, dimension zero means one-vertex top faces. -/
abbrev PureWeightedComplex (K : Finset (Finset ℕ)) (d : ℕ) :=
  PureWeightedComplexOfRank K (d + 1)

namespace PureWeightedComplex

/-- The uniform weighting for natural dimension `d`. Every face must extend to a face of
size `d + 1`, and that rank must be nonempty. -/
noncomputable abbrev uniform {K : Finset (Finset ℕ)} {d : ℕ} (hK : IsSimplicialComplex K)
    (hc : ∀ τ ∈ K, ∃ σ : facesOfCard K (d + 1), τ ⊆ σ.val)
    (hne : (facesOfCard K (d + 1)).Nonempty) : PureWeightedComplex K d :=
  PureWeightedComplexOfRank.uniform hK hc hne

end PureWeightedComplex

end MathlibExt.Combinatorics
