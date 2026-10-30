/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum

/-!
# Tests for the expected site frequency spectrum

Small random-joining histories, the expected block counts at the boundary levels `k = n` and
`k = 2`, the expected branch lengths `E L_i = 2 / i` for small samples, the spectrum
`E ξ_i = θ / i` for `n = 3`, and a non-vacuity witness: a concrete model (sample size `2`,
product of exponential holding times, the unique topology) satisfying every hypothesis of
`integral_sfs` for every `θ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum

open MathlibExt.Biology.PopulationGenetics.Coalescent
open MathlibExt.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum

/-- The single pair of positions among two blocks. -/
lemma blockPairs_two : blockPairs 2 = {(0, 1)} := by decide

/-- The three pairs of positions among three blocks. -/
lemma blockPairs_three : blockPairs 3 = {(0, 1), (0, 2), (1, 2)} := by decide

/-- Merging two singletons. -/
lemma mergeBlocks_two : mergeBlocks [1, 1] 0 1 = [2] := rfl

/-- Every merge of three singletons gives `[1, 2]`, which then merges to `[3]`. -/
lemma mergeBlocks_three :
    mergeBlocks [1, 1, 1] 0 1 = [1, 2] ∧ mergeBlocks [1, 1, 1] 0 2 = [1, 2] ∧
      mergeBlocks [1, 1, 1] 1 2 = [1, 2] ∧ mergeBlocks [1, 2] 0 1 = [3] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Two singletons always merge into one block of size `2`. -/
example : randomJoining 1 [1, 1] [[1, 1], [2]] = 1 := by
  simp only [randomJoining, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    blockPairs_two, sum_singleton, card_singleton, mergeBlocks_two]
  norm_num

/-- Every pair of three singletons gives the block sizes `[1, 2]`, then `[3]`. -/
example : randomJoining 2 [1, 1, 1] [[1, 1, 1], [1, 2], [3]] = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := mergeBlocks_three
  simp only [randomJoining, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    blockPairs_three]
  rw [sum_insert (by decide), sum_insert (by decide), sum_singleton]
  simp only [h1, h2, h3, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, blockPairs_two,
    sum_singleton, card_singleton, h4]
  norm_num

/-- A history that does not start at the initial blocks has probability `0`. -/
example : randomJoining 1 [1, 1] [[2], [2]] = 0 := by
  simp only [randomJoining, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    blockPairs_two]
  norm_num

/-- One merge of three singletons (`k = 2`): one singleton and one doubleton. -/
example : (joinStep^[1] (fun b => (b.count 1 : ℝ))) (List.replicate 3 1) = 1 ∧
    (joinStep^[1] (fun b => (b.count 2 : ℝ))) (List.replicate 3 1) = 1 := by
  have h1 := joinStep_iterate_count (n := 3) (k := 2) (i := 1) le_rfl (by norm_num) le_rfl
    (by norm_num)
  have h2 := joinStep_iterate_count (n := 3) (k := 2) (i := 2) le_rfl (by norm_num)
    (by norm_num) (by norm_num)
  rw [show 3 - 2 = 1 from rfl] at h1 h2
  rw [h1, h2]
  norm_num [Nat.choose]

/-- Bottom level `k = 2` for `n = 4`: each of the sizes `1, 2, 3` is expected `2/3` times. -/
example (i : ℕ) (hi : 1 ≤ i) (hi4 : i < 4) :
    (joinStep^[2] (fun b => (b.count i : ℝ))) (List.replicate 4 1) = 2 / 3 := by
  have h := joinStep_iterate_count (n := 4) (k := 2) le_rfl (by norm_num) hi hi4
  rw [show 4 - 2 = 2 from rfl] at h
  rw [h]
  interval_cases i <;> norm_num [Nat.choose]

/-- `n = 3`: the expected lengths of singleton and doubleton branches are `2` and `1`. -/
example : ∑ k ∈ (Icc 2 3 : Finset ℕ), (k : ℝ) * ((3 - 1 - 1).choose (k - 2) : ℝ) /
    ((3 - 1).choose (k - 1) : ℝ) * ((k.choose 2 : ℕ) : ℝ)⁻¹ = 2 := by
  rw [sum_blockCount_mul_inv_choose_two le_rfl (by norm_num)]
  norm_num

example : ∑ k ∈ (Icc 2 3 : Finset ℕ), (k : ℝ) * ((3 - 2 - 1).choose (k - 2) : ℝ) /
    ((3 - 1).choose (k - 1) : ℝ) * ((k.choose 2 : ℕ) : ℝ)⁻¹ = 1 := by
  rw [sum_blockCount_mul_inv_choose_two (by norm_num) (by norm_num)]
  norm_num

section Spectrum

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `n = 3`: `E ξ_1 = θ` and `E ξ_2 = θ / 2` (the boundary `i = n - 1`). -/
example (K : KingmanTimes μ 3) (hT : ∀ k, Measurable (K.T k))
    {τ : Ω → List (List ℕ)} (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (3 - 1) (List.replicate 3 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    {θ : ℝ} {ξ : ℕ → Ω → ℝ} (hξ_int : ∀ i, Integrable (ξ i) μ)
    (hξ : ∀ i, μ[ξ i | MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi] =ᵐ[μ]
      fun ω => θ / 2 * sfsLength 3 i (τ ω) (fun k => K.T k ω)) :
    μ[ξ 1] = θ ∧ μ[ξ 2] = θ / 2 := by
  refine ⟨?_, ?_⟩
  · rw [integral_sfs K hT hτ hτ_law h_indep hξ_int hξ le_rfl (by norm_num)]
    norm_num
  · rw [integral_sfs K hT hτ hτ_law h_indep hξ_int hξ (by norm_num) (by norm_num)]
    norm_num

end Spectrum

/-! ### Non-vacuity: a model satisfying every hypothesis -/

section Witness

/-- The product model of the holding times is a probability space. -/
instance : IsProbabilityMeasure (piMeasure 2) := by
  unfold piMeasure; infer_instance

/-- The unique block-size history for a sample of size `2`. -/
def tau2 : (Icc 2 2 → ℝ) → List (List ℕ) := fun _ => [[1, 1], [2]]

/-- The random-joining law for two singletons is the point mass at `[[1, 1], [2]]`. -/
lemma randomJoining_two (ps : List (List ℕ)) :
    randomJoining (2 - 1) (List.replicate 2 1) ps = if ps = [[1, 1], [2]] then 1 else 0 := by
  have hl : (List.replicate 2 1).length = 2 := rfl
  rcases ps with _ | ⟨b, rest⟩
  · simp [randomJoining, blockPairs_two]
  · by_cases hb : b = [1, 1]
    · subst hb
      by_cases hr : rest = [[2]]
      · subst hr
        simp only [randomJoining, hl, blockPairs_two, sum_singleton, card_singleton]
        norm_num [mergeBlocks_two]
      · simp only [randomJoining, hl, blockPairs_two, sum_singleton, card_singleton]
        simp [mergeBlocks_two, hr]
    · simp [randomJoining, blockPairs_two, hb]

/-- The holding times of the product model. -/
noncomputable def K2 : KingmanTimes (piMeasure 2) 2 := KingmanTimes.ofPi 2

/-- The number of sites carried by `i` copies, equal to its conditional mean. -/
noncomputable def xi2 (θ : ℝ) (i : ℕ) (ω : Icc 2 2 → ℝ) : ℝ :=
  θ / 2 * sfsLength 2 i (tau2 ω) (fun k => K2.T k ω)

/-- The holding times of the product model are measurable. -/
lemma measurable_K2 (k : ℕ) : Measurable (K2.T k) := by
  by_cases hk : k ∈ Icc 2 2
  · simp only [K2, KingmanTimes.ofPi, hk, ↓reduceDIte]
    exact measurable_pi_apply _
  · simp only [K2, KingmanTimes.ofPi, hk, ↓reduceDIte]
    exact measurable_const

/-- The constant topology is measurable. -/
lemma comap_tau2_le : MeasurableSpace.comap tau2 ⊤ ≤ MeasurableSpace.pi := by
  have : @Measurable _ _ MeasurableSpace.pi ⊤ tau2 := measurable_const
  exact this.comap_le

/-- The constant topology has the random-joining law. -/
lemma law_tau2 (ps : List (List ℕ)) :
    (piMeasure 2).real (tau2 ⁻¹' {ps}) = randomJoining (2 - 1) (List.replicate 2 1) ps := by
  rw [randomJoining_two]
  by_cases h : ps = [[1, 1], [2]]
  · subst h
    have hu : tau2 ⁻¹' {[[1, 1], [2]]} = Set.univ := by
      ext ω; simp [tau2]
    rw [hu, probReal_univ]
    simp
  · have : tau2 ⁻¹' {ps} = ∅ := by
      ext ω; simp [tau2, Ne.symm h]
    simp [this, h]

/-- A constant topology is independent of the holding times. -/
lemma indep_tau2 : Indep (MeasurableSpace.comap tau2 ⊤)
    (MeasurableSpace.comap (fun ω k => K2.T k ω) MeasurableSpace.pi) (piMeasure 2) := by
  have hbot : MeasurableSpace.comap tau2 ⊤ ≤ ⊥ := by
    rintro s ⟨t, -, rfl⟩
    rw [MeasurableSpace.measurableSet_bot_iff]
    by_cases h : [[1, 1], [2]] ∈ t
    · right; ext ω; simp [tau2, h]
    · left; ext ω; simp [tau2, h]
  exact indep_of_indep_of_le_left (indep_bot_left _) hbot

/-- The witness `ξ i` is integrable. -/
lemma integrable_xi2 (θ : ℝ) (i : ℕ) : Integrable (xi2 θ i) (piMeasure 2) := by
  unfold xi2 sfsLength tau2
  exact (integrable_finsetSum _ fun _ hk => (K2.integrable_T hk).const_mul _).const_mul _

/-- The witness `ξ i` is its own conditional mean given the genealogy. -/
lemma condExp_xi2 (θ : ℝ) (i : ℕ) :
    (piMeasure 2)[xi2 θ i | MeasurableSpace.comap tau2 ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K2.T k ω) MeasurableSpace.pi] =ᵐ[piMeasure 2]
      fun ω => θ / 2 * sfsLength 2 i (tau2 ω) (fun k => K2.T k ω) := by
  have hmT : MeasurableSpace.comap (fun ω k => K2.T k ω) MeasurableSpace.pi ≤
      MeasurableSpace.pi := (measurable_pi_iff.2 measurable_K2).comap_le
  refine (condExp_of_stronglyMeasurable (sup_le comap_tau2_le hmT) ?_
    (integrable_xi2 θ i)).eventuallyEq
  refine Measurable.stronglyMeasurable ?_
  have hF : Measurable fun x : ℕ → ℝ =>
      θ / 2 * ∑ k ∈ Icc 2 2, ((([[1, 1], [2]] : List (List ℕ)).getD (2 - k) []).count i : ℝ) *
        x k := by
    fun_prop
  exact (hF.comp (comap_measurable _)).mono le_sup_right le_rfl

/-- **Non-vacuity**: every hypothesis of `integral_sfs` holds for `n = 2`, the product model of
the holding times, the constant topology, and `ξ i` equal to its conditional mean; the
conclusion is `E ξ_1 = θ`. -/
example (θ : ℝ) : (piMeasure 2)[xi2 θ 1] = θ := by
  rw [integral_sfs K2 measurable_K2 comap_tau2_le law_tau2 indep_tau2 (integrable_xi2 θ)
    (condExp_xi2 θ) le_rfl (by norm_num)]
  norm_num

end Witness

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum
