/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.MutationPairwise

/-!
# Tests for pairwise differences under Poisson mutation marking

A sample of three genes with the history that merges genes `0` and `1` first, evaluated from the
definitions: the separating and shared branches of each pair (the pair `{0, 2}` shares no
branch), the coalescence times, and the path lengths. Then the random-joining probabilities for
`n = 3` by counting histories, the hand computation `E τ = E T₃ + (2/3) E T₂ = 1`, and the
boundary sample of size `2`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.MutationPairwise

open MathlibExt.Biology.PopulationGenetics.Coalescent

/-- The history of three genes that merges lineages `0` and `1` at both steps: first genes `0`
and `1`, then their ancestor with gene `2`. -/
def h01 : RankedHistory 3 := fun i =>
  ⟨{⟨0, by omega⟩, ⟨1, by omega⟩}, Finset.card_pair (by simp [Fin.ext_iff])⟩

/-- Epoch `k` of a three-gene genealogy, as an element of `Icc 2 3`. -/
abbrev e3 (k : ℕ) (hk : k ∈ Icc 2 3 := by decide) : Icc 2 3 := ⟨k, hk⟩

/-- Branch `j` of epoch `k`. -/
abbrev br (k : ℕ) (j : Fin k) (hk : k ∈ Icc 2 3 := by decide) : KingmanBranch 3 :=
  ⟨⟨k, hk⟩, j⟩

/-- The ancestral partitions of `h01`: singletons, then `{0, 1}, {2}`, then one block. -/
example : blocksAfter h01 0 = [{0}, {1}, {2}] ∧ blocksAfter h01 1 = [{0, 1}, {2}] ∧
    blocksAfter h01 2 = [{0, 1, 2}] := by
  decide +kernel

/-- Genes `0` and `1` coalesce at the first event; genes `0` and `2` only at the root. -/
example : PairApart h01 {0, 1} 0 ∧ ¬PairApart h01 {0, 1} 1 ∧ PairApart h01 {0, 2} 0 ∧
    PairApart h01 {0, 2} 1 := by
  decide +kernel

/-- The path between genes `0` and `1` is their two leaf branches; they share the branch above
their MRCA (lineage `0` while there are two lineages). -/
example : pairPath h01 {0, 1} = {br 3 0, br 3 1} ∧ pairShared h01 {0, 1} = {br 2 0} := by
  decide +kernel

/-- **A pair with no shared branches**: genes `0` and `2` coalesce at the root, so every
ancestral branch of either gene separates them (four branches) and none is shared. -/
example : pairPath h01 {0, 2} = {br 3 0, br 3 2, br 2 0, br 2 1} ∧ pairShared h01 {0, 2} = ∅ := by
  decide +kernel

/-- The pair `{1, 2}` is separated by the same branches as `{0, 2}` with leaf `1` for leaf `0`. -/
example : pairPath h01 {1, 2} = {br 3 1, br 3 2, br 2 0, br 2 1} ∧ pairShared h01 {1, 2} = ∅ := by
  decide +kernel

private theorem univ_Icc23 : (univ : Finset (Icc 2 3)) = {e3 2, e3 3} := by decide

/-- Coalescence times of `h01`, from the definition: `τ₀₁ = T₃`, `τ₀₂ = τ₁₂ = T₃ + T₂`. -/
example (t : Icc 2 3 → ℝ) : pairCoalTime h01 {0, 1} t = t (e3 3) ∧
    pairCoalTime h01 {0, 2} t = t (e3 2) + t (e3 3) ∧
    pairCoalTime h01 {1, 2} t = t (e3 2) + t (e3 3) := by
  have h1 : ¬PairApart h01 {0, 1} 1 := by decide +kernel
  have h2 : PairApart h01 {0, 1} 0 := by decide +kernel
  have h3 : PairApart h01 {0, 2} 1 := by decide +kernel
  have h4 : PairApart h01 {0, 2} 0 := by decide +kernel
  have h5 : PairApart h01 {1, 2} 1 := by decide +kernel
  have h6 : PairApart h01 {1, 2} 0 := by decide +kernel
  have hne : e3 2 ≠ e3 3 := by decide
  unfold pairCoalTime
  rw [univ_Icc23, Finset.sum_pair hne, Finset.sum_pair hne, Finset.sum_pair hne]
  simp only [e3, show 3 - 2 = 1 from rfl, show 3 - 3 = 0 from rfl, h1, h2, h3, h4, h5, h6,
    ite_true, ite_false, zero_add, and_self]

/-- Path length of `{0, 1}` in `h01`, from the definitions: the two leaf branches of epoch `3`,
total `2 T₃`. -/
example (t : Icc 2 3 → ℝ) :
    ∑ b ∈ pairPath h01 {0, 1}, kingmanBranchLength 3 t b = 2 * (t (e3 3)).toNNReal := by
  have hp : pairPath h01 {0, 1} = {br 3 0, br 3 1} := by decide +kernel
  rw [hp, Finset.sum_pair (by decide)]
  simp [kingmanBranchLength, two_mul]

/-- Path length of `{0, 2}` in `h01`, from the definitions: `2 (T₃ + T₂)`. -/
example (t : Icc 2 3 → ℝ) :
    ∑ b ∈ pairPath h01 {0, 2}, kingmanBranchLength 3 t b =
      2 * ((t (e3 3)).toNNReal + (t (e3 2)).toNNReal) := by
  have hp : pairPath h01 {0, 2} = {br 3 0, br 3 2, br 2 0, br 2 1} := by decide +kernel
  rw [hp, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_pair (by decide)]
  simp only [kingmanBranchLength]
  ring

/-- Per epoch, the separating branches of `{0, 2}`: two in each epoch (the pair is apart). -/
example : #{j : Fin 3 | (({0, 2} : Finset (Fin 3)) ∩ branchBlock h01 (br 3 j)).card = 1} = 2 ∧
    #{j : Fin 2 | (({0, 2} : Finset (Fin 3)) ∩ branchBlock h01 (br 2 j)).card = 1} = 2 := by
  decide +kernel

/-- Random joining with three genes, by counting histories: of the three histories, two keep
genes `0` and `1` apart after the first event (probability `2/3`). -/
example : #{h : RankedHistory 3 | PairApart h {0, 1} 1} = 2 ∧
    #{h : RankedHistory 3 | PairApart h {0, 1} 0} = 3 ∧ Fintype.card (RankedHistory 3) = 3 := by
  decide +kernel

/-- The closed form `(n - t - 1)(n + 1) / ((n - t + 1)(n - 1))` agrees with the count `2/3` for
`n = 3`, `t = 1`. -/
example : ((3 : ℝ) - (1 : ℕ) - 1) * (3 + 1) / ((3 - (1 : ℕ) + 1) * (3 - 1)) =
    (2 : ℝ) / 3 := by
  norm_num

/-- **Hand computation of `E τ` for three genes**: the pair is apart during epoch `3` surely and
during epoch `2` with probability `2/3`, and `E T₃ = 1/3`, `E T₂ = 1`, so
`E τ = 1/3 + (2/3) · 1 = 1`; the probabilities agree with `integral_pairApart_randomJoining`. -/
example :
    (∫ h, (if PairApart h {0, 1} (3 - 3) then (1 : ℝ) else 0) ∂randomJoining 3) = 1 ∧
    (∫ h, (if PairApart h {0, 1} (3 - 2) then (1 : ℝ) else 0) ∂randomJoining 3) = 2 / 3 ∧
    (((3 : ℕ).choose 2 : ℕ) : ℝ)⁻¹ * 1 + (((2 : ℕ).choose 2 : ℕ) : ℝ)⁻¹ * (2 / 3) = 1 := by
  have hs : ({0, 1} : Finset (Fin 3)) ∈ samplePairs 3 := by decide
  refine ⟨?_, ?_, by norm_num [Nat.choose]⟩
  · rw [integral_pairApart_randomJoining hs (by decide)]
    norm_num [pairSeparateProb]
  · rw [integral_pairApart_randomJoining hs (by decide)]
    norm_num [pairSeparateProb]

/-- The model value `E τ = 1` for three genes. -/
example : ∫ g, pairCoalTime g.2 {0, 1} g.1 ∂kingmanGenealogyMeasure 3 = 1 :=
  integral_pairCoalTime_kingmanGenealogyMeasure (by decide) (by decide)

/-- Three genes: `E[D₀₂] = θ` and `E π = θ` in the marked model. -/
example (θ : ℝ≥0) :
    ∫ p, pairDiff (fun p => p.1.2) Prod.snd {0, 2} p ∂kingmanTreeMutationMeasure 3 θ = θ ∧
      ∫ p, meanPairDiff 3 (pairDiff (fun p => p.1.2) Prod.snd) p
        ∂kingmanTreeMutationMeasure 3 θ = θ :=
  ⟨integral_pairDiff_kingmanTreeMutationMeasure (by decide) (by decide),
    integral_meanPairDiff_kingmanTreeMutationMeasure (by decide)⟩

/-- Boundary sample of size `2`: the only pair is separated by both branches of the single
epoch and shares none, and `E π = θ`. -/
example (h : RankedHistory 2) (θ : ℝ≥0) :
    (pairPath h {0, 1}).card = 2 ∧ pairShared h {0, 1} = ∅ ∧
      ∫ p, meanPairDiff 2 (pairDiff (fun p => p.1.2) Prod.snd) p
        ∂kingmanTreeMutationMeasure 2 θ = θ := by
  refine ⟨?_, ?_, integral_meanPairDiff_kingmanTreeMutationMeasure le_rfl⟩ <;> revert h <;>
    decide +kernel

/-- Zero mutation rate: no pairwise differences on average. -/
example : ∫ p, meanPairDiff 3 (pairDiff (fun p => p.1.2) Prod.snd) p
    ∂kingmanTreeMutationMeasure 3 0 = 0 := by
  simpa using integral_meanPairDiff_kingmanTreeMutationMeasure (n := 3) (θ := 0) (by decide)

/-! ### The law of `τ` and second moments -/

/-- Boundary sample of size `2`, from the definitions: the pair is apart during the only epoch, so
`τ = T₂`, the coordinate of `piMeasure 2` with law `Exp(C(2, 2)) = Exp(1)`. This is the value
`hasLaw_pairCoalTime_kingmanGenealogyMeasure` gives at `n = 2`. -/
example : HasLaw (fun g : (Icc 2 2 → ℝ) × RankedHistory 2 => pairCoalTime g.2 {0, 1} g.1)
    (expMeasure 1) (kingmanGenealogyMeasure 2) := by
  have hA : ∀ h : RankedHistory 2, PairApart h {0, 1} (2 - 2) := by decide +kernel
  have huniv : (univ : Finset (Icc 2 2)) = {⟨2, by decide⟩} := by decide
  have hτ : (fun g : (Icc 2 2 → ℝ) × RankedHistory 2 => pairCoalTime g.2 {0, 1} g.1) =
      (fun t : Icc 2 2 → ℝ => t ⟨2, by decide⟩) ∘ Prod.fst := by
    funext g
    simp only [pairCoalTime, huniv, Finset.sum_singleton, Function.comp_apply]
    rw [ite_eq_left (hA g.2)]
  have h1 : MeasurePreserving (fun t : Icc 2 2 → ℝ => t ⟨2, by decide⟩) (piMeasure 2)
      (expMeasure 1) := by
    have := measurePreserving_eval
      (fun k : Icc 2 2 => expMeasure (((k : ℕ).choose 2 : ℕ) : ℝ)) ⟨2, by decide⟩
    simpa [piMeasure] using this
  rw [hτ, kingmanGenealogyMeasure]
  exact (h1.comp (measurePreserving_fst (μ := piMeasure 2) (ν := randomJoining 2))).hasLaw

/-- `pairRatio m = (m - 1) / (m + 1)` at the first values, from the definition. -/
example : pairRatio 1 = 0 ∧ pairRatio 2 = 1 / 3 ∧ pairRatio 3 = 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [pairRatio]

/-- **The mixture identity for three lineages**, expanded from the definitions: the pair
coalesces in epoch `2` (weight `r₂ - r₁ = 1/3`, both epochs) or epoch `3` (weight
`r₃ - r₂ = 1/6`), and the mixture of the transforms is `r₃ / (1 - z)`. -/
example (z : ℂ) (h1 : z ≠ 1) (h3 : z ≠ 3) :
    ∑ m ∈ Icc 2 3, (pairRatio m - pairRatio (m - 1)) *
        ∏ k ∈ Icc m 3, ((k.choose 2 : ℕ) : ℂ) / (((k.choose 2 : ℕ) : ℂ) - z) =
      pairRatio 3 / (1 - z) := by
  have h1' : (1 : ℂ) - z ≠ 0 := sub_ne_zero.2 h1.symm
  have h3' : (3 : ℂ) - z ≠ 0 := sub_ne_zero.2 h3.symm
  rw [show Icc 2 3 = {2, 3} by decide, Finset.sum_pair (by decide),
    show Icc 3 3 = {3} by decide, show Icc 2 3 = {2, 3} by decide]
  simp only [Finset.prod_pair (show (2 : ℕ) ≠ 3 by decide), Finset.prod_singleton]
  norm_num [pairRatio, Nat.choose]
  field_simp
  ring

/-- The overlap of the paths of `{0, 1}` and `{0, 2}` in `h01`, from the definitions: the leaf
branch of gene `0`, length `T₃`. -/
example (t : Icc 2 3 → ℝ) : pairPathOverlap h01 {0, 1} {0, 2} t = max (t (e3 3)) 0 := by
  have hi : pairPath h01 {0, 1} ∩ pairPath h01 {0, 2} = {br 3 0} := by decide +kernel
  rw [pairPathOverlap, hi, Finset.sum_singleton]
  simp [kingmanBranchLength, Real.coe_toNNReal']

/-- The overlap of the paths of `{0, 2}` and `{1, 2}` in `h01`, from the definitions: the leaf
branch of gene `2` and both branches of epoch `2`, length `T₃ + 2 T₂`. -/
example (t : Icc 2 3 → ℝ) :
    pairPathOverlap h01 {0, 2} {1, 2} t = max (t (e3 3)) 0 + 2 * max (t (e3 2)) 0 := by
  have hi : pairPath h01 {0, 2} ∩ pairPath h01 {1, 2} = {br 3 2, br 2 0, br 2 1} := by
    decide +kernel
  rw [pairPathOverlap, hi, Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
  simp only [kingmanBranchLength, Real.coe_toNNReal']
  ring

/-- A pair overlaps its own path in full: from the definitions, `ℓ(path ∩ path) = 2 T₃` for
`{0, 1}` in `h01`. -/
example (t : Icc 2 3 → ℝ) :
    pairPathOverlap h01 {0, 1} {0, 1} t = 2 * max (t (e3 3)) 0 := by
  have hp : pairPath h01 {0, 1} = {br 3 0, br 3 1} := by decide +kernel
  rw [pairPathOverlap, Finset.inter_self, hp, Finset.sum_pair (by decide)]
  simp only [kingmanBranchLength, Real.coe_toNNReal']
  ring

/-- **Hand computation of `E τ²` for three genes**: `τ₀₁ = T₃ + 1[apart] T₂` with
`P(apart) = 2/3` independent of the epochs, `E T₃² = 2/9`, `E T₃ = 1/3`, `E T₂ = 1`,
`E T₂² = 2`, so `E τ² = 2/9 + 2 (2/3)(1/3) + (2/3) 2 = 2`, the `Exp(1)` second moment; it agrees
with the law `τ ~ Exp(1)` of `hasLaw_pairCoalTime_kingmanGenealogyMeasure`. -/
example : (2 : ℝ) / 3 ^ 2 + 2 * (2 / 3) * (1 / 3) * 1 + 2 / 3 * (2 / 1 ^ 2) = 2 ∧
    ∫ g, pairCoalTime g.2 {0, 1} g.1 ^ 2 ∂kingmanGenealogyMeasure 3 = 2 := by
  refine ⟨by norm_num, ?_⟩
  have h := (hasLaw_pairCoalTime_kingmanGenealogyMeasure (n := 3) (by decide)
    (s := {0, 1}) (by decide)).integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
  rw [integral_sq_expMeasure one_pos] at h
  simpa using h

/-- Three genes: `τ₀₂ ~ Exp(1)` in the marked model, `Var D₀₂ = θ + θ²`, and the covariance of two
pairs sharing gene `0` reduces to the genealogy. -/
example (θ : ℝ≥0) :
    HasLaw (fun p : ((Icc 2 3 → ℝ) × RankedHistory 3) × (KingmanBranch 3 → ℕ) =>
      pairCoalTime p.1.2 {0, 2} p.1.1) (expMeasure 1) (kingmanTreeMutationMeasure 3 θ) ∧
    Var[pairDiff (fun p => p.1.2) Prod.snd {0, 2}; kingmanTreeMutationMeasure 3 θ] =
      θ + θ ^ 2 ∧
    cov[pairDiff (fun p => p.1.2) Prod.snd {0, 1}, pairDiff (fun p => p.1.2) Prod.snd {0, 2};
        kingmanTreeMutationMeasure 3 θ] =
      θ ^ 2 * cov[fun g => pairCoalTime g.2 {0, 1} g.1, fun g => pairCoalTime g.2 {0, 2} g.1;
          kingmanGenealogyMeasure 3] +
        θ / 2 * ∫ g, pairPathOverlap g.2 {0, 1} {0, 2} g.1 ∂kingmanGenealogyMeasure 3 :=
  ⟨hasLaw_pairCoalTime_kingmanTreeMutationMeasure (by decide) (by decide),
    variance_pairDiff_kingmanTreeMutationMeasure (by decide) (by decide),
    covariance_pairDiff_kingmanTreeMutationMeasure (by decide) (by decide) (by decide)⟩

/-- Boundary sample of size `2` with zero mutation rate: `Var D = 0`. -/
example : Var[pairDiff (fun p => p.1.2) Prod.snd {0, 1}; kingmanTreeMutationMeasure 2 0] = 0 := by
  simpa using variance_pairDiff_kingmanTreeMutationMeasure (n := 2) (θ := 0) le_rfl (by decide)

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.MutationPairwise
