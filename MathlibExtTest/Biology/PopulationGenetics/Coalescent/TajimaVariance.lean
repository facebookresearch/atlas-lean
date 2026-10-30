/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.TajimaVariance

/-!
# Tests for Tajima's variance identities

Concrete values: `Var π` for samples of two, three and four, `Var(π - S/a₁) = 0` for a sample of
two (where `π = S` and `c₁ = c₂ = 0`), the pair counts for `n = 4`, the probabilities that a
pair is still separate (`1` at the top level, the junk value `0` at `n = 1` where the formula
divides by zero), the two telescoping sums at `n = 3`, and a witness that the hypotheses of
`variance_tajimaNumerator` are jointly satisfiable (a sample of two with `θ = 0`, on the
product model `KingmanTimes.ofPi 2`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.TajimaVariance

open MathlibExt.Biology.PopulationGenetics.Coalescent

/-- `n = 3`: `b₁ = 2/3`, `b₂ = 5/9`. -/
example : tajimaB1 3 = 2 / 3 ∧ tajimaB2 3 = 5 / 9 := by
  norm_num [tajimaB1, tajimaB2]

/-- `n = 4`: `b₁ = 5/9`, `b₂ = 23/54`. -/
example : tajimaB1 4 = 5 / 9 ∧ tajimaB2 4 = 23 / 54 := by
  norm_num [tajimaB1, tajimaB2]

/-- For a pair of a sample of four, one pair equals it, four share one gene, one is disjoint. -/
example (f : ℕ → ℝ) :
    ∑ t ∈ samplePairs 4, f #({0, 1} ∩ t) = f 2 + 4 * f 1 + f 0 := by
  rw [sum_samplePairs_card_inter (by decide)]
  norm_num

/-- At the top level (`k = n` lineages) every pair is separate. -/
example {n : ℕ} (hn : 2 ≤ n) : pairSeparateProb n n = 1 := by
  have h : (1 : ℝ) < n := by exact_mod_cast hn
  unfold pairSeparateProb
  rw [div_eq_one_iff_eq (by nlinarith)]

/-- With two lineages left, a pair of a sample of three is separate with probability `2/3`. -/
example : pairSeparateProb 3 2 = 2 / 3 := by
  norm_num [pairSeparateProb]

/-- Outside the domain `n ≥ 2`: at `n = 1` the formula divides by zero and returns Lean's junk
value `0`. -/
example (k : ℕ) : pairSeparateProb 1 k = 0 := by
  simp [pairSeparateProb]

/-- `n = 3`: `p₂ / C(2,2) + p₃ / C(3,2) = 2/3 + 1/3 = 1`. -/
example : ∑ k ∈ Icc 2 3, pairSeparateProb 3 k * ((k.choose 2 : ℕ) : ℝ)⁻¹ = 1 :=
  sum_pairSeparateProb_div_choose (by norm_num)

/-- `n = 3`, term by term: `2 · (2/3) · 1 + 3 · 1 · (1/3)² = 5/3 = (n + 2) / n`. -/
example : ∑ k ∈ Icc 2 3, ((k : ℕ) : ℝ) * pairSeparateProb 3 k * (((k.choose 2 : ℕ) : ℝ)⁻¹) ^ 2 =
    5 / 3 := by
  rw [sum_Icc_succ_top (by norm_num), Icc_self, sum_singleton]
  norm_num [pairSeparateProb, Nat.choose]

/-- `n = 4`, term by term: `∑ k p_k / C(k, 2)² = 3/2 = (n + 2) / n`. -/
example : ∑ k ∈ Icc 2 4, ((k : ℕ) : ℝ) * pairSeparateProb 4 k * (((k.choose 2 : ℕ) : ℝ)⁻¹) ^ 2 =
    3 / 2 := by
  rw [sum_Icc_succ_top (by norm_num), sum_Icc_succ_top (by norm_num), Icc_self, sum_singleton]
  norm_num [pairSeparateProb, Nat.choose]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- A sample of three: `Var π = (2/3) θ + (5/9) θ²` under the hypotheses of
`variance_meanPairDiff`. -/
example [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {D τ : Finset (Fin 3) → Ω → ℝ} {ℓ : Finset (Fin 3) → Finset (Fin 3) → Ω → ℝ} {θ : ℝ}
    (hτ : ∀ s ∈ samplePairs 3, HasLaw (τ s) (expMeasure 1) μ)
    (hτ₁ : ∀ s ∈ samplePairs 3, ∀ t ∈ samplePairs 3, #(s ∩ t) = 1 →
      μ[fun ω => τ s ω * τ t ω] = 4 / 3)
    (hτ₀ : ∀ s ∈ samplePairs 3, ∀ t ∈ samplePairs 3, Disjoint s t →
      μ[fun ω => τ s ω * τ t ω] = 11 / 9)
    (hℓ₂ : ∀ s ∈ samplePairs 3, ℓ s s =ᵐ[μ] fun ω => 2 * τ s ω)
    (hℓ₁ : ∀ s ∈ samplePairs 3, ∀ t ∈ samplePairs 3, #(s ∩ t) = 1 →
      ℓ s t =ᵐ[μ] fun ω => τ s ω + τ t ω - τ (symmDiff s t) ω)
    (hℓ₀ : ∀ s ∈ samplePairs 3, ∀ t ∈ samplePairs 3, Disjoint s t → μ[ℓ s t] = 2 / 3)
    (hD2 : ∀ s ∈ samplePairs 3, MemLp (D s) 2 μ)
    (hD : ∀ s ∈ samplePairs 3, μ[D s | m] =ᵐ[μ] fun ω => θ * τ s ω)
    (hDD : ∀ s ∈ samplePairs 3, ∀ t ∈ samplePairs 3,
      μ[fun ω => D s ω * D t ω | m] =ᵐ[μ]
        fun ω => θ ^ 2 * (τ s ω * τ t ω) + θ / 2 * ℓ s t ω) :
    Var[meanPairDiff 3 D; μ] = 2 / 3 * θ + 5 / 9 * θ ^ 2 := by
  rw [variance_meanPairDiff hm (by norm_num) hτ hτ₁ hτ₀ hℓ₂ hℓ₁ hℓ₀ hD2 hD hDD]
  norm_num [tajimaB1, tajimaB2]

/-- A sample of two: `π = D` and `c₁ = c₂ = 0`, so `Var(π - S/a₁) = 0`. -/
example [IsProbabilityMeasure μ] (K : KingmanTimes μ 2) {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {S : Ω → ℝ} {D τ : Finset (Fin 2) → Ω → ℝ}
    {ℓ : Finset (Fin 2) → Finset (Fin 2) → Ω → ℝ} {θ : ℝ}
    (hS2 : MemLp S 2 μ) (hS : μ[S | m] =ᵐ[μ] fun ω => θ / 2 * K.totalLength ω)
    (hSvar : Var[S; μ | m] =ᵐ[μ] fun ω => θ / 2 * K.totalLength ω)
    (hτ : ∀ s ∈ samplePairs 2, HasLaw (τ s) (expMeasure 1) μ)
    (hτ₁ : ∀ s ∈ samplePairs 2, ∀ t ∈ samplePairs 2, #(s ∩ t) = 1 →
      μ[fun ω => τ s ω * τ t ω] = 4 / 3)
    (hτ₀ : ∀ s ∈ samplePairs 2, ∀ t ∈ samplePairs 2, Disjoint s t →
      μ[fun ω => τ s ω * τ t ω] = 11 / 9)
    (hτL : ∀ s ∈ samplePairs 2,
      μ[fun ω => τ s ω * K.totalLength ω] = 2 * tajimaA1 2 + ((2 : ℕ) + 2 : ℝ) / (2 : ℕ))
    (hℓ₂ : ∀ s ∈ samplePairs 2, ℓ s s =ᵐ[μ] fun ω => 2 * τ s ω)
    (hℓ₁ : ∀ s ∈ samplePairs 2, ∀ t ∈ samplePairs 2, #(s ∩ t) = 1 →
      ℓ s t =ᵐ[μ] fun ω => τ s ω + τ t ω - τ (symmDiff s t) ω)
    (hℓ₀ : ∀ s ∈ samplePairs 2, ∀ t ∈ samplePairs 2, Disjoint s t → μ[ℓ s t] = 2 / 3)
    (hD2 : ∀ s ∈ samplePairs 2, MemLp (D s) 2 μ)
    (hD : ∀ s ∈ samplePairs 2, μ[D s | m] =ᵐ[μ] fun ω => θ * τ s ω)
    (hDD : ∀ s ∈ samplePairs 2, ∀ t ∈ samplePairs 2,
      μ[fun ω => D s ω * D t ω | m] =ᵐ[μ]
        fun ω => θ ^ 2 * (τ s ω * τ t ω) + θ / 2 * ℓ s t ω)
    (hDS : ∀ s ∈ samplePairs 2, μ[fun ω => D s ω * S ω | m] =ᵐ[μ]
      fun ω => θ ^ 2 / 2 * (τ s ω * K.totalLength ω) + θ * τ s ω) :
    Var[fun ω => meanPairDiff 2 D ω - S ω / tajimaA1 2; μ] = 0 := by
  rw [K.variance_tajimaNumerator hm le_rfl hS2 hS hSvar hτ hτ₁ hτ₀ hτL hℓ₂ hℓ₁ hℓ₀ hD2 hD
    hDD hDS]
  norm_num [tajimaC1, tajimaC2, tajimaA1, tajimaA2, tajimaB1, tajimaB2]

/-- The only pair of a sample of two is the whole sample. -/
lemma eq_univ_of_mem_samplePairs_two {s : Finset (Fin 2)} (hs : s ∈ samplePairs 2) :
    s = univ :=
  eq_univ_of_card s (by simpa using (mem_powersetCard.1 hs).2)

/-- Non-vacuity witness: the hypotheses of `variance_tajimaNumerator` hold jointly for a
sample of two with `θ = 0` on the product model `KingmanTimes.ofPi 2`, with `τ = T 2`, no
mutations (`D = S = 0`), shared length `ℓ = 2 τ` and the full σ-algebra as genealogy. (For
`n = 2` the hypotheses about two distinct pairs are vacuous.) -/
example : Var[fun ω => meanPairDiff 2 (fun _ _ => (0 : ℝ)) ω - (0 : ℝ) / tajimaA1 2;
    piMeasure 2] = tajimaC1 2 * 0 + tajimaC2 2 * 0 ^ 2 := by
  have : IsProbabilityMeasure (piMeasure 2) := by
    unfold piMeasure
    infer_instance
  set K := KingmanTimes.ofPi 2
  have hlaw : HasLaw (K.T 2) (expMeasure 1) (piMeasure 2) := by
    simpa using K.hasLaw 2 (by simp)
  have hm2 : MemLp (K.T 2) 2 (piMeasure 2) := hlaw.memLp_comp (f := id)
    ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
      (by simpa using integrable_pow_expMeasure one_pos 2))
  have hsq : (piMeasure 2)[K.T 2 ^ 2] = 2 := by
    have hv := variance_eq_sub hm2
    rw [hlaw.variance_eq_of_expMeasure one_pos, hlaw.integral_eq_inv_of_expMeasure one_pos] at hv
    linarith
  have hL : K.totalLength = fun ω => 2 * K.T 2 ω := by
    funext ω
    simp [KingmanTimes.totalLength]
  have hpair : ∀ s ∈ samplePairs 2, ∀ t ∈ samplePairs 2, #(s ∩ t) = 2 := by
    intro s hs t ht
    rw [eq_univ_of_mem_samplePairs_two hs, eq_univ_of_mem_samplePairs_two ht]
    simp
  refine K.variance_tajimaNumerator (m := MeasurableSpace.pi) (τ := fun _ => K.T 2)
    (ℓ := fun _ _ ω => 2 * K.T 2 ω) le_rfl le_rfl (MemLp.zero) ?_ ?_ (fun _ _ => hlaw)
    ?_ ?_ ?_ (fun _ _ => ae_of_all _ fun _ => rfl) ?_ ?_ (fun _ _ => MemLp.zero) ?_ ?_ ?_
  · simp
  · simp [condVar]
    rfl
  · intro s hs t ht h
    simp [hpair s hs t ht] at h
  · intro s hs t ht h
    have := hpair s hs t ht
    rw [disjoint_iff_inter_eq_empty.1 h] at this
    simp at this
  · intro s _
    rw [hL]
    simp only [tajimaA1]
    norm_num
    have : (fun ω => K.T 2 ω * (2 * K.T 2 ω)) = fun ω => 2 * (K.T 2 ^ 2) ω := by
      funext ω
      simp [sq]
      ring
    rw [this, integral_const_mul, hsq]
    norm_num
  · intro s hs t ht h
    simp [hpair s hs t ht] at h
  · intro s hs t ht h
    have := hpair s hs t ht
    rw [disjoint_iff_inter_eq_empty.1 h] at this
    simp at this
  · intro s _
    simp
  · intro s _ t _
    simp
  · intro s _
    simp

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.TajimaVariance
