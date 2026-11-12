/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.ExactTests.MultinomialTotals
public import Mathlib.Probability.HasLawExists

@[expose] public section

open MeasureTheory ProbabilityTheory Finset MathlibExt.Probability.Statistics.ExactTests

namespace MathlibExtTest.Probability.Statistics.ExactTests.MultinomialTotals

/-! ### Boundary values of the multinomial mass, computed from the definition -/

/-- `n = 0`: the point mass at the zero vector, for every `p`. -/
example (p : Fin 3 → ℝ) : multinomialReal 0 p 0 = 1 := by
  simp [multinomialReal, Nat.multinomial]

/-- Off the simplex the mass is `0`: `(1, 0, 0)` has total `1 ≠ 2`. -/
example (p : Fin 3 → ℝ) : multinomialReal 2 p ![1, 0, 0] = 0 := by
  simp [multinomialReal, Fin.sum_univ_three]

/-- One heterozygote and one `AA` homozygote among two individuals: `2 p₀ p₁`. -/
theorem multinomialReal_two_one_one (p : Fin 3 → ℝ) :
    multinomialReal 2 p ![1, 1, 0] = 2 * p 0 * p 1 := by
  simp [multinomialReal, Fin.sum_univ_three, Fin.prod_univ_three, Nat.multinomial_univ_three]
  ring

/-- A single draw in cell `1`: mass `p₁`. -/
theorem multinomialReal_one_single (p : Fin 3 → ℝ) : multinomialReal 1 p ![0, 1, 0] = p 1 := by
  simp [multinomialReal, Fin.sum_univ_three, Fin.prod_univ_three, Nat.multinomial_univ_three]

theorem multinomialReal_one_single' (p : Fin 3 → ℝ) : multinomialReal 1 p ![1, 0, 0] = p 0 := by
  simp [multinomialReal, Fin.sum_univ_three, Fin.prod_univ_three, Nat.multinomial_univ_three]

/-! ### The recurrence agrees with the definition on a concrete vector -/

/-- `multinomialReal_succ` at `n = 1`, `x = (1, 1, 0)`: the right side, evaluated from the
definition, is `P₁(0,1,0) p₀ + P₁(1,0,0) p₁ = 2 p₀ p₁`, matching the left side. -/
example (p : Fin 3 → ℝ) :
    (∑ i, if (![1, 1, 0] : Fin 3 → ℕ) i = 0 then 0 else
        multinomialReal 1 p (![1, 1, 0] - Pi.single i 1) * p i) = 2 * p 0 * p 1 := by
  have h0 : (![1, 1, 0] - Pi.single 0 1 : Fin 3 → ℕ) = ![0, 1, 0] := by
    funext j; fin_cases j <;> rfl
  have h1 : (![1, 1, 0] - Pi.single 1 1 : Fin 3 → ℕ) = ![1, 0, 0] := by
    funext j; fin_cases j <;> rfl
  simp only [Fin.sum_univ_three, h0, h1]
  simp [multinomialReal_one_single, multinomialReal_one_single']
  ring

example (p : Fin 3 → ℝ) :
    multinomialReal 2 p ![1, 1, 0] = ∑ i, if (![1, 1, 0] : Fin 3 → ℕ) i = 0 then 0 else
        multinomialReal 1 p (![1, 1, 0] - Pi.single i 1) * p i :=
  multinomialReal_succ 1 p _

/-! ### Non-vacuity: i.i.d. draws exist, and the theorems apply to them -/

/-- The uniform law on the three genotypes. -/
noncomputable abbrev unif3 : PMF (Fin 3) :=
  PMF.ofFintype (fun _ => 3⁻¹) (by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))

private lemma unif3_real (j : Fin 3) : unif3.toMeasure.real {j} = 1 / 3 := by
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton j)]
  simp [unif3]

/-- **Witness.** There is a probability space carrying independent genotype draws with uniform
genotype frequencies, i.e. the hypotheses of the sampling theorems are satisfiable. -/
theorem witness : ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ G : ℕ → Ω → Fin 3,
    IsProbabilityMeasure P ∧ (∀ k, Measurable (G k)) ∧ iIndepFun G P ∧
      ∀ k j, P.real {ω | G k ω = j} = 1 / 3 := by
  obtain ⟨Ω, mΩ, P, G, hGm, hG, hind, hP⟩ := exists_iid ℕ unif3.toMeasure
  refine ⟨Ω, mΩ, P, G, hP, hGm, hind, fun k j => ?_⟩
  rw [(hG k).measureReal_eq (p := (· = j)) (measurableSet_singleton j),
    Set.ofPred_eq_eq_singleton, unif3_real]

/-- On the witness, two individuals are one `AA` and one `AB` with probability `2/9`; the
expected value `2 · (1/3) · (1/3)` is computed from the definition of `multinomialReal`. -/
example : ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ G : ℕ → Ω → Fin 3,
    IsProbabilityMeasure P ∧
      P.real {ω | ∀ j, #{k ∈ range 2 | G k ω = j} = (![1, 1, 0] : Fin 3 → ℕ) j} = 2 / 9 := by
  obtain ⟨Ω, mΩ, P, G, hP, hGm, hind, hG⟩ := witness
  refine ⟨Ω, mΩ, P, G, hP, ?_⟩
  rw [measureReal_counts_eq_multinomialReal hGm hind hG, multinomialReal_two_one_one]
  norm_num

/-- On the witness, the genotype-count theorem gives `P(n_AA = 1, n_AB = 0, n_BB = 1) = 2/9`. -/
example : ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ G : ℕ → Ω → Fin 3,
    IsProbabilityMeasure P ∧
      P.real {ω | #{k ∈ range (1 + 0 + 1) | G k ω = 0} = 1 ∧
        #{k ∈ range (1 + 0 + 1) | G k ω = 1} = 0 ∧
        #{k ∈ range (1 + 0 + 1) | G k ω = 2} = 1} = 2 / 9 := by
  obtain ⟨Ω, mΩ, P, G, hP, hGm, hind, hG⟩ := witness
  refine ⟨Ω, mΩ, P, G, hP, ?_⟩
  rw [measureReal_genotypeCounts_eq hGm hind hG]
  norm_num [Nat.factorial]

/-- On the witness, the count vector has the multinomial law of the merged PMF. -/
example : ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ G : ℕ → Ω → Fin 3,
    ∃ (h₀ : ∀ _j : Fin 3, (0 : ℝ) ≤ 1 / 3) (h₁ : ∑ _j : Fin 3, (1 / 3 : ℝ) = 1),
      HasLaw (fun ω j => #{k ∈ range 5 | G k ω = j})
        (multinomial 5 (fun _ => 1 / 3) h₀ h₁).toMeasure P := by
  obtain ⟨Ω, mΩ, P, G, hP, hGm, hind, hG⟩ := witness
  have h₀ : ∀ _j : Fin 3, (0 : ℝ) ≤ 1 / 3 := fun _ => by norm_num
  have h₁ : ∑ _j : Fin 3, (1 / 3 : ℝ) = 1 := by norm_num
  exact ⟨Ω, mΩ, P, G, h₀, h₁, hasLaw_counts_multinomial hGm hind hG h₀ h₁ 5⟩

/-! ### Consistency at `n = 1` with the draw law itself -/

/-- For one draw, the count event `counts = e₁` is the event `X 0 = 1`, computed directly from
the definition of the counts; its probability `p 1` (from the hypothesis on the draw) agrees
with the theorem's `multinomialReal 1 p e₁`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Fin 3} {p : Fin 3 → ℝ} (hXm : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hX : ∀ k i, μ.real {ω | X k ω = i} = p i) :
    μ.real {ω | ∀ i, #{k ∈ range 1 | X k ω = i} = (![0, 1, 0] : Fin 3 → ℕ) i} = p 1 ∧
      μ.real {ω | ∀ i, #{k ∈ range 1 | X k ω = i} = (![0, 1, 0] : Fin 3 → ℕ) i} =
        multinomialReal 1 p ![0, 1, 0] := by
  have hset : {ω | ∀ i, #{k ∈ range 1 | X k ω = i} = (![0, 1, 0] : Fin 3 → ℕ) i} =
      {ω | X 0 ω = 1} := by
    ext ω
    obtain ⟨a, ha⟩ : ∃ a, X 0 ω = a := ⟨_, rfl⟩
    fin_cases a <;> simp [Fin.forall_fin_succ, filter_singleton, ha]
  refine ⟨by rw [hset, hX], measureReal_counts_eq_multinomialReal hXm hind hX 1 _⟩

/-! ### Lumping and the conditional binomial law on the witness -/

/-- Lumping all three genotypes into one cell: three individuals all fall in it with
probability `1`, as computed from the definition of `multinomialReal` with merged mass
`∑ᵢ 1/3 = 1`. -/
example : ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ G : ℕ → Ω → Fin 3,
    IsProbabilityMeasure P ∧
      P.real {ω | ∀ j : Fin 1, #{k ∈ range 3 | (fun _ => (0 : Fin 1)) (G k ω) = j} = 3} = 1 := by
  obtain ⟨Ω, mΩ, P, G, hP, hGm, hind, hG⟩ := witness
  refine ⟨Ω, mΩ, P, G, hP, ?_⟩
  rw [measureReal_lumpedCounts_eq_multinomialReal hGm hind hG (fun _ => (0 : Fin 1)) 3
    (fun _ => 3)]
  simp [multinomialReal, Nat.multinomial]
  norm_num

/-- One draw: the counts of cells `0` and `1` are indicators. -/
private lemma counts_one {Ω : Type*} (G : ℕ → Ω → Fin 3) (ω : Ω) (i : Fin 3) :
    #{k ∈ range 1 | G k ω = i} = if G 0 ω = i then 1 else 0 := by
  by_cases h : G 0 ω = i <;> simp [filter_singleton, h]

/-- **Conditional binomial, computed from definitions.** On the witness with one draw, the
event `C₀ + C₁ = 1` is `{G 0 = 0} ∪ {G 0 = 1}` (probability `2/3`) and `{C₀ = 1}` inside it is
`{G 0 = 0}` (probability `1/3`), so `P(C₀ = 1 | C₀ + C₁ = 1) = 1/2` by the definition of
conditional probability. The theorem's value `C(1,1) (1/2)^1 (1/2)^0` agrees. -/
example : ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ G : ℕ → Ω → Fin 3,
    IsProbabilityMeasure P ∧
      (P[|{ω | #{k ∈ range 1 | G k ω = 0} + #{k ∈ range 1 | G k ω = 1} = 1}]).real
        {ω | #{k ∈ range 1 | G k ω = 0} = 1} = 1 / 2 ∧
      (P[|{ω | #{k ∈ range 1 | G k ω = 0} + #{k ∈ range 1 | G k ω = 1} = 1}]).real
        {ω | #{k ∈ range 1 | G k ω = 0} = 1} =
        ((1 : ℕ).choose 1 : ℝ) * ((1 / 3) / (1 / 3 + 1 / 3)) ^ 1 *
          ((1 / 3) / (1 / 3 + 1 / 3)) ^ (1 - 1) := by
  obtain ⟨Ω, mΩ, P, G, hP, hGm, hind, hG⟩ := witness
  refine ⟨Ω, mΩ, P, G, hP, ?_, ?_⟩
  · have hS : {ω | #{k ∈ range 1 | G k ω = 0} + #{k ∈ range 1 | G k ω = 1} = 1} =
        {ω | G 0 ω = 0} ∪ {ω | G 0 ω = 1} := by
      ext ω
      simp only [counts_one, Set.mem_ofPred_eq, Set.mem_union]
      obtain ⟨a, ha⟩ : ∃ a, G 0 ω = a := ⟨_, rfl⟩
      fin_cases a <;> simp [ha]
    have hm0 : MeasurableSet {ω | G 0 ω = 0} := hGm 0 (measurableSet_singleton 0)
    have hm1 : MeasurableSet {ω | G 0 ω = 1} := hGm 0 (measurableSet_singleton 1)
    have hdisj : Disjoint {ω | G 0 ω = 0} {ω | G 0 ω = 1} :=
      Set.disjoint_left.2 fun ω h0 h1 => by
        simp only [Set.mem_ofPred_eq] at h0 h1
        rw [h0] at h1
        exact absurd h1 (by decide)
    have hinter : ({ω | G 0 ω = 0} ∪ {ω | G 0 ω = 1}) ∩ {ω | G 0 ω = 0} = {ω | G 0 ω = 0} :=
      Set.inter_eq_right.2 Set.subset_union_left
    have hAeq : ({ω | G 0 ω = 0} ∪ {ω | G 0 ω = 1}) ∩ {ω | #{k ∈ range 1 | G k ω = 0} = 1} =
        {ω | G 0 ω = 0} := by
      rw [← hinter]
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq, counts_one]
      by_cases h : G 0 ω = 0 <;> simp [h]
    rw [hS, measureReal_def, cond_apply (hm0.union hm1), hAeq, ENNReal.toReal_mul,
      ENNReal.toReal_inv, ← measureReal_def, ← measureReal_def,
      measureReal_union hdisj hm1, hG 0 0, hG 0 1]
    norm_num
  · rw [cond_measureReal_counts_eq_binomial hGm hind hG (by decide : (0 : Fin 3) ≠ 1)]
    intro h0
    have hsub : {ω | G 0 ω = 0} ⊆
        {ω | #{k ∈ range 1 | G k ω = 0} + #{k ∈ range 1 | G k ω = 1} = 1} := fun ω h => by
      simp only [Set.mem_ofPred_eq] at h ⊢
      rw [counts_one, counts_one, h]
      decide
    have hpos : P {ω | G 0 ω = 0} ≠ 0 := by
      intro hz
      have := hG 0 0
      rw [measureReal_def, hz] at this
      norm_num at this
    exact hpos (measure_mono_null hsub h0)

end MathlibExtTest.Probability.Statistics.ExactTests.MultinomialTotals
