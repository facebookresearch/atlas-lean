/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.Multinomial

/-!
# Fixed-total multinomial law of cell counts under i.i.d. sampling

Draw `n` observations `X 0, …, X (n - 1)` independently from a finite set of cells `ι`, each
landing in cell `i` with probability `p i`. The vector of cell counts
`i ↦ #{k < n | X k = i}` has total `n` and the multinomial law

`P(counts = x) = n! / ∏ᵢ xᵢ! · ∏ᵢ pᵢ ^ xᵢ` for `∑ᵢ xᵢ = n` (and `0` otherwise).

For genotype data (`ι = Fin 3`, the cells `AA`, `AB`, `BB`) this is the law of the genotype
count vector `(n_AA, n_AB, n_BB)` of a sample of `n` individuals drawn i.i.d. from a population
with genotype frequencies `p`; the conditional-binomial exact tests (McNemar, TDT) and the
Hardy–Weinberg exact test take this fixed-total sampling model as their starting point.

## Main results

* `multinomialReal_succ`: the one-step recurrence
  `P_{n+1}(x) = ∑_{i, xᵢ ≠ 0} P_n(x - eᵢ) pᵢ` of the multinomial mass function.
* `measureReal_counts_eq_multinomialReal`: **the cell counts of `n` i.i.d. draws are
  multinomial**, `P(counts = x) = multinomialReal n p x`, for every count vector `x`.
* `hasLaw_counts_multinomial`: the same statement as a `HasLaw` for the multinomial PMF of the
  merged `MathlibExt.Probability.Distributions.Multinomial`.
* `measureReal_genotypeCounts_eq`: the genotype case `ι = Fin 3`,
  `P(n_AA = a, n_AB = b, n_BB = c) = (a + b + c)! / (a! b! c!) · p₀^a p₁^b p₂^c`.
* `measureReal_lumpedCounts_eq_multinomialReal`: merging cells along `f : ι → κ` gives the
  multinomial law with the merged probabilities `q j = ∑_{f i = j} pᵢ`.
* `cond_measureReal_counts_eq_binomial`, `hasLaw_cond_counts_binomial`: for distinct cells
  `a ≠ b`, given `Cₐ + C_b = d`, the count `Cₐ` is `Bin(d, pₐ / (pₐ + p_b))`. This is the
  conditional law that the McNemar / TDT p-value theorems of `ConditionalBinomial` (#1564)
  take as the hypothesis `hcond` in the model with a fixed number of pairs. Discharging `hcond`
  still needs a small bridge: for `pₐ = p_b > 0` rewrite the success probability to `1/2`; for
  `pₐ = p_b = 0` the conditioning forces `d = 0`, where the law is `Bin(0, 0) = Bin(0, 1/2)`
  as a measure.

The cell counts are written inline as `#{k ∈ range n | X k ω = i}` (the `ℕ`-valued form of
`ProbabilityTheory.cellCount` from `GoodnessOfFit.Pearson`, which is real-valued and is not
imported here to keep the import narrow).

## Source

* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. I, 3rd ed.,
  Wiley (1968), §VI.9, "The multinomial distribution": the counts of `n` independent trials
  with `r` possible outcomes of probabilities `p₁, …, p_r` have the law
  `n! / (k₁! ⋯ k_r!) · p₁^{k₁} ⋯ p_r^{k_r}`.
* N. L. Johnson, S. Kotz and N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley
  (1997), ch. 35, §1 (genesis of the multinomial distribution from independent trials).
* B. S. Weir, *Genetic Data Analysis II*, Sinauer (1996), ch. 2 (multinomial sampling of
  genotype counts).
* A. Agresti, *Categorical Data Analysis*, 3rd ed., Wiley (2013), §11.1.1 (McNemar's test:
  conditional on the number of discordant pairs, a discordant count is binomial).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace MathlibExt.Probability.Statistics.ExactTests

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Recurrence

omit [Fintype ι] in
private lemma sub_single_apply_self (x : ι → ℕ) (i : ι) :
    (x - Pi.single i 1 : ι → ℕ) i = x i - 1 := by
  simp

omit [Fintype ι] in
private lemma sub_single_apply_of_ne (x : ι → ℕ) {i j : ι} (h : j ≠ i) :
    (x - Pi.single i 1 : ι → ℕ) j = x j := by
  simp [h]

private lemma sum_sub_single_add_one {x : ι → ℕ} {i : ι} (hx : x i ≠ 0) :
    ∑ j, (x - Pi.single i 1 : ι → ℕ) j + 1 = ∑ j, x j := by
  rw [Fintype.sum_eq_add_sum_compl i, Fintype.sum_eq_add_sum_compl i (f := x),
    sub_single_apply_self, sum_congr rfl fun j hj =>
      sub_single_apply_of_ne x (by simpa using hj)]
  omega

private lemma prod_factorial_sub_single {x : ι → ℕ} {i : ι} (hx : x i ≠ 0) :
    (∏ j, (((x - Pi.single i 1 : ι → ℕ) j).factorial : ℝ)) * x i = ∏ j, ((x j).factorial : ℝ) := by
  rw [Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i (f := fun j =>
      ((x j).factorial : ℝ)), sub_single_apply_self, prod_congr rfl fun j hj => by
      rw [sub_single_apply_of_ne x (by simpa using hj)]]
  have h := Nat.mul_factorial_pred hx
  have h' : (x i : ℝ) * ((x i - 1).factorial : ℝ) = (x i).factorial := by exact_mod_cast h
  rw [← h']
  ring

private lemma prod_pow_sub_single (p : ι → ℝ) {x : ι → ℕ} {i : ι} (hx : x i ≠ 0) :
    (∏ j, p j ^ (x - Pi.single i 1 : ι → ℕ) j) * p i = ∏ j, p j ^ x j := by
  rw [Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i (f := fun j =>
      p j ^ x j), sub_single_apply_self, prod_congr rfl fun j hj => by
      rw [sub_single_apply_of_ne x (by simpa using hj)]]
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hx
  rw [hm, Nat.succ_sub_one, pow_succ]
  ring

/-- **One-step recurrence of the multinomial mass.** Removing the last of `n + 1` throws:
`P_{n+1}(x) = ∑ᵢ [xᵢ ≠ 0] P_n(x - eᵢ) pᵢ` for every real vector `p` and every count vector `x`
(both sides vanish off the simplex `∑ᵢ xᵢ = n + 1`). -/
theorem multinomialReal_succ (n : ℕ) (p : ι → ℝ) (x : ι → ℕ) :
    multinomialReal (n + 1) p x =
      ∑ i, if x i = 0 then 0 else multinomialReal n p (x - Pi.single i 1) * p i := by
  by_cases hx : ∑ i, x i = n + 1
  · set K : ℝ := (n.factorial : ℝ) / (∏ j, ((x j).factorial : ℝ)) * ∏ j, p j ^ x j with hK
    have hterm : ∀ i, (if x i = 0 then 0 else multinomialReal n p (x - Pi.single i 1) * p i) =
        (x i : ℝ) * K := by
      intro i
      by_cases hi : x i = 0
      · simp [hi]
      · simp only [hi, ↓reduceIte]
        have hs : ∑ j, (x - Pi.single i 1 : ι → ℕ) j = n := by
          have := sum_sub_single_add_one hi
          omega
        rw [multinomialReal_eq_factorial_div hs, hK, ← prod_factorial_sub_single hi,
          ← prod_pow_sub_single p hi]
        have hxi : (x i : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hi
        have hP : (∏ j, (((x - Pi.single i 1 : ι → ℕ) j).factorial : ℝ)) ≠ 0 :=
          prod_ne_zero_iff.2 fun j _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
        field_simp
    rw [sum_congr rfl fun i _ => hterm i, ← sum_mul, multinomialReal_eq_factorial_div hx, hK]
    have hx' : (∑ i, (x i : ℝ)) = n + 1 := by exact_mod_cast hx
    rw [hx', Nat.factorial_succ]
    push_cast
    ring
  · rw [multinomialReal_of_sum_ne hx]
    symm
    refine sum_eq_zero fun i _ => ?_
    split_ifs with hi
    · rfl
    · rw [multinomialReal_of_sum_ne, zero_mul]
      have := sum_sub_single_add_one hi
      omega

end Recurrence

section Sampling

variable [MeasurableSpace ι] [MeasurableSingletonClass ι] {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω}

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Ω] in
/-- Adding the `(n + 1)`-st draw to the cell counts. -/
private lemma counts_succ (X : ℕ → Ω → ι) (n : ℕ) (ω : Ω) :
    (fun i => #{k ∈ range (n + 1) | X k ω = i}) =
      (fun i => #{k ∈ range n | X k ω = i}) + Pi.single (X n ω) 1 := by
  funext i
  rw [range_add_one, filter_insert]
  by_cases h : X n ω = i
  · subst h
    simp only [↓reduceIte]
    rw [card_insert_of_notMem (by simp)]
    simp
  · simp only [h, ↓reduceIte]
    simp [Ne.symm h]

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Ω] in
/-- The cell counts of the first `n` draws, as a function of the tuple of those draws. -/
private lemma counts_eq_comp (X : ℕ → Ω → ι) (n : ℕ) :
    (fun ω i => #{k ∈ range n | X k ω = i}) =
      (fun s : range n → ι => fun i => ∑ k : range n, if s k = i then 1 else 0) ∘
        (fun ω (k : range n) => X k ω) := by
  funext ω i
  simp only [Function.comp_apply, card_filter]
  exact (sum_coe_sort (range n) (fun k => if X k ω = i then 1 else 0)).symm

omit [Fintype ι] in
private lemma measurable_counts [Countable ι] {X : ℕ → Ω → ι} (hXm : ∀ k, Measurable (X k))
    (n : ℕ) :
    Measurable (fun ω i => #{k ∈ range n | X k ω = i}) := by
  rw [counts_eq_comp]
  exact (measurable_of_countable _).comp (measurable_pi_iff.2 fun k => hXm k)

omit [Fintype ι] in
/-- The cell counts of the first `n` draws are independent of the `n`-th draw. -/
private lemma indepFun_counts [Countable ι] {X : ℕ → Ω → ι} (hXm : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (n : ℕ) :
    IndepFun (fun ω i => #{k ∈ range n | X k ω = i}) (X n) μ := by
  have h := hind.indepFun_finset (range n) {n} (by simp) hXm
  have h' := h.comp (measurable_of_countable
    (fun s : range n → ι => fun i => ∑ k : range n, if s k = i then 1 else 0))
    (measurable_pi_apply (⟨n, mem_singleton_self n⟩ : ({n} : Finset ℕ)))
  rw [counts_eq_comp]
  exact h'

/-- **The cell counts of `n` i.i.d. draws are multinomial.** Let `X 0, X 1, …` be independent
draws from the finite set of cells `ι` with `P(X k = i) = p i` for every draw `k`. Then the
count vector `i ↦ #{k < n | X k = i}` of the first `n` draws has the multinomial law:
`P(counts = x) = multinomialReal n p x = n! / ∏ᵢ xᵢ! · ∏ᵢ pᵢ ^ xᵢ` if `∑ᵢ xᵢ = n`, and `0`
otherwise. -/
theorem measureReal_counts_eq_multinomialReal [IsProbabilityMeasure μ] {X : ℕ → Ω → ι}
    {p : ι → ℝ} (hXm : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hX : ∀ k i, μ.real {ω | X k ω = i} = p i) (n : ℕ) (x : ι → ℕ) :
    μ.real {ω | ∀ i, #{k ∈ range n | X k ω = i} = x i} = multinomialReal n p x := by
  induction n generalizing x with
  | zero =>
    by_cases hx : x = 0
    · subst hx
      simp [multinomialReal, Nat.multinomial]
    · have hset : {ω | ∀ i, #{k ∈ range 0 | X k ω = i} = x i} = ∅ := by
        ext ω
        simp only [range_zero, filter_empty, card_empty, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false, iff_false, not_forall]
        by_contra h
        push Not at h
        exact hx (funext fun i => (h i).symm)
      have hsum : ∑ i, x i ≠ 0 := by
        intro h0
        exact hx (funext fun i => (sum_eq_zero_iff.1 h0) i (mem_univ i))
      rw [hset, measureReal_empty, multinomialReal_of_sum_ne hsum]
  | succ n ih =>
    set C : Ω → ι → ℕ := fun ω i => #{k ∈ range n | X k ω = i} with hC
    have hCm : Measurable C := measurable_counts hXm n
    have hCX : IndepFun C (X n) μ := indepFun_counts hXm hind n
    -- split the event according to the cell of the last draw
    have hsplit : {ω | ∀ i, #{k ∈ range (n + 1) | X k ω = i} = x i} =
        ⋃ i ∈ (univ : Finset ι), (C ⁻¹' {y | y + Pi.single i 1 = x} ∩ X n ⁻¹' {i}) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff, mem_univ, true_and, exists_prop]
      rw [← funext_iff (f := fun i => #{k ∈ range (n + 1) | X k ω = i}), counts_succ]
      constructor
      · intro h
        exact ⟨X n ω, h, rfl⟩
      · rintro ⟨i, h, rfl⟩
        exact h
    have hmeasS : ∀ i, MeasurableSet (C ⁻¹' {y | y + Pi.single i 1 = x} ∩ X n ⁻¹' {i}) :=
      fun i => (hCm (Set.to_countable _).measurableSet).inter
        (hXm n (measurableSet_singleton i))
    rw [hsplit, measureReal_biUnion_finset _ fun i _ => hmeasS i, multinomialReal_succ]
    swap
    · intro i _ j _ hij
      exact Set.disjoint_left.2 fun ω hi hj => hij (hi.2.symm.trans hj.2)
    refine sum_congr rfl fun i _ => ?_
    have hmul : μ.real (C ⁻¹' {y | y + Pi.single i 1 = x} ∩ X n ⁻¹' {i}) =
        μ.real (C ⁻¹' {y | y + Pi.single i 1 = x}) * μ.real (X n ⁻¹' {i}) := by
      simp only [measureReal_def]
      rw [← ENNReal.toReal_mul]
      exact congrArg ENNReal.toReal (hCX.measure_inter_preimage_eq_mul _ _
        (Set.to_countable _).measurableSet (measurableSet_singleton i))
    rw [hmul, show X n ⁻¹' {i} = {ω | X n ω = i} from rfl, hX n i]
    by_cases hi : x i = 0
    · have hempty : {y : ι → ℕ | y + Pi.single i 1 = x} = ∅ := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        have := congrFun h i
        simp [hi] at this
      simp only [hi, ↓reduceIte]
      rw [hempty, Set.preimage_empty, measureReal_empty, zero_mul]
    · have hy : {y : ι → ℕ | y + Pi.single i 1 = x} = {x - Pi.single i 1} := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · rintro rfl
          funext j
          simp
        · rintro rfl
          funext j
          by_cases hj : j = i
          · subst hj
            simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]
            omega
          · simp [hj]
      simp only [hi, ↓reduceIte]
      rw [hy, ← ih (x - Pi.single i 1)]
      congr 2
      ext ω
      simp [C, funext_iff]

/-- **The cell counts of `n` i.i.d. draws are multinomial, as a law.** Under the hypotheses of
`measureReal_counts_eq_multinomialReal`, the count vector `i ↦ #{k < n | X k = i}` has law
`multinomial n p` (the PMF of the merged `Distributions.Multinomial`). The probability-vector
conditions `hp₀`, `hp₁` are needed only to form that PMF. -/
theorem hasLaw_counts_multinomial [IsProbabilityMeasure μ] {X : ℕ → Ω → ι} {p : ι → ℝ}
    (hXm : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hX : ∀ k i, μ.real {ω | X k ω = i} = p i) (hp₀ : ∀ i, 0 ≤ p i) (hp₁ : ∑ i, p i = 1)
    (n : ℕ) :
    HasLaw (fun ω i => #{k ∈ range n | X k ω = i}) (multinomial n p hp₀ hp₁).toMeasure μ where
  aemeasurable := (measurable_counts hXm n).aemeasurable
  map_eq := by
    refine Measure.ext_of_measureReal_singleton fun x => ?_
    have hpre : (fun ω i => #{k ∈ range n | X k ω = i}) ⁻¹' {x} =
        {ω | ∀ i, #{k ∈ range n | X k ω = i} = x i} := by
      ext ω
      simp [funext_iff]
    rw [map_measureReal_apply (measurable_counts hXm n) (measurableSet_singleton x), hpre,
      measureReal_counts_eq_multinomialReal hXm hind hX n x, measureReal_def,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x), multinomial_apply,
      ENNReal.toReal_ofReal (multinomialReal_nonneg hp₀ x)]

/-- **Genotype counts of an i.i.d. sample are multinomial.** Let `G 0, G 1, …` be independent
genotypes in `Fin 3` (the cells `AA`, `AB`, `BB`) with genotype frequencies
`P(G k = j) = p j`. Then for a sample of `n = a + b + c` individuals,
`P(n_AA = a, n_AB = b, n_BB = c) = n! / (a! b! c!) · p₀^a p₁^b p₂^c`. -/
theorem measureReal_genotypeCounts_eq [IsProbabilityMeasure μ] {G : ℕ → Ω → Fin 3}
    {p : Fin 3 → ℝ} (hGm : ∀ k, Measurable (G k)) (hind : iIndepFun G μ)
    (hG : ∀ k j, μ.real {ω | G k ω = j} = p j) (a b c : ℕ) :
    μ.real {ω | #{k ∈ range (a + b + c) | G k ω = 0} = a ∧
        #{k ∈ range (a + b + c) | G k ω = 1} = b ∧ #{k ∈ range (a + b + c) | G k ω = 2} = c} =
      ((a + b + c).factorial : ℝ) / (a.factorial * b.factorial * c.factorial) *
        (p 0 ^ a * p 1 ^ b * p 2 ^ c) := by
  have hset : {ω | #{k ∈ range (a + b + c) | G k ω = 0} = a ∧
        #{k ∈ range (a + b + c) | G k ω = 1} = b ∧ #{k ∈ range (a + b + c) | G k ω = 2} = c} =
      {ω | ∀ j, #{k ∈ range (a + b + c) | G k ω = j} = ![a, b, c] j} := by
    ext ω
    simp [Fin.forall_fin_succ]
  have hsum : ∑ j, ![a, b, c] j = a + b + c := by simp [Fin.sum_univ_three]
  rw [hset, measureReal_counts_eq_multinomialReal hGm hind hG,
    multinomialReal_eq_factorial_div hsum]
  simp [Fin.prod_univ_three]

omit [DecidableEq ι] in
/-- **Lumping cells.** Merging the cells of `ι` along a map `f : ι → κ` turns the cell counts of
`n` i.i.d. draws into the multinomial counts with the merged probabilities
`q j = ∑_{i : f i = j} p i`: `P(#{k < n | f (X k) = j} = y j ∀ j) = multinomialReal n q y`. -/
theorem measureReal_lumpedCounts_eq_multinomialReal [IsProbabilityMeasure μ] {κ : Type*}
    [Fintype κ] [DecidableEq κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    {X : ℕ → Ω → ι} {p : ι → ℝ} (hXm : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hX : ∀ k i, μ.real {ω | X k ω = i} = p i) (f : ι → κ) (n : ℕ) (y : κ → ℕ) :
    μ.real {ω | ∀ j, #{k ∈ range n | f (X k ω) = j} = y j} =
      multinomialReal n (fun j => ∑ i with f i = j, p i) y := by
  refine measureReal_counts_eq_multinomialReal (X := fun k ω => f (X k ω))
    (fun k => (measurable_of_countable f).comp (hXm k))
    (hind.comp (fun _ => f) fun _ => measurable_of_countable f) (fun k j => ?_) n y
  have hset : {ω | f (X k ω) = j} = ⋃ i ∈ ({i | f i = j} : Finset ι), {ω | X k ω = i} := by
    ext ω
    simp
  rw [hset, measureReal_biUnion_finset]
  · exact sum_congr rfl fun i _ => hX k i
  · intro i _ i' _ hii'
    exact Set.disjoint_left.2 fun ω hi hi' => hii' (hi.symm.trans hi')
  · exact fun i _ => hXm k (measurableSet_singleton i)

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Ω] in
/-- The lumped counts of all cells add up to the number of draws. -/
private lemma sum_counts {κ : Type*} [Fintype κ] [DecidableEq κ] (Y : ℕ → Ω → κ) (n : ℕ)
    (ω : Ω) : ∑ j, #{k ∈ range n | Y k ω = j} = n := by
  rw [← card_eq_sum_card_fiberwise (f := fun k => Y k ω) (fun _ _ => mem_coe.2 (mem_univ _)),
    card_range]

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Ω] in
/-- The counts of two distinct cells add up to the count of their union. -/
private lemma counts_add_counts (X : ℕ → Ω → ι) {a b : ι} (hab : a ≠ b) (n : ℕ) (ω : Ω) :
    #{k ∈ range n | X k ω = a} + #{k ∈ range n | X k ω = b} =
      #{k ∈ range n | X k ω = a ∨ X k ω = b} := by
  rw [filter_or, card_union_of_disjoint]
  exact disjoint_filter.2 fun k _ h h' => hab (h.symm.trans h')

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Ω] in
private lemma counts_add_counts_le (X : ℕ → Ω → ι) {a b : ι} (hab : a ≠ b) (n : ℕ) (ω : Ω) :
    #{k ∈ range n | X k ω = a} + #{k ∈ range n | X k ω = b} ≤ n := by
  rw [counts_add_counts X hab]
  exact (card_filter_le _ _).trans (card_range n).le

omit [Fintype ι] in
private lemma measurable_counts_add_counts [Countable ι] {X : ℕ → Ω → ι}
    (hXm : ∀ k, Measurable (X k)) (a b : ι) (n : ℕ) :
    Measurable fun ω => #{k ∈ range n | X k ω = a} + #{k ∈ range n | X k ω = b} :=
  ((measurable_pi_apply a).comp (measurable_counts hXm n)).add
    ((measurable_pi_apply b).comp (measurable_counts hXm n))

/-- The law of the number of draws landing in `{a, b}`: lumping to the two cells `{a, b}` and
the rest, `P(Cₐ + C_b = d) = n! / (d! (n - d)!) (pₐ + p_b)^d r^(n - d)` with
`r = ∑_{i ∉ {a, b}} pᵢ`. -/
private lemma measureReal_counts_add_counts [IsProbabilityMeasure μ] {X : ℕ → Ω → ι}
    {p : ι → ℝ} (hXm : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hX : ∀ k i, μ.real {ω | X k ω = i} = p i) {a b : ι} (hab : a ≠ b) {n d : ℕ}
    (hdn : d ≤ n) :
    μ.real {ω | #{k ∈ range n | X k ω = a} + #{k ∈ range n | X k ω = b} = d} =
      (n.factorial : ℝ) / (d.factorial * (n - d).factorial) *
        ((p a + p b) ^ d * (∑ i with ¬(i = a ∨ i = b), p i) ^ (n - d)) := by
  set h2 : ι → Fin 2 := fun i => if i = a ∨ i = b then 0 else 1 with hh2
  have hh0 : ∀ i, h2 i = 0 ↔ i = a ∨ i = b := fun i => by
    simp only [hh2]; split_ifs <;> simp_all
  have hh1 : ∀ i, h2 i = 1 ↔ ¬(i = a ∨ i = b) := fun i => by
    simp only [hh2]; split_ifs <;> simp_all
  have e0 : ∀ ω, #{k ∈ range n | h2 (X k ω) = 0} =
      #{k ∈ range n | X k ω = a} + #{k ∈ range n | X k ω = b} := fun ω => by
    simp only [hh0, counts_add_counts X hab]
  have e1 : ∀ ω, #{k ∈ range n | h2 (X k ω) = 0} + #{k ∈ range n | h2 (X k ω) = 1} = n :=
    fun ω => by
      have := sum_counts (fun k ω => h2 (X k ω)) n ω
      rwa [Fin.sum_univ_two] at this
  have q20 : ∑ i with h2 i = 0, p i = p a + p b := by
    simp only [hh0]
    rw [filter_or, sum_union (disjoint_filter.2 fun i _ h h' => hab (h.symm.trans h'))]
    simp [filter_eq']
  have q21 : ∑ i with h2 i = 1, p i = ∑ i with ¬(i = a ∨ i = b), p i := by
    simp only [hh1]
  have hset : {ω | #{k ∈ range n | X k ω = a} + #{k ∈ range n | X k ω = b} = d} =
      {ω | ∀ j, #{k ∈ range n | h2 (X k ω) = j} = ![d, n - d] j} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Fin.forall_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    have h0 := e0 ω
    have h1 := e1 ω
    omega
  have hsum : ∑ j, ![d, n - d] j = n := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  rw [hset, measureReal_lumpedCounts_eq_multinomialReal hXm hind hX h2 n,
    multinomialReal_eq_factorial_div hsum]
  simp [Fin.prod_univ_two, q20, q21]

omit [Fintype ι] in
/-- **Conditional binomial law in the fixed-total model.** For two distinct cells `a ≠ b` and
`n` i.i.d. draws, given that `d` of the draws land in `{a, b}` (an event of positive
probability), the number landing in `a` is binomial `Bin(d, p a / (p a + p b))`:
`P(Cₐ = m | Cₐ + C_b = d) = C(d, m) (pₐ / (pₐ + p_b))^m (p_b / (pₐ + p_b))^(d - m)`.
This is the conditional law on which the McNemar and TDT exact tests condition. -/
theorem cond_measureReal_counts_eq_binomial [Finite ι] [IsProbabilityMeasure μ] {X : ℕ → Ω → ι}
    {p : ι → ℝ} (hXm : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hX : ∀ k i, μ.real {ω | X k ω = i} = p i) {a b : ι} (hab : a ≠ b) {n d : ℕ}
    (hd : μ {ω | #{k ∈ range n | X k ω = a} + #{k ∈ range n | X k ω = b} = d} ≠ 0) (m : ℕ) :
    (μ[|{ω | #{k ∈ range n | X k ω = a} + #{k ∈ range n | X k ω = b} = d}]).real
        {ω | #{k ∈ range n | X k ω = a} = m} =
      (d.choose m : ℝ) * (p a / (p a + p b)) ^ m * (p b / (p a + p b)) ^ (d - m) := by
  have := Fintype.ofFinite ι
  set Ca : Ω → ℕ := fun ω => #{k ∈ range n | X k ω = a} with hCa
  set Cb : Ω → ℕ := fun ω => #{k ∈ range n | X k ω = b} with hCb
  set S : Set Ω := {ω | Ca ω + Cb ω = d} with hS
  set r : ℝ := ∑ i with ¬(i = a ∨ i = b), p i with hr
  -- lumping to the three cells `{a}`, `{b}` and the rest
  set g3 : ι → Fin 3 := fun i => if i = a then 0 else if i = b then 1 else 2 with hg3
  have hg0 : ∀ i, g3 i = 0 ↔ i = a := fun i => by
    simp only [hg3]; split_ifs <;> simp_all
  have hg1 : ∀ i, g3 i = 1 ↔ i = b := fun i => by
    simp only [hg3]; split_ifs <;> simp_all
  have hg2 : ∀ i, g3 i = 2 ↔ ¬(i = a ∨ i = b) := fun i => by
    simp only [hg3]; split_ifs <;> simp_all
  have c0 : ∀ ω, #{k ∈ range n | g3 (X k ω) = 0} = Ca ω := fun ω => by
    simp only [hCa, hg0]
  have c1 : ∀ ω, #{k ∈ range n | g3 (X k ω) = 1} = Cb ω := fun ω => by
    simp only [hCb, hg1]
  have c3 : ∀ ω, Ca ω + Cb ω + #{k ∈ range n | g3 (X k ω) = 2} = n := fun ω => by
    have := sum_counts (fun k ω => g3 (X k ω)) n ω
    rw [Fin.sum_univ_three, c0, c1] at this
    exact this
  have q30 : ∑ i with g3 i = 0, p i = p a := by simp only [hg0, sum_filter, sum_ite_eq']; simp
  have q31 : ∑ i with g3 i = 1, p i = p b := by simp only [hg1, sum_filter, sum_ite_eq']; simp
  have q32 : ∑ i with g3 i = 2, p i = r := by simp only [hg2, hr]
  have hSm : MeasurableSet S :=
    (measurable_counts_add_counts hXm a b n) (measurableSet_singleton d)
  have hdn : d ≤ n := by
    by_contra hdn
    apply hd
    have : S = ∅ := by
      ext ω
      simp only [hS, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      have : Ca ω + Cb ω ≤ n := counts_add_counts_le X hab n ω
      omega
    rw [this, measure_empty]
  have hSreal := measureReal_counts_add_counts hXm hind hX hab hdn
  rw [← hr] at hSreal
  have hSpos : μ.real S ≠ 0 := by
    rw [measureReal_def, ENNReal.toReal_ne_zero]
    exact ⟨hd, measure_ne_top μ S⟩
  have hcond : (μ[|S]).real {ω | Ca ω = m} = (μ.real S)⁻¹ * μ.real (S ∩ {ω | Ca ω = m}) := by
    simp only [measureReal_def, cond_apply hSm, ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [hcond]
  by_cases hmd : m ≤ d
  · have hset : S ∩ {ω | Ca ω = m} =
        {ω | ∀ j, #{k ∈ range n | g3 (X k ω) = j} = ![m, d - m, n - d] j} := by
      ext ω
      have := c3 ω
      simp only [hS, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩ j
        fin_cases j
        · change #{k ∈ range n | g3 (X k ω) = 0} = m
          rw [c0]; exact h2
        · change #{k ∈ range n | g3 (X k ω) = 1} = d - m
          rw [c1]; omega
        · change #{k ∈ range n | g3 (X k ω) = 2} = n - d
          omega
      · intro h
        have h0 := h 0
        have h1 := h 1
        have h3 := h 2
        simp only [c0, c1] at h0 h1
        simp at h0 h1 h3
        omega
    have hsum : ∑ j, ![m, d - m, n - d] j = n := by
      rw [Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      omega
    rw [hset, measureReal_lumpedCounts_eq_multinomialReal hXm hind hX g3 n,
      multinomialReal_eq_factorial_div hsum]
    simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, q30, q31, q32]
    have hSpos' := hSpos
    rw [hSreal] at hSpos'
    have hs : (p a + p b) ^ d ≠ 0 := fun h => hSpos' (by rw [h]; ring)
    have hr' : r ^ (n - d) ≠ 0 := fun h => hSpos' (by rw [h]; ring)
    rw [Nat.cast_choose ℝ hmd, hSreal, div_pow, div_pow]
    have hpow : (p a + p b) ^ d = (p a + p b) ^ m * (p a + p b) ^ (d - m) := by
      rw [← pow_add, Nat.add_sub_cancel' hmd]
    obtain ⟨hsm, hsdm⟩ := mul_ne_zero_iff.1 (hpow ▸ hs)
    have f1 : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have f2 : (d.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have f3 : ((n - d).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have f4 : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have f5 : ((d - m).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    rw [hpow]
    field_simp
  · have hset : S ∩ {ω | Ca ω = m} = ∅ := by
      ext ω
      simp only [hS, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
        not_and]
      omega
    rw [hset, measureReal_empty, mul_zero, Nat.choose_eq_zero_of_lt (by omega)]
    simp

omit [Fintype ι] in
/-- **Conditional binomial law in the fixed-total model, as a law.** Under the hypotheses of
`cond_measureReal_counts_eq_binomial`, given `Cₐ + C_b = d` (an event of positive probability)
the count `Cₐ` has law `Bin(d, pₐ / (pₐ + p_b))`. For `pₐ = p_b` (McNemar's null of marginal
homogeneity, or the TDT null of no transmission distortion) with `pₐ > 0` this is
`Bin(d, 1/2)` after rewriting the success probability; if `pₐ = p_b = 0` the conditioning forces
`d = 0` and the stated law is `Bin(0, 0)`, equal to `Bin(0, 1/2)` as a measure but not
syntactically. The nonnegativity `hp₀` is needed only to form the success probability in
`[0, 1]`. -/
theorem hasLaw_cond_counts_binomial [Finite ι] [IsProbabilityMeasure μ] {X : ℕ → Ω → ι} {p : ι → ℝ}
    (hXm : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hX : ∀ k i, μ.real {ω | X k ω = i} = p i) (hp₀ : ∀ i, 0 ≤ p i) {a b : ι} (hab : a ≠ b)
    {n d : ℕ}
    (hd : μ {ω | #{k ∈ range n | X k ω = a} + #{k ∈ range n | X k ω = b} = d} ≠ 0) :
    HasLaw (fun ω => #{k ∈ range n | X k ω = a})
      (binomial d ⟨p a / (p a + p b), div_nonneg (hp₀ a) (add_nonneg (hp₀ a) (hp₀ b)),
        div_le_one_of_le₀ (le_add_of_nonneg_right (hp₀ b)) (add_nonneg (hp₀ a) (hp₀ b))⟩)
      (μ[|{ω | #{k ∈ range n | X k ω = a} + #{k ∈ range n | X k ω = b} = d}]) where
  aemeasurable := ((measurable_pi_apply a).comp (measurable_counts hXm n)).aemeasurable
  map_eq := by
    have := Fintype.ofFinite ι
    have hCam : Measurable fun ω => #{k ∈ range n | X k ω = a} :=
      (measurable_pi_apply a).comp (measurable_counts hXm n)
    have := cond_isProbabilityMeasure (μ := μ) hd
    refine Measure.ext_of_measureReal_singleton fun m => ?_
    rw [map_measureReal_apply hCam (measurableSet_singleton m),
      show (fun ω => #{k ∈ range n | X k ω = a}) ⁻¹' {m} = {ω | #{k ∈ range n | X k ω = a} = m}
        from rfl, cond_measureReal_counts_eq_binomial hXm hind hX hab hd m,
      binomial_real_singleton]
    -- the success probabilities agree unless `pₐ + p_b = 0`, which forces `d = 0`
    by_cases hs : p a + p b = 0
    · have hd0 : d = 0 := by
        by_contra hd0
        have hdn : d ≤ n := by
          by_contra hdn
          apply hd
          have : {ω | #{k ∈ range n | X k ω = a} + #{k ∈ range n | X k ω = b} = d} = ∅ := by
            ext ω
            simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
            have := counts_add_counts_le X hab n ω
            omega
          rw [this, measure_empty]
        apply hd
        have h := measureReal_counts_add_counts hXm hind hX hab hdn
        rw [hs, zero_pow hd0, zero_mul, mul_zero] at h
        exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 h
      subst hd0
      simp
    · congr 1
      simp only
      congr 1
      field_simp
      ring

end Sampling

end MathlibExt.Probability.Statistics.ExactTests
