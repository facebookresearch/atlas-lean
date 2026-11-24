/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.FiniteSanov
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Topology.Order.Compact

/-!
# Gibbs' conditioning principle for finite alphabets

Let `Q > 0` be a distribution on a finite alphabet and `Γ` a set of distributions satisfying the
condition of Sanov's theorem in `MathlibExt.InformationTheory.FiniteSanov`, and suppose a unique
`P*` in the closure of `Γ` has `D(P* ‖ Q) = D(Γ ‖ Q)`. Conditioned on the event that the empirical
distribution of `n` independent draws from `Q` lies in `Γ`, the first `k` draws are asymptotically
independent with law `P*`: this is `tendsto_iidProb_prefix_div_iidProb` (Csiszár, "The method of
types", IEEE Trans. Inform. Theory 44 (1998), Corollary to Theorem III.3).

## Proof outline

* *Concentration.* For `δ > 0`, the distributions of `Γ` at distance at least `δ` from `P*` have
  divergence at least some `r' > r`: the closure of `Γ` is a compact subset of the probability
  simplex, the divergence is continuous because `Q > 0`, and `P*` is its only minimiser there.
  Sanov's bounds then make the probability that the empirical distribution lies in `Γ` but is
  `δ`-far from `P*` exponentially smaller than the probability that it lies in `Γ`. Hence the
  conditional mean of the bounded function `∏ᵢ P̂ₓ(yᵢ)` of the empirical distribution `P̂ₓ`, which
  is continuous in `P̂ₓ`, tends to `∏ᵢ P*(yᵢ)`.
* *Exchangeability.* The event `P̂ₓ ∈ Γ` and the weight `∏ⱼ Q(xⱼ)` are invariant under permutations
  of positions, so reading `y` at the positions `ι 0, …, ι (k - 1)` has the same conditional
  probability for every injective `ι : Fin k → Fin n`. Summing over all `n ^ k` maps `ι` counts,
  for each `x`, the `∏ᵢ n P̂ₓ(yᵢ)` maps with `x ∘ ι = y`; the non-injective maps form a fraction
  `1 - n (n - 1) ⋯ (n - k + 1) / n ^ k` of all maps, which tends to `0`. So the conditional
  probability of the prefix `y` and the conditional mean of `∏ᵢ P̂ₓ(yᵢ)` have the same limit.

## Implementation notes

The theorem keeps the full name it had in the former wanted module, so its namespace still reads
`GibbsConditioningWanted`. Its hypotheses `∑ₐ Q(a) = 1`, `P* ∈ closure Γ` and `D(P* ‖ Q) = r` are
part of that statement but are not used by the proof: the conditional probability does not change
when `Q` is rescaled, and a point of the closure of `Γ` with divergence `r` exists anyway, as a
limit point of the empirical distributions of the types `s n`. The `unusedVariables` linter is
turned off for this theorem only.

## References

* I. Csiszár, "The method of types", IEEE Trans. Inform. Theory 44 (1998), Section III, Corollary
  to Theorem III.3.
-/

namespace MathlibExt.InformationTheory.GibbsConditioningWanted

@[expose] public section

open Finset Real Filter Topology MathlibExt.InformationTheory.MethodOfTypes

section Auxiliary

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### Exchangeability: the prefix event averaged over all positions -/

/-- For a weight `F` on sequences that is invariant under permutations of positions, the weighted
number of sequences reading the word `y` at the positions `ι` is the same for every injective
`ι`. -/
private theorem sum_mul_ite_eq_of_injective {n k : ℕ} (F : (Fin n → α) → ℝ)
    (hF : ∀ (x : Fin n → α) (σ : Equiv.Perm (Fin n)), F (x ∘ σ) = F x) (y : Fin k → α)
    {ι ι' : Fin k → Fin n} (hι : Function.Injective ι) (hι' : Function.Injective ι') :
    ∑ x, F x * (if ∀ i, x (ι i) = y i then 1 else 0) =
      ∑ x, F x * (if ∀ i, x (ι' i) = y i then 1 else 0) := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair ι' ι hι' hι
  symm
  rw [← Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl α))]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h1 : (Equiv.arrowCongr σ.symm (Equiv.refl α)) x = x ∘ σ := by
    funext j
    simp [Equiv.arrowCongr_apply]
  rw [h1, hF]
  simp only [Function.comp_apply, hσ]

omit [Fintype α] in
/-- **Counting the readings of a word.** The number of maps `ι : Fin k → Fin n` with
`x (ι i) = y i` for all `i` is `∏ᵢ count (y i) (seqType x)`. -/
private theorem card_filter_forall_comp_eq {n k : ℕ} (x : Fin n → α) (y : Fin k → α) :
    #(univ.filter fun ι : Fin k → Fin n => ∀ i, x (ι i) = y i) =
      ∏ i, (seqType x : Multiset α).count (y i) := by
  have h : (univ.filter fun ι : Fin k → Fin n => ∀ i, x (ι i) = y i) =
      Fintype.piFinset fun i => univ.filter fun j => x j = y i := by
    ext ι
    simp [Fintype.mem_piFinset]
  rw [h, Fintype.card_piFinset]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [count_seqType, Fintype.card_subtype]

/-- **Exchangeability bound.** For a nonnegative weight `F` on sequences of length `n ≥ k`,
invariant under permutations of positions, write `N` for the weighted number of sequences
starting with the word `y`, `T` for the total weight, and `C(x) = ∏ᵢ count (y i) (seqType x)`.
Averaging the prefix event over all `n ^ k` maps `Fin k → Fin n`, of which `n (n - 1) ⋯ (n - k + 1)`
are injective, gives `n⁽ᵏ⁾ N ≤ ∑ₓ F(x) C(x) ≤ n⁽ᵏ⁾ N + (n ^ k - n⁽ᵏ⁾) T`, where `n⁽ᵏ⁾` is the
descending factorial. -/
private theorem descFactorial_mul_le_and_le {n k : ℕ} (hkn : k ≤ n)
    (F : (Fin n → α) → ℝ) (hF0 : ∀ x, 0 ≤ F x)
    (hF : ∀ (x : Fin n → α) (σ : Equiv.Perm (Fin n)), F (x ∘ σ) = F x) (y : Fin k → α) :
    (n.descFactorial k : ℝ) * ∑ x, F x * (if ∀ i, x (Fin.castLE hkn i) = y i then 1 else 0) ≤
        ∑ x, F x * ∏ i, ((seqType x : Multiset α).count (y i) : ℝ) ∧
      ∑ x, F x * ∏ i, ((seqType x : Multiset α).count (y i) : ℝ) ≤
        (n.descFactorial k : ℝ) * ∑ x, F x * (if ∀ i, x (Fin.castLE hkn i) = y i then 1 else 0) +
          ((n : ℝ) ^ k - n.descFactorial k) * ∑ x, F x := by
  classical
  set S : (Fin k → Fin n) → ℝ := fun ι => ∑ x, F x * (if ∀ i, x (ι i) = y i then 1 else 0)
    with hS
  have htot : ∑ ι, S ι = ∑ x, F x * ∏ i, ((seqType x : Multiset α).count (y i) : ℝ) := by
    simp only [hS]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.mul_sum, Finset.sum_boole, card_filter_forall_comp_eq]
    push_cast
    rfl
  have hinj : ∀ ι, Function.Injective ι → S ι = S (Fin.castLE hkn) := fun ι hι =>
    sum_mul_ite_eq_of_injective F hF y hι (Fin.castLE_injective hkn)
  have hS0 : ∀ ι, 0 ≤ S ι := fun ι =>
    Finset.sum_nonneg fun x _ => mul_nonneg (hF0 x) (by split_ifs <;> norm_num)
  have hS1 : ∀ ι, S ι ≤ ∑ x, F x := fun ι =>
    Finset.sum_le_sum fun x _ => by
      split_ifs
      · rw [mul_one]
      · rw [mul_zero]; exact hF0 x
  have hcard_inj : #(univ.filter fun ι : Fin k → Fin n => Function.Injective ι) =
      n.descFactorial k := by
    rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _),
      Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
  have hcard_all : #(univ.filter fun ι : Fin k → Fin n => Function.Injective ι) +
      #(univ.filter fun ι : Fin k → Fin n => ¬ Function.Injective ι) = n ^ k := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin]
  have hcard_not : (#(univ.filter fun ι : Fin k → Fin n => ¬ Function.Injective ι) : ℝ) =
      (n : ℝ) ^ k - n.descFactorial k := by
    rw [← hcard_inj]
    have := congrArg (fun m : ℕ => (m : ℝ)) hcard_all
    push_cast at this
    linarith
  have h1 : ∑ ι ∈ univ.filter (fun ι : Fin k → Fin n => Function.Injective ι), S ι =
      n.descFactorial k * S (Fin.castLE hkn) := by
    rw [Finset.sum_congr rfl fun ι hι => hinj ι (Finset.mem_filter.mp hι).2, Finset.sum_const,
      hcard_inj, nsmul_eq_mul]
  have h2 : 0 ≤ ∑ ι ∈ univ.filter (fun ι : Fin k → Fin n => ¬ Function.Injective ι), S ι :=
    Finset.sum_nonneg fun ι _ => hS0 ι
  have h3 : ∑ ι ∈ univ.filter (fun ι : Fin k → Fin n => ¬ Function.Injective ι), S ι ≤
      ((n : ℝ) ^ k - n.descFactorial k) * ∑ x, F x := by
    calc ∑ ι ∈ univ.filter (fun ι : Fin k → Fin n => ¬ Function.Injective ι), S ι
        ≤ ∑ _ι ∈ univ.filter (fun ι : Fin k → Fin n => ¬ Function.Injective ι), ∑ x, F x :=
          Finset.sum_le_sum fun ι _ => hS1 ι
      _ = ((n : ℝ) ^ k - n.descFactorial k) * ∑ x, F x := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard_not]
  have hsplit := Finset.sum_filter_add_sum_filter_not univ
    (fun ι : Fin k → Fin n => Function.Injective ι) S
  have hN : S (Fin.castLE hkn) =
      ∑ x, F x * (if ∀ i, x (Fin.castLE hkn i) = y i then 1 else 0) := rfl
  rw [← htot, ← hN, ← hsplit, h1]
  exact ⟨by linarith, by linarith⟩

/-! ### Concentration of the empirical distribution near `P*` -/

omit [DecidableEq α] in
/-- The divergence `P ↦ ∑ₐ P(a) log (P(a) / Q(a))` is continuous on all of `α → ℝ` when `Q > 0`,
with the convention `0 log 0 = 0` built into `Real.log`. -/
private theorem continuous_divergence {Q : α → ℝ} (hQ : ∀ a, 0 < Q a) :
    Continuous fun P : α → ℝ => ∑ a, P a * log (P a / Q a) := by
  have h : (fun P : α → ℝ => ∑ a, P a * log (P a / Q a)) =
      fun P => ∑ a, (P a * log (P a) - P a * log (Q a)) := by
    funext P
    refine Finset.sum_congr rfl fun a _ => ?_
    rcases eq_or_ne (P a) 0 with h | h
    · simp [h]
    · rw [log_div h (hQ a).ne']; ring
  rw [h]
  refine continuous_finsetSum _ fun a _ => ?_
  exact (Real.continuous_mul_log.comp (continuous_apply a)).sub
    ((continuous_apply a).mul continuous_const)

omit [DecidableEq α] in
/-- **A divergence gap away from `P*`.** If `P*` is the only point of the closure of `Γ` with
`D(P* ‖ Q) = r`, where `r ≤ D(P ‖ Q)` on `Γ`, then for every `δ > 0` the distributions of `Γ` at
distance at least `δ` from `P*` have divergence at least some `r' > r`. The closure of `Γ` is
compact, inside the probability simplex, and the divergence is continuous there. -/
private theorem exists_lt_forall_le_of_le_dist {Q : α → ℝ} (hQ : ∀ a, 0 < Q a)
    {Γ : Set (α → ℝ)} (hΓ : ∀ P ∈ Γ, (∀ a, 0 ≤ P a) ∧ ∑ a, P a = 1)
    {r : ℝ} (hr : ∀ P ∈ Γ, r ≤ ∑ a, P a * log (P a / Q a)) {Ps : α → ℝ}
    (huniq : ∀ P ∈ closure Γ, ∑ a, P a * log (P a / Q a) = r → P = Ps)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ r' > r, ∀ P ∈ Γ, δ ≤ dist P Ps → r' ≤ ∑ a, P a * log (P a / Q a) := by
  set D : (α → ℝ) → ℝ := fun P => ∑ a, P a * log (P a / Q a)
  have hDc : Continuous D := continuous_divergence hQ
  set K : Set (α → ℝ) := closure Γ ∩ {P | δ ≤ dist P Ps}
  have hsub : Γ ⊆ Set.Icc 0 1 := by
    intro P hP
    obtain ⟨h0, h1⟩ := hΓ P hP
    refine ⟨fun a => h0 a, fun a => ?_⟩
    change P a ≤ 1
    rw [← h1]
    exact Finset.single_le_sum (fun b _ => h0 b) (Finset.mem_univ a)
  have hKc : IsCompact K :=
    (isCompact_Icc.closure_of_subset hsub).inter_right
      (isClosed_le continuous_const (continuous_id.dist continuous_const))
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨r + 1, by linarith, fun P hP hPδ => ?_⟩
    have hPK : P ∈ K := ⟨subset_closure hP, hPδ⟩
    rw [hKe] at hPK
    exact absurd hPK (Set.notMem_empty P)
  obtain ⟨P₀, hP₀K, hP₀min⟩ := hKc.exists_isMinOn hKne hDc.continuousOn
  have hcl : closure Γ ⊆ {P | r ≤ D P} := closure_minimal hr (isClosed_le continuous_const hDc)
  have hle : r ≤ D P₀ := hcl hP₀K.1
  have hne : D P₀ ≠ r := fun h => by
    have hP₀ := huniq P₀ hP₀K.1 h
    have h2 : δ ≤ dist P₀ Ps := hP₀K.2
    rw [hP₀, dist_self] at h2
    linarith
  exact ⟨D P₀, lt_of_le_of_ne hle (Ne.symm hne), fun P hP hPδ => hP₀min ⟨subset_closure hP, hPδ⟩⟩

/-- **Conditional concentration near `P*`.** Under the hypotheses of the main theorem, for every
`δ > 0` and `ε > 0`, eventually the probability that the empirical distribution lies in `Γ` at
distance at least `δ` from `P*` is at most `ε` times the probability that it lies in `Γ`. The proof
compares Sanov's upper bound for the far part of `Γ`, with the rate `r' > r` of
`exists_lt_forall_le_of_le_dist`, with Sanov's lower bound for `Γ`. -/
private theorem eventually_sum_far_le {Q : α → ℝ} (hQ : ∀ a, 0 < Q a)
    {Γ : Set (α → ℝ)} [DecidablePred (· ∈ Γ)]
    (hΓ : ∀ P ∈ Γ, (∀ a, 0 ≤ P a) ∧ ∑ a, P a = 1)
    {r : ℝ} (hr : ∀ P ∈ Γ, r ≤ ∑ a, P a * log (P a / Q a))
    (s : ∀ n : ℕ, Sym α n) (hs : ∀ᶠ n in atTop, empirical (s n) ∈ Γ)
    (hlim : Tendsto (fun n => ∑ a, empirical (s n) a * log (empirical (s n) a / Q a))
      atTop (𝓝 r))
    {Ps : α → ℝ} (huniq : ∀ P ∈ closure Γ, ∑ a, P a * log (P a / Q a) = r → P = Ps)
    {δ : ℝ} (hδ : 0 < δ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ∑ x ∈ univ.filter (fun x : Fin n → α => empirical (seqType x) ∈ Γ),
          (∏ i, Q (x i)) * (if δ ≤ dist (empirical (seqType x)) Ps then 1 else 0) ≤
        ε * iidProb Q (univ.filter fun x : Fin n → α => empirical (seqType x) ∈ Γ) := by
  classical
  obtain ⟨r', hr'r, hr'⟩ := exists_lt_forall_le_of_le_dist hQ hΓ hr huniq hδ
  set c := (r' - r) / 3 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hQ0 : ∀ a, 0 ≤ Q a := fun a => (hQ a).le
  set Γδ : Set (α → ℝ) := {P | P ∈ Γ ∧ δ ≤ dist P Ps} with hΓδ
  have hexp : Tendsto (fun n : ℕ => exp (-(n : ℝ) * c)) atTop (𝓝 0) := by
    have := tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_mul_const hc0)
    refine this.congr fun n => ?_
    simp [neg_mul]
  filter_upwards [eventually_pow_card_le_exp (α := α) hc0,
    eventually_exp_le_iidProb_empirical_mem hQ0 s hs
      (Eventually.of_forall fun n a _ => hQ a) hlim hc0,
    eventually_gt_atTop 0, hexp.eventually (ge_mem_nhds hε)] with n hpow hlow hn hexpn
  have hup := iidProb_empirical_mem_le hn.ne' hQ0 Γδ (r := r')
    (fun P hP _ _ _ => hr' P hP.1 hP.2)
  have hL : ∑ x ∈ univ.filter (fun x : Fin n → α => empirical (seqType x) ∈ Γ),
        (∏ i, Q (x i)) * (if δ ≤ dist (empirical (seqType x)) Ps then 1 else 0) =
      iidProb Q (univ.filter fun x : Fin n → α => empirical (seqType x) ∈ Γδ) := by
    rw [iidProb, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h1 : empirical (seqType x) ∈ Γ <;>
      by_cases h2 : δ ≤ dist (empirical (seqType x)) Ps <;>
      simp [hΓδ, h1, h2]
  rw [hL]
  calc iidProb Q (univ.filter fun x : Fin n → α => empirical (seqType x) ∈ Γδ)
      ≤ ((n : ℝ) + 1) ^ Fintype.card α * exp (-(n : ℝ) * r') := hup
    _ ≤ exp (n * c) * exp (-(n : ℝ) * r') := mul_le_mul_of_nonneg_right hpow (exp_pos _).le
    _ = exp (-(n : ℝ) * c) * exp (-(n : ℝ) * (r + c)) := by
        rw [← exp_add, ← exp_add]; congr 1; rw [hc]; ring
    _ ≤ ε * iidProb Q (univ.filter fun x : Fin n → α => empirical (seqType x) ∈ Γ) :=
        mul_le_mul hexpn hlow (exp_pos _).le hε.le

omit [Fintype α] in
/-- The empirical distribution of an `n`-type, `n ≥ 1`, takes values in `[0, 1]`. -/
private theorem empirical_le_one {n : ℕ} (hn : n ≠ 0) (s : Sym α n) (a : α) :
    empirical s a ≤ 1 := by
  unfold empirical
  rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
  exact_mod_cast count_le s a

/-- **The conditional mean of `∏ᵢ P̂(yᵢ)` tends to `∏ᵢ P*(yᵢ)`.** Under the hypotheses of the main
theorem, the average of `∏ᵢ P̂ₓ(yᵢ)` over the sequences `x` whose empirical distribution `P̂ₓ` lies
in `Γ`, weighted by their probability, tends to `∏ᵢ P*(yᵢ)`. -/
private theorem tendsto_sum_mul_prod_empirical_div {Q : α → ℝ} (hQ : ∀ a, 0 < Q a)
    {Γ : Set (α → ℝ)} [DecidablePred (· ∈ Γ)]
    (hΓ : ∀ P ∈ Γ, (∀ a, 0 ≤ P a) ∧ ∑ a, P a = 1)
    {r : ℝ} (hr : ∀ P ∈ Γ, r ≤ ∑ a, P a * log (P a / Q a))
    (s : ∀ n : ℕ, Sym α n) (hs : ∀ᶠ n in atTop, empirical (s n) ∈ Γ)
    (hlim : Tendsto (fun n => ∑ a, empirical (s n) a * log (empirical (s n) a / Q a))
      atTop (𝓝 r))
    {Ps : α → ℝ} (huniq : ∀ P ∈ closure Γ, ∑ a, P a * log (P a / Q a) = r → P = Ps)
    {k : ℕ} (y : Fin k → α) :
    Tendsto (fun n : ℕ =>
      (∑ x ∈ univ.filter (fun x : Fin n → α => empirical (seqType x) ∈ Γ),
          (∏ i, Q (x i)) * ∏ i, empirical (seqType x) (y i)) /
        iidProb Q (univ.filter fun x : Fin n → α => empirical (seqType x) ∈ Γ))
      atTop (𝓝 (∏ i, Ps (y i))) := by
  set L := ∏ i, Ps (y i)
  set f : (α → ℝ) → ℝ := fun P => ∏ i, P (y i)
  have hfc : Continuous f := continuous_finsetProd _ fun i _ => continuous_apply (y i)
  have hQ0 : ∀ a, 0 ≤ Q a := fun a => (hQ a).le
  rw [Metric.tendsto_nhds]
  intro ε hε
  set M := 1 + |L| with hM
  have hM0 : 0 < M := by positivity
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuous_iff.mp hfc Ps (ε / 3) (by positivity)
  filter_upwards [eventually_sum_far_le hQ hΓ hr s hs hlim huniq hδ
      (ε := ε / (3 * M)) (by positivity),
    eventually_exp_le_iidProb_empirical_mem hQ0 s hs
      (Eventually.of_forall fun n a _ => hQ a) hlim one_pos,
    eventually_gt_atTop 0] with n hfar hlow hn
  set A := univ.filter (fun x : Fin n → α => empirical (seqType x) ∈ Γ)
  set den := iidProb Q A with hden
  have hden0 : 0 < den := (exp_pos _).trans_le hlow
  set far := ∑ x ∈ A, (∏ i, Q (x i)) * (if δ ≤ dist (empirical (seqType x)) Ps then 1 else 0)
    with hfar_def
  have hpt : ∀ x ∈ A, |f (empirical (seqType x)) - L| ≤
      ε / 3 + M * (if δ ≤ dist (empirical (seqType x)) Ps then 1 else 0) := by
    intro x _
    by_cases h : δ ≤ dist (empirical (seqType x)) Ps
    · rw [ite_eq_left h, mul_one]
      have h0 : 0 ≤ f (empirical (seqType x)) :=
        Finset.prod_nonneg fun i _ => empirical_nonneg (seqType x) (y i)
      have h1 : f (empirical (seqType x)) ≤ 1 :=
        Finset.prod_le_one₀ (fun i _ => empirical_nonneg _ _)
          (fun i _ => empirical_le_one hn.ne' _ _)
      calc |f (empirical (seqType x)) - L| ≤ |f (empirical (seqType x))| + |L| := abs_sub _ _
        _ ≤ 1 + |L| := by rw [abs_of_nonneg h0]; linarith
        _ ≤ ε / 3 + M := by rw [hM]; linarith
    · rw [ite_eq_right h, mul_zero, add_zero]
      push Not at h
      have := hfδ _ h
      rw [Real.dist_eq] at this
      exact this.le
  have hsum : |(∑ x ∈ A, (∏ i, Q (x i)) * f (empirical (seqType x))) - L * den| ≤
      ε / 3 * den + M * far := by
    rw [hden, iidProb, Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc |∑ x ∈ A, ((∏ i, Q (x i)) * f (empirical (seqType x)) - L * ∏ i, Q (x i))|
        ≤ ∑ x ∈ A, |(∏ i, Q (x i)) * f (empirical (seqType x)) - L * ∏ i, Q (x i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x ∈ A, (∏ i, Q (x i)) * |f (empirical (seqType x)) - L| := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [mul_comm L, ← mul_sub, abs_mul,
            abs_of_nonneg (Finset.prod_nonneg fun i _ => hQ0 _)]
      _ ≤ ∑ x ∈ A, (∏ i, Q (x i)) *
            (ε / 3 + M * (if δ ≤ dist (empirical (seqType x)) Ps then 1 else 0)) :=
          Finset.sum_le_sum fun x hx =>
            mul_le_mul_of_nonneg_left (hpt x hx) (Finset.prod_nonneg fun i _ => hQ0 _)
      _ = ε / 3 * ∑ x ∈ A, ∏ i, Q (x i) + M * far := by
          rw [hfar_def, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun x _ => ?_
          ring
  have hfar' : M * far ≤ ε / 3 * den := by
    calc M * far ≤ M * (ε / (3 * M) * den) := mul_le_mul_of_nonneg_left hfar hM0.le
      _ = ε / 3 * den := by field_simp
  have heq : (∑ x ∈ A, (∏ i, Q (x i)) * f (empirical (seqType x))) / den - L =
      ((∑ x ∈ A, (∏ i, Q (x i)) * f (empirical (seqType x))) - L * den) / den := by
    field_simp
  change |(∑ x ∈ A, (∏ i, Q (x i)) * f (empirical (seqType x))) / den - L| < ε
  rw [heq, abs_div, abs_of_pos hden0, div_lt_iff₀ hden0]
  have := mul_pos hε hden0
  linarith

end Auxiliary

/-! ### Gibbs' conditioning principle -/

set_option linter.unusedVariables false in
/-- **Gibbs' conditioning principle, finite alphabet** (Csiszár, "The method of types", IEEE
Trans. Inform. Theory 44 (1998), Corollary to Theorem III.3). Let `Q > 0` be a distribution on a
finite alphabet and `Γ` a set of distributions satisfying (III.21), in the form: `r ≤ D(P ‖ Q)` on
`Γ`, and some `n`-types `s n`, in `Γ` for all large `n`, have `D(P̂_{s n} ‖ Q) → r`, so
`r = D(Γ ‖ Q)`; for nonempty `Γ` this form is equivalent to (III.21), since `D(Γ ‖ Q) < ∞` when
`Q > 0`. If a unique `P*` in the closure
of `Γ` has `D(P* ‖ Q) = r`, then for every `k` and every word `y` of length `k`, the conditional
probability that the first `k` of `n` independent draws from `Q` spell `y`, given that their
empirical distribution lies in `Γ`, tends to `∏ᵢ P*(yᵢ)`. The source allows any `Q`; this
statement assumes `Q > 0`. -/
theorem tendsto_iidProb_prefix_div_iidProb {α : Type*} [Fintype α] [DecidableEq α]
    {Q : α → ℝ} (hQ : ∀ a, 0 < Q a) (hQ1 : ∑ a, Q a = 1)
    {Γ : Set (α → ℝ)} [DecidablePred (· ∈ Γ)]
    (hΓ : ∀ P ∈ Γ, (∀ a, 0 ≤ P a) ∧ ∑ a, P a = 1)
    {r : ℝ} (hr : ∀ P ∈ Γ, r ≤ ∑ a, P a * log (P a / Q a))
    (s : ∀ n : ℕ, Sym α n) (hs : ∀ᶠ n in atTop, empirical (s n) ∈ Γ)
    (hlim : Tendsto (fun n => ∑ a, empirical (s n) a * log (empirical (s n) a / Q a))
      atTop (𝓝 r))
    {Ps : α → ℝ} (hPs : Ps ∈ closure Γ) (hPsD : ∑ a, Ps a * log (Ps a / Q a) = r)
    (huniq : ∀ P ∈ closure Γ, ∑ a, P a * log (P a / Q a) = r → P = Ps)
    (k : ℕ) (y : Fin k → α) :
    Tendsto (fun n : ℕ =>
      iidProb Q (univ.filter fun x : Fin n → α =>
          empirical (seqType x) ∈ Γ ∧ ∀ i : Fin k, ∀ h : (i : ℕ) < n, x ⟨i, h⟩ = y i) /
        iidProb Q (univ.filter fun x : Fin n → α => empirical (seqType x) ∈ Γ))
      atTop (𝓝 (∏ i, Ps (y i))) := by
  classical
  have hQ0 : ∀ a, 0 ≤ Q a := fun a => (hQ a).le
  set L := ∏ i, Ps (y i)
  set den : ℕ → ℝ := fun n =>
    iidProb Q (univ.filter fun x : Fin n → α => empirical (seqType x) ∈ Γ) with hden
  set num : ℕ → ℝ := fun n => iidProb Q (univ.filter fun x : Fin n → α =>
    empirical (seqType x) ∈ Γ ∧ ∀ i : Fin k, ∀ h : (i : ℕ) < n, x ⟨i, h⟩ = y i) with hnum
  set E : ℕ → ℝ := fun n => ∑ x ∈ univ.filter (fun x : Fin n → α => empirical (seqType x) ∈ Γ),
    (∏ i, Q (x i)) * ∏ i, empirical (seqType x) (y i) with hE
  set ρ : ℕ → ℝ := fun n => (n.descFactorial k : ℝ) / (n : ℝ) ^ k with hρ
  have hv : Tendsto (fun n => E n / den n) atTop (𝓝 L) :=
    tendsto_sum_mul_prod_empirical_div hQ hΓ hr s hs hlim huniq y
  have hρlim : Tendsto ρ atTop (𝓝 1) := by
    have hlow : Tendsto (fun n : ℕ => (1 + (1 - (k : ℝ)) / n) ^ k) atTop (𝓝 1) := by
      have := ((tendsto_const_nhds (x := (1 : ℝ))).add
        (tendsto_const_div_atTop_nhds_zero_nat (1 - (k : ℝ)))).pow k
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop k, eventually_gt_atTop 0] with n hkn hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have h1 : 1 + (1 - (k : ℝ)) / n = ((n + 1 - k : ℕ) : ℝ) / n := by
        rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
        field_simp
        ring
      rw [h1, div_pow]
      exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.pow_sub_le_descFactorial n k)
        (by positivity)
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      change (n.descFactorial k : ℝ) / (n : ℝ) ^ k ≤ 1
      rw [div_le_one (by positivity)]
      exact_mod_cast Nat.descFactorial_le_pow n k
  have hpos : ∀ᶠ n in atTop, 0 < den n := by
    filter_upwards [eventually_exp_le_iidProb_empirical_mem hQ0 s hs
      (Eventually.of_forall fun n a _ => hQ a) hlim one_pos] with n hn
    exact (exp_pos _).trans_le hn
  have hkey : ∀ᶠ n in atTop, ρ n * (num n / den n) ≤ E n / den n ∧
      E n / den n ≤ ρ n * (num n / den n) + (1 - ρ n) := by
    filter_upwards [eventually_ge_atTop k, eventually_gt_atTop 0, hpos] with n hkn hn hden0
    set F : (Fin n → α) → ℝ := fun x =>
      if empirical (seqType x) ∈ Γ then ∏ i, Q (x i) else 0 with hF
    have hF0 : ∀ x, 0 ≤ F x := fun x => by
      simp only [hF]
      split_ifs
      · exact Finset.prod_nonneg fun i _ => hQ0 _
      · exact le_rfl
    have hFσ : ∀ (x : Fin n → α) (σ : Equiv.Perm (Fin n)), F (x ∘ σ) = F x := by
      intro x σ
      simp only [hF, seqType_comp_perm, Function.comp_apply]
      rw [Equiv.prod_comp σ (fun i => Q (x i))]
    obtain ⟨h1, h2⟩ := descFactorial_mul_le_and_le hkn F hF0 hFσ y
    have hT : ∑ x, F x = den n := by
      simp only [hF, hden, iidProb, Finset.sum_filter]
    have hN : ∑ x, F x * (if ∀ i, x (Fin.castLE hkn i) = y i then 1 else 0) = num n := by
      simp only [hnum, iidProb, Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hiff : (∀ i, x (Fin.castLE hkn i) = y i) ↔
          ∀ i : Fin k, ∀ h : (i : ℕ) < n, x ⟨i, h⟩ = y i :=
        ⟨fun h i _ => h i, fun h i => h i (lt_of_lt_of_le i.2 hkn)⟩
      simp only [hF]
      by_cases hx : empirical (seqType x) ∈ Γ
      · by_cases hy : ∀ i, x (Fin.castLE hkn i) = y i
        · have hc : empirical (seqType x) ∈ Γ ∧
              ∀ i : Fin k, ∀ h : (i : ℕ) < n, x ⟨i, h⟩ = y i := ⟨hx, hiff.mp hy⟩
          rw [ite_eq_left hc, ite_eq_left hy, ite_eq_left hx, mul_one]
        · have hc : ¬ (empirical (seqType x) ∈ Γ ∧
              ∀ i : Fin k, ∀ h : (i : ℕ) < n, x ⟨i, h⟩ = y i) := fun h => hy (hiff.mpr h.2)
          rw [ite_eq_right hc, ite_eq_right hy, mul_zero]
      · have hc : ¬ (empirical (seqType x) ∈ Γ ∧
            ∀ i : Fin k, ∀ h : (i : ℕ) < n, x ⟨i, h⟩ = y i) := fun h => hx h.1
        rw [ite_eq_right hc, ite_eq_right hx, zero_mul]
    have hcount : ∀ x : Fin n → α, ∏ i, ((seqType x : Multiset α).count (y i) : ℝ) =
        (n : ℝ) ^ k * ∏ i, empirical (seqType x) (y i) := by
      intro x
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have : ∀ i, ((seqType x : Multiset α).count (y i) : ℝ) =
          (n : ℝ) * empirical (seqType x) (y i) := by
        intro i
        unfold empirical
        field_simp
      simp only [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
    have hC : ∑ x, F x * ∏ i, ((seqType x : Multiset α).count (y i) : ℝ) =
        (n : ℝ) ^ k * E n := by
      simp only [hE, Finset.mul_sum, Finset.sum_filter, hF, hcount]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> ring
    rw [hN, hC] at h1
    rw [hN, hC, hT] at h2
    have hNpos : (0 : ℝ) < (n : ℝ) ^ k := by positivity
    have hden' : 0 < (n : ℝ) ^ k * den n := mul_pos hNpos hden0
    have e1 : ρ n * (num n / den n) = (n.descFactorial k * num n) / ((n : ℝ) ^ k * den n) := by
      simp only [hρ]
      field_simp
    have e2 : E n / den n = ((n : ℝ) ^ k * E n) / ((n : ℝ) ^ k * den n) := by
      field_simp
    have e3 : ρ n * (num n / den n) + (1 - ρ n) =
        (n.descFactorial k * num n + ((n : ℝ) ^ k - n.descFactorial k) * den n) /
          ((n : ℝ) ^ k * den n) := by
      simp only [hρ]
      field_simp
    rw [e3, e1, e2]
    exact ⟨div_le_div_of_nonneg_right h1 hden'.le, div_le_div_of_nonneg_right h2 hden'.le⟩
  have hρpos : ∀ᶠ n in atTop, 0 < ρ n := hρlim.eventually (lt_mem_nhds one_pos)
  change Tendsto (fun n => num n / den n) atTop (𝓝 L)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun n => (E n / den n - (1 - ρ n)) / ρ n) (h := fun n => (E n / den n) / ρ n)
    ?_ ?_ ?_ ?_
  · have h := (hv.sub ((tendsto_const_nhds (x := (1 : ℝ))).sub hρlim)).div hρlim one_ne_zero
    rw [sub_self, sub_zero, div_one] at h
    exact h
  · have h := hv.div hρlim one_ne_zero
    rw [div_one] at h
    exact h
  · filter_upwards [hkey, hρpos] with n h hρn
    rw [div_le_iff₀ hρn]
    linarith [h.2]
  · filter_upwards [hkey, hρpos] with n h hρn
    rw [le_div_iff₀ hρn]
    linarith [h.1]

end

end MathlibExt.InformationTheory.GibbsConditioningWanted
