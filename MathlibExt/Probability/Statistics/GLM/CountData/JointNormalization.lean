/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GLM.CountData.Model

/-!
# Count-matrix model: joint normalization and joint identifiability

The count-matrix model of `MathlibExt.Probability.Statistics.GLM.CountData.Model` (counts
`K_{g,j}` of genes `g` in samples `j`, independent across entries, with Poisson or negative
binomial law of mean `μ_{g,j} = s_j q_{g, condition j}`) is the observation model of DESeq2
(Love, Huber, Anders, *Moderated estimation of fold change and dispersion for RNA-seq data with
DESeq2*, Genome Biology 15 (2014) 550, Methods: `K_ij ~ NB(μ_ij, α_i)`, `μ_ij = s_j q_ij`) and
of edgeR (Robinson, McCarthy, Smyth, Bioinformatics 26 (2010) 139–140). Its likelihood
`CountModel.likelihood Y = ∏_g ∏_j P(K_{g,j} = Y g j)` was defined there as a product of entry
masses; this file proves that it is a probability mass function on count matrices and that the
law it defines identifies the parameters.

## Main results

* `CountModel.hasSum_likelihood`, `CountModel.tsum_likelihood`: **joint normalization**, the
  likelihood sums to `1` over all count matrices `Y : G → J → ℕ`.
* `CountModel.hasSum_likelihood_entry`, `CountModel.tsum_likelihood_entry`: the entry `(g, j)`
  of the joint law has the model's entry law `countPMF g j`.
* Joint identifiability, from the joint law of the whole count matrix:
  `CountModel.countPMF_eq_of_likelihood_eq` (entry laws), `CountModel.rate_eq_of_likelihood_eq`
  (rates, for a known nonzero library size), `CountModel.law_eq_of_likelihood_eq` (Poisson versus
  negative binomial and the shape, via the dispersion: `CountModel.law_eq_of_countPMF_eq`,
  `CountLaw.eq_of_dispersion_eq`); `CountModel.likelihood_eq_iff` (with known positive library
  sizes, equal joint laws if and only if equal laws and equal rates at every sample's condition)
  and `CountModel.eq_of_likelihood_eq` (with a known design in which every condition has a
  replicate, the parameters are identified).
* `CountModel.likelihood_rescale`: multiplying all library sizes by `t ≠ 0` and dividing all
  rates by `t` does not change the joint law, so library sizes are identified only up to a common
  scale and are taken as known in the identifiability results (DESeq fixes the scale by its
  median-of-ratios normalization of size factors).

A sample with library size `0` carries no information
(`CountModel.countPMF_eq_of_librarySize_eq_zero`), hence the nonzero library size hypotheses.

## Implementation notes

The finite-product summation lemma (`∑_x ∏_i f i (x i) = ∏_i ∑_k f i k` for nonnegative
summable families over a finite index type) is proved here by induction over the finite index
type, as Mathlib has only the finite-sum version `Finset.prod_univ_sum` and the two-factor
`HasSum.mul`.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.GLM.CountData

open Finset

universe u

/-- A finite product of nonnegative summable families is summable over the function space, with
sum the product of the sums. -/
private theorem hasSum_prod_pi {κ : Type*} :
    ∀ (ι : Type u) [Fintype ι] (f : ι → κ → ℝ) (a : ι → ℝ), (∀ i k, 0 ≤ f i k) →
      (∀ i, HasSum (f i) (a i)) → HasSum (fun x : ι → κ => ∏ i, f i (x i)) (∏ i, a i) := by
  refine Fintype.induction_empty_option ?_ ?_ ?_
  · intro α β _ e ih f a hf0 hf
    let _ : Fintype α := Fintype.ofEquiv β e.symm
    have h := ih (fun i => f (e i)) (fun i => a (e i)) (fun i k => hf0 _ k) (fun i => hf _)
    rw [← (e.arrowCongr (Equiv.refl κ)).symm.hasSum_iff] at h
    rw [← Fintype.prod_equiv e (fun i => a (e i)) a (fun _ => rfl)]
    refine h.congr_fun fun x => ?_
    change ∏ b, f b (x b) = ∏ i, f (e i) (x (e i))
    exact (Fintype.prod_equiv e _ _ fun _ => rfl).symm
  · intro f a _ _
    simp
  · intro α _ ih f a hf0 hf
    have hg := ih (fun i => f (some i)) (fun i => a (some i)) (fun i k => hf0 _ k)
      (fun i => hf _)
    have hn : ∀ i, Summable fun k => ‖f i k‖ := fun i =>
      (hf i).summable.congr fun k => (Real.norm_of_nonneg (hf0 i k)).symm
    have hgn : Summable fun y : α → κ => ‖∏ i, f (some i) (y i)‖ :=
      hg.summable.congr fun y =>
        (Real.norm_of_nonneg (prod_nonneg fun i _ => hf0 _ _)).symm
    have hs : Summable fun z : κ × (α → κ) => f none z.1 * ∏ i, f (some i) (z.2 i) :=
      summable_mul_of_summable_norm (f := f none) (g := fun y : α → κ => ∏ i, f (some i) (y i))
        (hn none) hgn
    have hmul := HasSum.mul (f := f none) (g := fun y : α → κ => ∏ i, f (some i) (y i))
      (hf none) hg hs
    rw [← (Equiv.piOptionEquivProd (β := fun _ : Option α => κ)).hasSum_iff] at hmul
    rw [Fintype.prod_option]
    refine hmul.congr_fun fun x => ?_
    simp [Fintype.prod_option]

/-- **Marginalization over one coordinate.** If every factor sums to `1`, restricting the
coordinate `i₀` to the event `p` sums to the mass of `p` under the factor `f i₀`. -/
private theorem hasSum_prod_pi_ite {ι : Type u} {κ : Type*} [Fintype ι] (f : ι → κ → ℝ)
    (hf0 : ∀ i k, 0 ≤ f i k) (hf : ∀ i, HasSum (f i) 1) (i₀ : ι) (p : κ → Prop)
    [DecidablePred p] {b : ℝ} (hb : HasSum (fun k => if p k then f i₀ k else 0) b) :
    HasSum (fun x : ι → κ => if p (x i₀) then ∏ i, f i (x i) else 0) b := by
  classical
  have h := hasSum_prod_pi ι (fun i k => if i = i₀ ∧ ¬p k then 0 else f i k)
    (fun i => if i = i₀ then b else 1)
    (fun i k => by split_ifs <;> simp [hf0])
    (fun i => by
      by_cases hi : i = i₀
      · subst hi
        simpa [ite_not] using hb
      · simpa [hi] using hf i)
  rw [Fintype.prod_ite_eq'] at h
  refine h.congr_fun fun x => ?_
  by_cases hp : p (x i₀)
  · rw [ite_eq_left hp]
    refine prod_congr rfl fun i _ => ?_
    by_cases hi : i = i₀
    · subst hi
      simp [hp]
    · simp [hi]
  · rw [ite_eq_right hp]
    exact (prod_eq_zero (mem_univ i₀) (by simp [hp])).symm

/-- A valid count law is determined by its dispersion: `0` only for Poisson, and `1 / θ`
determines the shape `θ > 0` of the negative binomial. -/
theorem CountLaw.eq_of_dispersion_eq {L L' : CountLaw} (hL : L.Valid) (hL' : L'.Valid)
    (h : L.dispersion = L'.dispersion) : L = L' := by
  cases L with
  | poisson =>
    cases L' with
    | poisson => rfl
    | negBinomial θ' =>
      have hθ' : 0 < θ' := hL'
      simp only [CountLaw.dispersion_poisson, CountLaw.dispersion_negBinomial] at h
      exact absurd h.symm (inv_pos.2 hθ').ne'
  | negBinomial θ =>
    cases L' with
    | poisson =>
      have hθ : 0 < θ := hL
      simp only [CountLaw.dispersion_poisson, CountLaw.dispersion_negBinomial] at h
      exact absurd h (inv_pos.2 hθ).ne'
    | negBinomial θ' =>
      simp only [CountLaw.dispersion_negBinomial, inv_inj] at h
      rw [h]

namespace CountModel

variable {G J C : Type*} {M M' : CountModel G J C}

/-- Entry masses are nonnegative on the parameter domain. -/
theorem countPMF_nonneg (hM : M.Valid) (g : G) (j : J) (k : ℕ) : 0 ≤ M.countPMF g j k :=
  CountLaw.pmf_nonneg (hM.law_valid g) (mean_nonneg hM g j) k

/-- The likelihood of the counts of one gene (a row of the count matrix) sums to `1`. -/
private theorem hasSum_row [Fintype J] (hM : M.Valid) (g : G) :
    HasSum (fun y : J → ℕ => ∏ j, M.countPMF g j (y j)) 1 := by
  simpa using hasSum_prod_pi J (fun j => M.countPMF g j) (fun _ => 1)
    (countPMF_nonneg hM g) (hasSum_countPMF hM g)

/-- **Joint normalization.** On the parameter domain, the likelihood of the count matrix (the
product of the entry masses over all genes and samples) sums to `1` over all count matrices
`Y : G → J → ℕ`: it is a probability mass function on count matrices. -/
theorem hasSum_likelihood [Fintype G] [Fintype J] (hM : M.Valid) : HasSum M.likelihood 1 := by
  have h := hasSum_prod_pi G (fun g (y : J → ℕ) => ∏ j, M.countPMF g j (y j)) (fun _ => 1)
    (fun g y => prod_nonneg fun j _ => countPMF_nonneg hM g j (y j)) (hasSum_row hM)
  rw [prod_const_one] at h
  exact h

/-- The likelihood is summable over count matrices. -/
theorem summable_likelihood [Fintype G] [Fintype J] (hM : M.Valid) : Summable M.likelihood :=
  (hasSum_likelihood hM).summable

/-- **Joint normalization**, `tsum` form: `∑_Y L(Y) = 1`. -/
theorem tsum_likelihood [Fintype G] [Fintype J] (hM : M.Valid) :
    ∑' Y : G → J → ℕ, M.likelihood Y = 1 :=
  (hasSum_likelihood hM).tsum_eq

/-- **Entry marginals of the joint law.** Summing the likelihood over the count matrices whose
entry `(g, j)` equals `k` gives the entry mass `countPMF g j k`: under the joint law the count of
gene `g` in sample `j` has the law `(law g).pmf (mean g j)` of the model. -/
theorem hasSum_likelihood_entry [Fintype G] [Fintype J] (hM : M.Valid) (g : G) (j : J)
    (k : ℕ) :
    HasSum (fun Y : G → J → ℕ => if Y g j = k then M.likelihood Y else 0)
      (M.countPMF g j k) := by
  have hb : HasSum (fun k' : ℕ => if k' = k then M.countPMF g j k' else 0)
      (M.countPMF g j k) := by
    convert hasSum_ite_eq k (M.countPMF g j k) using 1
    funext k'
    split_ifs with h
    · rw [h]
    · rfl
  have hrow := hasSum_prod_pi_ite (fun j' => M.countPMF g j') (countPMF_nonneg hM g)
    (hasSum_countPMF hM g) j (· = k) hb
  have h := hasSum_prod_pi_ite (fun g' (y : J → ℕ) => ∏ j', M.countPMF g' j' (y j'))
    (fun g' y => prod_nonneg fun j' _ => countPMF_nonneg hM g' j' (y j')) (hasSum_row hM) g
    (fun y => y j = k) hrow
  exact h

/-- **Entry marginals**, `tsum` form. -/
theorem tsum_likelihood_entry [Fintype G] [Fintype J] (hM : M.Valid) (g : G) (j : J) (k : ℕ) :
    ∑' Y : G → J → ℕ, (if Y g j = k then M.likelihood Y else 0) = M.countPMF g j k :=
  (hasSum_likelihood_entry hM g j k).tsum_eq

/-! ### Joint identifiability -/

/-- The joint law of the count matrix determines the law of every entry. -/
theorem countPMF_eq_of_likelihood_eq [Fintype G] [Fintype J] (hM : M.Valid) (hM' : M'.Valid)
    (h : M.likelihood = M'.likelihood) (g : G) (j : J) : M.countPMF g j = M'.countPMF g j := by
  funext k
  refine (hasSum_likelihood_entry hM g j k).unique ?_
  simpa [h] using hasSum_likelihood_entry hM' g j k

/-- **Rates are identified by the joint law.** If two valid models have the same likelihood on
count matrices and sample `j` has the same nonzero library size in both, then every gene has the
same rate in the condition of `j`. -/
theorem rate_eq_of_likelihood_eq [Fintype G] [Fintype J] (hM : M.Valid) (hM' : M'.Valid)
    (h : M.likelihood = M'.likelihood) (g : G) {j : J}
    (hs : M.librarySize j = M'.librarySize j) (hj : M.librarySize j ≠ 0) :
    M.rate g (M.condition j) = M'.rate g (M'.condition j) :=
  rate_eq_of_countPMF_eq hM hM' g hs hj (countPMF_eq_of_likelihood_eq hM hM' h g j)

/-- **The count law of an entry with positive mean determines the gene's law.** Its mean is
`mean g j` and its variance is `mean + α mean²`; for `mean > 0` this fixes the dispersion `α`,
and the dispersion fixes the law (`CountLaw.eq_of_dispersion_eq`). No knowledge of the library
sizes of the second model is needed. -/
theorem law_eq_of_countPMF_eq (hM : M.Valid) (hM' : M'.Valid) (g : G) {j : J}
    (hj : 0 < M.librarySize j) (h : M.countPMF g j = M'.countPMF g j) :
    M.law g = M'.law g := by
  have hmean : M.mean g j = M'.mean g j := by
    have h1 := hasSum_mul_countPMF hM g j
    rw [h] at h1
    exact h1.unique (hasSum_mul_countPMF hM' g j)
  have hvar := variance_countPMF hM g j
  rw [h, variance_countPMF hM' g j, ← hmean] at hvar
  have hm := mean_pos hM g hj
  have hα : (M.law g).dispersion * M.mean g j ^ 2 = (M'.law g).dispersion * M.mean g j ^ 2 := by
    linarith
  exact CountLaw.eq_of_dispersion_eq (hM.law_valid g) (hM'.law_valid g)
    (mul_right_cancel₀ (pow_ne_zero 2 hm.ne') hα)

/-- **Laws are identified by the joint law**: Poisson versus negative binomial, and the
negative binomial shape, from any sample with positive library size. -/
theorem law_eq_of_likelihood_eq [Fintype G] [Fintype J] (hM : M.Valid) (hM' : M'.Valid)
    (h : M.likelihood = M'.likelihood) (g : G) {j : J} (hj : 0 < M.librarySize j) :
    M.law g = M'.law g :=
  law_eq_of_countPMF_eq hM hM' g hj (countPMF_eq_of_likelihood_eq hM hM' h g j)

/-- **Joint identifiability.** For valid models with the same, positive library sizes and at
least one sample, the joint law of the count matrix determines the count law of every gene and the
rate of every gene in the condition of every sample, and conversely. -/
theorem likelihood_eq_iff [Fintype G] [Fintype J] [Nonempty J] (hM : M.Valid) (hM' : M'.Valid)
    (hs : M.librarySize = M'.librarySize) (hpos : ∀ j, 0 < M.librarySize j) :
    M.likelihood = M'.likelihood ↔
      M.law = M'.law ∧ ∀ g j, M.rate g (M.condition j) = M'.rate g (M'.condition j) := by
  constructor
  · intro h
    obtain ⟨j⟩ := ‹Nonempty J›
    exact ⟨funext fun g => law_eq_of_likelihood_eq hM hM' h g (hpos j),
      fun g j => rate_eq_of_likelihood_eq hM hM' h g (congrFun hs j) (hpos j).ne'⟩
  · rintro ⟨hlaw, hrate⟩
    funext Y
    simp only [likelihood, countPMF, mean, hlaw, hrate, hs]

/-- **Parameter identifiability with a known design.** If two valid models share the condition
map (every condition having a replicate) and the positive library sizes, and there is at least
one sample, equal joint laws force equal models: the parameters `(law, rate)` are identified. -/
theorem eq_of_likelihood_eq [Fintype G] [Fintype J] [Nonempty J] (hM : M.Valid)
    (hM' : M'.Valid) (hc : M.condition = M'.condition) (hsurj : Function.Surjective M.condition)
    (hs : M.librarySize = M'.librarySize) (hpos : ∀ j, 0 < M.librarySize j)
    (h : M.likelihood = M'.likelihood) : M = M' := by
  obtain ⟨hlaw, hrate⟩ := (likelihood_eq_iff hM hM' hs hpos).1 h
  have hrate' : M.rate = M'.rate := by
    funext g c
    obtain ⟨j, rfl⟩ := hsurj c
    rw [hrate g j, hc]
  cases M
  cases M'
  simp_all

/-! ### Library sizes are identified only up to scale -/

/-- The model with library sizes multiplied by `t` and rates divided by `t`. -/
noncomputable def rescale (M : CountModel G J C) (t : ℝ) : CountModel G J C where
  law := M.law
  condition := M.condition
  librarySize j := M.librarySize j * t
  rate g c := M.rate g c / t

/-- Rescaling by `t > 0` stays in the parameter domain. -/
theorem valid_rescale (hM : M.Valid) {t : ℝ} (ht : 0 < t) : (M.rescale t).Valid where
  law_valid := hM.law_valid
  librarySize_nonneg j := mul_nonneg (hM.librarySize_nonneg j) ht.le
  rate_pos g c := div_pos (hM.rate_pos g c) ht

/-- Rescaling by `t ≠ 0` leaves every entry mean unchanged. -/
theorem mean_rescale (M : CountModel G J C) {t : ℝ} (ht : t ≠ 0) (g : G) (j : J) :
    (M.rescale t).mean g j = M.mean g j := by
  simp only [mean, rescale]
  field_simp

/-- **Rescaling is invisible in the joint law.** Multiplying every library size by `t ≠ 0` and
dividing every rate by `t` leaves every entry mean, hence the likelihood, unchanged; this is why
`rate_eq_of_likelihood_eq` and `likelihood_eq_iff` take the library sizes as known. -/
theorem likelihood_rescale [Fintype G] [Fintype J] (M : CountModel G J C) {t : ℝ} (ht : t ≠ 0) :
    (M.rescale t).likelihood = M.likelihood := by
  funext Y
  simp only [likelihood, countPMF, mean_rescale M ht]
  rfl

end CountModel

end MathlibExt.Probability.Statistics.GLM.CountData
