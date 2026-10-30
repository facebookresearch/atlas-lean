/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.Tajima
public import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Independence.Integration
import Mathlib.Data.Nat.Choose.Cast

/-!
# Tajima's variance identities: `Var π`, `Cov(π, S)` and `Var(π - S / a₁)`

For a sample of `n ≥ 2` genes under Kingman's coalescent (time in units of `2N` generations)
with infinite-sites mutation at scaled rate `θ = 4Nu` (rate `θ / 2` per unit branch length),
let `D s` be the number of differences between the two sequences of the pair `s`, `π` their
mean over the `C(n, 2)` pairs (`meanPairDiff`) and `S` the number of segregating sites. Then

* `Var π = b₁ θ + b₂ θ²` with `b₁ = (n + 1) / (3 (n - 1))`, `b₂ = 2 (n² + n + 3) / (9 n (n - 1))`
  (Tajima 1983);
* `Cov(π, S) = θ + (n + 2) θ² / (2 n)`;
* hence `Var(π - S / a₁) = c₁ θ + c₂ θ²` with Tajima's (1989) constants `c₁`, `c₂`, the variance
  in the denominator of Tajima's `D`.

## Model assumptions

The mutation process enters through conditional moments given the genealogy σ-algebra `m`:
given the genealogy, mutations on disjoint pieces of the tree are independent Poisson counts
with mean `θ / 2` times the length. So, with `τ s` the coalescence time of the pair `s` (the
path between the two genes has length `2 τ s`) and `ℓ s t` the length shared by the paths of
the pairs `s` and `t`,

* `E[D s | m] = θ τ s` and `E[D s D t | m] = θ² τ s τ t + (θ / 2) ℓ s t`
  (conditional covariance `(θ / 2) ℓ s t`);
* `E[D s S | m] = (θ² / 2) τ s L + θ τ s`, where `L` is the total branch length: the path of a
  pair lies in the tree, so the conditional covariance is `(θ / 2) · 2 τ s`;
* `E[S | m] = Var[S | m] = (θ / 2) L` (as in `Coalescent/Tajima.lean`).

The genealogy enters through the following properties of Kingman's coalescent, which are
**hypotheses here** (they are not derived from `KingmanTimes` and the random-joining law of
`Coalescent/Topology.lean`, which are not coupled in the library):

* each `τ s` is exponential with rate `1`, so `E τ s = 1`, `E (τ s)² = 2`;
* `E[τ s τ t] = 4/3` if the pairs share one gene and `11/9` if they are disjoint (the
  coalescent of three, resp. four, genes);
* the shared lengths: `ℓ s s = 2 τ s`; for pairs `{i, j}`, `{i, k}` sharing one gene,
  `ℓ = τ_{ij} + τ_{ik} - τ_{jk}` (the distance from `i` to the path from `j` to `k`; here
  `{j, k}` is the symmetric difference of the pairs); for disjoint pairs `E ℓ = 2/3`;
* `E[τ s L] = 2 a₁ + (n + 2) / n`. `integral_pairTime_mul_totalLength` derives this from the
  representation `τ s = ∑_k 1[s separate while k lineages] T k` with the classical
  probability `(k - 1) (n + 1) / ((n - 1) (k + 1))` that a given pair is still separate when
  there are `k` lineages, under independence of topology and holding times.

The constants `4/3`, `11/9`, `2/3` follow by conditioning on the ranked topology of three or
four genes (equally likely ranked histories, independent holding times `Exp(C(k, 2))`).
Integrability of the products is part of the hypotheses: each `D s` and `S` is square
integrable, and an integral hypothesis with a nonzero value forces integrability (Mathlib's
integral of a non-integrable function is `0`). The identities hold for every real `θ`
(biologically `θ > 0`).

## Main results

* `sum_samplePairs_card_inter`: among the `C(n, 2)` pairs, `1` equals a given pair, `2 (n - 2)`
  share one gene with it and `C(n - 2, 2)` are disjoint from it.
* `variance_meanPairDiff`: `Var π = b₁ θ + b₂ θ²` (Tajima 1983).
* `KingmanTimes.covariance_meanPairDiff_segSites`: `Cov(π, S) = θ + (n + 2) θ² / (2 n)`.
* `KingmanTimes.variance_tajimaNumerator`: `Var(π - S / a₁) = c₁ θ + c₂ θ²` (Tajima 1989).
* `KingmanTimes.integral_pairTime_mul_totalLength`: `E[τ s L] = 2 a₁ + (n + 2) / n`.

## References

* F. Tajima, *Evolutionary relationship of DNA sequences in finite populations*, Genetics 105
  (1983), 437–460.
* F. Tajima, *Statistical method for testing the neutral mutation hypothesis by DNA
  polymorphism*, Genetics 123 (1989), 585–595.
* J. Wakeley, *Coalescent Theory: An Introduction* (2009), ch. 4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

noncomputable section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent

/-! ### Counting pairs by overlap -/

/-- A sample pair has two elements. -/
private theorem pair_card {n : ℕ} {s : Finset (Fin n)} (hs : s ∈ samplePairs n) :
    #s = 2 := (mem_powersetCard.mp hs).2

/-- Two sample pairs meet in two genes exactly when they are equal. -/
private theorem pair_inter_eq_two {n : ℕ} {s t : Finset (Fin n)}
    (hs : s ∈ samplePairs n) (ht : t ∈ samplePairs n) : #(s ∩ t) = 2 ↔ t = s := by
  constructor
  · intro h
    have hst : s ∩ t = s :=
      eq_of_subset_of_card_le inter_subset_left (by rw [pair_card hs, h])
    have hsub : s ⊆ t := hst ▸ inter_subset_right
    exact (eq_of_subset_of_card_le hsub (by rw [pair_card hs, pair_card ht])).symm
  · rintro rfl
    simpa using pair_card hs

/-- Two sample pairs sharing one gene have a pair as symmetric difference. -/
private theorem pair_symmDiff {n : ℕ} {s t : Finset (Fin n)}
    (hs : s ∈ samplePairs n) (ht : t ∈ samplePairs n) (h : #(s ∩ t) = 1) :
    symmDiff s t ∈ samplePairs n := by
  apply mem_powersetCard.mpr
  refine ⟨subset_univ _, ?_⟩
  rw [symmDiff_def, sup_eq_union, card_union_of_disjoint disjoint_sdiff_sdiff,
    card_sdiff, card_sdiff]
  rw [inter_comm t s, h, pair_card hs, pair_card ht]

/-- Among the pairs of a sample of size `n`, one equals a given pair `s`, `2 (n - 2)` share
exactly one gene with it and `C(n - 2, 2)` are disjoint from it. -/
theorem sum_samplePairs_card_inter {n : ℕ} {s : Finset (Fin n)} (hs : s ∈ samplePairs n)
    (f : ℕ → ℝ) :
    ∑ t ∈ samplePairs n, f #(s ∩ t) =
      f 2 + 2 * ((n - 2 : ℕ) : ℝ) * f 1 + (((n - 2).choose 2 : ℕ) : ℝ) * f 0 := by
  classical
  have hsc := pair_card hs
  have hn : 2 ≤ n := by
    simpa [hsc] using card_le_card (subset_univ s)
  let A := (samplePairs n).filter (fun t => #(s ∩ t) = 2)
  let B := (samplePairs n).filter (fun t => #(s ∩ t) = 1)
  let C := (samplePairs n).filter (fun t => #(s ∩ t) = 0)
  have hA : A = {s} := by
    ext t
    simp only [A, mem_filter, mem_singleton]
    constructor
    · rintro ⟨ht, h⟩
      exact (pair_inter_eq_two hs ht).mp h
    · rintro rfl
      exact ⟨hs, by simpa using hsc⟩
  have hC : C = ((univ : Finset (Fin n)) \ s).powersetCard 2 := by
    ext t
    simp only [C, mem_filter, mem_powersetCard, card_eq_zero, ← disjoint_iff_inter_eq_empty]
    constructor
    · rintro ⟨⟨hu, hc⟩, hd⟩
      exact ⟨subset_sdiff.mpr ⟨hu, hd.symm⟩, hc⟩
    · rintro ⟨hu, hc⟩
      exact ⟨⟨subset_univ _, hc⟩, (subset_sdiff.mp hu).2.symm⟩
  have hCc : #C = (n - 2).choose 2 := by
    rw [hC, card_powersetCard, card_sdiff_of_subset (subset_univ s)]
    simp [hsc]
  have split (g : ℕ → ℝ) :
      ∑ t ∈ samplePairs n, g #(s ∩ t) = (#A : ℝ) * g 2 + (#B : ℝ) * g 1 +
        (#C : ℝ) * g 0 := by
    have hpoint : ∀ t ∈ samplePairs n,
        g #(s ∩ t) = (if #(s ∩ t) = 2 then g 2 else 0) +
          (if #(s ∩ t) = 1 then g 1 else 0) +
          (if #(s ∩ t) = 0 then g 0 else 0) := by
      intro t ht
      have hle : #(s ∩ t) ≤ 2 := hsc ▸ card_le_card inter_subset_left
      have hh : #(s ∩ t) = 0 ∨ #(s ∩ t) = 1 ∨ #(s ∩ t) = 2 := by omega
      rcases hh with hh | hh | hh <;> simp [hh]
    rw [sum_congr rfl hpoint, sum_add_distrib, sum_add_distrib]
    simp only [← sum_filter, sum_const, nsmul_eq_mul, A, B, C]
  have htotal : (#A : ℝ) + (#B : ℝ) + (#C : ℝ) = (n.choose 2 : ℝ) := by
    simpa [card_powersetCard] using (split (fun _ => 1)).symm
  have hBc : (#B : ℝ) = 2 * ((n - 2 : ℕ) : ℝ) := by
    rw [hA, card_singleton, hCc] at htotal
    have hn2 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
      exact Nat.cast_sub hn
    rw [Nat.cast_choose_two, Nat.cast_choose_two, hn2] at htotal
    rw [hn2]
    nlinarith
  rw [split, hA, card_singleton, hBc, hCc]
  simp

/-! ### Variance of the mean number of pairwise differences -/

section Pairwise

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : ℕ}

/-- The variance of `π` from the moments of the pair coalescence times (proof of
`variance_meanPairDiff`). -/
private theorem variance_meanPairDiff_aux [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {D τ : Finset (Fin n) → Ω → ℝ} {ℓ : Finset (Fin n) → Finset (Fin n) → Ω → ℝ}
    {θ : ℝ} (hn : 2 ≤ n)
    (hτm : ∀ s ∈ samplePairs n, MemLp (τ s) 2 μ)
    (hτi : ∀ s ∈ samplePairs n, μ[τ s] = 1)
    (hτ₂ : ∀ s ∈ samplePairs n, μ[fun ω => τ s ω * τ s ω] = 2)
    (hτ₁ : ∀ s ∈ samplePairs n, ∀ t ∈ samplePairs n, #(s ∩ t) = 1 →
      μ[fun ω => τ s ω * τ t ω] = 4 / 3)
    (hτ₀ : ∀ s ∈ samplePairs n, ∀ t ∈ samplePairs n, Disjoint s t →
      μ[fun ω => τ s ω * τ t ω] = 11 / 9)
    (hℓ₂ : ∀ s ∈ samplePairs n, ℓ s s =ᵐ[μ] fun ω => 2 * τ s ω)
    (hℓ₁ : ∀ s ∈ samplePairs n, ∀ t ∈ samplePairs n, #(s ∩ t) = 1 →
      ℓ s t =ᵐ[μ] fun ω => τ s ω + τ t ω - τ (symmDiff s t) ω)
    (hℓ₀ : ∀ s ∈ samplePairs n, ∀ t ∈ samplePairs n, Disjoint s t → μ[ℓ s t] = 2 / 3)
    (hD2 : ∀ s ∈ samplePairs n, MemLp (D s) 2 μ)
    (hD : ∀ s ∈ samplePairs n, μ[D s | m] =ᵐ[μ] fun ω => θ * τ s ω)
    (hDD : ∀ s ∈ samplePairs n, ∀ t ∈ samplePairs n,
      μ[fun ω => D s ω * D t ω | m] =ᵐ[μ]
        fun ω => θ ^ 2 * (τ s ω * τ t ω) + θ / 2 * ℓ s t ω) :
    Var[meanPairDiff n D; μ] = tajimaB1 n * θ + tajimaB2 n * θ ^ 2 := by
  classical
  have hτint : ∀ s ∈ samplePairs n, Integrable (τ s) μ :=
    fun s hs => (hτm s hs).integrable one_le_two
  have hDint : ∀ s ∈ samplePairs n, Integrable (D s) μ :=
    fun s hs => (hD2 s hs).integrable one_le_two
  have hprod : ∀ s ∈ samplePairs n, ∀ t ∈ samplePairs n,
      Integrable (fun ω => D s ω * D t ω) μ :=
    fun s hs t ht => (hD2 s hs).integrable_mul (hD2 t ht)
  have hτprod : ∀ s ∈ samplePairs n, ∀ t ∈ samplePairs n,
      Integrable (fun ω => τ s ω * τ t ω) μ :=
    fun s hs t ht => (hτm s hs).integrable_mul (hτm t ht)
  have hDi : ∀ s ∈ samplePairs n, μ[D s] = θ := by
    intro s hs
    calc
      μ[D s] = μ[μ[D s | m]] := (integral_condExp hm).symm
      _ = μ[fun ω => θ * τ s ω] := by
        apply integral_congr_ae
        exact hD s hs
      _ = θ := by rw [integral_const_mul, hτi s hs, mul_one]
  have hCcard : #(samplePairs n) = n.choose 2 := by simp
  have hCn : (n.choose 2 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hn).ne'
  have hπm : MemLp (meanPairDiff n D) 2 μ :=
    (memLp_finsetSum (samplePairs n) hD2).const_mul _
  have hπi : μ[meanPairDiff n D] = θ := by
    change μ[fun ω => (n.choose 2 : ℝ)⁻¹ * ∑ s ∈ samplePairs n, D s ω] = θ
    rw [integral_const_mul, integral_finsetSum _ hDint]
    rw [sum_congr rfl hDi, sum_const, nsmul_eq_mul, hCcard]
    field_simp [hCn]
  have hformula : ∀ s ∈ samplePairs n, ∀ t ∈ samplePairs n,
      Integrable (ℓ s t) μ → μ[fun ω => D s ω * D t ω] =
        θ ^ 2 * μ[fun ω => τ s ω * τ t ω] + θ / 2 * μ[ℓ s t] := by
    intro s hs t ht hLint
    calc
      μ[fun ω => D s ω * D t ω] = μ[μ[fun ω => D s ω * D t ω | m]] :=
        (integral_condExp hm).symm
      _ = μ[fun ω => θ ^ 2 * (τ s ω * τ t ω) + θ / 2 * ℓ s t ω] := by
        apply integral_congr_ae
        exact hDD s hs t ht
      _ = _ := by
        rw [integral_add ((hτprod s hs t ht).const_mul _) (hLint.const_mul _)]
        rw [integral_const_mul, integral_const_mul]
  let g : ℕ → ℝ := fun k =>
    if k = 2 then 2 * θ ^ 2 + θ else
      if k = 1 then (4 / 3) * θ ^ 2 + θ / 2 else (11 / 9) * θ ^ 2 + θ / 3
  have hmoment : ∀ s ∈ samplePairs n, ∀ t ∈ samplePairs n,
      μ[fun ω => D s ω * D t ω] = g #(s ∩ t) := by
    intro s hs t ht
    by_cases htwo : #(s ∩ t) = 2
    · have heq := (pair_inter_eq_two hs ht).mp htwo
      subst t
      have hLint : Integrable (ℓ s s) μ :=
        ((hτint s hs).const_mul 2).congr (hℓ₂ s hs).symm
      have hLi : μ[ℓ s s] = 2 := by
        rw [integral_congr_ae (hℓ₂ s hs), integral_const_mul, hτi s hs, mul_one]
      rw [hformula s hs s hs hLint, hτ₂ s hs, hLi]
      simp [g, pair_card hs]
      ring
    · by_cases hone : #(s ∩ t) = 1
      · have hsd := pair_symmDiff hs ht hone
        have hLint : Integrable (ℓ s t) μ :=
          (((hτint s hs).add (hτint t ht)).sub (hτint _ hsd)).congr
            (hℓ₁ s hs t ht hone).symm
        have hLi : μ[ℓ s t] = 1 := by
          rw [integral_congr_ae (hℓ₁ s hs t ht hone)]
          rw [integral_sub (show Integrable (fun ω => τ s ω + τ t ω) μ from
            (hτint s hs).add (hτint t ht)) (hτint _ hsd)]
          rw [integral_add (hτint s hs) (hτint t ht)]
          rw [hτi s hs, hτi t ht, hτi _ hsd]
          norm_num
        rw [hformula s hs t ht hLint, hτ₁ s hs t ht hone, hLi]
        simp [g, hone]
        ring
      · have hle : #(s ∩ t) ≤ 2 := (pair_card hs) ▸ card_le_card inter_subset_left
        have hzero : #(s ∩ t) = 0 := by omega
        have hd : Disjoint s t := disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp hzero)
        have hLint : Integrable (ℓ s t) μ :=
          Integrable.of_integral_ne_zero (by rw [hℓ₀ s hs t ht hd]; norm_num)
        rw [hformula s hs t ht hLint, hτ₀ s hs t ht hd, hℓ₀ s hs t ht hd]
        simp [g, hzero]
        ring
  have hπsquare : μ[(meanPairDiff n D) ^ 2] = (n.choose 2 : ℝ)⁻¹ ^ 2 *
      ∑ s ∈ samplePairs n, ∑ t ∈ samplePairs n, μ[fun ω => D s ω * D t ω] := by
    have hpoint : (meanPairDiff n D) ^ 2 = fun ω => (n.choose 2 : ℝ)⁻¹ ^ 2 *
        ∑ s ∈ samplePairs n, ∑ t ∈ samplePairs n, D s ω * D t ω := by
      funext ω
      change ((n.choose 2 : ℝ)⁻¹ * ∑ s ∈ samplePairs n, D s ω) ^ 2 = _
      rw [mul_pow, pow_two (∑ s ∈ samplePairs n, D s ω), sum_mul_sum]
    rw [hpoint, integral_const_mul]
    congr 1
    rw [integral_finsetSum _ (fun s hs =>
      integrable_finsetSum _ (fun t ht => hprod s hs t ht))]
    apply sum_congr rfl
    intro s hs
    exact integral_finsetSum _ (fun t ht => hprod s hs t ht)
  have hsum : (∑ s ∈ samplePairs n, ∑ t ∈ samplePairs n,
      μ[fun ω => D s ω * D t ω]) = (n.choose 2 : ℝ) *
        (g 2 + 2 * ((n - 2 : ℕ) : ℝ) * g 1 + ((n - 2).choose 2 : ℝ) * g 0) := by
    calc
      _ = ∑ s ∈ samplePairs n,
          (g 2 + 2 * ((n - 2 : ℕ) : ℝ) * g 1 + ((n - 2).choose 2 : ℝ) * g 0) := by
        apply sum_congr rfl
        intro s hs
        rw [sum_congr rfl (fun t ht => hmoment s hs t ht)]
        exact sum_samplePairs_card_inter hs g
      _ = _ := by rw [sum_const, nsmul_eq_mul, hCcard]
  rw [variance_eq_sub hπm, hπi, hπsquare, hsum]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn2 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := Nat.cast_sub hn
  simp only [inv_pow, ↓reduceIte, OfNat.one_ne_ofNat, OfNat.zero_ne_ofNat, zero_ne_one, g]
  rw [Nat.cast_choose_two, Nat.cast_choose_two, hn2]
  unfold tajimaB1 tajimaB2
  field_simp [hn0, hn1]
  ring

/-- A random variable with law `Exp(1)` is square integrable, with mean `1` and second
moment `2`. -/
private theorem expOne_moments [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : HasLaw X (expMeasure 1) μ) :
    MemLp X 2 μ ∧ μ[X] = 1 ∧ μ[fun ω => X ω * X ω] = 2 := by
  have hm : MemLp X 2 μ := hX.memLp_comp (f := id)
    ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
      (by simpa using integrable_pow_expMeasure one_pos 2))
  have h1 : μ[X] = 1 := by rw [hX.integral_eq_inv_of_expMeasure one_pos, inv_one]
  refine ⟨hm, h1, ?_⟩
  have hv := variance_eq_sub hm
  rw [hX.variance_eq_of_expMeasure one_pos, h1] at hv
  have hsq : (fun ω => X ω * X ω) = X ^ 2 := by
    funext ω
    simp [sq]
  rw [hsq]
  linarith

/-- **Variance of the mean number of pairwise differences** (Tajima 1983):
`Var π = b₁ θ + b₂ θ²` for a sample of size `n ≥ 2`, under the conditional-moment model of the
module docstring: `τ s ~ Exp(1)`, `E[τ s τ t] = 4/3` (one shared gene), `11/9` (disjoint
pairs); the shared path lengths `ℓ`; `E[D s | m] = θ τ s` and
`E[D s D t | m] = θ² τ s τ t + (θ / 2) ℓ s t`. -/
theorem variance_meanPairDiff [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {D τ : Finset (Fin n) → Ω → ℝ} {ℓ : Finset (Fin n) → Finset (Fin n) → Ω → ℝ} {θ : ℝ}
    (hn : 2 ≤ n)
    (hτ : ∀ s ∈ samplePairs n, HasLaw (τ s) (expMeasure 1) μ)
    (hτ₁ : ∀ s ∈ samplePairs n, ∀ t ∈ samplePairs n, #(s ∩ t) = 1 →
      μ[fun ω => τ s ω * τ t ω] = 4 / 3)
    (hτ₀ : ∀ s ∈ samplePairs n, ∀ t ∈ samplePairs n, Disjoint s t →
      μ[fun ω => τ s ω * τ t ω] = 11 / 9)
    (hℓ₂ : ∀ s ∈ samplePairs n, ℓ s s =ᵐ[μ] fun ω => 2 * τ s ω)
    (hℓ₁ : ∀ s ∈ samplePairs n, ∀ t ∈ samplePairs n, #(s ∩ t) = 1 →
      ℓ s t =ᵐ[μ] fun ω => τ s ω + τ t ω - τ (symmDiff s t) ω)
    (hℓ₀ : ∀ s ∈ samplePairs n, ∀ t ∈ samplePairs n, Disjoint s t → μ[ℓ s t] = 2 / 3)
    (hD2 : ∀ s ∈ samplePairs n, MemLp (D s) 2 μ)
    (hD : ∀ s ∈ samplePairs n, μ[D s | m] =ᵐ[μ] fun ω => θ * τ s ω)
    (hDD : ∀ s ∈ samplePairs n, ∀ t ∈ samplePairs n,
      μ[fun ω => D s ω * D t ω | m] =ᵐ[μ]
        fun ω => θ ^ 2 * (τ s ω * τ t ω) + θ / 2 * ℓ s t ω) :
    Var[meanPairDiff n D; μ] = tajimaB1 n * θ + tajimaB2 n * θ ^ 2 :=
  variance_meanPairDiff_aux hm hn (fun s hs => (expOne_moments (hτ s hs)).1)
    (fun s hs => (expOne_moments (hτ s hs)).2.1) (fun s hs => (expOne_moments (hτ s hs)).2.2)
    hτ₁ hτ₀ hℓ₂ hℓ₁ hℓ₀ hD2 hD hDD

end Pairwise

/-! ### Covariance of `π` and `S` -/

/-- The covariance of `π` and `S` from the moments of the genealogy (proof of
`KingmanTimes.covariance_meanPairDiff_segSites`); `L` is the total branch length. -/
private theorem covariance_meanPairDiff_segSites_aux {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {n : ℕ} [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {S L : Ω → ℝ} {D τ : Finset (Fin n) → Ω → ℝ} {θ : ℝ} (hn : 2 ≤ n)
    (hL : Integrable L μ) (hLi : μ[L] = 2 * tajimaA1 n)
    (hS2 : MemLp S 2 μ) (hS : μ[S | m] =ᵐ[μ] fun ω => θ / 2 * L ω)
    (hτm : ∀ s ∈ samplePairs n, MemLp (τ s) 2 μ)
    (hτi : ∀ s ∈ samplePairs n, μ[τ s] = 1)
    (hτL : ∀ s ∈ samplePairs n,
      μ[fun ω => τ s ω * L ω] = 2 * tajimaA1 n + ((n : ℝ) + 2) / n)
    (hD2 : ∀ s ∈ samplePairs n, MemLp (D s) 2 μ)
    (hD : ∀ s ∈ samplePairs n, μ[D s | m] =ᵐ[μ] fun ω => θ * τ s ω)
    (hDS : ∀ s ∈ samplePairs n, μ[fun ω => D s ω * S ω | m] =ᵐ[μ]
      fun ω => θ ^ 2 / 2 * (τ s ω * L ω) + θ * τ s ω) :
    cov[meanPairDiff n D, S; μ] = θ + ((n : ℝ) + 2) / (2 * n) * θ ^ 2 := by
  classical
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  have hchoose : (n.choose 2 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hn).ne'
  have hcard : (samplePairs n).card = n.choose 2 := by
    simp [samplePairs]
  have ha : 0 ≤ tajimaA1 n := by
    exact sum_nonneg fun i _ => inv_nonneg.mpr (Nat.cast_nonneg i)
  have hτLi : ∀ s ∈ samplePairs n, Integrable (fun ω => τ s ω * L ω) μ := by
    intro s hs
    apply Integrable.of_integral_ne_zero
    rw [hτL s hs]
    exact ne_of_gt (add_pos_of_nonneg_of_pos (mul_nonneg (by norm_num) ha)
      (div_pos (by positivity) hnpos))
  have hDi : ∀ s ∈ samplePairs n, μ[D s] = θ := by
    intro s hs
    calc
      μ[D s] = μ[μ[D s | m]] := (integral_condExp (f := D s) hm).symm
      _ = μ[fun ω => θ * τ s ω] := by
        apply integral_congr_ae
        exact hD s hs
      _ = θ := by rw [integral_const_mul, hτi s hs, mul_one]
  have hSi : μ[S] = θ * tajimaA1 n := by
    calc
      μ[S] = μ[μ[S | m]] := (integral_condExp (f := S) hm).symm
      _ = μ[fun ω => θ / 2 * L ω] := by
        apply integral_congr_ae
        exact hS
      _ = θ / 2 * μ[L] := hL.integral_smul (θ / 2)
      _ = θ * tajimaA1 n := by rw [hLi]; ring
  have hDSi : ∀ s ∈ samplePairs n,
      μ[fun ω => D s ω * S ω] =
        θ ^ 2 / 2 * (2 * tajimaA1 n + ((n : ℝ) + 2) / n) + θ := by
    intro s hs
    calc
      μ[fun ω => D s ω * S ω] = μ[μ[fun ω => D s ω * S ω | m]] :=
        (integral_condExp (f := fun ω => D s ω * S ω) hm).symm
      _ = μ[fun ω => θ ^ 2 / 2 * (τ s ω * L ω) + θ * τ s ω] := by
        apply integral_congr_ae
        exact hDS s hs
      _ = θ ^ 2 / 2 * (2 * tajimaA1 n + ((n : ℝ) + 2) / n) + θ := by
        rw [integral_add ((hτLi s hs).const_mul _)
            (((hτm s hs).integrable (by norm_num)).const_mul _),
          integral_const_mul, integral_const_mul, hτL s hs, hτi s hs, mul_one]
  have hπ2 : MemLp (meanPairDiff n D) 2 μ :=
    (memLp_finsetSum (samplePairs n) hD2).const_mul _
  have hπi : μ[meanPairDiff n D] = θ := by
    unfold meanPairDiff
    rw [integral_const_mul,
      integral_finsetSum _ (fun s hs => (hD2 s hs).integrable (by norm_num)),
      sum_congr rfl hDi]
    simp [hcard, hchoose]
  have hπSi : μ[fun ω => meanPairDiff n D ω * S ω] =
      θ ^ 2 / 2 * (2 * tajimaA1 n + ((n : ℝ) + 2) / n) + θ := by
    simp_rw [meanPairDiff, mul_assoc, sum_mul]
    rw [integral_const_mul,
      integral_finsetSum (f := fun s ω => D s ω * S ω) _
        (fun s hs => (hD2 s hs).integrable_mul hS2),
      sum_congr rfl hDSi]
    simp only [sum_const, nsmul_eq_mul, hcard]
    rw [← mul_assoc, inv_mul_cancel₀ hchoose, one_mul]
  rw [covariance_eq_sub hπ2 hS2]
  change μ[fun ω => meanPairDiff n D ω * S ω] - μ[meanPairDiff n D] * μ[S] = _
  rw [hπSi, hπi, hSi]
  field_simp
  ring

/-- The mean number of pairwise differences is square integrable when each `D s` is. -/
private theorem memLp_meanPairDiff {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {n : ℕ} {D : Finset (Fin n) → Ω → ℝ} (hD2 : ∀ s ∈ samplePairs n, MemLp (D s) 2 μ) :
    MemLp (meanPairDiff n D) 2 μ :=
  (memLp_finsetSum (samplePairs n) hD2).const_mul _

/-! ### The probability that a pair is still separate -/

/-- The probability `(k - 1) (n + 1) / ((n - 1) (k + 1))` that a given pair of a sample of
size `n` is still in two distinct lineages while the genealogy has `k` lineages
(`2 ≤ k ≤ n`, `n ≥ 2`; at `n = 1` the definition divides by zero and returns `0`). -/
def pairSeparateProb (n k : ℕ) : ℝ :=
  ((k : ℝ) - 1) * ((n : ℝ) + 1) / (((n : ℝ) - 1) * ((k : ℝ) + 1))

/-- `∑_{k=2}^n 1 / (k (k + 1)) = 1/2 - 1/(n + 1)`. -/
private theorem sum_recip_mul_succ (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ Icc 2 n, 1 / ((k : ℝ) * ((k : ℝ) + 1)) =
      1 / 2 - 1 / ((n : ℝ) + 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [sum_Icc_succ_top (Nat.le_trans hn (Nat.le_succ n)), ih]
    norm_num only [Nat.cast_add, Nat.cast_one]
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
    field_simp [h1, h2]
    ring

/-- `∑_{k=2}^n 1 / ((k - 1) k (k + 1)) = 1/4 - 1/(2 n (n + 1))`. -/
private theorem sum_recip_pred_mul_succ (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ Icc 2 n, 1 / (((k : ℝ) - 1) * (k : ℝ) * ((k : ℝ) + 1)) =
      1 / 4 - 1 / (2 * (n : ℝ) * ((n : ℝ) + 1)) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [sum_Icc_succ_top (Nat.le_trans hn (Nat.le_succ n)), ih]
    norm_num only [Nat.cast_add, Nat.cast_one]
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have h0 : (n : ℝ) ≠ 0 := by linarith
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
    field_simp [h0, h1, h2]
    ring

/-- `∑_{k=2}^n p_k / C(k, 2) = 1`: the mean coalescence time of a pair is `1`. -/
theorem sum_pairSeparateProb_div_choose {n : ℕ} (hn : 2 ≤ n) :
    ∑ k ∈ Icc 2 n, pairSeparateProb n k * ((k.choose 2 : ℕ) : ℝ)⁻¹ = 1 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn2 : (n : ℝ) + 1 ≠ 0 := by positivity
  calc
    _ = ∑ k ∈ Icc 2 n,
        (2 * ((n : ℝ) + 1) / ((n : ℝ) - 1)) *
          (1 / ((k : ℝ) * ((k : ℝ) + 1))) := by
      apply sum_congr rfl
      intro k hk
      have hk' : (2 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
      have hk0 : (k : ℝ) ≠ 0 := by linarith
      have hk1 : (k : ℝ) - 1 ≠ 0 := by linarith
      have hk2 : (k : ℝ) + 1 ≠ 0 := by positivity
      rw [pairSeparateProb, Nat.cast_choose_two]
      field_simp [hn1, hk0, hk1, hk2]
    _ = (2 * ((n : ℝ) + 1) / ((n : ℝ) - 1)) *
        (1 / 2 - 1 / ((n : ℝ) + 1)) := by
      rw [← mul_sum, sum_recip_mul_succ n hn]
    _ = 1 := by
      field_simp [hn1, hn2]
      ring

/-- `∑_{k=2}^n k p_k / C(k, 2)² = (n + 2) / n`. -/
theorem sum_mul_pairSeparateProb_div_choose_sq {n : ℕ} (hn : 2 ≤ n) :
    ∑ k ∈ Icc 2 n, (k : ℝ) * pairSeparateProb n k * (((k.choose 2 : ℕ) : ℝ)⁻¹) ^ 2 =
      ((n : ℝ) + 2) / n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn2 : (n : ℝ) + 1 ≠ 0 := by positivity
  calc
    _ = ∑ k ∈ Icc 2 n,
        (4 * ((n : ℝ) + 1) / ((n : ℝ) - 1)) *
          (1 / (((k : ℝ) - 1) * (k : ℝ) * ((k : ℝ) + 1))) := by
      apply sum_congr rfl
      intro k hk
      have hk' : (2 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
      have hk0 : (k : ℝ) ≠ 0 := by linarith
      have hk1 : (k : ℝ) - 1 ≠ 0 := by linarith
      have hk2 : (k : ℝ) + 1 ≠ 0 := by positivity
      rw [pairSeparateProb, Nat.cast_choose_two]
      field_simp [hn1, hk0, hk1, hk2]
      ring
    _ = (4 * ((n : ℝ) + 1) / ((n : ℝ) - 1)) *
        (1 / 4 - 1 / (2 * (n : ℝ) * ((n : ℝ) + 1))) := by
      rw [← mul_sum, sum_recip_pred_mul_succ n hn]
    _ = ((n : ℝ) + 2) / n := by
      field_simp [hn0, hn1, hn2]
      ring

/-! ### Tajima's variance identity -/

namespace KingmanTimes

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : ℕ} (K : KingmanTimes μ n)

/-- **Covariance of `π` and `S`**: `Cov(π, S) = θ + (n + 2) θ² / (2 n)` for `n ≥ 2`, if
`τ s ~ Exp(1)`, `E[τ s L] = 2 a₁ + (n + 2) / n` (`L` the total branch length),
`E[D s | m] = θ τ s`, `E[S | m] = (θ / 2) L` and `E[D s S | m] = (θ² / 2) τ s L + θ τ s` (the
path of each pair lies in the tree). This is the covariance behind Tajima's (1989) `c₁, c₂`. -/
theorem covariance_meanPairDiff_segSites [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {S : Ω → ℝ} {D τ : Finset (Fin n) → Ω → ℝ} {θ : ℝ} (hn : 2 ≤ n)
    (hS2 : MemLp S 2 μ) (hS : μ[S | m] =ᵐ[μ] fun ω => θ / 2 * K.totalLength ω)
    (hτ : ∀ s ∈ samplePairs n, HasLaw (τ s) (expMeasure 1) μ)
    (hτL : ∀ s ∈ samplePairs n,
      μ[fun ω => τ s ω * K.totalLength ω] = 2 * tajimaA1 n + ((n : ℝ) + 2) / n)
    (hD2 : ∀ s ∈ samplePairs n, MemLp (D s) 2 μ)
    (hD : ∀ s ∈ samplePairs n, μ[D s | m] =ᵐ[μ] fun ω => θ * τ s ω)
    (hDS : ∀ s ∈ samplePairs n, μ[fun ω => D s ω * S ω | m] =ᵐ[μ]
      fun ω => θ ^ 2 / 2 * (τ s ω * K.totalLength ω) + θ * τ s ω) :
    cov[meanPairDiff n D, S; μ] = θ + ((n : ℝ) + 2) / (2 * n) * θ ^ 2 :=
  covariance_meanPairDiff_segSites_aux hm hn K.integrable_totalLength
    (by rw [K.integral_totalLength, tajimaA1_eq_harmonic]) hS2 hS
    (fun s hs => (expOne_moments (hτ s hs)).1) (fun s hs => (expOne_moments (hτ s hs)).2.1)
    hτL hD2 hD hDS

/-- **Tajima's variance identity** (Tajima 1989): `Var(π - S / a₁) = c₁ θ + c₂ θ²` for a
sample of size `n ≥ 2`, under the hypotheses of `variance_meanPairDiff`,
`covariance_meanPairDiff_segSites` and `variance_segSites`. -/
theorem variance_tajimaNumerator [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {S : Ω → ℝ} {D τ : Finset (Fin n) → Ω → ℝ}
    {ℓ : Finset (Fin n) → Finset (Fin n) → Ω → ℝ} {θ : ℝ} (hn : 2 ≤ n)
    (hS2 : MemLp S 2 μ) (hS : μ[S | m] =ᵐ[μ] fun ω => θ / 2 * K.totalLength ω)
    (hSvar : Var[S; μ | m] =ᵐ[μ] fun ω => θ / 2 * K.totalLength ω)
    (hτ : ∀ s ∈ samplePairs n, HasLaw (τ s) (expMeasure 1) μ)
    (hτ₁ : ∀ s ∈ samplePairs n, ∀ t ∈ samplePairs n, #(s ∩ t) = 1 →
      μ[fun ω => τ s ω * τ t ω] = 4 / 3)
    (hτ₀ : ∀ s ∈ samplePairs n, ∀ t ∈ samplePairs n, Disjoint s t →
      μ[fun ω => τ s ω * τ t ω] = 11 / 9)
    (hτL : ∀ s ∈ samplePairs n,
      μ[fun ω => τ s ω * K.totalLength ω] = 2 * tajimaA1 n + ((n : ℝ) + 2) / n)
    (hℓ₂ : ∀ s ∈ samplePairs n, ℓ s s =ᵐ[μ] fun ω => 2 * τ s ω)
    (hℓ₁ : ∀ s ∈ samplePairs n, ∀ t ∈ samplePairs n, #(s ∩ t) = 1 →
      ℓ s t =ᵐ[μ] fun ω => τ s ω + τ t ω - τ (symmDiff s t) ω)
    (hℓ₀ : ∀ s ∈ samplePairs n, ∀ t ∈ samplePairs n, Disjoint s t → μ[ℓ s t] = 2 / 3)
    (hD2 : ∀ s ∈ samplePairs n, MemLp (D s) 2 μ)
    (hD : ∀ s ∈ samplePairs n, μ[D s | m] =ᵐ[μ] fun ω => θ * τ s ω)
    (hDD : ∀ s ∈ samplePairs n, ∀ t ∈ samplePairs n,
      μ[fun ω => D s ω * D t ω | m] =ᵐ[μ]
        fun ω => θ ^ 2 * (τ s ω * τ t ω) + θ / 2 * ℓ s t ω)
    (hDS : ∀ s ∈ samplePairs n, μ[fun ω => D s ω * S ω | m] =ᵐ[μ]
      fun ω => θ ^ 2 / 2 * (τ s ω * K.totalLength ω) + θ * τ s ω) :
    Var[fun ω => meanPairDiff n D ω - S ω / tajimaA1 n; μ] =
      tajimaC1 n * θ + tajimaC2 n * θ ^ 2 := by
  have ha1 : 0 < tajimaA1 n := by
    rw [tajimaA1_eq_harmonic]
    exact_mod_cast harmonic_pos (by omega)
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hSa : MemLp (fun ω => S ω / tajimaA1 n) 2 μ := by
    simpa [div_eq_mul_inv, mul_comm] using hS2.const_mul (tajimaA1 n)⁻¹
  rw [variance_fun_sub (memLp_meanPairDiff hD2) hSa,
    variance_meanPairDiff hm hn hτ hτ₁ hτ₀ hℓ₂ hℓ₁ hℓ₀ hD2 hD hDD, covariance_fun_div_right,
    K.covariance_meanPairDiff_segSites hm hn hS2 hS hτ hτL hD2 hD hDS]
  have hvS : Var[fun ω => S ω / tajimaA1 n; μ] = (θ * tajimaA1 n + θ ^ 2 * tajimaA2 n) /
      tajimaA1 n ^ 2 := by
    simp_rw [div_eq_mul_inv, mul_comm _ (tajimaA1 n)⁻¹]
    rw [variance_const_mul, K.variance_segSites hm hS2 hS hSvar]
    field_simp
  rw [hvS]
  unfold tajimaC1 tajimaC2
  field_simp
  ring

/-- `E[T k T k'] = C(k, 2)⁻¹ C(k', 2)⁻¹ + [k = k'] C(k, 2)⁻²` (independent exponential holding
times). -/
private theorem integral_T_mul_T [IsProbabilityMeasure μ] {k k' : ℕ} (hk : k ∈ Icc 2 n)
    (hk' : k' ∈ Icc 2 n) :
    μ[fun ω => K.T k ω * K.T k' ω] = ((k.choose 2 : ℕ) : ℝ)⁻¹ * ((k'.choose 2 : ℕ) : ℝ)⁻¹ +
      if k = k' then (((k.choose 2 : ℕ) : ℝ)⁻¹) ^ 2 else 0 := by
  by_cases h : k = k'
  · subst h
    have hm : MemLp (K.T k) 2 μ := (K.hasLaw k hk).memLp_comp (f := id)
      ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
        (by simpa using integrable_pow_expMeasure (choose_two_pos hk) 2))
    have hv := variance_eq_sub hm
    rw [(K.hasLaw k hk).variance_eq_of_expMeasure (choose_two_pos hk), K.integral_T hk] at hv
    have hsq : (fun ω => K.T k ω * K.T k ω) = K.T k ^ 2 := by
      funext ω
      simp [sq]
    simp only [hsq, ↓reduceIte]
    linarith
  · have hind : IndepFun (K.T k) (K.T k') μ :=
      K.indep.indepFun (i := ⟨k, hk⟩) (j := ⟨k', hk'⟩) (fun h' => h (congrArg Subtype.val h'))
    rw [IndepFun.integral_fun_mul_eq_mul_integral hind (K.integrable_T hk).aestronglyMeasurable
      (K.integrable_T hk').aestronglyMeasurable, K.integral_T hk, K.integral_T hk']
    simp [h]

/-- **Pair coalescence time against the total branch length**: if the coalescence time of a
pair is `τ = ∑_{k=2}^n χ k T k`, where `χ k` indicates that the pair is still in two distinct
lineages while there are `k` lineages, and the topology is independent of the holding times in
the sense `E[χ k T k T k'] = p k E[T k T k']` with `p k = pairSeparateProb n k`, then
`E[τ L] = 2 a₁ + (n + 2) / n` for `n ≥ 2`. Only this factorization is used, so `χ k` need not
be an indicator in the statement. -/
theorem integral_pairTime_mul_totalLength [IsProbabilityMeasure μ] {χ : ℕ → Ω → ℝ}
    {τ : Ω → ℝ} (hn : 2 ≤ n) (hτ : τ = fun ω => ∑ k ∈ Icc 2 n, χ k ω * K.T k ω)
    (hχ : ∀ k ∈ Icc 2 n, ∀ k' ∈ Icc 2 n,
      μ[fun ω => χ k ω * (K.T k ω * K.T k' ω)] =
        pairSeparateProb n k * μ[fun ω => K.T k ω * K.T k' ω]) :
    μ[fun ω => τ ω * K.totalLength ω] = 2 * tajimaA1 n + ((n : ℝ) + 2) / n := by
  have hp : ∀ k ∈ Icc 2 n, 0 < pairSeparateProb n k := by
    intro k hk
    have h2 : (2 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.1 hk).1
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    unfold pairSeparateProb
    apply div_pos <;> nlinarith
  have hTT : ∀ k ∈ Icc 2 n, ∀ k' ∈ Icc 2 n, 0 < μ[fun ω => K.T k ω * K.T k' ω] := by
    intro k hk k' hk'
    rw [K.integral_T_mul_T hk hk']
    have := choose_two_pos hk
    have := choose_two_pos hk'
    split_ifs <;> positivity
  have hint : ∀ k ∈ Icc 2 n, ∀ k' ∈ Icc 2 n,
      Integrable (fun ω => χ k ω * (K.T k ω * K.T k' ω)) μ := fun k hk k' hk' =>
    Integrable.of_integral_ne_zero (by
      rw [hχ k hk k' hk']
      exact (mul_pos (hp k hk) (hTT k hk k' hk')).ne')
  have hexp : (fun ω => τ ω * K.totalLength ω) = fun ω => ∑ k ∈ Icc 2 n, ∑ k' ∈ Icc 2 n,
      (k' : ℝ) * (χ k ω * (K.T k ω * K.T k' ω)) := by
    funext ω
    rw [hτ, totalLength, sum_mul_sum]
    refine sum_congr rfl fun k _ => sum_congr rfl fun k' _ => ?_
    ring
  rw [hexp, integral_finsetSum _ fun k hk => integrable_finsetSum _ fun k' hk' =>
    (hint k hk k' hk').const_mul _]
  have inner : ∀ k ∈ Icc 2 n, μ[fun ω => ∑ k' ∈ Icc 2 n,
      (k' : ℝ) * (χ k ω * (K.T k ω * K.T k' ω))] =
      pairSeparateProb n k * ((k.choose 2 : ℕ) : ℝ)⁻¹ *
          ∑ k' ∈ Icc 2 n, (k' : ℝ) * ((k'.choose 2 : ℕ) : ℝ)⁻¹ +
        (k : ℝ) * pairSeparateProb n k * (((k.choose 2 : ℕ) : ℝ)⁻¹) ^ 2 := by
    intro k hk
    rw [integral_finsetSum _ fun k' hk' => (hint k hk k' hk').const_mul _]
    rw [sum_congr rfl fun k' hk' => by
      rw [integral_const_mul, hχ k hk k' hk', K.integral_T_mul_T hk hk']]
    simp only [mul_add, sum_add_distrib, mul_ite, mul_zero, sum_ite_eq, hk, ↓reduceIte, mul_sum]
    congr 1
    · exact sum_congr rfl fun k' _ => by ring
    · ring
  rw [sum_congr rfl inner, sum_add_distrib, ← sum_mul, sum_pairSeparateProb_div_choose hn,
    one_mul, sum_mul_inv_choose_two, sum_mul_pairSeparateProb_div_choose_sq hn,
    tajimaA1_eq_harmonic]

end KingmanTimes

end MathlibExt.Biology.PopulationGenetics.Coalescent
