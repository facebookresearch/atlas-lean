/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.CancerGenomics.DetectionPower
public import Mathlib.Order.Filter.Extr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-!
# Cancer cell fraction: grid posterior, threshold clonal call, and the MLE

Landau et al. (2013, Experimental Procedures) convert a somatic mutation seen in `a` of `n`
reads, at a locus of absolute copy number `q` in a sample of purity `α`, into a cancer cell
fraction (CCF) `c`: a mutation present in one copy in a fraction `c` of cancer cells has
expected allelic fraction `f(c) = α c / (2 (1 - α) + α q)` (ABSOLUTE, Carter et al. 2012,
Eq. 2 with multiplicity `c`), so `P(c | a) ∝ π(c) Binom(a | n, f(c))` on a regular grid of
`100` values `c ∈ [0.01, 1]` with a uniform prior `π`. A mutation is called clonal when
`P(c > 0.95 | a) > 0.5`.

This file proves, for any nonnegative prior on any grid:

* the binomial family is totally positive of order two in `(a, p)` (monotone likelihood
  ratio), `binomPmf_mul_le_mul`;
* hence the posterior tail `P(c > t | a)` is nondecreasing in the read count `a`
  (`posteriorTail_mono`), and the clonal call is a read-count threshold: for every `t` and `γ`
  there is `a₀` with `clonal ↔ a₀ ≤ a` for all `a ≤ n` (`exists_threshold`);
* the continuous maximum-likelihood CCF (derived here; Landau et al. use the grid) is
  `ĉ = min 1 (a / (n κ))`, `κ = α / (2 (1 - α) + α q)` (`isMaxOn_ccfMLE`).

The general TP2-implies-monotone-posterior lemma, `posteriorTail_mono_of_tp2`, is stated for
an arbitrary finite family of kernels.

## Main results

* `posteriorTail_mono_of_tp2`: monotone likelihood ratio implies stochastically increasing
  posteriors on a finite grid.
* `binomPmf_mul_le_mul`: `Binom(a | n, p) Binom(a' | n, p') ≥ Binom(a' | n, p) Binom(a | n, p')`
  for `a ≤ a'`, `0 ≤ p ≤ p' ≤ 1`.
* `posteriorTail_mono`, `exists_threshold`: the clonal call is a read-count threshold.
* `isMaxOn_ccfMLE`: the continuous MLE of the CCF.

## References

* D. A. Landau et al., *Evolution and impact of subclonal mutations in chronic lymphocytic
  leukemia*, Cell 152 (2013), 714–726 (Experimental Procedures, CCF estimation).
* S. L. Carter et al., *Absolute quantification of somatic DNA alterations in human cancer*,
  Nat. Biotechnol. 30 (2012), 413–421.
* S. Karlin, H. Rubin, *The theory of decision procedures for distributions with monotone
  likelihood ratio*, Ann. Math. Statist. 27 (1956), 272–299 (monotone likelihood ratio).
* P. R. Milgrom, *Good news and bad news: representation theorems and applications*, Bell J.
  Econ. 12 (1981), 380–391 (monotone likelihood ratio gives stochastically larger
  posteriors).
-/

@[expose] public section

namespace MathlibExt.Biology.CancerGenomics.CancerCellFraction

open Finset MathlibExt.Biology.CancerGenomics.Absolute
  MathlibExt.Biology.CancerGenomics.DetectionPower

variable {ι : Type*} [Fintype ι]

/-- Posterior probability that the parameter `c i` exceeds `t`, for prior weights `prior` and
likelihoods `lik i` of the observed data: `∑_{c i > t} prior i lik i / ∑_i prior i lik i`. -/
noncomputable def tailRatio (prior lik c : ι → ℝ) (t : ℝ) : ℝ :=
  (∑ i with t < c i, prior i * lik i) / ∑ i, prior i * lik i

/-- **Monotone likelihood ratio implies stochastically larger posteriors.** If the kernels
`L` (data `x`) and `L'` (data `x'`) satisfy the TP2 inequality `L' i L j ≥ L i L' j` whenever
`c j ≤ c i`, then for a nonnegative prior every posterior tail `P(c > t)` is at least as large
under `L'` as under `L` (both normalizers positive). -/
theorem posteriorTail_mono_of_tp2 (prior L L' c : ι → ℝ) (t : ℝ)
    (hprior : ∀ i, 0 ≤ prior i)
    (htp2 : ∀ i j, c j ≤ c i → L i * L' j ≤ L' i * L j)
    (hZ : 0 < ∑ i, prior i * L i) (hZ' : 0 < ∑ i, prior i * L' i) :
    tailRatio prior L c t ≤ tailRatio prior L' c t := by
  unfold tailRatio
  rw [div_le_div_iff₀ hZ hZ']
  set A : Finset ι := univ.filter fun i => t < c i
  set B : Finset ι := univ.filter fun i => ¬ t < c i
  have hsplit : ∀ g : ι → ℝ, ∑ i, g i = ∑ i ∈ A, g i + ∑ i ∈ B, g i := fun g =>
    (sum_filter_add_sum_filter_not univ (fun i => t < c i) g).symm
  rw [hsplit fun i => prior i * L' i, hsplit fun i => prior i * L i]
  have key : (∑ i ∈ A, prior i * L i) * (∑ j ∈ B, prior j * L' j) ≤
      (∑ i ∈ A, prior i * L' i) * (∑ j ∈ B, prior j * L j) := by
    rw [sum_mul_sum, sum_mul_sum]
    refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
    have hci : t < c i := (mem_filter.1 hi).2
    have hcj : ¬ t < c j := (mem_filter.1 hj).2
    have := htp2 i j (by linarith [not_lt.1 hcj])
    have h2 := mul_nonneg (hprior i) (hprior j)
    nlinarith
  nlinarith [key]

/-- **The binomial family is TP2** (monotone likelihood ratio in the success probability):
for `a ≤ a'` and `0 ≤ p ≤ p' ≤ 1`,
`Binom(a | n, p') Binom(a' | n, p) ≤ Binom(a' | n, p') Binom(a | n, p)`. -/
theorem binomPmf_mul_le_mul {n a a' : ℕ} {p p' : ℝ} (haa' : a ≤ a') (hp0 : 0 ≤ p)
    (hpp' : p ≤ p') (hp1 : p' ≤ 1) :
    binomPmf n p' a * binomPmf n p a' ≤ binomPmf n p' a' * binomPmf n p a := by
  rcases le_or_gt a' n with ha' | ha'
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le haa'
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le ha'
    have hna : n - a = d + e := by omega
    have hna' : n - (a + d) = e := by omega
    unfold binomPmf
    rw [hna, hna']
    have hp0' : 0 ≤ p' := hp0.trans hpp'
    have h1 : 0 ≤ 1 - p' := by linarith
    have h2 : 0 ≤ 1 - p := by linarith
    have hcross : p * (1 - p') ≤ p' * (1 - p) := by nlinarith
    have hpow : (p * (1 - p')) ^ d ≤ (p' * (1 - p)) ^ d :=
      pow_le_pow_left₀ (mul_nonneg hp0 h1) hcross d
    have hc : (0 : ℝ) ≤ n.choose a * n.choose (a + d) := by positivity
    have hrest : 0 ≤ p' ^ a * p ^ a * (1 - p') ^ e * (1 - p) ^ e := by positivity
    have := mul_le_mul_of_nonneg_left hpow (mul_nonneg hc hrest)
    calc (n.choose a : ℝ) * p' ^ a * (1 - p') ^ (d + e) *
          ((n.choose (a + d) : ℝ) * p ^ (a + d) * (1 - p) ^ e)
        = n.choose a * n.choose (a + d) *
            (p' ^ a * p ^ a * (1 - p') ^ e * (1 - p) ^ e) * (p * (1 - p')) ^ d := by
          rw [mul_pow]; ring
      _ ≤ n.choose a * n.choose (a + d) *
            (p' ^ a * p ^ a * (1 - p') ^ e * (1 - p) ^ e) * (p' * (1 - p)) ^ d := this
      _ = (n.choose (a + d) : ℝ) * p' ^ (a + d) * (1 - p') ^ e *
            ((n.choose a : ℝ) * p ^ a * (1 - p) ^ (d + e)) := by
          rw [mul_pow]; ring
  · rw [binomPmf_eq_zero p ha', binomPmf_eq_zero p' ha']
    simp

/-- Landau et al.'s posterior probability that the CCF exceeds `t`, given `a` of `n` reads,
purity `α`, copy number `q`, a prior `prior` on the grid points `grid k`:
`∑_{grid k > t} π_k Binom(a | n, f(grid k)) / ∑_k π_k Binom(a | n, f(grid k))`, with
`f(c) = α c / (α q + 2 (1 - α))`. -/
noncomputable def posteriorTail {m : ℕ} (prior grid : Fin m → ℝ) (α q : ℝ) (n a : ℕ)
    (t : ℝ) : ℝ :=
  tailRatio prior (fun k => binomPmf n (somaticAF α q (grid k)) a) grid t

/-- Landau et al.'s clonal call: `P(CCF > t | a) > γ` (they take `t = 0.95`, `γ = 0.5`). -/
def IsClonal {m : ℕ} (prior grid : Fin m → ℝ) (α q : ℝ) (n a : ℕ) (t γ : ℝ) : Prop :=
  γ < posteriorTail prior grid α q n a t

/-- Hypotheses on the CCF grid model: purity `0 < α ≤ 1`, copy number `q > 0`, grid in
`[0, q]` and within the defining CCF bound `≤ 1`, a nonnegative prior, and one grid point
of positive prior weight whose allelic fraction lies strictly inside `(0, 1)` (this makes
every posterior well defined). -/
structure GridModel {m : ℕ} (prior grid : Fin m → ℝ) (α q : ℝ) : Prop where
  purity_pos : 0 < α
  purity_le_one : α ≤ 1
  copy_pos : 0 < q
  grid_nonneg : ∀ k, 0 ≤ grid k
  grid_le : ∀ k, grid k ≤ q
  grid_le_one : ∀ k, grid k ≤ 1
  prior_nonneg : ∀ k, 0 ≤ prior k
  exists_interior : ∃ k, 0 < prior k ∧ 0 < somaticAF α q (grid k) ∧ somaticAF α q (grid k) < 1

/-- In a grid model every posterior normalizer `∑_k π_k Binom(a | n, f(grid k))`, `a ≤ n`,
is positive. -/
theorem GridModel.normalizer_pos {m : ℕ} {prior grid : Fin m → ℝ} {α q : ℝ}
    (h : GridModel prior grid α q) {n a : ℕ} (ha : a ≤ n) :
    0 < ∑ k, prior k * binomPmf n (somaticAF α q (grid k)) a := by
  obtain ⟨k, hk, hf0, hf1⟩ := h.exists_interior
  refine lt_of_lt_of_le (mul_pos hk (binomPmf_pos hf0 hf1 ha)) ?_
  refine single_le_sum (f := fun k => prior k * binomPmf n (somaticAF α q (grid k)) a)
    (fun j _ => mul_nonneg (h.prior_nonneg j) (binomPmf_nonneg ?_ ?_ a)) (mem_univ k)
  · exact somaticAF_nonneg h.purity_pos.le h.purity_le_one h.copy_pos (h.grid_nonneg j)
  · exact somaticAF_le_one h.purity_pos.le h.purity_le_one h.copy_pos (h.grid_le j)

/-- **The CCF posterior is stochastically increasing in the read count** (Landau et al. 2013
with the monotone-likelihood-ratio argument): `P(CCF > t | a) ≤ P(CCF > t | a')` for
`a ≤ a' ≤ n`. -/
theorem posteriorTail_mono {m : ℕ} {prior grid : Fin m → ℝ} {α q : ℝ}
    (h : GridModel prior grid α q) {n a a' : ℕ} (haa' : a ≤ a') (ha' : a' ≤ n) (t : ℝ) :
    posteriorTail prior grid α q n a t ≤ posteriorTail prior grid α q n a' t := by
  unfold posteriorTail
  refine posteriorTail_mono_of_tp2 _ _ _ _ t h.prior_nonneg (fun i j hji => ?_)
    (h.normalizer_pos (haa'.trans ha')) (h.normalizer_pos ha')
  have hα0 := h.purity_pos.le
  have hf := somaticAF_mono_mult hα0 h.purity_le_one h.copy_pos hji (q := q)
  have := binomPmf_mul_le_mul (n := n) haa'
    (somaticAF_nonneg hα0 h.purity_le_one h.copy_pos (h.grid_nonneg j)) hf
    (somaticAF_le_one hα0 h.purity_le_one h.copy_pos (h.grid_le i))
  linarith [mul_comm (binomPmf n (somaticAF α q (grid i)) a)
    (binomPmf n (somaticAF α q (grid j)) a')]

/-- **The clonal call is upward closed in the read count.** -/
theorem IsClonal.mono {m : ℕ} {prior grid : Fin m → ℝ} {α q : ℝ}
    (h : GridModel prior grid α q) {n a a' : ℕ} {t γ : ℝ} (haa' : a ≤ a') (ha' : a' ≤ n)
    (hc : IsClonal prior grid α q n a t γ) : IsClonal prior grid α q n a' t γ :=
  lt_of_lt_of_le hc (posteriorTail_mono h haa' ha' t)

/-- **The clonal call is a read-count threshold**: for every CCF threshold `t` and posterior
level `γ` there is `a₀` such that, for `a ≤ n`, the mutation is called clonal iff `a₀ ≤ a`
(`a₀ = n + 1` when no count is called clonal). -/
theorem exists_threshold {m : ℕ} {prior grid : Fin m → ℝ} {α q : ℝ}
    (h : GridModel prior grid α q) (n : ℕ) (t γ : ℝ) :
    ∃ a₀, ∀ a ≤ n, IsClonal prior grid α q n a t γ ↔ a₀ ≤ a := by
  classical
  by_cases hex : ∃ a ≤ n, IsClonal prior grid α q n a t γ
  · refine ⟨Nat.find hex, fun a ha => ⟨fun hc => Nat.find_min' hex ⟨ha, hc⟩, fun hle => ?_⟩⟩
    obtain ⟨h1, h2⟩ := Nat.find_spec hex
    exact h2.mono h hle ha
  · simp only [not_exists, not_and] at hex
    exact ⟨n + 1, fun a ha => ⟨fun hc => absurd hc (hex a ha), fun hle => by omega⟩⟩

/-- The continuous maximum-likelihood CCF `ĉ = min 1 (a / (n κ))` for the allelic-fraction
slope `κ = α / (α q + 2 (1 - α))`. Landau et al. (2013) use the grid posterior; this continuous
maximizer over `[0, 1]` is derived here. -/
noncomputable def ccfMLE (α q : ℝ) (n a : ℕ) : ℝ := min 1 ((a : ℝ) / n / somaticAF α q 1)

/-- **The continuous CCF MLE**: for `0 < α ≤ 1`, `q ≥ 1`, `a ≤ n` and `0 < n`, the likelihood
`c ↦ Binom(a | n, f(c))` on `[0, 1]` is maximized at `ĉ = min 1 (a / (n κ))`. -/
theorem isMaxOn_ccfMLE {α q : ℝ} {n a : ℕ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hq : 1 ≤ q)
    (ha : a ≤ n) (hn : 0 < n) :
    IsMaxOn (fun c => binomPmf n (somaticAF α q c) a) (Set.Icc 0 1) (ccfMLE α q n a) := by
  have hq0 : 0 < q := by linarith
  set κ := somaticAF α q 1 with hκ
  have hκpos : 0 < κ := div_pos (by simpa using hα0) (mixCopy_pos hα0.le hα1 hq0)
  have hκ1 : κ ≤ 1 := somaticAF_le_one hα0.le hα1 hq0 hq
  have hlin : ∀ c, somaticAF α q c = κ * c := fun c => by
    simp only [hκ, somaticAF]; ring
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have han : (a : ℝ) / n ≤ 1 := by
    rw [div_le_one hn']; exact_mod_cast ha
  have han0 : 0 ≤ (a : ℝ) / n := by positivity
  intro c hc
  simp only [Set.mem_ofPred_eq, hlin]
  rcases le_total ((a : ℝ) / n / κ) 1 with hle | hle
  · -- interior optimum: `κ ĉ = a / n`
    have hĉ : κ * ccfMLE α q n a = a / n := by
      simp only [ccfMLE, ← hκ, min_eq_right hle]; field_simp
    rw [hĉ]
    rcases le_total (κ * c) ((a : ℝ) / n) with h1 | h1
    · exact binomPmf_le_binomPmf_of_le_div ha (mul_nonneg hκpos.le hc.1) h1 le_rfl
    · exact binomPmf_le_binomPmf_of_div_le ha le_rfl h1
        (by nlinarith [hc.2, hc.1])
  · -- boundary optimum `ĉ = 1`, and `κ ≤ a / n`
    have hĉ : ccfMLE α q n a = 1 := by simp only [ccfMLE, ← hκ, min_eq_left hle]
    rw [hĉ, mul_one]
    have hκa : κ ≤ (a : ℝ) / n := by rwa [le_div_iff₀ hκpos, one_mul] at hle
    exact binomPmf_le_binomPmf_of_le_div ha (mul_nonneg hκpos.le hc.1)
      (by nlinarith [hc.2]) hκa

end MathlibExt.Biology.CancerGenomics.CancerCellFraction
