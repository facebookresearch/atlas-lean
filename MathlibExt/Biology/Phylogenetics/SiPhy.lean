/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Phylogenetics.SubstitutionModels
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# SiPhy: the M-step for the rate scaling `ω` and the constraint vector `π`

SiPhy (Garber et al. 2009) models the substitutions at an aligned site by the rate matrix
`Q a b = ω R a b π b` (`a ≠ b`), the product of an overall rate `ω`, a symmetric neutral
exchangeability matrix `R` and a site-specific constraint vector `π` (Eq. 10). This is the
general time-reversible matrix `gtrRate π R` scaled by `ω` (`siphyRate`), so `π` is its
equilibrium distribution.

SiPhy fits `ω` and `π` by EM. With the expected numbers `n a b` of `a → b` substitutions, the
expected times `τ a` spent in each state (both summed over the branches of the tree, Holmes and
Rubin 2002) and the posterior `r b` of the root state, the expected complete-data
log-likelihood is (Eq. 6)
`∑_{a ≠ b} n a b log Q a b + ∑ a, τ a Q a a + ∑ b, r b log π b` (`expectedLogLik`).
Setting its derivatives to zero gives the closed-form updates of Eqs. 7–8: the rate
`ω = N / ∑ b, e b π b` (`omegaUpdate`) and the constraint vector `π b = c b / (ω e b + γ)` with a
Lagrange multiplier `γ` for `∑ π = 1`. The explicit forms below are our derivation from Eq. 6
and Eq. 10, with `N = ∑_{a ≠ b} n a b`, `c b = ∑_{a ≠ b} n a b + r b` (`inCount`) and
`e b = ∑_{a ≠ b} τ a R a b` (`exitWeight`).

## Main results

* `isRateMatrix_siphyRate`, `isDetailedBalance_siphyRate`: `ω R π` is a rate matrix in
  detailed balance with `π` (for symmetric `R`).
* `expectedLogLik_siphyRate`: Eq. 6 for the SiPhy matrix splits into an `ω` part, a constant
  and the concave `π` part `piObjective`.
* `expectedLogLik_le_omegaUpdate`, `expectedLogLik_lt_omegaUpdate`: the `ω` update is the unique
  maximizer over `ω > 0` for fixed `π`.
* `existsUnique_lagrange`: the multiplier `γ` exists and is unique.
* `piObjective_lt`, `expectedLogLik_lt_piUpdate`: the `π` update is the unique maximizer over the
  positive probability vectors for fixed `ω`.

## References

* M. Garber, M. Guttman, M. Clamp, M. C. Zody, N. Friedman, X. Xie, *Identifying novel
  constrained elements by exploiting biased substitution patterns*, Bioinformatics 25 (2009),
  i54–i62, Eqs. 6–8 and 10.
* I. Holmes and G. M. Rubin, *An expectation maximization algorithm for training hidden
  substitution models*, J. Mol. Biol. 317 (2002), 753–764.
-/

@[expose] public section

open Finset Matrix ProbabilityTheory MathlibExt.Biology.Phylogenetics.SubstitutionModels
open Real (log log_mul log_div log_le_sub_one_of_pos log_lt_sub_one_of_pos)

namespace MathlibExt.Biology.Phylogenetics.SiPhy

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The SiPhy rate matrix** `Q a b = ω R a b π b` for `a ≠ b` (Garber et al. 2009, Eq. 10),
with rows summing to zero: `ω` times the GTR matrix with exchangeabilities `R` and base
frequencies `π`. -/
noncomputable def siphyRate (ω : ℝ) (R : Matrix ι ι ℝ) (π : ι → ℝ) : Matrix ι ι ℝ :=
  ω • gtrRate π R

/-- With `ω ≥ 0`, nonnegative `R` and nonnegative `π`, the SiPhy matrix is a rate matrix. -/
theorem isRateMatrix_siphyRate {ω : ℝ} {R : Matrix ι ι ℝ} {π : ι → ℝ} (hω : 0 ≤ ω)
    (hR : ∀ a b, 0 ≤ R a b) (hπ : ∀ b, 0 ≤ π b) : IsRateMatrix (siphyRate ω R π) := by
  have h := isRateMatrix_gtrRate hπ hR
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · simpa [siphyRate] using mul_nonneg hω (h.nonneg_of_ne hab)
  · simp [siphyRate, ← mul_sum, h.sum_row a]

/-- **`π` is the equilibrium of the SiPhy matrix**: for symmetric `R` it is in detailed balance
with `π`, for every `ω`. -/
theorem isDetailedBalance_siphyRate (ω : ℝ) {R : Matrix ι ι ℝ} (hR : ∀ a b, R a b = R b a)
    (π : ι → ℝ) : IsDetailedBalance π (siphyRate ω R π) := by
  intro a b
  have := isDetailedBalance_gtrRate π hR a b
  simp only [siphyRate, Matrix.smul_apply, smul_eq_mul]
  linear_combination ω * this

/-- **The expected complete-data log-likelihood** of a rate matrix `Q` and root distribution `π`
(Garber et al. 2009, Eq. 6): `∑_{a ≠ b} n a b log Q a b + ∑ a, τ a Q a a + ∑ b, r b log π b`,
for expected substitution counts `n`, expected state durations `τ` and the root posterior `r`. -/
noncomputable def expectedLogLik (n : Matrix ι ι ℝ) (τ r : ι → ℝ) (Q : Matrix ι ι ℝ)
    (π : ι → ℝ) : ℝ :=
  ∑ a, ∑ b, (if a = b then 0 else n a b * log (Q a b)) + ∑ a, τ a * Q a a +
    ∑ b, r b * log (π b)

/-- The expected total number of substitutions `N = ∑_{a ≠ b} n a b`. -/
def totalCount (n : Matrix ι ι ℝ) : ℝ := ∑ a, ∑ b, if a = b then 0 else n a b

/-- The weight `c b = ∑_{a ≠ b} n a b + r b` of state `b`: substitutions into `b` plus the root
posterior of `b`. -/
def inCount (n : Matrix ι ι ℝ) (r : ι → ℝ) (b : ι) : ℝ :=
  ∑ a, (if a = b then 0 else n a b) + r b

/-- The time-weighted exchange rate into `b`, `e b = ∑_{a ≠ b} τ a R a b`. -/
def exitWeight (τ : ι → ℝ) (R : Matrix ι ι ℝ) (b : ι) : ℝ :=
  ∑ a, if a = b then 0 else τ a * R a b

/-- The part of Eq. 6 that depends on `π` (for fixed `ω`):
`∑ b, (c b * log (π b) - d b * π b)`. -/
noncomputable def piObjective (c d π : ι → ℝ) : ℝ := ∑ b, (c b * log (π b) - d b * π b)

/-- The `n log R` constant of Eq. 6. -/
noncomputable def exchangeTerm (n R : Matrix ι ι ℝ) : ℝ :=
  ∑ a, ∑ b, if a = b then 0 else n a b * log (R a b)

private theorem sum_erase_eq_sum_ite {M : Type*} [AddCommMonoid M] (a : ι) (f : ι → M) :
    ∑ k ∈ univ.erase a, f k = ∑ k, if a = k then 0 else f k := by
  rw [sum_ite, sum_const_zero, zero_add]
  exact sum_congr (by ext k; simp [eq_comm]) fun _ _ => rfl

/-- **Eq. 6 for the SiPhy matrix**: for `ω > 0`, positive off-diagonal `R` and positive `π`,
`expectedLogLik = N log ω + ∑_{a ≠ b} n a b log R a b + piObjective c (ω e) π`. -/
theorem expectedLogLik_siphyRate (n : Matrix ι ι ℝ) (τ r : ι → ℝ) {ω : ℝ}
    {R : Matrix ι ι ℝ} {π : ι → ℝ} (hω : 0 < ω) (hR : ∀ a b, a ≠ b → 0 < R a b)
    (hπ : ∀ b, 0 < π b) :
    expectedLogLik n τ r (siphyRate ω R π) π =
      totalCount n * log ω + exchangeTerm n R +
        piObjective (inCount n r) (fun b => ω * exitWeight τ R b) π := by
  have hoff : ∀ a b, a ≠ b → log (siphyRate ω R π a b) = log ω + log (R a b) + log (π b) := by
    intro a b hab
    have : siphyRate ω R π a b = ω * (R a b * π b) := by
      simp [siphyRate, gtrRate, hab]
    rw [this, log_mul hω.ne' (mul_pos (hR a b hab) (hπ b)).ne',
      log_mul (hR a b hab).ne' (hπ b).ne']
    ring
  have hdiag : ∀ a, τ a * siphyRate ω R π a a =
      -∑ b, if a = b then 0 else ω * (τ a * R a b) * π b := by
    intro a
    have : siphyRate ω R π a a = ω * -∑ k ∈ univ.erase a, R a k * π k := by
      simp [siphyRate, gtrRate]
    rw [this, sum_erase_eq_sum_ite a (fun k => R a k * π k), mul_neg, mul_neg, mul_sum,
      mul_sum]
    congr 1
    refine sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  have hpt : ∀ a b, (if a = b then 0 else n a b * log (siphyRate ω R π a b)) =
      (if a = b then 0 else n a b) * log ω + (if a = b then 0 else n a b * log (R a b)) +
        (if a = b then 0 else n a b) * log (π b) := by
    intro a b
    by_cases hab : a = b
    · simp [hab]
    · simp only [hab, ite_false, hoff a b hab]; ring
  have h1 : ∑ a, ∑ b, (if a = b then 0 else n a b * log (siphyRate ω R π a b)) =
      totalCount n * log ω + exchangeTerm n R +
        ∑ b, (∑ a, if a = b then 0 else n a b) * log (π b) := by
    simp only [hpt, sum_add_distrib, totalCount, exchangeTerm, sum_mul]
    rw [sum_comm (f := fun a b => (if a = b then 0 else n a b) * log (π b))]
  have h2 : ∑ a, τ a * siphyRate ω R π a a = -∑ b, ω * exitWeight τ R b * π b := by
    simp only [hdiag, sum_neg_distrib, exitWeight, mul_sum, sum_mul]
    rw [sum_comm]
    congr 1
    refine sum_congr rfl fun b _ => sum_congr rfl fun a _ => ?_
    split_ifs <;> ring
  rw [expectedLogLik, h1, h2]
  simp only [piObjective, inCount, sum_sub_distrib, add_mul, sum_add_distrib]
  ring

/-! ## The rate update -/

/-- **The SiPhy rate update** (Eq. 7, for fixed `π`): `ω = N / ∑ b, e b π b`. -/
noncomputable def omegaUpdate (n : Matrix ι ι ℝ) (τ : ι → ℝ) (R : Matrix ι ι ℝ)
    (π : ι → ℝ) : ℝ :=
  totalCount n / ∑ b, exitWeight τ R b * π b

private theorem omega_part_le {N D ω : ℝ} (hN : 0 < N) (hD : 0 < D) (hω : 0 < ω) :
    N * log ω - ω * D ≤ N * log (N / D) - N / D * D := by
  have hω' : 0 < N / D := div_pos hN hD
  have hlog := log_le_sub_one_of_pos (div_pos hω hω')
  rw [log_div hω.ne' hω'.ne'] at hlog
  have : N * (log ω - log (N / D)) ≤ N * (ω / (N / D) - 1) :=
    mul_le_mul_of_nonneg_left hlog hN.le
  have e : N * (ω / (N / D) - 1) = ω * D - N / D * D := by field_simp
  linarith

private theorem omega_part_lt {N D ω : ℝ} (hN : 0 < N) (hD : 0 < D) (hω : 0 < ω)
    (hne : ω ≠ N / D) : N * log ω - ω * D < N * log (N / D) - N / D * D := by
  have hω' : 0 < N / D := div_pos hN hD
  have hlog := log_lt_sub_one_of_pos (div_pos hω hω') (by
    rwa [Ne, div_eq_one_iff_eq hω'.ne'])
  rw [log_div hω.ne' hω'.ne'] at hlog
  have : N * (log ω - log (N / D)) < N * (ω / (N / D) - 1) := mul_lt_mul_of_pos_left hlog hN
  have e : N * (ω / (N / D) - 1) = ω * D - N / D * D := by field_simp
  linarith

omit [DecidableEq ι] in
private theorem piObjective_smul (c e π : ι → ℝ) (ω : ℝ) :
    piObjective c (fun b => ω * e b) π = ∑ b, c b * log (π b) - ω * ∑ b, e b * π b := by
  simp only [piObjective, sum_sub_distrib, mul_sum, mul_assoc]

/-- **The rate update maximizes Eq. 6 over `ω > 0`** for a fixed positive `π`, when the expected
number of substitutions `N` and the time-weighted rate `∑ b, e b π b` are positive. -/
theorem expectedLogLik_le_omegaUpdate (n : Matrix ι ι ℝ) (τ r : ι → ℝ) {R : Matrix ι ι ℝ}
    {π : ι → ℝ} (hR : ∀ a b, a ≠ b → 0 < R a b) (hπ : ∀ b, 0 < π b) (hN : 0 < totalCount n)
    (hD : 0 < ∑ b, exitWeight τ R b * π b) {ω : ℝ} (hω : 0 < ω) :
    expectedLogLik n τ r (siphyRate ω R π) π ≤
      expectedLogLik n τ r (siphyRate (omegaUpdate n τ R π) R π) π := by
  rw [expectedLogLik_siphyRate n τ r hω hR hπ,
    expectedLogLik_siphyRate n τ r (show 0 < omegaUpdate n τ R π from div_pos hN hD) hR hπ,
    piObjective_smul, piObjective_smul]
  have := omega_part_le hN hD hω
  unfold omegaUpdate
  linarith

/-- **The rate update is the unique maximizer**: any other `ω > 0` gives a strictly smaller
value of Eq. 6. -/
theorem expectedLogLik_lt_omegaUpdate (n : Matrix ι ι ℝ) (τ r : ι → ℝ) {R : Matrix ι ι ℝ}
    {π : ι → ℝ} (hR : ∀ a b, a ≠ b → 0 < R a b) (hπ : ∀ b, 0 < π b) (hN : 0 < totalCount n)
    (hD : 0 < ∑ b, exitWeight τ R b * π b) {ω : ℝ} (hω : 0 < ω)
    (hne : ω ≠ omegaUpdate n τ R π) :
    expectedLogLik n τ r (siphyRate ω R π) π <
      expectedLogLik n τ r (siphyRate (omegaUpdate n τ R π) R π) π := by
  rw [expectedLogLik_siphyRate n τ r hω hR hπ,
    expectedLogLik_siphyRate n τ r (show 0 < omegaUpdate n τ R π from div_pos hN hD) hR hπ,
    piObjective_smul, piObjective_smul]
  have := omega_part_lt hN hD hω hne
  unfold omegaUpdate
  linarith

/-! ## The constraint-vector update -/

omit [DecidableEq ι] in
/-- **The Lagrange multiplier of the `π` update exists and is unique**: for positive `c` and
nonnegative `d` on a nonempty finite alphabet there is exactly one `γ` with `d b + γ > 0` for
all `b` and `∑ b, c b / (d b + γ) = 1`. -/
theorem existsUnique_lagrange [Nonempty ι] {c d : ι → ℝ} (hc : ∀ b, 0 < c b)
    (hd : ∀ b, 0 ≤ d b) :
    ∃! γ : ℝ, (∀ b, 0 < d b + γ) ∧ ∑ b, c b / (d b + γ) = 1 := by
  classical
  obtain ⟨b₀, _, hb₀⟩ := exists_min_image univ d univ_nonempty
  have hmin : ∀ b, d b₀ ≤ d b := fun b => hb₀ b (mem_univ b)
  let C : ℝ := ∑ b, c b
  let ε : ℝ := min 1 (c b₀)
  let a : ℝ := -d b₀ + ε
  let z : ℝ := C + 1
  let g : ℝ → ℝ := fun x => ∑ b, c b / (d b + x)
  have hC : 0 < C := sum_pos (fun b _ => hc b) univ_nonempty
  have hε : 0 < ε := lt_min (by norm_num) (hc b₀)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεc : ε ≤ c b₀ := min_le_right _ _
  have haz : a ≤ z := by dsimp [a, z]; linarith [hd b₀]
  have hden : ∀ x, a ≤ x → ∀ b, 0 < d b + x := by
    intro x hx b
    dsimp [a] at hx
    linarith [hmin b]
  have hga : 1 ≤ g a := by
    have hb : 1 ≤ c b₀ / (d b₀ + a) := by
      have heq : d b₀ + a = ε := by dsimp [a]; ring
      rw [heq]
      exact (le_div_iff₀ hε).2 (by simpa using hεc)
    exact hb.trans (single_le_sum
      (fun b _ => (div_pos (hc b) (hden a le_rfl b)).le) (mem_univ b₀))
  have hgz : g z < 1 := by
    have hlt : g z < ∑ b, c b / C := by
      apply sum_lt_sum_of_nonempty univ_nonempty
      intro b _
      exact div_lt_div_of_pos_left (hc b) hC (by dsimp [z]; linarith [hd b])
    have heq : (∑ b, c b / C) = 1 := by
      simp only [div_eq_mul_inv, ← sum_mul]
      exact mul_inv_cancel₀ (ne_of_gt hC)
    exact heq ▸ hlt
  have hcont : ContinuousOn g (Set.Icc a z) := by
    apply continuousOn_finsetSum
    intro b _
    exact continuousOn_const.div (continuousOn_const.add continuousOn_id)
      (fun x hx => ne_of_gt (hden x hx.1 b))
  obtain ⟨γ, hγmem, hγsum⟩ := intermediate_value_Icc' haz hcont ⟨hgz.le, hga⟩
  have hanti : ∀ {x y : ℝ}, (∀ b, 0 < d b + x) → x < y → g y < g x := by
    intro x y hx hxy
    apply sum_lt_sum_of_nonempty univ_nonempty
    intro b _
    exact div_lt_div_of_pos_left (hc b) (hx b) (by linarith)
  refine ⟨γ, ⟨hden γ hγmem.1, hγsum⟩, ?_⟩
  intro y hy
  rcases lt_trichotomy y γ with hlt | heq | hgt
  · have h := hanti hy.1 hlt
    have hyone : g y = 1 := hy.2
    linarith
  · exact heq
  · have h := hanti (hden γ hγmem.1) hgt
    have hyone : g y = 1 := hy.2
    linarith

omit [DecidableEq ι] in
/-- **The `π` update is the unique maximizer** of `piObjective c d` over the positive
probability vectors: with `γ` as in `existsUnique_lagrange`, every other positive `π` summing to
one has a strictly smaller objective than `b ↦ c b / (d b + γ)`. -/
theorem piObjective_lt {c d : ι → ℝ} {γ : ℝ} (hc : ∀ b, 0 < c b) (hγ : ∀ b, 0 < d b + γ)
    (hsum : ∑ b, c b / (d b + γ) = 1) {π : ι → ℝ} (hπ : ∀ b, 0 < π b) (hπs : ∑ b, π b = 1)
    (hne : π ≠ fun b => c b / (d b + γ)) :
    piObjective c d π < piObjective c d (fun b => c b / (d b + γ)) := by
  classical
  let q : ι → ℝ := fun b => c b / (d b + γ)
  have hq : ∀ b, 0 < q b := fun b => div_pos (hc b) (hγ b)
  have halg : ∀ b, c b * (π b / q b - 1) = (d b + γ) * (π b - q b) := by
    intro b
    dsimp [q]
    field_simp [ne_of_gt (hc b), ne_of_gt (hγ b)]
  have hle : ∀ b, c b * log (π b) - d b * π b ≤
      (c b * log (q b) - d b * q b) + γ * (π b - q b) := by
    intro b
    have h := mul_le_mul_of_nonneg_left
      (log_le_sub_one_of_pos (div_pos (hπ b) (hq b))) (hc b).le
    rw [log_div (ne_of_gt (hπ b)) (ne_of_gt (hq b)), halg b] at h
    nlinarith
  obtain ⟨b₀, hb₀⟩ := Function.ne_iff.mp hne
  have hratio : π b₀ / q b₀ ≠ 1 := by
    intro h
    apply hb₀
    exact (div_eq_one_iff_eq (ne_of_gt (hq b₀))).mp h
  have hlt : c b₀ * log (π b₀) - d b₀ * π b₀ <
      (c b₀ * log (q b₀) - d b₀ * q b₀) + γ * (π b₀ - q b₀) := by
    have h := mul_lt_mul_of_pos_left
      (log_lt_sub_one_of_pos (div_pos (hπ b₀) (hq b₀)) hratio) (hc b₀)
    rw [log_div (ne_of_gt (hπ b₀)) (ne_of_gt (hq b₀)), halg b₀] at h
    nlinarith
  have hstrict := sum_lt_sum (fun b _ => hle b) ⟨b₀, mem_univ b₀, hlt⟩
  have hqsum : ∑ b, q b = 1 := hsum
  have hdiff : (∑ b, (π b - q b)) = 0 := by
    rw [sum_sub_distrib, hπs, hqsum]
    ring
  have hcancel : (∑ b, ((c b * log (q b) - d b * q b) + γ * (π b - q b))) =
      ∑ b, (c b * log (q b) - d b * q b) := by
    rw [sum_add_distrib, ← mul_sum, hdiff]
    ring
  rw [hcancel] at hstrict
  exact hstrict

/-- **The SiPhy constraint-vector update** (Eq. 8, for fixed `ω`):
`π b = c b / (ω e b + γ)`, with `γ` the Lagrange multiplier of `existsUnique_lagrange`. -/
noncomputable def piUpdate [Nonempty ι] (n : Matrix ι ι ℝ) (τ r : ι → ℝ) (ω : ℝ)
    (R : Matrix ι ι ℝ) (hc : ∀ b, 0 < inCount n r b) (hd : ∀ b, 0 ≤ ω * exitWeight τ R b)
    (b : ι) : ℝ :=
  inCount n r b / (ω * exitWeight τ R b + (existsUnique_lagrange hc hd).exists.choose)

/-- **The constraint-vector update is the unique maximizer of Eq. 6** over the positive
probability vectors `π` (the rate matrix `ω R π` and the root distribution both use `π`), for
fixed `ω > 0`, positive off-diagonal `R` and positive weights `c`. -/
theorem expectedLogLik_lt_piUpdate [Nonempty ι] (n : Matrix ι ι ℝ) (τ r : ι → ℝ) {ω : ℝ}
    {R : Matrix ι ι ℝ} (hω : 0 < ω) (hR : ∀ a b, a ≠ b → 0 < R a b)
    (hc : ∀ b, 0 < inCount n r b) (hd : ∀ b, 0 ≤ ω * exitWeight τ R b) {π : ι → ℝ}
    (hπ : ∀ b, 0 < π b) (hπs : ∑ b, π b = 1) (hne : π ≠ piUpdate n τ r ω R hc hd) :
    expectedLogLik n τ r (siphyRate ω R π) π <
      expectedLogLik n τ r (siphyRate ω R (piUpdate n τ r ω R hc hd))
        (piUpdate n τ r ω R hc hd) := by
  obtain ⟨hγ, hsum⟩ := (existsUnique_lagrange hc hd).exists.choose_spec
  have hpos : ∀ b, 0 < piUpdate n τ r ω R hc hd b := fun b => div_pos (hc b) (hγ b)
  rw [expectedLogLik_siphyRate n τ r hω hR hπ, expectedLogLik_siphyRate n τ r hω hR hpos]
  have := piObjective_lt hc hγ hsum hπ hπs hne
  unfold piUpdate at this ⊢
  linarith

end MathlibExt.Biology.Phylogenetics.SiPhy
