/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.CoalescentFStatistics

/-!
# f-statistics see only the centred leaf covariance

For allele frequencies `p : P → Ω → ℝ` of finitely many populations, let
`p̄ ω = (1 / n) ∑ X, p X ω` be the mean frequency across the populations at outcome `ω`, and
let the centred leaf covariance be

  `K X Y = 𝔼[(p X - p̄) * (p Y - p̄)]` (`centredCov`),

the second-moment matrix of the frequencies centred across populations (at each outcome, the mean
over populations is subtracted, as in a principal component analysis of population frequencies; no
centring over loci is involved, so `K` is not a covariance over `Ω`). Peter (2016) discusses the
interpretation of `f2` through covariances. The `f2` matrix and `K` determine each other:
`f2 X Y = K X X + K Y Y - 2 K X Y` (`f2_eq_centredCov`) and, conversely, `K` is half the double
centring of the `f2` matrix (`centredCov_eq_doubleCenter_f2`; this is the classical-scaling
identity of Torgerson and Gower for squared distances). Since every f-statistic is a linear
combination of `f2` statistics, two frequency models have the same f-statistics if and only if
they have the same centred leaf covariance (`f2_eq_iff_centredCov_eq`): f-statistics see a model
only through `K`.

Different admixture graphs can therefore have exactly the same f-statistics (Maier et al.
2023 document, for real data, many alternative graphs that fit about as well as published
ones). We give an explicit pair on
three populations: if `C` is an `α : 1 - α` mixture of `A` and `B` followed by private drift
`c`, with `A` and `B` on edges of drift lengths `a` and `b` from the root, then the star tree
with leaf edges `(1 - α)(a + b)`, `α (a + b)` and `c - α (1 - α)(a + b)` has the same `f2`, hence
the same `f3` and `f4`, at every pair of populations (`f2_star_eq_f2_admix`,
`f4_star_eq_f4_admix`). Its edge lengths are nonnegative exactly when
`f3 C A B = c - α (1 - α)(a + b) ≥ 0`, i.e. when post-admixture drift masks the admixture
(`starLen_nonneg`). This explicit pair is our construction.

## Main results

* `centredCov`, `centredCov_comm`, `sum_centredCov_eq_zero`, `f2_eq_centredCov`,
  `centredCov_eq_doubleCenter_f2`, `f2_eq_iff_centredCov_eq`.
* `starWeight`, `admixWeight`, `starLen`: the tree and admixture models on three populations;
  `hasBinaryLoadings_star`, `not_hasBinaryLoadings_admix`, `admixWeight_two`.
* `f2_star_eq_f2_admix`, `f4_star_eq_f4_admix`, `starLen_nonneg`: the f-indistinguishable
  pair.

## References

* W. S. Torgerson, *Multidimensional scaling: I. Theory and method*, Psychometrika 17 (1952),
  401–419.
* J. C. Gower, *Some distance properties of latent root and vector methods used in multivariate
  analysis*, Biometrika 53 (1966), 325–338.
* B. M. Peter, *Admixture, population structure, and F-statistics*, Genetics 202 (2016),
  1485–1501.
* R. Maier, P. Flegontov, O. Flegontova, U. Işıldak, P. Changmai, D. Reich, *On the limits of
  fitting complex models of population history to f-statistics*, eLife 12 (2023), e85492.
-/

@[expose] public section

open MeasureTheory MathlibExt.Biology.PopulationGenetics.FStatistics
  MathlibExt.Biology.PopulationGenetics.CoalescentFStatistics

namespace MathlibExt.Biology.PopulationGenetics.FStatisticsCovariance

section Covariance

variable {Ω P : Type*} {m : MeasurableSpace Ω} [Fintype P]

/-- The mean frequency `p̄ ω = (1 / n) ∑ X, p X ω` across the `n` populations. -/
noncomputable def popMean (p : P → Ω → ℝ) (ω : Ω) : ℝ := (∑ X, p X ω) / Fintype.card P

/-- The centred leaf covariance `K X Y = 𝔼[(p X - p̄) * (p Y - p̄)]`: the second moments of the
frequencies centred across populations (not over `Ω`). -/
noncomputable def centredCov (μ : Measure Ω) (p : P → Ω → ℝ) (X Y : P) : ℝ :=
  ∫ ω, (p X ω - popMean p ω) * (p Y ω - popMean p ω) ∂μ

variable {μ : Measure Ω} {p : P → Ω → ℝ}

private theorem memLp_sub_popMean (hp : ∀ X, MemLp (p X) 2 μ) (X : P) :
    MemLp (fun ω => p X ω - popMean p ω) 2 μ := by
  have h : MemLp (fun ω => ∑ Z, p Z ω) 2 μ := memLp_finsetSum Finset.univ fun Z _ => hp Z
  have e : (fun ω => popMean p ω) = fun ω => (Fintype.card P : ℝ)⁻¹ * ∑ Z, p Z ω := by
    funext ω
    rw [popMean, div_eq_inv_mul]
  have h2 : MemLp (fun ω => popMean p ω) 2 μ := by
    rw [e]
    exact h.const_mul _
  exact (hp X).sub h2

private theorem integrable_centred (hp : ∀ X, MemLp (p X) 2 μ) (X Y : P) :
    Integrable (fun ω => (p X ω - popMean p ω) * (p Y ω - popMean p ω)) μ :=
  (memLp_sub_popMean hp X).integrable_mul (memLp_sub_popMean hp Y)

/-- The centred leaf covariance is symmetric in the two populations. -/
theorem centredCov_comm (X Y : P) : centredCov μ p X Y = centredCov μ p Y X := by
  unfold centredCov
  congr 1 with ω
  ring

/-- For square-integrable frequencies, each row of the centred leaf covariance sums to zero:
centring across populations makes `∑ Y, K X Y = 𝔼[(p X - p̄) * ∑ Y, (p Y - p̄)] = 0`. -/
theorem sum_centredCov_eq_zero (hp : ∀ X, MemLp (p X) 2 μ) (X : P) :
    ∑ Y, centredCov μ p X Y = 0 := by
  have : Nonempty P := ⟨X⟩
  have hn : (Fintype.card P : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold centredCov
  rw [← integral_finsetSum _ fun Y _ => integrable_centred hp X Y]
  have h0 : ∀ ω, ∑ Y, (p X ω - popMean p ω) * (p Y ω - popMean p ω) = 0 := fun ω => by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, popMean, mul_div_cancel₀ _ hn, sub_self, mul_zero]
  simp_rw [h0, integral_zero]

/-- `f2` from the centred leaf covariance: `f2 X Y = K X X + K Y Y - 2 K X Y`. -/
theorem f2_eq_centredCov (hp : ∀ X, MemLp (p X) 2 μ) (X Y : P) :
    f2 μ p X Y = centredCov μ p X X + centredCov μ p Y Y - 2 * centredCov μ p X Y := by
  unfold f2 centredCov
  have h : ∀ ω, (p X ω - p Y ω) ^ 2 =
      (p X ω - popMean p ω) * (p X ω - popMean p ω) +
        (p Y ω - popMean p ω) * (p Y ω - popMean p ω) -
        2 * ((p X ω - popMean p ω) * (p Y ω - popMean p ω)) := fun ω => by ring
  simp_rw [h]
  have i1 : Integrable (fun ω => (p X ω - popMean p ω) * (p X ω - popMean p ω) +
      (p Y ω - popMean p ω) * (p Y ω - popMean p ω)) μ :=
    (integrable_centred hp X X).add (integrable_centred hp Y Y)
  rw [integral_sub i1 ((integrable_centred hp X Y).const_mul 2),
    integral_add (integrable_centred hp X X) (integrable_centred hp Y Y), integral_const_mul]

/-- The centred leaf covariance from `f2`: `K` is half the double centring of the `f2` matrix,
`K X Y = (f̄2 X· + f̄2 ·Y - f2 X Y - f̄2 ··) / 2`. -/
theorem centredCov_eq_doubleCenter_f2 (hp : ∀ X, MemLp (p X) 2 μ) (X Y : P) :
    centredCov μ p X Y = doubleCenter (f2 μ p) X Y / 2 := by
  have : Nonempty P := ⟨X⟩
  have hn : (Fintype.card P : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hrow : ∑ k, f2 μ p X k = Fintype.card P * centredCov μ p X X + ∑ k, centredCov μ p k k := by
    simp_rw [f2_eq_centredCov hp X, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, sum_centredCov_eq_zero hp X, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    ring
  have hcol : ∑ k, f2 μ p k Y = ∑ k, centredCov μ p k k + Fintype.card P * centredCov μ p Y Y := by
    have : ∀ k, f2 μ p k Y =
        centredCov μ p k k + centredCov μ p Y Y - 2 * centredCov μ p Y k := fun k => by
      rw [f2_eq_centredCov hp k Y, centredCov_comm k Y]
    simp_rw [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_centredCov_eq_zero hp Y, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have hall : ∑ k, ∑ l, f2 μ p k l = 2 * Fintype.card P * ∑ k, centredCov μ p k k := by
    have : ∀ k, ∑ l, f2 μ p k l =
        Fintype.card P * centredCov μ p k k + ∑ k, centredCov μ p k k := fun k => by
      simp_rw [f2_eq_centredCov hp k, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, sum_centredCov_eq_zero hp k, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      ring
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    ring
  unfold doubleCenter
  rw [hrow, hcol, hall, f2_eq_centredCov hp X Y]
  field_simp
  ring

/-- f-statistics see a model only through its centred leaf covariance: two square-integrable
frequency models have the same `f2` at every pair (hence the same `f3` and `f4`, by `f3_eq_f2`
and `f4_eq_f2`) if and only if they have the same centred leaf covariance. -/
theorem f2_eq_iff_centredCov_eq {Ω' : Type*} {m' : MeasurableSpace Ω'} {μ' : Measure Ω'}
    {p' : P → Ω' → ℝ} (hp : ∀ X, MemLp (p X) 2 μ) (hp' : ∀ X, MemLp (p' X) 2 μ') :
    (∀ X Y, f2 μ p X Y = f2 μ' p' X Y) ↔ ∀ X Y, centredCov μ p X Y = centredCov μ' p' X Y := by
  constructor
  · intro h X Y
    have hf : f2 μ p = f2 μ' p' := funext fun X => funext fun Y => h X Y
    rw [centredCov_eq_doubleCenter_f2 hp, centredCov_eq_doubleCenter_f2 hp', hf]
  · intro h X Y
    rw [f2_eq_centredCov hp, f2_eq_centredCov hp', h, h, h]

end Covariance

/-! ### An f-indistinguishable pair: a star tree and an admixture -/

section Pair

/-- Lineage weights of the star tree on three populations `0 = A`, `1 = B`, `2 = C`: edge `e`
is the leaf edge of population `e`. -/
def starWeight : Fin 3 → Fin 3 → ℝ := fun X e => if X = e then 1 else 0

/-- Lineage weights of the admixture model: `A` and `B` sit on edges `0` and `1`, and `C` is an
`α : 1 - α` mixture of `A` and `B` followed by drift on its private edge `2`. -/
def admixWeight (α : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun X e => if X = 2 then ![α, 1 - α, 1] e else starWeight X e

/-- Edge lengths of the star tree matching the admixture model with edge lengths `a`, `b`, `c`:
`(1 - α)(a + b)`, `α (a + b)` and `c - α (1 - α)(a + b)`. -/
def starLen (α a b c : ℝ) : Fin 3 → ℝ :=
  ![(1 - α) * (a + b), α * (a + b), c - α * (1 - α) * (a + b)]

/-- In the admixture model, `C` is the `α : 1 - α` mixture of `A` and `B` plus its private
edge. -/
theorem admixWeight_two (α : ℝ) :
    admixWeight α 2 = α • admixWeight α 0 + (1 - α) • admixWeight α 1 + Pi.single 2 1 := by
  funext e
  fin_cases e <;> simp [admixWeight, starWeight]

variable {Ω Ω' : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'} {μ : Measure Ω}
  {μ' : Measure Ω'}

/-- The star-tree model has binary loadings. -/
theorem hasBinaryLoadings_star {M : DriftModel μ (Fin 3) (Fin 3)} (hw : M.weight = starWeight) :
    M.HasBinaryLoadings := by
  intro X e
  rw [hw]
  unfold starWeight
  split_ifs <;> simp

/-- For `α ∉ {0, 1}` the admixture model does not have binary loadings. -/
theorem not_hasBinaryLoadings_admix {α : ℝ} (h0 : α ≠ 0) (h1 : α ≠ 1)
    {M : DriftModel μ (Fin 3) (Fin 3)} (hw : M.weight = admixWeight α) :
    ¬ M.HasBinaryLoadings := by
  intro hM
  rcases hM 2 0 with h | h <;> simp [hw, admixWeight] at h <;> contradiction

/-- The star tree and the admixture model have the same `f2` at every pair of populations. -/
theorem f2_star_eq_f2_admix {α a b c : ℝ} {M : DriftModel μ (Fin 3) (Fin 3)}
    {M' : DriftModel μ' (Fin 3) (Fin 3)} (hw : M.weight = starWeight)
    (hl : M.len = starLen α a b c) (hw' : M'.weight = admixWeight α) (hl' : M'.len = ![a, b, c])
    (X Y : Fin 3) : f2 μ M.freq X Y = f2 μ' M'.freq X Y := by
  rw [M.f2_freq, M'.f2_freq, hw, hl, hw', hl']
  fin_cases X <;> fin_cases Y <;>
    simp [starWeight, admixWeight, starLen, Fin.sum_univ_three] <;> ring

/-- The star tree and the admixture model have the same `f4` (hence the same `f3`) at every
quadruple of populations. -/
theorem f4_star_eq_f4_admix {α a b c : ℝ} {M : DriftModel μ (Fin 3) (Fin 3)}
    {M' : DriftModel μ' (Fin 3) (Fin 3)} (hw : M.weight = starWeight)
    (hl : M.len = starLen α a b c) (hw' : M'.weight = admixWeight α) (hl' : M'.len = ![a, b, c])
    (A B C D : Fin 3) : f4 μ M.freq A B C D = f4 μ' M'.freq A B C D := by
  rw [f4_eq_f2 M.memLp_freq, f4_eq_f2 M'.memLp_freq]
  simp only [f2_star_eq_f2_admix hw hl hw' hl']

/-- The matching star tree has nonnegative edge lengths when `0 ≤ α ≤ 1`, `a, b ≥ 0`, and the
private drift of `C` is at least `α (1 - α)(a + b)`, i.e. when `f3 C A B ≥ 0` in the admixture
model. -/
theorem starLen_nonneg {α a b c : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : α * (1 - α) * (a + b) ≤ c) (e : Fin 3) : 0 ≤ starLen α a b c e := by
  fin_cases e
  · change 0 ≤ (1 - α) * (a + b)
    exact mul_nonneg (by linarith) (by linarith)
  · change 0 ≤ α * (a + b)
    exact mul_nonneg hα0 (by linarith)
  · change 0 ≤ c - α * (1 - α) * (a + b)
    linarith

end Pair

variable {Ω Ω' : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'} {μ : Measure Ω}
  {μ' : Measure Ω'}

/-- The star tree (weights `starWeight`, lengths `starLen α a b c`) and the admixture model
(weights `admixWeight α`, lengths `![a, b, c]`) have the same `f3` at every triple of
populations. -/
theorem f3_star_eq_f3_admix {α a b c : ℝ} {M : DriftModel μ (Fin 3) (Fin 3)}
    {M' : DriftModel μ' (Fin 3) (Fin 3)} (hw : M.weight = starWeight)
    (hl : M.len = starLen α a b c) (hw' : M'.weight = admixWeight α) (hl' : M'.len = ![a, b, c])
    (C A B : Fin 3) : f3 μ M.freq C A B = f3 μ' M'.freq C A B := by
  rw [f3_eq_f4, f3_eq_f4]
  exact f4_star_eq_f4_admix hw hl hw' hl' C A C B

/-- At `α = 0` the admixture model degenerates to the matching star tree: for every drift model
with weights `admixWeight 0` and lengths `![a, b, c]` there is, on the same measure space, a
star-tree drift model with weights `starWeight` and lengths `starLen 0 a b c` (that is,
`![a + b, 0, c]`) whose population frequencies are exactly the same functions. -/
theorem exists_star_freq_eq_of_admix_zero {a b c : ℝ} (M : DriftModel μ (Fin 3) (Fin 3))
    (hw : M.weight = admixWeight 0) (hl : M.len = ![a, b, c]) :
    ∃ M' : DriftModel μ (Fin 3) (Fin 3), M'.weight = starWeight ∧ M'.len = starLen 0 a b c ∧
      M'.freq = M.freq := by
  have hi : ∀ e f : Fin 3, Integrable (fun ω => M.incr e ω * M.incr f ω) μ := fun e f =>
    (M.memLp_incr e).integrable_mul (M.memLp_incr f)
  have h01 : ∫ ω, M.incr 0 ω * M.incr 1 ω ∂μ = 0 := M.inner_incr 0 1 (by decide)
  have h02 : ∫ ω, M.incr 0 ω * M.incr 2 ω ∂μ = 0 := M.inner_incr 0 2 (by decide)
  have h12 : ∫ ω, M.incr 1 ω * M.incr 2 ω ∂μ = 0 := M.inner_incr 1 2 (by decide)
  have hl0 : ∫ ω, M.incr 0 ω ^ 2 ∂μ = a := by rw [M.sq_incr, hl]; rfl
  have hl1 : ∫ ω, M.incr 1 ω ^ 2 ∂μ = b := by rw [M.sq_incr, hl]; rfl
  have hl2 : ∫ ω, M.incr 2 ω ^ 2 ∂μ = c := by rw [M.sq_incr, hl]; rfl
  have hsq : ∀ e : Fin 3, Integrable (fun ω => M.incr e ω ^ 2) μ := fun e =>
    (M.memLp_incr e).integrable_sq
  have hd0 : ∫ ω, (M.incr 0 ω - M.incr 1 ω) * M.incr 2 ω ∂μ = 0 := by
    simp_rw [sub_mul]
    rw [integral_sub (hi 0 2) (hi 1 2), h02, h12, sub_zero]
  have hdd : ∫ ω, (M.incr 0 ω - M.incr 1 ω) * (M.incr 0 ω - M.incr 1 ω) ∂μ = a + b := by
    have e1 : ∀ ω, (M.incr 0 ω - M.incr 1 ω) * (M.incr 0 ω - M.incr 1 ω) =
        M.incr 0 ω ^ 2 + M.incr 1 ω ^ 2 - 2 * (M.incr 0 ω * M.incr 1 ω) := fun ω => by ring
    have hsum : Integrable (fun ω => M.incr 0 ω ^ 2 + M.incr 1 ω ^ 2) μ := (hsq 0).add (hsq 1)
    have hcross : Integrable (fun ω => 2 * (M.incr 0 ω * M.incr 1 ω)) μ := (hi 0 1).const_mul 2
    simp_rw [e1]
    rw [integral_sub hsum hcross, integral_add (hsq 0) (hsq 1), integral_const_mul, hl0, hl1, h01]
    ring
  refine ⟨{ root := fun ω => M.root ω + M.incr 1 ω
            incr := ![fun ω => M.incr 0 ω - M.incr 1 ω, fun _ => 0, M.incr 2]
            len := starLen 0 a b c
            weight := starWeight
            memLp_root := M.memLp_root.add (M.memLp_incr 1)
            memLp_incr := ?_
            inner_incr := ?_
            sq_incr := ?_ }, rfl, rfl, ?_⟩
  · intro e
    fin_cases e
    · exact (M.memLp_incr 0).sub (M.memLp_incr 1)
    · exact MemLp.zero'
    · exact M.memLp_incr 2
  · intro e f hef
    fin_cases e <;> fin_cases f <;> simp at hef ⊢
    · exact hd0
    · simp_rw [mul_comm (M.incr 2 _)]
      exact hd0
  · intro e
    fin_cases e
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, starLen]
      rw [show (fun ω => (M.incr 0 ω - M.incr 1 ω) ^ 2) =
          fun ω => (M.incr 0 ω - M.incr 1 ω) * (M.incr 0 ω - M.incr 1 ω) from
          funext fun ω => sq _, hdd]
      ring
    · simp [starLen]
    · simp [starLen, hl2]
  · funext X ω
    fin_cases X
    · simp [DriftModel.freq, hw, admixWeight, starWeight]
    · simp [DriftModel.freq, hw, admixWeight, starWeight]
    · simp [DriftModel.freq, hw, admixWeight, starWeight, Fin.sum_univ_three]
      ring

end MathlibExt.Biology.PopulationGenetics.FStatisticsCovariance
