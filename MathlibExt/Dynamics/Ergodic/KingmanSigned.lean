/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Dynamics.Ergodic.KingmanSigned.Filling

/-!
# Kingman's subadditive ergodic theorem

Let `T` preserve a finite measure `μ` and let `X` be a subadditive cocycle over `T`: integrable
functions with `X (m + n) ≤ X m + X n ∘ T^m` almost everywhere. If the time constant is finite,
i.e. `inf_n (∫ X n dμ) / n > -∞`, then `X n / n` converges almost everywhere to a finite limit.
No sign condition on `X` is assumed.

The signed case reduces to the nonnegative one. With the additive cocycle
`addCoc n = ∑_{k<n} X 1 ∘ T^k`, the defect `Zc n = addCoc n - X n` is nonnegative a.e., and for
every level `M` the truncation `Vc M n = (M n - Zc n)⁺` is a nonnegative subadditive cocycle, so
`Vc M n / n = M - min (Zc n / n) M` converges by the nonnegative theorem
(`StatMech.KingmanFilling.tendsto_div_kingmanLimit_ae_of_nonneg`). Fatou's lemma and the bound
on the time constant make `liminf Zc n / n` finite a.e., so `Zc n / n` converges; `addCoc n / n`
converges by Birkhoff's theorem, and hence so does `X n / n`.

## Main definitions

* `StatMech.KingmanSigned.addCoc T X`: the additive cocycle of `X 1`.
* `StatMech.KingmanSigned.Zc`, `StatMech.KingmanSigned.Wc`: the defect `addCoc - X` and its
  negative.
* `StatMech.KingmanSigned.Sc`, `StatMech.KingmanSigned.Vc`: the shifted defect `M n - Zc n` and
  its positive part.

## Main results

* `StatMech.KingmanSigned.kingman_ae_general`: Kingman's subadditive ergodic theorem.
* `StatMech.KingmanSigned.exists_invariant_limit_of_nonneg`: for nonnegative cocycles, the limit
  is integrable and invariant; this contains
  `MathlibExt.Dynamics.Ergodic.KingmanWanted.kingman_subadditive`.

## References

* J. F. C. Kingman, *The ergodic theory of subadditive stochastic processes*, J. Roy. Statist.
  Soc. Ser. B 30 (1968), 499–510.
* J. M. Steele, *Kingman's subadditive ergodic theorem*, Ann. Inst. H. Poincaré Probab.
  Statist. 25 (1989), 93–98.
-/

@[expose] public section

open MeasureTheory Filter Topology ENNReal

namespace StatMech

namespace KingmanSigned

open Kingman BirkhoffAE KingmanAE KingmanFilling

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {X : ℕ → α → ℝ}

/-- The additive cocycle `n ↦ ∑_{k<n} X 1 ∘ T^[k]` (the Birkhoff sums of `X 1`). -/
noncomputable def addCoc (T : α → α) (X : ℕ → α → ℝ) (n : ℕ) (x : α) : ℝ :=
  birkhoffSum T (X 1) n x

/-- The subadditivity defect `addCoc n - X n` (`0` at `n = 0`); it is nonnegative a.e. -/
noncomputable def Zc (T : α → α) (X : ℕ → α → ℝ) (n : ℕ) (x : α) : ℝ :=
  if n = 0 then 0 else addCoc T X n x - X n x

/-- The negative defect `X n - addCoc n` (`0` at `n = 0`), a nonpositive subadditive cocycle. -/
noncomputable def Wc (T : α → α) (X : ℕ → α → ℝ) (n : ℕ) (x : α) : ℝ :=
  if n = 0 then 0 else X n x - addCoc T X n x

omit [MeasurableSpace α] in
theorem addCoc_add (m n : ℕ) (x : α) :
    addCoc T X (m + n) x = addCoc T X m x + addCoc T X n (T^[m] x) :=
  birkhoffSum_add_right_apply T (X 1) m n x

omit [MeasurableSpace α] in
theorem Wc_eq_neg (n : ℕ) (x : α) : Wc T X n x = - Zc T X n x := by
  unfold Wc Zc; rcases eq_or_ne n 0 with hn | hn
  · simp [hn]
  · simp only [ite_eq_right hn]; ring

omit [MeasurableSpace α] in
theorem Zc_one (x : α) : Zc T X 1 x = 0 := by
  unfold Zc addCoc; simp [birkhoffSum_one]

omit [MeasurableSpace α] in
theorem Zc_div_eq {n : ℕ} (hn : 1 ≤ n) (x : α) :
    Zc T X n x / n = (addCoc T X n x - X n x) / n := by
  unfold Zc; rw [ite_eq_right (by omega)]

theorem integrable_addCoc (h : SubadditiveCocycle T μ X) (n : ℕ) :
    Integrable (addCoc T X n) μ :=
  MathlibExt.Probability.BirkhoffErgodicL1.integrable_birkhoffSum_of_measurePreserving
    h.measurePreserving (h.integrable 1) n

theorem integrable_Wc (h : SubadditiveCocycle T μ X) (n : ℕ) :
    Integrable (Wc T X n) μ := by
  unfold Wc
  rcases eq_or_ne n 0 with hn | hn
  · simp [hn]
  · simp only [ite_eq_right hn]
    exact (h.integrable n).sub (integrable_addCoc h n)

theorem integrable_Zc (h : SubadditiveCocycle T μ X) (n : ℕ) :
    Integrable (Zc T X n) μ := by
  have := integrable_Wc h n
  rw [show Zc T X n = fun x => - Wc T X n x by funext x; rw [Wc_eq_neg]; ring]
  exact this.neg

/-- The negative defect is a subadditive cocycle. -/
theorem Wc_subaddCocycle (h : SubadditiveCocycle T μ X) : SubadditiveCocycle T μ (Wc T X) := by
  refine ⟨h.measurePreserving, integrable_Wc h, ?_⟩
  intro m n
  filter_upwards [h.subadditive m n] with x hx
  rcases eq_or_ne m 0 with hm | hm
  · subst hm
    rcases eq_or_ne n 0 with hn | hn
    · subst hn; simp [Wc]
    · have h0 : Wc T X 0 x = 0 := by simp [Wc]
      simp only [h0, zero_add, Function.iterate_zero, id, le_refl]
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    have h0 : Wc T X 0 (T^[m] x) = 0 := by simp [Wc]
    simp only [h0, add_zero, le_refl]
  have hmn : m + n ≠ 0 := by omega
  simp only [Wc, ite_eq_right hm, ite_eq_right hn, ite_eq_right hmn, addCoc_add]
  linarith [hx]

theorem Wc_nonpos_ae (h : SubadditiveCocycle T μ X) {n : ℕ} (hn : 1 ≤ n) : Wc T X n ≤ᵐ[μ] 0 := by
  filter_upwards [h.ae_le_birkhoffSum] with x hx
  simp only [Wc, ite_eq_right (by omega : n ≠ 0), addCoc, Pi.zero_apply]
  linarith [hx n hn]

theorem Zc_nonneg_ae (h : SubadditiveCocycle T μ X) {n : ℕ} (hn : 1 ≤ n) : 0 ≤ᵐ[μ] Zc T X n := by
  filter_upwards [Wc_nonpos_ae h hn] with x hx
  rw [Wc_eq_neg] at hx; simp only [Pi.zero_apply] at hx ⊢; linarith

theorem Zc_nonneg_ae_all (h : SubadditiveCocycle T μ X) (n : ℕ) : 0 ≤ᵐ[μ] Zc T X n := by
  rcases eq_or_ne n 0 with hn | hn
  · subst hn; filter_upwards with x; simp [Zc]
  · exact Zc_nonneg_ae h (by omega)

/-- The shifted defect `X n + M n - addCoc n`, a subadditive cocycle for every `M`. -/
noncomputable def Sc (T : α → α) (X : ℕ → α → ℝ) (M : ℝ) (n : ℕ) (x : α) : ℝ :=
  X n x + (M * n - addCoc T X n x)

/-- The truncated defect `(Sc M n)⁺ = (M n - Zc n)⁺`, a nonnegative subadditive cocycle. -/
noncomputable def Vc (T : α → α) (X : ℕ → α → ℝ) (M : ℝ) (n : ℕ) (x : α) : ℝ :=
  (Sc T X M n x)⁺

omit [MeasurableSpace α] in
theorem Sc_eq_sub (M : ℝ) {n : ℕ} (hn : 1 ≤ n) (x : α) :
    Sc T X M n x = M * n - Zc T X n x := by
  unfold Sc Zc; rw [ite_eq_right (by omega)]; ring

omit [MeasurableSpace α] in
theorem Vc_nonneg (M : ℝ) (n : ℕ) (x : α) : 0 ≤ Vc T X M n x := le_max_right _ _

variable [IsFiniteMeasure μ]

theorem integrable_Sc (h : SubadditiveCocycle T μ X) (M : ℝ) (n : ℕ) :
    Integrable (Sc T X M n) μ := by
  unfold Sc
  exact (h.integrable n).add ((integrable_const (M * n)).sub (integrable_addCoc h n))

theorem integrable_Vc (h : SubadditiveCocycle T μ X) (M : ℝ) (n : ℕ) :
    Integrable (Vc T X M n) μ := (integrable_Sc h M n).pos_part

/-- The truncated defect is a nonnegative subadditive cocycle. -/
theorem Vc_subaddCocycle (h : SubadditiveCocycle T μ X) (M : ℝ) :
    SubadditiveCocycle T μ (Vc T X M) := by
  refine ⟨h.measurePreserving, integrable_Vc h M, ?_⟩
  intro m n
  filter_upwards [h.subadditive m n] with x hx
  have hS : Sc T X M (m + n) x ≤ Sc T X M m x + Sc T X M n (T^[m] x) := by
    unfold Sc
    rw [addCoc_add]
    push_cast
    linarith [hx]
  unfold Vc
  rcases le_total (Sc T X M (m + n) x) 0 with hle | hle
  · rw [posPart_eq_zero.mpr hle]
    have : (0 : ℝ) ≤ (Sc T X M m x)⁺ + (Sc T X M n (T^[m] x))⁺ := by positivity
    linarith
  · rw [posPart_eq_self.mpr hle]
    nlinarith [le_posPart (Sc T X M m x), le_posPart (Sc T X M n (T^[m] x)),
      posPart_nonneg (Sc T X M m x), posPart_nonneg (Sc T X M n (T^[m] x))]

omit [MeasurableSpace α] [IsFiniteMeasure μ] in
theorem Vc_div_eq (M : ℝ) {n : ℕ} (hn : 1 ≤ n) (x : α) :
    Vc T X M n x / n = M - min (Zc T X n x / n) M := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold Vc
  rw [Sc_eq_sub M hn]
  rcases le_total (Zc T X n x / n) M with hle | hle
  · rw [min_eq_left hle]
    have hge : (0 : ℝ) ≤ M * n - Zc T X n x := by rw [div_le_iff₀ hn0] at hle; nlinarith
    rw [posPart_eq_self.mpr hge]; field_simp
  · rw [min_eq_right hle]
    have hle' : M * n - Zc T X n x ≤ 0 := by rw [le_div_iff₀ hn0] at hle; nlinarith
    rw [posPart_eq_zero.mpr hle']; ring

omit [IsFiniteMeasure μ] in
theorem integral_addCoc_eq (h : SubadditiveCocycle T μ X) (n : ℕ) :
    ∫ x, addCoc T X n x ∂μ = n * ∫ x, X 1 x ∂μ := by
  unfold addCoc; simp only [birkhoffSum]
  rw [integral_finsetSum]
  · rw [Finset.sum_congr rfl (fun i _ => Kingman.integral_comp_iterate T h.measurePreserving (X 1)
      (h.integrable 1).aestronglyMeasurable i)]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  · intro i _
    exact (h.measurePreserving.iterate i).integrable_comp_of_integrable (h.integrable 1)

omit [IsFiniteMeasure μ] in
theorem integral_Zc_div (h : SubadditiveCocycle T μ X) {n : ℕ} (hn : 1 ≤ n) :
    ∫ x, Zc T X n x / n ∂μ = (∫ x, X 1 x ∂μ) - (∫ x, X n x ∂μ) / n := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [integral_div]
  unfold Zc
  simp only [ite_eq_right (by omega : n ≠ 0)]
  rw [integral_sub (integrable_addCoc h n) (h.integrable n), integral_addCoc_eq h n, sub_div,
    mul_div_cancel_left₀ _ hn0]

omit [IsFiniteMeasure μ] in
/-- If the time constant is finite, `liminf_n Zc n / n < ∞` almost everywhere (Fatou). -/
theorem ae_liminf_lt_top (h : SubadditiveCocycle T μ X)
    (hbdd : BddBelow (Set.range fun n => SubadditiveCocycle.expSeq X μ n / n)) :
    ∀ᵐ x ∂μ, liminf (fun n => ENNReal.ofReal (Zc T X n x / n)) atTop < ∞ := by
  obtain ⟨B, hB⟩ := hbdd
  set C : ℝ := ((∫ x, X 1 x ∂μ) - B) ⊔ 0 with hC
  set g : ℕ → α → ℝ≥0∞ := fun n x => ENNReal.ofReal (Zc T X n x / n) with hg
  have hgmeas : ∀ n, AEMeasurable (g n) μ := fun n =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((integrable_Zc h n).aestronglyMeasurable.aemeasurable.div_const _)
  have hnn : ∀ n, 0 ≤ᵐ[μ] fun x => Zc T X n x / n := by
    intro n; filter_upwards [Zc_nonneg_ae_all h n] with x hx
    have : (0 : ℝ) ≤ Zc T X n x := hx
    positivity
  have hbn : ∀ n, ∫ x, Zc T X n x / n ∂μ ≤ C := by
    intro n
    rcases eq_or_ne n 0 with hn | hn
    · subst hn
      have : ∫ x, Zc T X 0 x / (0 : ℕ) ∂μ = 0 := by simp
      rw [this]; exact le_sup_right
    · have hn1 : 1 ≤ n := by omega
      rw [integral_Zc_div h hn1]
      have hge : B ≤ (∫ x, X n x ∂μ) / n :=
        hB ⟨n, by simp only [SubadditiveCocycle.expSeq]⟩
      have : (∫ x, X 1 x ∂μ) - (∫ x, X n x ∂μ) / n ≤ (∫ x, X 1 x ∂μ) - B := by linarith
      exact le_trans this le_sup_left
  have hfatou : ∫⁻ x, liminf (fun n => g n x) atTop ∂μ ≤ liminf (fun n => ∫⁻ x, g n x ∂μ) atTop :=
    lintegral_liminf_le' hgmeas
  have heq : ∀ n, ∫⁻ x, g n x ∂μ = ENNReal.ofReal (∫ x, Zc T X n x / n ∂μ) := fun n => by
    rw [hg, ← ofReal_integral_eq_lintegral_ofReal ((integrable_Zc h n).div_const _) (hnn n)]
  have hbound : liminf (fun n => ∫⁻ x, g n x ∂μ) atTop ≤ ENNReal.ofReal C := by
    refine le_trans liminf_le_limsup ?_
    refine limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall (fun n => ?_))
    rw [heq n]; exact ENNReal.ofReal_le_ofReal (hbn n)
  have hltop : ∫⁻ x, liminf (fun n => g n x) atTop ∂μ < ∞ :=
    lt_of_le_of_lt (le_trans hfatou hbound) (by simp)
  exact ae_lt_top' (AEMeasurable.liminf hgmeas) hltop.ne

omit [IsFiniteMeasure μ] in
theorem core_conv (a : ℕ → ℝ) (M m : ℝ) (hconv : Tendsto (fun n => min (a n) M) atTop (𝓝 m))
    (hmM : m < M) : Tendsto a atTop (𝓝 m) := by
  have hev : ∀ᶠ n in atTop, min (a n) M < M := hconv.eventually_mem (Iio_mem_nhds hmM)
  have heq : ∀ᶠ n in atTop, a n = min (a n) M := by
    filter_upwards [hev] with n hn
    rcases le_total (a n) M with hle | hle
    · rw [min_eq_left hle]
    · rw [min_eq_right hle] at hn; exact absurd hn (lt_irrefl M)
  exact hconv.congr' (heq.mono fun n hn => hn.symm)

omit [IsFiniteMeasure μ] in
theorem pointwise_conv (a : ℕ → ℝ) (mfun : ℕ → ℝ)
    (hconv : ∀ M : ℕ, Tendsto (fun n => min (a n) (M : ℝ)) atTop (𝓝 (mfun M)))
    (hLtop : liminf (fun n => ENNReal.ofReal (a n)) atTop < ∞) :
    ∃ L : ℝ, Tendsto a atTop (𝓝 L) := by
  set Linf := liminf (fun n => ENNReal.ofReal (a n)) atTop with hLinf
  set M : ℕ := ⌈Linf.toReal⌉₊ + 1 with hM
  have hofR : ENNReal.ofReal (mfun M) ≤ Linf := by
    have hc : Tendsto (fun n => ENNReal.ofReal (min (a n) (M : ℝ))) atTop
        (𝓝 (ENNReal.ofReal (mfun M))) := (ENNReal.continuous_ofReal.tendsto _).comp (hconv M)
    rw [← hc.liminf_eq]
    exact liminf_le_liminf
      (Eventually.of_forall (fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)))
  have hmle : mfun M ≤ Linf.toReal := (ENNReal.ofReal_le_iff_le_toReal hLtop.ne).mp hofR
  have hltM : Linf.toReal < (M : ℝ) := by
    rw [hM]; push_cast; linarith [Nat.le_ceil Linf.toReal]
  exact ⟨mfun M, core_conv a (M : ℝ) (mfun M) (hconv M) (lt_of_le_of_lt hmle hltM)⟩

theorem ae_truncated_conv (h : SubadditiveCocycle T μ X) :
    ∀ᵐ x ∂μ, ∀ M : ℕ, Tendsto (fun n => min (Zc T X n x / n) (M : ℝ)) atTop
      (𝓝 ((M : ℝ) - kingmanLimit T (Vc T X (M : ℝ)) x)) := by
  rw [ae_all_iff]
  intro M
  have hV := tendsto_div_kingmanLimit_ae_of_nonneg (Vc_subaddCocycle h (M : ℝ))
    (fun n => Eventually.of_forall (fun x => Vc_nonneg (M : ℝ) n x))
  filter_upwards [hV] with x hx
  have heq : ∀ᶠ n in atTop, min (Zc T X n x / n) (M : ℝ) = (M : ℝ) - Vc T X (M : ℝ) n x / n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Vc_div_eq (M : ℝ) hn]; ring
  rw [tendsto_congr' heq]
  exact tendsto_const_nhds.sub hx

theorem ae_tendsto_Zc_div (h : SubadditiveCocycle T μ X)
    (hbdd : BddBelow (Set.range fun n => SubadditiveCocycle.expSeq X μ n / n)) :
    ∀ᵐ x ∂μ, ∃ L : ℝ, Tendsto (fun n => Zc T X n x / n) atTop (𝓝 L) := by
  filter_upwards [ae_truncated_conv h, ae_liminf_lt_top h hbdd] with x htrunc hltop
  exact pointwise_conv (fun n => Zc T X n x / n)
    (fun M => (M : ℝ) - kingmanLimit T (Vc T X (M : ℝ)) x) htrunc hltop

/-- If the time constant is finite, `X n / n` converges almost everywhere. -/
theorem ae_tendsto_X_div (h : SubadditiveCocycle T μ X)
    (hbdd : BddBelow (Set.range fun n => SubadditiveCocycle.expSeq X μ n / n)) :
    ∀ᵐ x ∂μ, ∃ L : ℝ, Tendsto (fun n => X n x / n) atTop (𝓝 L) := by
  have hbirk : ∀ᵐ x ∂μ, Tendsto (fun n => addCoc T X n x / n) atTop
      (𝓝 (birkhoffLimit T (X 1) x)) := by
    filter_upwards [tendsto_birkhoffAverage_ae h.measurePreserving (h.integrable 1)] with x hx
    have heq : ∀ n, addCoc T X n x / n = birkhoffAverage ℝ T (X 1) n x := by
      intro n; simp only [addCoc, birkhoffAverage, smul_eq_mul]; ring
    rw [show (fun n => addCoc T X n x / n) = fun n => birkhoffAverage ℝ T (X 1) n x from
      funext heq]
    exact hx
  filter_upwards [ae_tendsto_Zc_div h hbdd, hbirk] with x ⟨L, hL⟩ hA
  refine ⟨birkhoffLimit T (X 1) x - L, ?_⟩
  have heq : ∀ᶠ n in atTop, X n x / n = addCoc T X n x / n - Zc T X n x / n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Zc_div_eq hn]; ring
  rw [tendsto_congr' heq]
  exact hA.sub hL

omit [MeasurableSpace α] [IsFiniteMeasure μ] in
theorem tendsto_X_div_kingmanLimit {x : α} {L : ℝ}
    (hL : Tendsto (fun n => X n x / n) atTop (𝓝 L)) :
    Tendsto (fun n => X n x / n) atTop (𝓝 (kingmanLimit T X x)) := by
  have hE : Tendsto (fun n => ((X n x / n : ℝ) : EReal)) atTop (𝓝 ((L : ℝ) : EReal)) := by
    rw [EReal.tendsto_coe]; exact hL
  have hgs : gStar T X x = ((L : ℝ) : EReal) := by
    unfold gStar; exact hE.limsup_eq
  rw [show kingmanLimit T X x = L by rw [kingmanLimit, hgs]; simp]
  exact hL

/-- **Kingman's subadditive ergodic theorem** (J. F. C. Kingman, *The ergodic theory of
subadditive stochastic processes*, 1968): if `X` is a subadditive cocycle over a map `T`
preserving the finite measure `μ` and `inf_n (∫ X n dμ) / n > -∞`, then `X n / n` converges
`μ`-almost everywhere to the finite limit `kingmanLimit T X`. The sign of `X` is arbitrary.
Invariance and integrability of the limit, and `∫ kingmanLimit = gamma`, are not stated here; for
nonnegative cocycles see `exists_invariant_limit_of_nonneg`, which contains
`MathlibExt.Dynamics.Ergodic.KingmanWanted.kingman_subadditive`. -/
theorem kingman_ae_general (h : SubadditiveCocycle T μ X)
    (hbdd : BddBelow (Set.range fun n => SubadditiveCocycle.expSeq X μ n / n)) :
    ∀ᵐ x ∂μ, Tendsto (fun n => X n x / n) atTop (𝓝 (kingmanLimit T X x)) := by
  filter_upwards [ae_tendsto_X_div h hbdd] with x ⟨L, hL⟩
  exact tendsto_X_div_kingmanLimit hL

/-- Kingman's theorem for nonnegative cocycles, with integrable and invariant limit: if `T`
preserves the finite measure `μ` and `X` is a nonnegative integrable subadditive cocycle, then
`X n / n` converges a.e. to an integrable `T`-invariant function. This is
`MathlibExt.Dynamics.Ergodic.KingmanWanted.kingman_subadditive` without its hypotheses that each
`X n` is measurable and `X 0 = 0`, and for finite rather than probability measures. -/
theorem exists_invariant_limit_of_nonneg (hT : MeasurePreserving T μ μ)
    (hX_int : ∀ n, Integrable (X n) μ) (hX_nonneg : ∀ n, ∀ᵐ x ∂μ, 0 ≤ X n x)
    (hX_subadd : ∀ m n, ∀ᵐ x ∂μ, X (m + n) x ≤ X m x + X n (T^[m] x)) :
    ∃ g : α → ℝ, Integrable g μ ∧ (∀ᵐ x ∂μ, g (T x) = g x) ∧
      ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => X n x / (n : ℝ)) atTop (𝓝 (g x)) := by
  have h : SubadditiveCocycle T μ X := ⟨hT, hX_int, hX_subadd⟩
  have hbot : ∀ᵐ x ∂μ, ⊥ < gStar T X x := by
    filter_upwards [gStar_nonneg_ae (T := T) hX_nonneg] with x hx
    exact lt_of_lt_of_le EReal.bot_lt_zero hx
  have hint := integrable_kingmanLimit h hX_nonneg
  exact ⟨kingmanLimit T X, hint,
    kingmanLimit_comp_ae h (gStar_le_gStarLow_ae h hX_nonneg) hbot hint,
    tendsto_div_kingmanLimit_ae_of_nonneg h hX_nonneg⟩

end KingmanSigned

end StatMech
