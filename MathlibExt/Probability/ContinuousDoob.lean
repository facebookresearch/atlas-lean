/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.L2Space
import MathlibExt.Probability.DoobLpInequality
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Doob's `L²` maximal inequality in continuous time

For a square-integrable martingale `M` indexed by `ℝ≥0` with continuous paths,
`E[(sup_{0 ≤ s ≤ t} |M s|)²] ≤ 4 E[M_t²]`.

The proof is the classical reduction to discrete time. At dyadic level `n`, the values
`M(t k / 2^n)`, `k ≤ 2^n`, form a discrete martingale for the filtration `ℱ(t k / 2^n)`, so the
repository's discrete inequality (`MeasureTheory.Martingale.doob_sq_maximal_ineq`) bounds the
second moment of their running maximum by `4 E[M_t²]`. These maxima increase with `n`, their
supremum is the supremum over `[0, t]` by path continuity, and monotone convergence concludes.
The integrals on the left are lower Lebesgue integrals, so no integrability of the supremum is
assumed.

## Main results

* `MeasureTheory.Martingale.lintegral_iSup_sq_le_of_continuous`: **Doob's `L²` inequality in
  continuous time**.

## References

* J.-F. Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Graduate Texts in
  Mathematics 274, Springer, 2016, Chapter 3, section "Continuous time martingales and
  supermartingales".
* J.-F. Le Gall, *Intégration, Probabilités et Processus Aléatoires* (ENS lecture notes),
  Proposition 12.4.3 (the discrete-time inequality).
-/

@[expose] public section

open Filter Topology Set
open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- The `k`-th point of the dyadic grid of level `n` on `[0, t]`, frozen at `t` after `2^n`. -/
private noncomputable def gridPt (t : ℝ≥0) (n k : ℕ) : ℝ≥0 :=
  t * (min k (2 ^ n) : ℕ) / 2 ^ n

private lemma gridPt_mono (t : ℝ≥0) (n : ℕ) : Monotone (gridPt t n) := fun a b hab ↦ by
  unfold gridPt
  gcongr

private lemma gridPt_top (t : ℝ≥0) (n : ℕ) : gridPt t n (2 ^ n) = t := by
  simp [gridPt]

private lemma gridPt_le (t : ℝ≥0) (n k : ℕ) : gridPt t n k ≤ t := by
  unfold gridPt
  rw [div_le_iff₀ (by positivity)]
  gcongr
  exact_mod_cast min_le_right _ _

private lemma gridPt_double (t : ℝ≥0) (n k : ℕ) (hk : k ≤ 2 ^ n) :
    gridPt t (n + 1) (2 * k) = gridPt t n k := by
  unfold gridPt
  rw [min_eq_left hk, min_eq_left (by rw [pow_succ]; omega)]
  push_cast
  rw [pow_succ]
  field_simp

/-- The dyadic grid of level `n` as a discrete filtration. -/
private noncomputable def gridFiltration (ℱ : Filtration ℝ≥0 m0) (t : ℝ≥0) (n : ℕ) :
    Filtration ℕ m0 where
  seq k := ℱ (gridPt t n k)
  mono' _ _ h := ℱ.mono (gridPt_mono t n h)
  le' _ := ℱ.le _

/-- The running maximum of `|M|` along the dyadic grid of level `n`. -/
private noncomputable def gridMax (M : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (2 ^ n + 1)).sup' Finset.nonempty_range_add_one fun k ↦ |M (gridPt t n k) ω|

private lemma gridMax_mono (M : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    Monotone fun n ↦ gridMax M t n ω := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  refine Finset.sup'_le _ _ fun k hk ↦ ?_
  have hk' : k ≤ 2 ^ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  rw [← gridPt_double t n k hk']
  exact Finset.le_sup' (fun j ↦ |M (gridPt t (n + 1) j) ω|)
    (Finset.mem_range.2 (by rw [pow_succ]; omega))

/-- **Doob's `L²` maximal inequality in continuous time.** Let `M` be a martingale indexed by
`ℝ≥0`, with continuous paths and `M t ∈ L²` for every `t`, on a probability space. Then for every
`t ≥ 0`, `E[(sup_{0 ≤ s ≤ t} |M s|)²] ≤ 4 E[M_t²]` (Le Gall, *Brownian Motion, Martingales, and
Stochastic Calculus*, Chapter 3, section "Continuous time martingales and supermartingales"; the
discrete-time inequality is Proposition 12.4.3 of his ENS notes, with `p = 2`). -/
theorem Martingale.lintegral_iSup_sq_le_of_continuous [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 m0} {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hcont : ∀ ω, Continuous fun t ↦ M t ω) (hL2 : ∀ t, MemLp (M t) 2 μ) (t : ℝ≥0) :
    ∫⁻ ω, (⨆ s : Set.Icc (0 : ℝ≥0) t, ENNReal.ofReal |M s ω|) ^ 2 ∂μ ≤
      4 * ∫⁻ ω, ENNReal.ofReal (M t ω ^ 2) ∂μ := by
  have hMmeas : ∀ s, Measurable (M s) := fun s ↦ ((hM.1 s).mono (ℱ.le s)).measurable
  -- the discrete martingales
  have hdisc : ∀ n, Martingale (fun k ↦ M (gridPt t n k)) (gridFiltration ℱ t n) μ := fun n ↦
    ⟨fun k ↦ hM.1 (gridPt t n k), fun i j hij ↦ hM.2 _ _ (gridPt_mono t n hij)⟩
  have hmeasMax : ∀ n, Measurable (gridMax M t n) := fun n ↦ by
    have h := Finset.measurable_sup' (Finset.nonempty_range_add_one (n := 2 ^ n))
      (f := fun k ω ↦ |M (gridPt t n k) ω|)
      fun k _ ↦ continuous_abs.measurable.comp (hMmeas _)
    convert h using 1
    ext ω
    rw [gridMax, Finset.sup'_apply]
  -- the discrete bound, as a lower integral
  have hbound : ∀ n, ∫⁻ ω, ENNReal.ofReal (gridMax M t n ω ^ 2) ∂μ ≤
      4 * ∫⁻ ω, ENNReal.ofReal (M t ω ^ 2) ∂μ := by
    intro n
    have hD := (hdisc n).doob_sq_maximal_ineq (fun k ↦ hL2 _) (2 ^ n)
    simp only [gridPt_top] at hD
    have hint_sq : Integrable (fun ω ↦ M t ω ^ 2) μ := (hL2 t).integrable_sq
    have hint_max : Integrable (fun ω ↦ gridMax M t n ω ^ 2) μ := by
      refine Integrable.mono' (integrable_finsetSum (Finset.range (2 ^ n + 1))
        fun k _ ↦ (hL2 (gridPt t n k)).integrable_sq)
        ((hmeasMax n).pow_const 2).aestronglyMeasurable
        (ae_of_all _ fun ω ↦ ?_)
      obtain ⟨k, hk, hkmax⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
        (fun k ↦ |M (gridPt t n k) ω|)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rw [gridMax, hkmax, sq_abs]
      exact Finset.single_le_sum (f := fun j ↦ M (gridPt t n j) ω ^ 2)
        (fun j _ ↦ sq_nonneg _) hk
    rw [← ofReal_integral_eq_lintegral_ofReal hint_max (ae_of_all _ fun _ ↦ sq_nonneg _),
      ← ofReal_integral_eq_lintegral_ofReal hint_sq (ae_of_all _ fun _ ↦ sq_nonneg _),
      ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal hD
  -- the supremum over `[0, t]` is the increasing limit of the dyadic maxima
  have hsup : ∀ ω, (⨆ s : Set.Icc (0 : ℝ≥0) t, ENNReal.ofReal |M s ω|) =
      ⨆ n, ENNReal.ofReal (gridMax M t n ω) := by
    intro ω
    apply le_antisymm
    · refine iSup_le fun s ↦ ?_
      rcases eq_or_ne t 0 with ht | ht
      · have hs0 : (s : ℝ≥0) = 0 := le_antisymm (ht ▸ s.2.2) s.2.1
        refine le_iSup_of_le 0 (ENNReal.ofReal_le_ofReal ?_)
        have h0 : gridPt t 0 0 = 0 := by simp [gridPt]
        rw [hs0, ← h0]
        exact Finset.le_sup' (fun j ↦ |M (gridPt t 0 j) ω|) (Finset.mem_range.2 (by norm_num))
      · -- dyadic times approaching `s` from below
        set kn : ℕ → ℕ := fun n ↦ ⌊(s : ℝ≥0) * 2 ^ n / t⌋₊ with hkn
        have hkle : ∀ n, kn n ≤ 2 ^ n := fun n ↦ by
          rw [hkn]
          refine Nat.floor_le_of_le ?_
          rw [div_le_iff₀ (pos_iff_ne_zero.2 ht)]
          push_cast
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left s.2.2 (by positivity)
        have hgrid : ∀ n, (gridPt t n (kn n) : ℝ) ≤ s ∧ (s : ℝ) - t / 2 ^ n < gridPt t n (kn n) :=
          fun n ↦ by
            have htpos : (0 : ℝ) < t := by exact_mod_cast pos_iff_ne_zero.2 ht
            have hfl := Nat.floor_le (a := (s : ℝ≥0) * 2 ^ n / t) (by positivity)
            have hlt := Nat.lt_floor_add_one ((s : ℝ≥0) * 2 ^ n / t)
            have hfl' : ((kn n : ℝ≥0) : ℝ) ≤ (s : ℝ) * 2 ^ n / t := by rw [hkn]; exact_mod_cast hfl
            have hlt' : (s : ℝ) * 2 ^ n / t < ((kn n : ℝ≥0) : ℝ) + 1 := by
              rw [hkn]; exact_mod_cast hlt
            simp only [gridPt, min_eq_left (hkle n)]
            push_cast at hfl' hlt' ⊢
            rw [le_div_iff₀ htpos] at hfl'
            rw [div_lt_iff₀ htpos] at hlt'
            constructor
            · rw [div_le_iff₀ (by positivity)]; linarith
            · rw [lt_div_iff₀ (by positivity), sub_mul, div_mul_cancel₀ _ (by positivity)]
              linarith
        have htend : Tendsto (fun n ↦ gridPt t n (kn n)) atTop (𝓝 (s : ℝ≥0)) := by
          rw [← NNReal.tendsto_coe]
          have hlim : Tendsto (fun n : ℕ ↦ (s : ℝ) - t / 2 ^ n) atTop (𝓝 s) := by
            have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
              (by norm_num)).const_mul (t : ℝ)).const_sub (s : ℝ)
            simpa [div_eq_mul_inv, inv_pow] using h
          exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds
            (fun n ↦ (hgrid n).2.le) fun n ↦ (hgrid n).1
        have hval : Tendsto (fun n ↦ ENNReal.ofReal |M (gridPt t n (kn n)) ω|) atTop
            (𝓝 (ENNReal.ofReal |M s ω|)) :=
          (ENNReal.continuous_ofReal.tendsto _).comp
            ((continuous_abs.tendsto _).comp ((hcont ω).tendsto _ |>.comp htend))
        refine le_of_tendsto' hval fun n ↦ le_iSup_of_le n (ENNReal.ofReal_le_ofReal ?_)
        exact Finset.le_sup' (fun j ↦ |M (gridPt t n j) ω|)
          (Finset.mem_range.2 (Nat.lt_succ_of_le (hkle n)))
    · refine iSup_le fun n ↦ ?_
      obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
        (fun k ↦ |M (gridPt t n k) ω|)
      rw [gridMax, hk]
      exact le_iSup (fun s : Set.Icc (0 : ℝ≥0) t ↦ ENNReal.ofReal |M s ω|)
        ⟨gridPt t n k, zero_le, gridPt_le t n k⟩
  -- monotone convergence
  simp_rw [hsup, ENNReal.iSup_pow]
  rw [lintegral_iSup (f := fun n ω ↦ ENNReal.ofReal (gridMax M t n ω) ^ 2)
    (fun n ↦ ((ENNReal.measurable_ofReal.comp (hmeasMax n)).pow_const 2))
    (fun a b hab ω ↦ pow_le_pow_left₀ zero_le
      (ENNReal.ofReal_le_ofReal (gridMax_mono M t ω hab)) 2)]
  refine iSup_le fun n ↦ ?_
  calc ∫⁻ ω, ENNReal.ofReal (gridMax M t n ω) ^ 2 ∂μ
      = ∫⁻ ω, ENNReal.ofReal (gridMax M t n ω ^ 2) ∂μ := by
        refine lintegral_congr fun ω ↦ ?_
        have h0 : 0 ≤ gridMax M t n ω := (abs_nonneg _).trans
          (Finset.le_sup' (fun j ↦ |M (gridPt t n j) ω|) (Finset.mem_range.2 (Nat.succ_pos _)))
        rw [ENNReal.ofReal_pow h0]
    _ ≤ _ := hbound n

end MeasureTheory
