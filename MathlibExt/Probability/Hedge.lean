/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith

@[expose] public section


open Finset

/-- Secant bound for `exp`: on `[0, 1]`, `exp (-η * x)` lies below the
chord from `(0, 1)` to `(1, exp (-η))`. -/
private lemma exp_secant (η x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (-η * x) ≤ 1 + (Real.exp (-η) - 1) * x := by
  have h := convexOn_exp.2 (Set.mem_univ (-η)) (Set.mem_univ 0) hx.1
    (sub_nonneg.mpr hx.2) (by ring : x + (1 - x) = 1)
  simp only [smul_eq_mul, Real.exp_zero, mul_one] at h
  calc Real.exp (-η * x) = Real.exp (x * -η + (1 - x) * 0) := by congr 1; ring
    _ ≤ x * Real.exp (-η) + (1 - x) := h
    _ = 1 + (Real.exp (-η) - 1) * x := by ring

/-- The `1 + μ * (exp s - 1)` expression in Hoeffding's core inequality. -/
private noncomputable def hD (μ : ℝ) (s : ℝ) : ℝ := 1 + μ * (Real.exp s - 1)

/-- Gap function: `s ^ 2 / 8 - (log (hD μ s) - s * μ)`. -/
private noncomputable def hpsi (μ : ℝ) (s : ℝ) : ℝ :=
  s ^ 2 / 8 - (Real.log (hD μ s) - s * μ)

private lemma hD_pos (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (s : ℝ) :
    0 < hD μ s := by
  have he : (0 : ℝ) < Real.exp s := Real.exp_pos s
  by_cases hμ0 : μ = 0
  · subst hμ0; simp [hD]
  · have hμpos : (0 : ℝ) < μ := lt_of_le_of_ne hμ.1 (fun h => hμ0 h.symm)
    have h2 : (0 : ℝ) < μ * Real.exp s := mul_pos hμpos he
    have h3 : (0 : ℝ) ≤ 1 - μ := by linarith [hμ.2]
    have h4 : hD μ s = (1 - μ) + μ * Real.exp s := by simp only [hD]; ring
    rw [h4]; linarith

private lemma hD_deriv (μ : ℝ) (s : ℝ) :
    HasDerivAt (hD μ) (μ * Real.exp s) s := by
  show HasDerivAt (fun s => 1 + μ * (Real.exp s - 1)) (μ * Real.exp s) s
  exact (((Real.hasDerivAt_exp s).sub_const 1).const_mul μ).const_add 1

private lemma hpsi_deriv1 (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (s : ℝ) :
    HasDerivAt (hpsi μ) (s / 4 - (μ * Real.exp s / hD μ s - μ)) s := by
  have hsq : HasDerivAt (fun s : ℝ => s ^ 2 / 8) (s / 4) s := by
    have h2 := (hasDerivAt_pow 2 s).div_const 8
    have hval : (Nat.cast 2 * s ^ (2 - 1)) / 8 = s / 4 := by
      have e1 : ((2 : ℕ) - 1) = 1 := rfl
      rw [e1, pow_one]
      ring
    rw [hval] at h2
    exact h2
  have hlog : HasDerivAt (fun s : ℝ => Real.log (hD μ s))
      (μ * Real.exp s / hD μ s) s :=
    (hD_deriv μ s).log (ne_of_gt (hD_pos μ hμ s))
  have hlin : HasDerivAt (fun s : ℝ => s * μ) μ s := by
    simpa using (hasDerivAt_id s).mul_const μ
  show HasDerivAt (fun s => s ^ 2 / 8 - (Real.log (hD μ s) - s * μ)) _ s
  exact hsq.fun_sub (hlog.fun_sub hlin)

private lemma hpsi_deriv2 (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (s : ℝ) :
    HasDerivAt (deriv (hpsi μ))
      (1 / 4 - μ * (1 - μ) * Real.exp s / (hD μ s) ^ 2) s := by
  have heq : deriv (hpsi μ) =
      fun s => s / 4 - (μ * Real.exp s / hD μ s - μ) :=
    funext (fun s => (hpsi_deriv1 μ hμ s).deriv)
  rw [heq]
  have hDne : hD μ s ≠ 0 := ne_of_gt (hD_pos μ hμ s)
  have ha : HasDerivAt (fun s : ℝ => s / 4) (1 / 4) s := by
    simpa using (hasDerivAt_id s).div_const 4
  have hnum : HasDerivAt (fun s : ℝ => μ * Real.exp s) (μ * Real.exp s) s :=
    (Real.hasDerivAt_exp s).const_mul μ
  have hquot : HasDerivAt (fun y : ℝ => μ * Real.exp y / hD μ y)
      ((μ * Real.exp s * hD μ s - μ * Real.exp s * (μ * Real.exp s)) /
        (hD μ s) ^ 2) s :=
    hnum.fun_div (hD_deriv μ s) hDne
  have hnum_eq : (μ * Real.exp s * hD μ s - μ * Real.exp s * (μ * Real.exp s)) =
      μ * (1 - μ) * Real.exp s := by
    simp only [hD]; ring
  have hb : HasDerivAt (fun s : ℝ => μ * Real.exp s / hD μ s - μ)
      (μ * (1 - μ) * Real.exp s / (hD μ s) ^ 2) s := by
    have h := hquot.sub_const μ
    rw [hnum_eq] at h
    exact h
  exact ha.fun_sub hb

private lemma hpsi_mono (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    Monotone (deriv (hpsi μ)) := by
  apply monotone_of_deriv_nonneg
      (fun x => (hpsi_deriv2 μ hμ x).differentiableAt)
  intro x
  rw [(hpsi_deriv2 μ hμ x).deriv]
  have hDne : hD μ x ≠ 0 := ne_of_gt (hD_pos μ hμ x)
  have hpp : μ * (1 - μ) * Real.exp x / (hD μ x) ^ 2 =
      (μ * Real.exp x / hD μ x) * (1 - μ * Real.exp x / hD μ x) := by
    field_simp
    simp only [hD]
    ring
  rw [hpp]
  have hid : (μ * Real.exp x / hD μ x) * (1 - μ * Real.exp x / hD μ x) =
      1 / 4 - (μ * Real.exp x / hD μ x - 1 / 2) ^ 2 := by ring
  rw [hid]
  linarith [sq_nonneg (μ * Real.exp x / hD μ x - 1 / 2)]

private lemma hD_zero (μ : ℝ) : hD μ 0 = 1 := by simp [hD, Real.exp_zero]

private lemma hpsi_deriv0 (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    deriv (hpsi μ) 0 = 0 := by
  rw [(hpsi_deriv1 μ hμ 0).deriv, hD_zero]
  simp [Real.exp_zero]

private lemma hpsi_zero (μ : ℝ) : hpsi μ 0 = 0 := by
  simp [hpsi, hD_zero, Real.log_one]

private lemma hpsi_nonneg (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (s : ℝ)
    (hs : s ≤ 0) : 0 ≤ hpsi μ s := by
  have hdiff : Differentiable ℝ (hpsi μ) :=
    fun x => (hpsi_deriv1 μ hμ x).differentiableAt
  have hderiv : ∀ x ∈ interior (Set.Iic 0), deriv (hpsi μ) x ≤ 0 := by
    intro x hx
    have hxIic : x ∈ Set.Iic 0 := interior_subset hx
    have hx0 : x ≤ 0 := Set.mem_Iic.mp hxIic
    have hle := hpsi_mono μ hμ hx0
    rw [hpsi_deriv0 μ hμ] at hle
    exact hle
  have hanti : AntitoneOn (hpsi μ) (Set.Iic 0) :=
    antitoneOn_of_deriv_nonpos (convex_Iic 0) hdiff.continuous.continuousOn
      (hdiff.differentiableOn.mono interior_subset) hderiv
  have hsIic : s ∈ Set.Iic 0 := Set.mem_Iic.mpr hs
  have h0Iic : (0 : ℝ) ∈ Set.Iic 0 := Set.mem_Iic.mpr (le_refl 0)
  have h := hanti hsIic h0Iic hs
  rw [hpsi_zero] at h
  exact h

/-- Hoeffding's lemma, core inequality: for `μ ∈ [0, 1]` and `s ≤ 0`,
`1 + μ (e ^ s - 1) ≤ e ^ (s * μ + s ^ 2 / 8)`. -/
private lemma hoeffding_core (μ s : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1)
    (hs : s ≤ 0) :
    1 + μ * (Real.exp s - 1) ≤ Real.exp (s * μ + s ^ 2 / 8) := by
  have hpos1 : (0 : ℝ) < hD μ s := hD_pos μ hμ s
  have hpos2 : (0 : ℝ) < Real.exp (s * μ + s ^ 2 / 8) := Real.exp_pos _
  have hlog : Real.log (hD μ s) ≤ s * μ + s ^ 2 / 8 := by
    have h := hpsi_nonneg μ hμ s hs
    simp only [hpsi] at h
    linarith
  have hiff := (Real.log_le_log_iff hpos1 hpos2).mp
  rw [Real.log_exp] at hiff
  have hle : hD μ s ≤ Real.exp (s * μ + s ^ 2 / 8) := hiff hlog
  simpa [hD] using hle

/-- One-step potential bound: with positive weights `w`, losses in `[0, 1]`
and `A` the weighted average loss,
`∑ j, w j * exp (-η * L j) ≤ (∑ j, w j) * exp (-η * A + η ^ 2 / 8)`. -/
private lemma onestep {N : ℕ} (hN : 0 < N) (w : Fin N → ℝ) (L : Fin N → ℝ)
    (η : ℝ) (hw : ∀ j, 0 < w j) (hL : ∀ j, L j ∈ Set.Icc (0 : ℝ) 1)
    (hη : 0 < η) :
    ∑ j, w j * Real.exp (-η * L j) ≤ (∑ j, w j) *
      Real.exp (-η * ((∑ j, w j * L j) / (∑ j, w j)) + η ^ 2 / 8) := by
  have hPpos : (0 : ℝ) < ∑ j, w j :=
    Finset.sum_pos (fun j _ => hw j) ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  have hPne : (∑ j, w j) ≠ 0 := ne_of_gt hPpos
  have hSnonneg : (0 : ℝ) ≤ ∑ j, w j * L j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (le_of_lt (hw j)) (hL j).1)
  have hSle : (∑ j, w j * L j) ≤ ∑ j, w j := by
    have h : ∀ j ∈ (Finset.univ : Finset (Fin N)), w j * L j ≤ w j * 1 :=
      fun j _ => mul_le_mul_of_nonneg_left (hL j).2 (le_of_lt (hw j))
    have h2 := Finset.sum_le_sum h
    simpa using h2
  have hA01 : (∑ j, w j * L j) / (∑ j, w j) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hSnonneg (le_of_lt hPpos)
    · exact (div_le_one hPpos).mpr hSle
  have hsec : ∀ j, Real.exp (-η * L j) ≤ 1 + (Real.exp (-η) - 1) * L j :=
    fun j => exp_secant η (L j) (hL j)
  have hsum : ∑ j, w j * Real.exp (-η * L j) ≤
      ∑ j, w j * (1 + (Real.exp (-η) - 1) * L j) :=
    Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_left (hsec j) (le_of_lt (hw j)))
  have hexpand : (∑ j, w j * (1 + (Real.exp (-η) - 1) * L j)) =
      (∑ j, w j) + (Real.exp (-η) - 1) * (∑ j, w j * L j) := by
    have h1 : ∀ j : Fin N, w j * (1 + (Real.exp (-η) - 1) * L j) =
        w j + (Real.exp (-η) - 1) * (w j * L j) := fun j => by ring
    have h2 : (∑ j, w j * (1 + (Real.exp (-η) - 1) * L j)) =
        ∑ j, (w j + (Real.exp (-η) - 1) * (w j * L j)) :=
      Finset.sum_congr rfl (fun j _ => h1 j)
    rw [h2, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcore := hoeffding_core ((∑ j, w j * L j) / (∑ j, w j)) (-η) hA01
    (neg_nonpos.mpr (le_of_lt hη))
  rw [show (-η : ℝ) ^ 2 = η ^ 2 by ring] at hcore
  have h3 : (∑ j, w j) + (Real.exp (-η) - 1) * (∑ j, w j * L j) ≤
      (∑ j, w j) * Real.exp (-η * ((∑ j, w j * L j) / (∑ j, w j)) +
        η ^ 2 / 8) := by
    have hfactor : (∑ j, w j) + (Real.exp (-η) - 1) * (∑ j, w j * L j) =
        (∑ j, w j) * (1 + (Real.exp (-η) - 1) *
          ((∑ j, w j * L j) / (∑ j, w j))) := by
      field_simp
    rw [hfactor]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hPpos)
    have hcomm : 1 + (Real.exp (-η) - 1) * ((∑ j, w j * L j) / (∑ j, w j)) =
        1 + ((∑ j, w j * L j) / (∑ j, w j)) * (Real.exp (-η) - 1) := by ring
    rw [hcomm]
    exact hcore
  calc ∑ j, w j * Real.exp (-η * L j)
      ≤ ∑ j, w j * (1 + (Real.exp (-η) - 1) * L j) := hsum
    _ = (∑ j, w j) + (Real.exp (-η) - 1) * (∑ j, w j * L j) := hexpand
    _ ≤ (∑ j, w j) * Real.exp (-η * ((∑ j, w j * L j) / (∑ j, w j)) +
          η ^ 2 / 8) := h3

/-- ℕ-indexed Hedge weight: same cumulative-loss form as `hedgeW`, with the
round as a natural number. -/
private noncomputable def cumW {N T : ℕ} (loss : Fin T → Fin N → ℝ) (η : ℝ)
    (t : ℕ) (j : Fin N) : ℝ :=
  Real.exp (-η * ∑ s ∈ Finset.univ.filter (fun s : Fin T => s.val < t),
    loss s j)

/-- ℕ-indexed potential: total weight at round `t`. -/
private noncomputable def cumPhi {N T : ℕ} (loss : Fin T → Fin N → ℝ)
    (η : ℝ) (t : ℕ) : ℝ :=
  ∑ j, cumW loss η t j

/-- Loss at ℕ-indexed round `t` (zero past the horizon). -/
private noncomputable def roundLoss {N T : ℕ} (loss : Fin T → Fin N → ℝ)
    (t : ℕ) (j : Fin N) : ℝ :=
  if h : t < T then loss ⟨t, h⟩ j else 0

/-- Weighted average loss at ℕ-indexed round `t`. -/
private noncomputable def avgLoss {N T : ℕ} (loss : Fin T → Fin N → ℝ)
    (η : ℝ) (t : ℕ) : ℝ :=
  (∑ j, cumW loss η t j * roundLoss loss t j) / cumPhi loss η t

private lemma filter_succ {T : ℕ} (t : ℕ) (h : t < T) :
    Finset.univ.filter (fun s : Fin T => s.val < t + 1) =
      insert ⟨t, h⟩ (Finset.univ.filter (fun s : Fin T => s.val < t)) := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro hs
    have hle : s.val < t ∨ s.val = t := by omega
    rcases hle with hlt | heq
    · exact Or.inr hlt
    · exact Or.inl (Fin.ext heq)
  · rintro (rfl | hlt)
    · show t < t + 1
      omega
    · omega

private lemma cumW_succ {N T : ℕ} (loss : Fin T → Fin N → ℝ) (η : ℝ)
    (t : ℕ) (h : t < T) (j : Fin N) :
    cumW loss η (t + 1) j =
      cumW loss η t j * Real.exp (-η * roundLoss loss t j) := by
  have hmem : (⟨t, h⟩ : Fin T) ∉
      Finset.univ.filter (fun s : Fin T => s.val < t) := by simp
  have hRL : roundLoss loss t j = loss ⟨t, h⟩ j := dite_eq_left h
  unfold cumW
  rw [filter_succ t h, Finset.sum_insert hmem, hRL]
  have hexp : -η * (loss ⟨t, h⟩ j +
      ∑ s ∈ Finset.univ.filter (fun s : Fin T => s.val < t), loss s j) =
      -η * (∑ s ∈ Finset.univ.filter (fun s : Fin T => s.val < t),
        loss s j) + -η * loss ⟨t, h⟩ j := by ring
  rw [hexp, Real.exp_add]

private lemma phi_pos {N T : ℕ} (hN : 0 < N) (loss : Fin T → Fin N → ℝ)
    (η : ℝ) (t : ℕ) : 0 < cumPhi loss η t :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨⟨0, hN⟩, Finset.mem_univ _⟩

/-- Multiplicative (Hedge) weight of expert `i` at round `t`:
exponential in the cumulative loss so far. -/
noncomputable def hedgeW {N T : ℕ} (loss : Fin T → Fin N → ℝ) (η : ℝ)
    (t : Fin T) (i : Fin N) : ℝ :=
  Real.exp (-η * ∑ s ∈ Finset.univ.filter (fun s => s < t), loss s i)

private lemma hedgeW_eq_cumW {N T : ℕ} (loss : Fin T → Fin N → ℝ) (η : ℝ)
    (t : ℕ) (h : t < T) (j : Fin N) :
    hedgeW loss η ⟨t, h⟩ j = cumW loss η t j := by
  have hF : Finset.univ.filter (fun s : Fin T => s < ⟨t, h⟩) =
      Finset.univ.filter (fun s : Fin T => s.val < t) := by
    apply Finset.filter_congr
    intro s _
    show (s < ⟨t, h⟩) ↔ (s.val < t)
    exact Fin.lt_def
  unfold hedgeW cumW
  rw [hF]

/-- Hedge regret bound: for losses in `[0, 1]`, the Hedge
algorithm's total expected loss (the `w`-weighted average loss per
round) is at most the loss of any single expert plus
`(log N) / η + η * T / 8`. -/
theorem hedge_regret {N T : ℕ} (hN : 0 < N)
    (loss : Fin T → Fin N → ℝ)
    (hloss : ∀ t i, loss t i ∈ Set.Icc (0 : ℝ) 1)
    {η : ℝ} (hη : 0 < η) (i : Fin N) :
    (∑ t, (∑ j, hedgeW loss η t j * loss t j) /
      (∑ j, hedgeW loss η t j)) ≤
      (∑ t, loss t i) + Real.log N / η + η * T / 8 := by
  have hphi : ∀ t, 0 < cumPhi loss η t := phi_pos hN loss η
  -- One-step log-potential bound.
  have honesteplog : ∀ t : ℕ, t < T →
      Real.log (cumPhi loss η (t + 1)) ≤ Real.log (cumPhi loss η t) +
        (-η * avgLoss loss η t + η ^ 2 / 8) := by
    intro t ht
    have hRL : ∀ j, roundLoss loss t j ∈ Set.Icc (0 : ℝ) 1 := by
      intro j
      have h : roundLoss loss t j = loss ⟨t, ht⟩ j := dite_eq_left ht
      rw [h]
      exact hloss _ _
    have ho := onestep hN (cumW loss η t) (roundLoss loss t) η
      (fun j => Real.exp_pos _) hRL hη
    have hPhi : cumPhi loss η (t + 1) =
        ∑ j, cumW loss η t j * Real.exp (-η * roundLoss loss t j) := by
      simp only [cumPhi]
      apply Finset.sum_congr rfl
      intro j _
      exact cumW_succ loss η t ht j
    have hle : cumPhi loss η (t + 1) ≤ cumPhi loss η t *
        Real.exp (-η * avgLoss loss η t + η ^ 2 / 8) := by
      rw [hPhi]
      exact ho
    have hlog := Real.log_le_log (hphi (t + 1)) hle
    rw [Real.log_mul (ne_of_gt (hphi t)) (Real.exp_ne_zero _),
      Real.log_exp] at hlog
    exact hlog
  -- Telescope over all rounds.
  have htele : Real.log (cumPhi loss η T) - Real.log (cumPhi loss η 0) ≤
      ∑ t ∈ Finset.range T, (-η * avgLoss loss η t + η ^ 2 / 8) := by
    have hsub : ∑ t ∈ Finset.range T, (Real.log (cumPhi loss η (t + 1)) -
        Real.log (cumPhi loss η t)) =
        Real.log (cumPhi loss η T) - Real.log (cumPhi loss η 0) :=
      Finset.sum_range_sub (fun t => Real.log (cumPhi loss η t)) T
    have hle : ∑ t ∈ Finset.range T, (Real.log (cumPhi loss η (t + 1)) -
        Real.log (cumPhi loss η t)) ≤
        ∑ t ∈ Finset.range T, (-η * avgLoss loss η t + η ^ 2 / 8) :=
      Finset.sum_le_sum (fun t htm => by
        have h := honesteplog t (Finset.mem_range.mp htm)
        linarith)
    rw [hsub] at hle
    exact hle
  -- Massage the telescoped RHS into `-η * total + T * (η ^ 2 / 8)`.
  have hsum : ∑ t ∈ Finset.range T, (-η * avgLoss loss η t + η ^ 2 / 8) =
      -η * (∑ t ∈ Finset.range T, avgLoss loss η t) + T * (η ^ 2 / 8) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  have hS0 : Finset.univ.filter (fun s : Fin T => s.val < 0) = ∅ := by
    ext s
    simp
  have hphi0 : cumPhi loss η 0 = (N : ℝ) := by
    simp only [cumPhi, cumW, hS0, Finset.sum_empty, mul_zero, Real.exp_zero]
    simp
  have htele' : Real.log (cumPhi loss η T) - Real.log N ≤
      -η * (∑ t ∈ Finset.range T, avgLoss loss η t) + T * (η ^ 2 / 8) := by
    have h1 := htele
    rw [hsum, hphi0] at h1
    exact h1
  -- The final potential dominates the fixed expert's weight.
  have hST : Finset.univ.filter (fun s : Fin T => s.val < T) =
      Finset.univ := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_of_true s.isLt trivial
  have hE : (∑ s, loss s i) =
      ∑ t ∈ Finset.range T, roundLoss loss t i := by
    refine (Finset.sum_fin_eq_sum_range (fun s : Fin T => loss s i)).trans ?_
    apply Finset.sum_congr rfl
    intro t _
    show (if h : t < T then loss ⟨t, h⟩ i else 0) = roundLoss loss t i
    rfl
  have hcum : cumW loss η T i =
      Real.exp (-η * (∑ t ∈ Finset.range T, roundLoss loss t i)) := by
    unfold cumW
    rw [hST, hE]
  have hlow : -η * (∑ t ∈ Finset.range T, roundLoss loss t i) ≤
      Real.log (cumPhi loss η T) := by
    have hsingle : cumW loss η T i ≤ cumPhi loss η T :=
      Finset.single_le_sum (f := fun j => cumW loss η T j)
        (fun _ _ => (Real.exp_pos _).le) (Finset.mem_univ i)
    rw [hcum] at hsingle
    have h := Real.log_le_log (Real.exp_pos _) hsingle
    rw [Real.log_exp] at h
    exact h
  -- Assemble the ℕ-indexed bound.
  have hmain : (∑ t ∈ Finset.range T, avgLoss loss η t) ≤
      (∑ t ∈ Finset.range T, roundLoss loss t i) + Real.log N / η +
        η * T / 8 := by
    have hle : η * (∑ t ∈ Finset.range T, avgLoss loss η t) ≤
        η * (∑ t ∈ Finset.range T, roundLoss loss t i) + Real.log N +
          T * η ^ 2 / 8 := by
      linarith [htele', hlow]
    have hdiv : (∑ t ∈ Finset.range T, avgLoss loss η t) ≤
        (η * (∑ t ∈ Finset.range T, roundLoss loss t i) + Real.log N +
          T * η ^ 2 / 8) / η := by
      rw [le_div_iff₀ hη]
      linarith [hle]
    have heq : (η * (∑ t ∈ Finset.range T, roundLoss loss t i) +
        Real.log N + T * η ^ 2 / 8) / η =
        (∑ t ∈ Finset.range T, roundLoss loss t i) + Real.log N / η +
          η * T / 8 := by
      have hηne : η ≠ 0 := ne_of_gt hη
      field_simp
    rw [heq] at hdiv
    exact hdiv
  -- Transfer back to the pinned `Fin T` sums.
  have hLHS : (∑ t, (∑ j, hedgeW loss η t j * loss t j) /
      (∑ j, hedgeW loss η t j)) =
      ∑ t ∈ Finset.range T, avgLoss loss η t := by
    refine (Finset.sum_fin_eq_sum_range (fun t : Fin T =>
      (∑ j, hedgeW loss η t j * loss t j) /
        (∑ j, hedgeW loss η t j))).trans ?_
    apply Finset.sum_congr rfl
    intro t htm
    have hmem : t < T := Finset.mem_range.mp htm
    show (if h : t < T then
        (∑ j, hedgeW loss η ⟨t, h⟩ j * loss ⟨t, h⟩ j) /
          (∑ j, hedgeW loss η ⟨t, h⟩ j) else 0) = avgLoss loss η t
    rw [dite_eq_left hmem]
    simp only [avgLoss, roundLoss, cumPhi, dite_eq_left hmem,
      hedgeW_eq_cumW loss η t hmem]
  rw [hLHS, hE]
  exact hmain
