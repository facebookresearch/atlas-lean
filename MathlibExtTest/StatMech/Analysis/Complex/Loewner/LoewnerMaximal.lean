/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.Loewner.LoewnerMaximal

/-!
# Tests for `MathlibExt.Analysis.Complex.Loewner.LoewnerMaximal`

Driving function `W = 0`, point `z = I`, explicit trajectory `g_t(I) = I √(1 - 4t)`:
* `LoewnerForwardSolution` is inhabited on `[0, S]` for every `S < 1/4`, and not for any `T ≥ 1/4`
  (the trajectory hits the real line at `t = 1/4`). Hence `IsBeforeLoewnerLifetime 0 I t ↔
  0 ≤ t < 1/4`, the lifetime of `I` is exactly `1/4`, and `loewnerMaximalMaps 0 t I = I √(1 - 4t)`.
* `loewner_maximal_forward_exists`, `loewnerMaximalMaps_satisfiesMaximalLoewnerEquation`,
  `loewnerMaximalMaps_bijOn_upperHalfPlane`, `loewnerMaximalMapsHomeomorph`,
  `isOpen_loewnerUnswallowedDomain`, `isConnected_loewnerUnswallowedDomain`,
  `ofReal_im_sq_div_eight_le_loewnerLifetime` instantiated at `W = 0`.
* `loewnerSwallowedSet_isCompactHull` with a nonempty hull: `I ∈ K_{1/4}`, `I ∉ K_{1/8}`;
  `loewnerSwallowedSet_zero`, `loewnerSwallowedSet_monotoneOn`.
-/

@[expose] public section

open StatMech.SLE Complex Set
open UpperHalfPlane (upperHalfPlaneSet)

namespace MathlibExtTest.StatMech.Analysis.Complex.Loewner.LoewnerMaximal

/-- The explicit Loewner trajectory of `z = I` for `W = 0`: `g_t(I) = I √(1 - 4t)`. -/
noncomputable def gI (t : ℝ) : ℂ := I * ((Real.sqrt (1 - 4 * t) : ℝ) : ℂ)

lemma im_gI (t : ℝ) : (gI t).im = Real.sqrt (1 - 4 * t) := by simp [gI]

lemma gI_zero : gI 0 = I := by simp [gI]

/-- `g_t(I) = I √(1 - 4t)` solves `ġ = 2 / g` (the Loewner equation for `W = 0`) for `t < 1/4`. -/
theorem hasDerivAt_gI {t : ℝ} (ht : t < 1 / 4) :
    HasDerivAt gI (loewnerField (fun _ => 0) t (gI t)) t := by
  have hpos : 0 < 1 - 4 * t := by linarith
  have hs : 0 < Real.sqrt (1 - 4 * t) := Real.sqrt_pos.mpr hpos
  have h1 : HasDerivAt (fun u : ℝ => 1 - 4 * u) (-4) t := by
    simpa using ((hasDerivAt_id t).const_mul 4).const_sub 1
  have h2 := (h1.sqrt hpos.ne').ofReal_comp.const_mul I
  have hs' : ((Real.sqrt (1 - 4 * t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hval : loewnerField (fun _ => 0) t (gI t) =
      I * (((-4) / (2 * Real.sqrt (1 - 4 * t)) : ℝ) : ℂ) := by
    simp only [loewnerField_apply, gI, Complex.ofReal_zero, sub_zero]
    push_cast
    field_simp
    ring_nf
    simp
  rw [hval]
  exact h2

lemma gI_mem_upper {t : ℝ} (ht : t < 1 / 4) : gI t ∈ upperHalfPlaneSet := by
  rw [mem_upperHalfPlane, im_gI]
  exact Real.sqrt_pos.mpr (by linarith)

lemma continuousOn_gI {b : ℝ} (hb : b < 1 / 4) : ContinuousOn gI (Icc 0 b) :=
  fun t ht => (hasDerivAt_gI (by linarith [ht.2])).continuousAt.continuousWithinAt

/-- The explicit forward solution from `I` on `[0, S]`, `S < 1/4`. -/
noncomputable def solI {S : ℝ} (hS : S < 1 / 4) : LoewnerForwardSolution (fun _ => 0) I S where
  curve := gI
  initial := gI_zero
  deriv t ht := (hasDerivAt_gI (by linarith [ht.2])).hasDerivWithinAt
  upper t ht := gI_mem_upper (by linarith [ht.2])

-- `1/8` is an admissible duration for `I`.
example : IsLoewnerAdmissibleDuration (fun _ => 0) I (1 / 8) :=
  ⟨by norm_num, ⟨solI (by norm_num)⟩⟩

/-- No forward solution from `I` reaches time `1/4`: `I` is swallowed at `t = 1/4`. -/
theorem not_forwardSolution {T : ℝ} (hT : 1 / 4 ≤ T)
    (h : LoewnerForwardSolution (fun _ => 0) I T) : False := by
  set c := (h.curve (1 / 4)).im with hc
  have hc0 : 0 < c := h.upper (1 / 4) ⟨by norm_num, hT⟩
  have hanti := h.im_antitoneOn
  have hc1 : c ≤ 1 := by
    have : (h.curve (1 / 4)).im ≤ (h.curve 0).im :=
      hanti ⟨le_rfl, by linarith⟩ ⟨by norm_num, hT⟩ (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [h.initial, Complex.I_im] at this
    exact this
  set t := 1 / 4 - c ^ 2 / 8 with ht
  have ht0 : 0 < t := by nlinarith
  have htq : t < 1 / 4 := by nlinarith
  have heq : (solI htq).curve t = h.curve t :=
    LoewnerForwardSolution.eqOn_overlap ht0 (by linarith) (solI htq) h
      ⟨ht0.le, le_min le_rfl (by linarith)⟩
  have hle : c ≤ (h.curve t).im := hanti ⟨ht0.le, by linarith⟩ ⟨by norm_num, hT⟩ htq.le
  rw [← heq] at hle
  change c ≤ (gI t).im at hle
  rw [im_gI, show 1 - 4 * t = c ^ 2 / 2 by rw [ht]; ring] at hle
  have : Real.sqrt (c ^ 2 / 2) < c := (Real.sqrt_lt' hc0).mpr (by nlinarith)
  linarith

/-- Admissible durations for `I` are exactly `(0, 1/4)`. -/
theorem admissible_iff {T : ℝ} :
    IsLoewnerAdmissibleDuration (fun _ => 0) I T ↔ 0 < T ∧ T < 1 / 4 := by
  constructor
  · rintro ⟨hT, ⟨h⟩⟩
    exact ⟨hT, lt_of_not_ge fun hT' => not_forwardSolution hT' h⟩
  · rintro ⟨hT, hT'⟩
    exact ⟨hT, ⟨solI hT'⟩⟩

/-- `t` is before the lifetime of `I` iff `0 ≤ t < 1/4`. -/
theorem isBefore_iff {t : ℝ} :
    IsBeforeLoewnerLifetime (fun _ => 0) I t ↔ 0 ≤ t ∧ t < 1 / 4 := by
  constructor
  · intro h
    obtain ⟨T, hT, htT⟩ := (isBeforeLoewnerLifetime_iff_exists_admissible h.1).1 h
    exact ⟨h.1, htT.trans (admissible_iff.1 hT).2⟩
  · rintro ⟨h0, h1⟩
    refine (isBeforeLoewnerLifetime_iff_exists_admissible h0).2 ⟨(t + 1 / 4) / 2, ?_, by linarith⟩
    exact admissible_iff.2 ⟨by linarith, by linarith⟩

-- The lifetime of `I` for `W = 0` is exactly `1/4`.
example : loewnerLifetime (fun _ => 0) I = ENNReal.ofReal (1 / 4) := by
  apply le_antisymm
  · refine iSup_le fun T => ENNReal.ofReal_le_ofReal (admissible_iff.1 T.2).2.le
  · refine le_of_forall_lt fun x hx => ?_
    have hxtop : x ≠ ⊤ := ne_top_of_lt hx
    have hxr : x.toReal < 1 / 4 := ENNReal.toReal_lt_of_lt_ofReal hx
    have hS : max x.toReal (1 / 8) < 1 / 4 := max_lt hxr (by norm_num)
    calc x = ENNReal.ofReal x.toReal := (ENNReal.ofReal_toReal hxtop).symm
      _ < ENNReal.ofReal ((max x.toReal (1 / 8) + 1 / 4) / 2) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
            (by linarith [le_max_left x.toReal (1 / 8)])
      _ ≤ loewnerLifetime (fun _ => 0) I :=
          ofReal_le_loewnerLifetime (admissible_iff.2 ⟨by positivity, by linarith⟩)

-- The general lower bound `T_z ≥ (Im z)²/8` at `z = I`.
example : ENNReal.ofReal (1 / 8) ≤ loewnerLifetime (fun _ => 0) I := by
  simpa using ofReal_im_sq_div_eight_le_loewnerLifetime (W := fun _ => 0) continuous_const
    (z := I) (by simp)

-- The maximal map at `I` is the explicit trajectory before the lifetime.
theorem maximalMaps_I {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1 / 4) :
    loewnerMaximalMaps (fun _ => 0) t I = gI t :=
  loewnerMaximalCurve_eq_forwardSolution (T := (t + 1 / 4) / 2) (by linarith)
    (solI (by linarith)) ⟨h0, by linarith⟩

-- `I ∈ H_t` iff `0 ≤ t < 1/4`.
example {t : ℝ} : I ∈ loewnerUnswallowedDomain (fun _ => 0) t ↔ 0 ≤ t ∧ t < 1 / 4 := by
  simp [loewnerUnswallowedDomain, isBefore_iff]

-- The swallowed set `K_{1/4}` contains `I`; `K_{1/8}` does not; `K_0 = ∅`.
theorem I_mem_K : I ∈ loewnerSwallowedSet (fun _ => 0) (1 / 4) :=
  ⟨by simp, fun h => by simpa using (isBefore_iff.1 h.2).2⟩
example : I ∉ loewnerSwallowedSet (fun _ => 0) (1 / 8) :=
  fun h => h.2 ⟨by simp, isBefore_iff.2 ⟨by norm_num, by norm_num⟩⟩
example : loewnerSwallowedSet (fun _ => 0) 0 = ∅ := loewnerSwallowedSet_zero continuous_const

-- Monotonicity: `I ∈ K_1`.
example : I ∈ loewnerSwallowedSet (fun _ => 0) 1 :=
  loewnerSwallowedSet_monotoneOn _ (by norm_num : (1 / 4 : ℝ) ∈ Ici 0)
    (by norm_num : (1 : ℝ) ∈ Ici 0) (by norm_num) I_mem_K

-- `K_{1/4}` is a nonempty compact `ℍ`-hull.
example : IsCompactHull (loewnerSwallowedSet (fun _ => 0) (1 / 4)) ∧
    (loewnerSwallowedSet (fun _ => 0) (1 / 4)).Nonempty :=
  ⟨loewnerSwallowedSet_isCompactHull continuous_const (by norm_num), ⟨I, I_mem_K⟩⟩

-- `loewner_maximal_forward_exists` at `z = I`: the derivative at `t = 1/8` is `2 / g_{1/8}(I)`.
example : HasDerivAt (loewnerMaximalCurve (fun _ => 0) I)
    (loewnerField (fun _ => 0) (1 / 8) (loewnerMaximalCurve (fun _ => 0) I (1 / 8))) (1 / 8) := by
  obtain ⟨-, -, -, -, hd⟩ :=
    loewner_maximal_forward_exists (W := fun _ => 0) continuous_const (z := I) (by simp)
  exact hd _ (by norm_num) (isBefore_iff.2 ⟨by norm_num, by norm_num⟩).2

-- The maximal family satisfies the maximal Loewner equation for `W = 0` and `W = id`.
example : SatisfiesMaximalLoewnerEquation (fun _ => 0) (loewnerUnswallowedDomain (fun _ => 0))
    (loewnerMaximalMaps (fun _ => 0)) :=
  loewnerMaximalMaps_satisfiesMaximalLoewnerEquation continuous_const
example :
    SatisfiesMaximalLoewnerEquation id (loewnerUnswallowedDomain id) (loewnerMaximalMaps id) :=
  loewnerMaximalMaps_satisfiesMaximalLoewnerEquation continuous_id

-- `g_{1/8} : H_{1/8} → ℍ` is a bijection; `H_{1/8}` is open and connected.
example : BijOn (loewnerMaximalMaps (fun _ => 0) (1 / 8))
    (loewnerUnswallowedDomain (fun _ => 0) (1 / 8)) upperHalfPlaneSet :=
  loewnerMaximalMaps_bijOn_upperHalfPlane continuous_const (by norm_num)
example : IsOpen (loewnerUnswallowedDomain (fun _ => 0) (1 / 8)) ∧
    IsConnected (loewnerUnswallowedDomain (fun _ => 0) (1 / 8)) :=
  ⟨isOpen_loewnerUnswallowedDomain continuous_const (by norm_num),
    isConnected_loewnerUnswallowedDomain continuous_const (by norm_num)⟩

-- The homeomorphism `H_{1/8} ≃ₜ ℍ` sends `I` to `I √(1/2)`.
example (hI : I ∈ loewnerUnswallowedDomain (fun _ => 0) (1 / 8)) :
    ((loewnerMaximalMapsHomeomorph (W := fun _ => 0) continuous_const
      (t := 1 / 8) (by norm_num) ⟨I, hI⟩ : upperHalfPlaneSet) : ℂ) =
      I * ((Real.sqrt (1 / 2) : ℝ) : ℂ) := by
  change loewnerMaximalMaps (fun _ => 0) (1 / 8) I = _
  rw [maximalMaps_I (by norm_num) (by norm_num), gI]
  norm_num

end MathlibExtTest.StatMech.Analysis.Complex.Loewner.LoewnerMaximal
