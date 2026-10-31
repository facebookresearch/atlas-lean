/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.InnerProductSpace.Continuous

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.ToeplitzHausdorffWanted

open scoped _root_.InnerProductSpace

/-- **Numerical range.** For a bounded linear operator $A$ on a complex inner product space $E$,
the numerical range of $A$ is the set
$W(A) = \{\langle A x, x \rangle : x \in E,\ \|x\| = 1\} \subseteq \mathbb{C}$, where the inner
product $\langle \cdot, \cdot \rangle$ of $E$ is conjugate-linear in its first argument and linear
in its second. -/
noncomputable def numericalRange
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) : Set ℂ :=
  { c : ℂ | ∃ x : E, ‖x‖ = 1 ∧ inner (𝕜 := ℂ) (A x) x = c }

/-- **Membership in the numerical range.** Let $A$ be a bounded linear operator on a complex inner
product space $E$. A complex number $c$ lies in the numerical range $W(A)$ if and only if there is
a vector $x \in E$ with $\|x\| = 1$ and $\langle A x, x \rangle = c$. -/
theorem mem_numericalRange_iff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) (c : ℂ) :
    c ∈ numericalRange A ↔ ∃ x : E, ‖x‖ = 1 ∧ inner (𝕜 := ℂ) (A x) x = c :=
  Iff.rfl

/-- **Unit vectors give points of the numerical range.** Let $A$ be a bounded linear operator on a
complex inner product space $E$. For every $x \in E$ with $\|x\| = 1$, the number
$\langle A x, x \rangle$ lies in the numerical range $W(A)$. -/
theorem inner_mem_numericalRange
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) {x : E} (hx : ‖x‖ = 1) :
    inner (𝕜 := ℂ) (A x) x ∈ numericalRange A :=
  ⟨x, hx, rfl⟩

/-- The exponential `exp (φ * I)` has norm one. -/
private theorem exp_im_unit (φ : ℝ) : ‖Complex.exp ((φ : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.exp_ofReal_mul_I, Complex.ofReal_cos, Complex.ofReal_sin,
    Complex.norm_cos_add_sin_mul_I]

/-- Shifting the phase by `π` negates the exponential. -/
private theorem exp_im_add_pi (φ : ℝ) :
    Complex.exp (((φ + Real.pi : ℝ) : ℂ) * Complex.I)
      = -Complex.exp ((φ : ℂ) * Complex.I) := by
  have h : (((φ + Real.pi : ℝ) : ℂ) * Complex.I)
      = (φ : ℂ) * Complex.I + ((Real.pi : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_add_pi_mul_I]

/-- **Toeplitz–Hausdorff theorem without completeness.** The numerical range of a bounded linear
operator on a complex inner product space is convex. Completeness of the space is not needed. -/
theorem toeplitz_hausdorff_general
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) :
    Convex ℝ (numericalRange A) := by
  intro p hp q hq a b ha hb hab
  obtain ⟨x, hx1, hpx⟩ := hp
  obtain ⟨y, hy1, hqy⟩ := hq
  by_cases hval : p = q
  · subst hval
    have hseg : a • p + b • p = p := by rw [← add_smul, hab, one_smul]
    rw [hseg]
    exact ⟨x, hx1, hpx⟩
  · -- Normalize around the midpoint `m`, half-difference `d`.
    have hpm : p = (p + q) / 2 + (p - q) / 2 := by ring
    have hqm : q = (p + q) / 2 - (p - q) / 2 := by ring
    set m : ℂ := (p + q) / 2 with hm
    set d : ℂ := (p - q) / 2 with hd
    have hd0 : d ≠ 0 := by
      intro h
      apply hval
      rw [hpm, hqm, h, add_zero, sub_zero]
    set rv : ℝ := ‖d‖ with hrv
    have hrv0 : 0 < rv := norm_pos_iff.mpr hd0
    have hrvC : ((rv : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hrv0
    set u : ℂ := d / ((rv : ℝ) : ℂ) with hu
    have hu0 : u ≠ 0 := by
      rw [hu]
      exact div_ne_zero hd0 hrvC
    have hu_inv : u⁻¹ * d = ((rv : ℝ) : ℂ) := by
      rw [hu, inv_div]
      exact div_mul_cancel₀ _ hd0
    have hud : u * ((rv : ℝ) : ℂ) = d := by
      rw [← hu_inv]
      exact mul_inv_cancel_left₀ hu0 d
    -- Centered cross-term constants.
    set Cx : ℂ := inner (𝕜 := ℂ) (A y) x - m * inner (𝕜 := ℂ) y x with hCx
    set Dx : ℂ := inner (𝕜 := ℂ) (A x) y - m * inner (𝕜 := ℂ) x y with hDx
    -- Phase exponential and its basic facts.
    set α : ℝ → ℂ := fun φ => Complex.exp ((φ : ℂ) * Complex.I) with hα
    have hαne : ∀ φ : ℝ, α φ ≠ 0 := fun φ => Complex.exp_ne_zero _
    have hαnorm : ∀ φ : ℝ, ‖α φ‖ = 1 := fun φ => exp_im_unit φ
    have hαconj : ∀ φ : ℝ, α φ * (starRingEnd ℂ) (α φ) = 1 := by
      intro φ
      rw [RCLike.mul_conj, hαnorm φ]
      norm_num
    have hαflip : ∀ φ : ℝ, α (φ + Real.pi) = -α φ := fun φ => exp_im_add_pi φ
    have hconjflip : ∀ φ : ℝ, (starRingEnd ℂ) (α (φ + Real.pi))
        = -(starRingEnd ℂ) (α φ) := by
      intro φ
      rw [hαflip φ, map_neg]
    have hαcont : Continuous α := by
      simp only [hα]
      exact Complex.continuous_exp.comp
        (Complex.continuous_ofReal.mul
          (continuous_const : Continuous fun _ : ℝ => Complex.I))
    -- The real function whose zero gives the good phase.
    set F : ℝ → ℝ := fun φ =>
      (u⁻¹ * ((starRingEnd ℂ) (α φ) * Cx + α φ * Dx)).im with hF
    have hFcont : Continuous F := by
      have e1 : Continuous fun φ : ℝ => (starRingEnd ℂ) (α φ) * Cx :=
        (Complex.continuous_conj.comp hαcont).mul
          (continuous_const : Continuous fun _ : ℝ => Cx)
      have e2 : Continuous fun φ : ℝ => α φ * Dx :=
        hαcont.mul (continuous_const : Continuous fun _ : ℝ => Dx)
      have e3 : Continuous fun φ : ℝ
          => (starRingEnd ℂ) (α φ) * Cx + α φ * Dx := e1.add e2
      have e4 : Continuous fun φ : ℝ
          => u⁻¹ * ((starRingEnd ℂ) (α φ) * Cx + α φ * Dx) :=
        (continuous_const : Continuous fun _ : ℝ => u⁻¹).mul e3
      have e5 : Continuous fun φ : ℝ
          => (u⁻¹ * ((starRingEnd ℂ) (α φ) * Cx + α φ * Dx)).im :=
        Complex.continuous_im.comp e4
      simp only [hF]
      exact e5
    have hFflip : ∀ φ : ℝ, F (φ + Real.pi) = -F φ := by
      intro φ
      have e : (u⁻¹ * ((starRingEnd ℂ) (α (φ + Real.pi)) * Cx
          + α (φ + Real.pi) * Dx))
          = -(u⁻¹ * ((starRingEnd ℂ) (α φ) * Cx + α φ * Dx)) := by
        rw [hconjflip φ, hαflip φ]
        ring
      change (u⁻¹ * ((starRingEnd ℂ) (α (φ + Real.pi)) * Cx
          + α (φ + Real.pi) * Dx)).im
        = -(u⁻¹ * ((starRingEnd ℂ) (α φ) * Cx + α φ * Dx)).im
      rw [e, Complex.neg_im]
    have hFpi : F Real.pi = -F 0 := by
      have h1 := hFflip 0
      rwa [zero_add] at h1
    obtain ⟨φ₀, hφ₀mem, hφ₀⟩ : ∃ φ₀ ∈ Set.Icc (0 : ℝ) Real.pi, F φ₀ = 0 := by
      by_cases h0 : F 0 = 0
      · exact ⟨0, ⟨le_refl 0, Real.pi_nonneg⟩, h0⟩
      · rcases lt_or_gt_of_ne h0 with hneg | hpos
        · have hmem : (0 : ℝ) ∈ Set.Icc (F 0) (F Real.pi) := by
            rw [Set.mem_Icc, hFpi]
            exact ⟨le_of_lt hneg, by linarith⟩
          have h := intermediate_value_Icc Real.pi_nonneg hFcont.continuousOn hmem
          rw [Set.mem_image] at h
          obtain ⟨t, ht, hFt⟩ := h
          exact ⟨t, ht, hFt⟩
        · have hmem : (0 : ℝ) ∈ Set.Icc (F Real.pi) (F 0) := by
            rw [Set.mem_Icc, hFpi]
            exact ⟨by linarith, le_of_lt hpos⟩
          have h := intermediate_value_Icc' Real.pi_nonneg hFcont.continuousOn hmem
          rw [Set.mem_image] at h
          obtain ⟨t, ht, hFt⟩ := h
          exact ⟨t, ht, hFt⟩
    -- The cross term `K` is real.
    set K : ℂ := u⁻¹ * ((starRingEnd ℂ) (α φ₀) * Cx + α φ₀ * Dx) with hK
    have hKim : K.im = 0 := by
      rw [hK]
      exact hφ₀
    have hKre : K = ((K.re : ℝ) : ℂ) := by
      have h := Complex.re_add_im K
      rw [hKim, Complex.ofReal_zero, zero_mul, add_zero] at h
      exact h.symm
    by_cases hdep : ∃ μ : ℂ, y = μ • x
    · -- Dependent case: the two values coincide.
      obtain ⟨μ, hμ⟩ := hdep
      have hμ1 : ‖μ‖ = 1 := by
        have e : ‖y‖ = ‖μ‖ * ‖x‖ := by rw [hμ, norm_smul]
        rw [hy1, hx1, mul_one] at e
        exact e.symm
      have e : inner (𝕜 := ℂ) (A (μ • x)) (μ • x)
          = (starRingEnd ℂ) μ * (μ * p) := by
        rw [map_smul, inner_smul_left, inner_smul_right, hpx]
      have hμμ : (starRingEnd ℂ) μ * μ = 1 := by
        rw [RCLike.conj_mul, hμ1]
        norm_num
      have h2 : (starRingEnd ℂ) μ * (μ * p) = p := by
        rw [← mul_assoc, hμμ, one_mul]
      rw [hμ, e, h2] at hqy
      exact absurd hqy hval
    · -- Independent case: build a curve of unit vectors.
      have hx0 : x ≠ 0 := by
        intro h
        rw [h, norm_zero] at hx1
        norm_num at hx1
      set c1 : ℝ → ℂ := fun t => ((Real.cos t : ℝ) : ℂ) with hc1
      set c2 : ℝ → ℂ := fun t => ((Real.sin t : ℝ) : ℂ) * α φ₀ with hc2
      set z : ℝ → E := fun t => c1 t • x + c2 t • y with hz
      have hc1conj : ∀ t : ℝ, (starRingEnd ℂ) (c1 t) = c1 t := by
        intro t
        simp only [hc1]
        exact Complex.conj_ofReal _
      have hc2conj : ∀ t : ℝ, (starRingEnd ℂ) (c2 t)
          = ((Real.sin t : ℝ) : ℂ) * (starRingEnd ℂ) (α φ₀) := by
        intro t
        simp only [hc2]
        rw [map_mul, Complex.conj_ofReal]
      have hz_ne : ∀ t : ℝ, z t ≠ 0 := by
        intro t ht
        have e : c1 t • x + c2 t • y = 0 := ht
        by_cases h2 : c2 t = 0
        · have hsin0 : Real.sin t = 0 := by
            have hmul : ((Real.sin t : ℝ) : ℂ) * α φ₀ = 0 := h2
            rcases mul_eq_zero.mp hmul with h | h
            · exact Complex.ofReal_eq_zero.mp h
            · exact absurd h (hαne φ₀)
          have hcos0 : Real.cos t ≠ 0 := by
            intro hc
            have hsq := Real.sin_sq_add_cos_sq t
            rw [hsin0, hc] at hsq
            norm_num at hsq
          have hc1ne : c1 t ≠ 0 := by
            simp only [hc1, ne_eq, Complex.ofReal_eq_zero]
            exact hcos0
          have hzx : c1 t • x = 0 := by
            have h0 : c2 t • y = 0 := by simp [h2]
            rwa [h0, add_zero] at e
          have hx00 : x = 0 := by
            have h3 := congrArg ((c1 t)⁻¹ • ·) hzx
            simp only [inv_smul_smul₀ hc1ne, smul_zero] at h3
            exact h3
          exact hx0 hx00
        · have e2 : c2 t • y = -(c1 t • x) := by
            have h := eq_neg_of_add_eq_zero_left e
            rw [h]
            simp
          have ey : y = (c2 t)⁻¹ • (c2 t • y) := (inv_smul_smul₀ h2 y).symm
          rw [e2, smul_neg, ← mul_smul, ← neg_smul] at ey
          exact hdep ⟨-((c2 t)⁻¹ * c1 t), ey⟩
      set N : ℝ → ℝ := fun t => ‖z t‖ with hN
      have hNpos : ∀ t : ℝ, 0 < N t := fun t => norm_pos_iff.mpr (hz_ne t)
      have hNne : ∀ t : ℝ, N t ≠ 0 := fun t => ne_of_gt (hNpos t)
      have hc1cont : Continuous c1 :=
        Complex.continuous_ofReal.comp Real.continuous_cos
      have hc2cont : Continuous c2 :=
        (Complex.continuous_ofReal.comp Real.continuous_sin).mul
          (continuous_const : Continuous fun _ : ℝ => α φ₀)
      have hzcont : Continuous z :=
        (hc1cont.smul (continuous_const : Continuous fun _ : ℝ => x)).add
          (hc2cont.smul (continuous_const : Continuous fun _ : ℝ => y))
      have hNcont : Continuous N := hzcont.norm
      set w : ℝ → E := fun t => (((N t)⁻¹ : ℝ) : ℂ) • z t with hw
      have hwcont : Continuous w := by
        have hscont : Continuous fun t : ℝ => (((N t)⁻¹ : ℝ) : ℂ) :=
          Complex.continuous_ofReal.comp
            (hNcont.inv₀ (fun t => ne_of_gt (hNpos t)))
        exact hscont.smul hzcont
      have hw1 : ∀ t : ℝ, ‖w t‖ = 1 := by
        intro t
        have hs : ‖(((N t)⁻¹ : ℝ) : ℂ)‖ = (N t)⁻¹ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hNpos t))]
        simp only [hw]
        rw [norm_smul, hs]
        change (N t)⁻¹ * N t = 1
        exact inv_mul_cancel₀ (hNne t)
      set V : ℝ → ℂ := fun t => inner (𝕜 := ℂ) (A (w t)) (w t) with hV
      have hVcont : Continuous V := by
        have e : Continuous fun t : ℝ => (A (w t), w t) :=
          (A.cont.comp hwcont).prodMk hwcont
        have e2 : Continuous fun t : ℝ => inner (𝕜 := ℂ) (A (w t)) (w t) :=
          continuous_inner.comp e
        simp only [hV]
        exact e2
      set G : ℝ → ℝ := fun t => (u⁻¹ * (V t - m)).re with hG
      have hGcont : Continuous G := by
        have e1 : Continuous fun t : ℝ => V t - m :=
          hVcont.sub (continuous_const : Continuous fun _ : ℝ => m)
        have e2 : Continuous fun t : ℝ => u⁻¹ * (V t - m) :=
          (continuous_const : Continuous fun _ : ℝ => u⁻¹).mul e1
        have e3 : Continuous fun t : ℝ => (u⁻¹ * (V t - m)).re :=
          Complex.continuous_re.comp e2
        simp only [hG]
        exact e3
      have hxx : inner (𝕜 := ℂ) x x = 1 := by
        have e : inner (𝕜 := ℂ) x x = ((‖x‖ : ℂ)) ^ 2 :=
          inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x
        rw [e, hx1]
        norm_num
      have hyy : inner (𝕜 := ℂ) y y = 1 := by
        have e : inner (𝕜 := ℂ) y y = ((‖y‖ : ℂ)) ^ 2 :=
          inner_self_eq_norm_sq_to_K (𝕜 := ℂ) y
        rw [e, hy1]
        norm_num
      have eA : ∀ t : ℝ, A (z t) = c1 t • A x + c2 t • A y := by
        intro t
        simp only [hz]
        rw [map_add, map_smul, map_smul]
      have eZ : ∀ t : ℝ, inner (𝕜 := ℂ) (A (z t)) (z t)
          = (starRingEnd ℂ) (c1 t) * (c1 t * p)
            + (starRingEnd ℂ) (c2 t) * (c1 t * inner (𝕜 := ℂ) (A y) x)
            + ((starRingEnd ℂ) (c1 t) * (c2 t * inner (𝕜 := ℂ) (A x) y)
              + (starRingEnd ℂ) (c2 t) * (c2 t * q)) := by
        intro t
        rw [eA t]
        simp only [hz]
        simp only [inner_add_left, inner_add_right, inner_smul_left,
          inner_smul_right, hpx, hqy]
        ring
      have eN : ∀ t : ℝ, inner (𝕜 := ℂ) (z t) (z t)
          = (starRingEnd ℂ) (c1 t) * (c1 t * 1)
            + (starRingEnd ℂ) (c2 t) * (c1 t * inner (𝕜 := ℂ) y x)
            + ((starRingEnd ℂ) (c1 t) * (c2 t * inner (𝕜 := ℂ) x y)
              + (starRingEnd ℂ) (c2 t) * (c2 t * 1)) := by
        intro t
        simp only [hz]
        simp only [inner_add_left, inner_add_right, inner_smul_left,
          inner_smul_right, hxx, hyy]
        ring
      have hexpand : ∀ t : ℝ, inner (𝕜 := ℂ) (A (z t)) (z t)
          - m * inner (𝕜 := ℂ) (z t) (z t)
          = (c1 t * (starRingEnd ℂ) (c1 t)) * d
            + (c2 t * (starRingEnd ℂ) (c2 t)) * (-d)
            + ((c1 t * (starRingEnd ℂ) (c2 t)) * Cx
              + (c2 t * (starRingEnd ℂ) (c1 t)) * Dx) := by
        intro t
        rw [eZ t, eN t]
        simp only [hpm, hqm, hCx, hDx]
        ring
      have e1c : ∀ t : ℝ, c1 t * (starRingEnd ℂ) (c1 t)
          = ((Real.cos t ^ 2 : ℝ) : ℂ) := by
        intro t
        rw [hc1conj t]
        simp only [hc1, Complex.ofReal_pow]
        ring
      have e2c : ∀ t : ℝ, c2 t * (starRingEnd ℂ) (c2 t)
          = ((Real.sin t ^ 2 : ℝ) : ℂ) := by
        intro t
        rw [hc2conj t]
        simp only [hc2, Complex.ofReal_pow]
        linear_combination ((Real.sin t : ℝ) : ℂ) ^ 2 * hαconj φ₀
      have e3c : ∀ t : ℝ, c1 t * (starRingEnd ℂ) (c2 t)
          = ((Real.cos t * Real.sin t : ℝ) : ℂ)
            * (starRingEnd ℂ) (α φ₀) := by
        intro t
        rw [hc2conj t]
        simp only [hc1, Complex.ofReal_mul]
        ring
      have e4c : ∀ t : ℝ, c2 t * (starRingEnd ℂ) (c1 t)
          = ((Real.cos t * Real.sin t : ℝ) : ℂ) * α φ₀ := by
        intro t
        rw [hc1conj t]
        simp only [hc1, hc2, Complex.ofReal_mul]
        ring
      have hW : ∀ t : ℝ, u⁻¹ * (inner (𝕜 := ℂ) (A (z t)) (z t)
          - m * inner (𝕜 := ℂ) (z t) (z t))
          = ((Real.cos t ^ 2 : ℝ) : ℂ) * ((rv : ℝ) : ℂ)
            - ((Real.sin t ^ 2 : ℝ) : ℂ) * ((rv : ℝ) : ℂ)
            + ((Real.cos t * Real.sin t : ℝ) : ℂ) * ((K.re : ℝ) : ℂ) := by
        intro t
        have eK : u⁻¹ * ((starRingEnd ℂ) (α φ₀) * Cx + α φ₀ * Dx)
            = ((K.re : ℝ) : ℂ) := by
          rw [← hK]
          exact hKre
        rw [hexpand t, e1c t, e2c t, e3c t, e4c t]
        linear_combination ((Real.cos t ^ 2 : ℝ) : ℂ) * hu_inv
          - ((Real.sin t ^ 2 : ℝ) : ℂ) * hu_inv
          + ((Real.cos t * Real.sin t : ℝ) : ℂ) * eK
      have hsconj : ∀ t : ℝ, (starRingEnd ℂ) (((N t)⁻¹ : ℝ) : ℂ)
          = (((N t)⁻¹ : ℝ) : ℂ) := fun t => Complex.conj_ofReal _
      have hZZ : ∀ t : ℝ, inner (𝕜 := ℂ) (z t) (z t)
          = (((N t) ^ 2 : ℝ) : ℂ) := by
        intro t
        have e : inner (𝕜 := ℂ) (z t) (z t) = ((‖z t‖ : ℂ)) ^ 2 :=
          inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (z t)
        rw [e]
        simp only [hN]
        rw [Complex.ofReal_pow]
      have hVw : ∀ t : ℝ, V t
          = (((N t)⁻¹ * (N t)⁻¹ : ℝ) : ℂ)
            * inner (𝕜 := ℂ) (A (z t)) (z t) := by
        intro t
        simp only [hV, hw]
        rw [map_smul, inner_smul_left, inner_smul_right, hsconj t,
          ← mul_assoc, ← Complex.ofReal_mul]
      have hscN : ∀ t : ℝ, (((N t)⁻¹ * (N t)⁻¹ : ℝ) : ℂ)
          * inner (𝕜 := ℂ) (z t) (z t) = 1 := by
        intro t
        rw [hZZ t, ← Complex.ofReal_mul]
        have hNt : (N t)⁻¹ * N t = 1 := inv_mul_cancel₀ (hNne t)
        have hss : (N t)⁻¹ * (N t)⁻¹ * (N t ^ 2) = 1 := by
          have e : (N t)⁻¹ * (N t)⁻¹ * (N t ^ 2)
              = ((N t)⁻¹ * N t) * ((N t)⁻¹ * N t) := by ring
          rw [e, hNt, mul_one]
        rw [hss, Complex.ofReal_one]
      have hmaster : ∀ t : ℝ, V t - m
          = (((N t)⁻¹ * (N t)⁻¹ : ℝ) : ℂ)
            * (inner (𝕜 := ℂ) (A (z t)) (z t)
              - m * inner (𝕜 := ℂ) (z t) (z t)) := by
        intro t
        linear_combination (hVw t) + m * (hscN t)
      have hmaster2 : ∀ t : ℝ, u⁻¹ * (V t - m)
          = (((N t)⁻¹ * (N t)⁻¹ : ℝ) : ℂ)
            * (((Real.cos t ^ 2 : ℝ) : ℂ) * ((rv : ℝ) : ℂ)
              - ((Real.sin t ^ 2 : ℝ) : ℂ) * ((rv : ℝ) : ℂ)
              + ((Real.cos t * Real.sin t : ℝ) : ℂ) * ((K.re : ℝ) : ℂ)) := by
        intro t
        rw [hmaster t, mul_left_comm, hW t]
      have hImw : ∀ t : ℝ, (u⁻¹ * (V t - m)).im = 0 := by
        intro t
        rw [hmaster2 t]
        simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, zero_mul, add_zero, sub_zero]
      have hVeq : ∀ t : ℝ, V t = m + u * (((G t : ℝ)) : ℂ) := by
        intro t
        have hGre : (((G t : ℝ)) : ℂ) = u⁻¹ * (V t - m) := by
          have h := Complex.re_add_im (u⁻¹ * (V t - m))
          rw [hImw t] at h
          have hGdef : G t = (u⁻¹ * (V t - m)).re := rfl
          rw [hGdef]
          simpa using h
        have e2 : u * (((G t : ℝ)) : ℂ) = V t - m := by
          rw [hGre]
          exact mul_inv_cancel_left₀ hu0 _
        linear_combination (-e2)
      have hG0 : G 0 = rv := by
        have ec1 : c1 0 = 1 := by
          simp only [hc1]
          rw [Real.cos_zero, Complex.ofReal_one]
        have ec2 : c2 0 = 0 := by
          simp only [hc2]
          rw [Real.sin_zero, Complex.ofReal_zero, zero_mul]
        have ez : z 0 = x := by
          simp only [hz]
          rw [ec1, ec2, one_smul, zero_smul, add_zero]
        have eN0 : N 0 = 1 := by
          simp only [hN]
          rw [ez, hx1]
        have ew : w 0 = x := by
          have e1 : ((((1 : ℝ))⁻¹ : ℝ) : ℂ) = 1 := by simp
          simp only [hw]
          rw [eN0, ez, e1, one_smul]
        have eV : V 0 = p := by
          simp only [hV]
          rw [ew]
          exact hpx
        have epm : p - m = d := by linear_combination hpm
        have eud : u⁻¹ * (p - m) = ((rv : ℝ) : ℂ) := by rw [epm, hu_inv]
        change (u⁻¹ * (V 0 - m)).re = rv
        rw [eV, eud, Complex.ofReal_re]
      have hGpi2 : G (Real.pi / 2) = -rv := by
        have ec1 : c1 (Real.pi / 2) = 0 := by
          simp only [hc1]
          rw [Real.cos_pi_div_two, Complex.ofReal_zero]
        have ec2 : c2 (Real.pi / 2) = α φ₀ := by
          simp only [hc2]
          rw [Real.sin_pi_div_two, Complex.ofReal_one, one_mul]
        have ez : z (Real.pi / 2) = α φ₀ • y := by
          simp only [hz]
          rw [ec1, ec2, zero_smul, zero_add]
        have eN0 : N (Real.pi / 2) = 1 := by
          simp only [hN]
          rw [ez, norm_smul, hαnorm φ₀, hy1, mul_one]
        have ew : w (Real.pi / 2) = α φ₀ • y := by
          have e1 : ((((1 : ℝ))⁻¹ : ℝ) : ℂ) = 1 := by simp
          simp only [hw]
          rw [eN0, ez, e1, one_smul]
        have eV : V (Real.pi / 2) = q := by
          simp only [hV]
          rw [ew, map_smul, inner_smul_left, inner_smul_right, hqy]
          linear_combination q * hαconj φ₀
        have eqm : q - m = -d := by linear_combination hqm
        have eud : u⁻¹ * (q - m) = -((rv : ℝ) : ℂ) := by
          rw [eqm, mul_neg, hu_inv]
        change (u⁻¹ * (V (Real.pi / 2) - m)).re = -rv
        rw [eV, eud, Complex.neg_re, Complex.ofReal_re]
      have hrv_le : (0 : ℝ) ≤ Real.pi / 2 := le_of_lt Real.pi_div_two_pos
      set s₀ : ℝ := (2 * a - 1) * rv with hs₀
      have hs₀mem : s₀ ∈ Set.Icc (-rv) rv := by
        have ha1 : a ≤ 1 := by linarith [hab, hb]
        rw [Set.mem_Icc, hs₀]
        constructor
        · nlinarith [mul_nonneg ha (le_of_lt hrv0)]
        · nlinarith [mul_le_mul_of_nonneg_right ha1 (le_of_lt hrv0)]
      have hmem : s₀ ∈ Set.Icc (G (Real.pi / 2)) (G 0) := by
        rw [hGpi2, hG0]
        exact hs₀mem
      have h := intermediate_value_Icc' hrv_le hGcont.continuousOn hmem
      rw [Set.mem_image] at h
      obtain ⟨t, ht, hGt⟩ := h
      have hfin : a • p + b • q = V t := by
        have hb1 : b = 1 - a := by linarith [hab]
        rw [hb1, hVeq t, hGt]
        change ((a : ℝ) : ℂ) * p + ((1 - a : ℝ) : ℂ) * q
          = m + u * ((s₀ : ℝ) : ℂ)
        rw [hpm, hqm, hs₀]
        have hud2 : u * ((((2 * a - 1) * rv : ℝ)) : ℂ)
            = (2 * ((a : ℝ) : ℂ) - 1) * d := by
          push_cast
          rw [← hud]
          ring
        rw [hud2]
        push_cast
        ring
      exact ⟨w t, hw1 t, hfin.symm⟩


/--
**Toeplitz–Hausdorff theorem.** The numerical range of a bounded linear operator on a complex
Hilbert space is convex.

Proves `Wanted` entry `toeplitz_hausdorff`.

Source: O. Toeplitz, Das algebraische Analogon zu einem Satze von Fejer, Math. Z. 2 (1918), 187-197,
DOI 10.1007/BF01212904; F. Hausdorff, Der Wertvorrat einer Bilinearform, Math. Z. 3 (1919), 314-316,
DOI 10.1007/BF01292610.
It follows from `toeplitz_hausdorff_general`; the hypothesis `CompleteSpace E` is unused and keeps
the source's shape.
-/
@[nolint unusedArguments]
theorem toeplitz_hausdorff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A : E →L[ℂ] E) :
    Convex ℝ (numericalRange A) :=
  toeplitz_hausdorff_general A

end MathlibExt.Analysis.InnerProductSpace.ToeplitzHausdorffWanted
