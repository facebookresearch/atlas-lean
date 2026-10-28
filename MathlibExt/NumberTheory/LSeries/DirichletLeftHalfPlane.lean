/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LSeries.DirichletXi
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import MathlibExt.NumberTheory.LSeries.RiemannZetaLogDerivZeros
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# `L'/L(s, χ)` on the left half-plane

Through the functional equation, the logarithmic derivative of a primitive Dirichlet `L`-function
on `Re s < 0` is expressed by its values on `Re s > 1`, and is bounded on `Re s ≤ -1` away from the
trivial zeros. We also factor `L(s, χ) = ξ(s, χ) H(s)` with an explicit entire cofactor `H`.

## Main statements

* `DirichletCharacter.exists_parity_gammaFactor_eq`: the parity `a ∈ {0, 1}` of `χ`, with
  `(1 - χ(-1))/2 = a` and both `χ` and `χ⁻¹` having gamma factor `Γℝ(s + a)`.
* `DirichletCharacter.LFunction_eq_xi_mul_cofactor`: for modulus `q ≠ 1`,
  `L(s, χ) = ξ(s, χ) q^{-(s+a)/2} π^{(s+a)/2} Γ((s+a)/2)⁻¹`, with the cofactor entire
  (`DirichletCharacter.differentiable_xi_cofactor`) and of logarithmic derivative
  `-log q / 2 + log π / 2 - ψ((s+a)/2)/2` (`DirichletCharacter.logDeriv_xi_cofactor`).
* `DirichletCharacter.IsPrimitive.rootNumber_ne_zero`: the root number of a primitive character
  does not vanish.
* `DirichletCharacter.LFunction_ne_zero_and_logDeriv_eq_of_re_neg`: for primitive `χ` and
  `Re s < 0` off the trivial zeros,
  `L'/L(s, χ) = -log q + log π - ψ((1-s+a)/2)/2 - ψ(1-(s+a)/2)/2 + (π/2) cot(π(s+a)/2)
    - L'/L(1-s, χ⁻¹)`.
* `DirichletCharacter.exists_norm_logDeriv_LFunction_le_of_two_le_re`: `L'/L(s, χ)` is bounded on
  `Re s ≥ 2`, uniformly in `χ`.
* `DirichletCharacter.exists_norm_logDeriv_LFunction_le_of_re_le_neg_one`:
  `‖L'/L(s, χ)‖ ≤ log q + log (‖s‖ + 2) + C` on `Re s ≤ -1` where `|cot(π(s+a)/2)| ≤ 2`.
-/

@[expose] public section

open Filter Topology ArithmeticFunction LSeries

namespace DirichletCharacter

/-! ### The parity of `χ` -/

/-- The parity `a ∈ {0, 1}` of `χ`: `(1 - χ(-1))/2 = a`, and the gamma factors of `χ` and `χ⁻¹` are
`Γℝ(s + a)`. -/
theorem exists_parity_gammaFactor_eq {N : ℕ} (χ : DirichletCharacter ℂ N) :
    ∃ a : ℝ, (a = 0 ∨ a = 1) ∧ (1 - χ (-1)) / 2 = (a : ℂ) ∧
      (∀ w, χ.gammaFactor w = Complex.Gammaℝ (w + a)) ∧
      (∀ w, χ⁻¹.gammaFactor w = Complex.Gammaℝ (w + a)) := by
  have hinv : χ⁻¹ (-1) = χ (-1) := by
    rw [MulChar.inv_apply_eq_inv']
    rcases χ.even_or_odd with h | h
    · rw [show χ (-1) = 1 from h, inv_one]
    · rw [show χ (-1) = -1 from h, inv_neg, inv_one]
  rcases χ.even_or_odd with h | h
  · have h' : χ⁻¹.Even := hinv.trans h
    refine ⟨0, Or.inl rfl, ?_, fun w => ?_, fun w => ?_⟩
    · rw [show χ (-1) = 1 from h]; simp
    · rw [h.gammaFactor_def]; simp
    · rw [h'.gammaFactor_def]; simp
  · have h' : χ⁻¹.Odd := hinv.trans h
    refine ⟨1, Or.inr rfl, ?_, fun w => ?_, fun w => ?_⟩
    · rw [show χ (-1) = -1 from h]; norm_num
    · rw [h.gammaFactor_def]; simp
    · rw [h'.gammaFactor_def]; simp

/-! ### `L = ξ H` with `H` entire -/

/-- `L(s, χ) = ξ(s, χ) q^{-(s+a)/2} π^{(s+a)/2} Γ((s+a)/2)⁻¹` for `χ` of parity `a` and modulus
`q ≠ 1`, at every `s`. -/
theorem LFunction_eq_xi_mul_cofactor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : q ≠ 1) {a : ℝ} (hapar : (1 - χ (-1)) / 2 = (a : ℂ))
    (hgf : ∀ w, χ.gammaFactor w = Complex.Gammaℝ (w + a)) (s : ℂ) :
    LFunction χ s = xi χ s * ((q : ℂ) ^ (-((s + a) / 2)) *
      ((Real.pi : ℂ) ^ ((s + a) / 2) * (Complex.Gamma ((s + a) / 2))⁻¹)) := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [LFunction_eq_completed_div_gammaFactor χ s (Or.inr hq), hgf, Complex.Gammaℝ_def, xi, hapar,
    Complex.cpow_neg, neg_div, Complex.cpow_neg]
  have h1 : (q : ℂ) ^ ((s + a) / 2) ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have h2 : (Real.pi : ℂ) ^ ((s + a) / 2) ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  rw [div_eq_mul_inv, mul_inv, inv_inv]
  field_simp

/-- The cofactor `H(s) = q^{-(s+a)/2} π^{(s+a)/2} Γ((s+a)/2)⁻¹` of `L = ξ H` is entire. -/
theorem differentiable_xi_cofactor (q : ℕ) [NeZero q] (a : ℝ) :
    Differentiable ℂ (fun s : ℂ => (q : ℂ) ^ (-((s + a) / 2)) *
      ((Real.pi : ℂ) ^ ((s + a) / 2) * (Complex.Gamma ((s + a) / 2))⁻¹)) := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  intro s
  have hl : DifferentiableAt ℂ (fun s : ℂ => (s + a) / 2) s := by fun_prop
  have hG : DifferentiableAt ℂ (fun s : ℂ => (Complex.Gamma ((s + a) / 2))⁻¹) s :=
    DifferentiableAt.comp (g := fun s : ℂ => (Complex.Gamma s)⁻¹)
      (f := fun s : ℂ => (s + a) / 2) s (Complex.differentiable_one_div_Gamma ((s + a) / 2)) hl
  exact (hl.neg.const_cpow (Or.inl hq0)).mul ((hl.const_cpow (Or.inl hpi)).mul hG)

/-- The cofactor `H` of `L = ξ H` vanishes only where `(s+a)/2 ∈ -ℕ`. -/
theorem xi_cofactor_ne_zero (q : ℕ) [NeZero q] (a : ℝ) {s : ℂ}
    (hs : ∀ n : ℕ, (s + a) / 2 ≠ -(n : ℂ)) :
    (q : ℂ) ^ (-((s + a) / 2)) *
      ((Real.pi : ℂ) ^ ((s + a) / 2) * (Complex.Gamma ((s + a) / 2))⁻¹) ≠ 0 := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine mul_ne_zero (by rw [Ne, Complex.cpow_eq_zero_iff]; tauto)
    (mul_ne_zero (by rw [Ne, Complex.cpow_eq_zero_iff]; tauto) (inv_ne_zero ?_))
  exact Complex.Gamma_ne_zero hs

/-- `H'/H(w) = -log q / 2 + log π / 2 - ψ((w+a)/2)/2` for the cofactor `H` of `L = ξ H`, off the
zeros of `H`. -/
theorem logDeriv_xi_cofactor (q : ℕ) [NeZero q] (a : ℝ) {w : ℂ}
    (hw : ∀ m : ℕ, (w + a) / 2 ≠ -m) :
    logDeriv (fun w : ℂ => (q : ℂ) ^ (-((w + a) / 2)) *
      ((Real.pi : ℂ) ^ ((w + a) / 2) * (Complex.Gamma ((w + a) / 2))⁻¹)) w =
      -(Complex.log q) / 2 + Complex.log Real.pi / 2 - Complex.digamma ((w + a) / 2) / 2 := by
  have hqc : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hΓ0 : Complex.Gamma ((w + a) / 2) ≠ 0 := Complex.Gamma_ne_zero hw
  have hΓd : DifferentiableAt ℂ Complex.Gamma ((w + a) / 2) :=
    Complex.differentiableAt_Gamma _ hw
  have hlin : HasDerivAt (fun w : ℂ => (w + a) / 2) (1 / 2) w := by
    simpa using ((hasDerivAt_id w).add_const (a : ℂ)).div_const 2
  have hlin' : HasDerivAt (fun w : ℂ => -((w + a) / 2)) (-(1 / 2)) w := hlin.neg
  have h1 := hlin'.const_cpow (c := (q : ℂ)) (Or.inl hqc)
  have h2 := hlin.const_cpow (c := (Real.pi : ℂ)) (Or.inl hpi)
  have h3 : HasDerivAt (fun w : ℂ => (Complex.Gamma ((w + a) / 2))⁻¹)
      (-(deriv Complex.Gamma ((w + a) / 2) * (1 / 2)) / Complex.Gamma ((w + a) / 2) ^ 2) w :=
    (hΓd.hasDerivAt.comp w hlin).inv hΓ0
  have hd := h1.fun_mul (h2.fun_mul h3)
  have hA : (q : ℂ) ^ (-((w + a) / 2)) ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hqc]
  have hB : (Real.pi : ℂ) ^ ((w + a) / 2) ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hpi]
  rw [logDeriv_apply, hd.deriv, Complex.digamma_def, logDeriv_apply]
  field_simp
  ring

/-! ### The left half-plane formula for `L'/L` -/

/-- The root number of a primitive Dirichlet character does not vanish. -/
theorem IsPrimitive.rootNumber_ne_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) : χ.rootNumber ≠ 0 := by
  intro h0
  have hFE := hχ.completedLFunction_one_sub (-1)
  rw [h0, mul_zero, zero_mul] at hFE
  have hL := LFunction_eq_completed_div_gammaFactor χ (1 - -1) (Or.inl (by norm_num))
  rw [hFE, zero_div] at hL
  exact LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num)) (by norm_num) hL

/-- The functional equation solved for `L(s, χ)` on `Re s < 0`. -/
private lemma LFunction_eq_rootNumber_mul_of_re_neg {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {a : ℝ}
    (hgf : ∀ w, χ.gammaFactor w = Complex.Gammaℝ (w + a))
    (hgf' : ∀ w, χ⁻¹.gammaFactor w = Complex.Gammaℝ (w + a)) (ha0 : 0 ≤ a)
    {s : ℂ} (hs : s.re < 0) (hsin : Complex.sin (Real.pi * ((s + a) / 2)) ≠ 0) :
    LFunction χ s = χ.rootNumber / Real.pi * ((N : ℂ) ^ (1 / 2 - s) *
      ((Real.pi : ℂ) ^ (s - 1 / 2) * (Complex.Gamma ((1 - s + a) / 2) *
        (Complex.Gamma (1 - (s + a) / 2) * (Complex.sin (Real.pi * ((s + a) / 2)) *
          LFunction χ⁻¹ (1 - s)))))) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have h1s : 1 - s ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)]
  have hFE := hχ.completedLFunction_one_sub (1 - s)
  rw [sub_sub_cancel] at hFE
  have hre : 0 < (1 - s + a).re := by simp; linarith
  have hG1 : Complex.Gammaℝ (1 - s + a) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hre
  have hL' := LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s) (Or.inl h1s)
  rw [hgf'] at hL'
  have hC : completedLFunction χ⁻¹ (1 - s) =
      Complex.Gammaℝ (1 - s + a) * LFunction χ⁻¹ (1 - s) := by
    rw [hL']; field_simp
  rw [hFE, hC, hgf, Complex.Gammaℝ_def, Complex.Gammaℝ_def]
  have hrefl := Complex.Gamma_mul_Gamma_one_sub ((s + a) / 2)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hprod : Complex.Gamma ((s + a) / 2) * Complex.Gamma (1 - (s + a) / 2) ≠ 0 := by
    rw [hrefl]; exact div_ne_zero hpi hsin
  have hΓ1 := right_ne_zero_of_mul hprod
  have hcp : (Real.pi : ℂ) ^ (-(1 - s + a) / 2) = (Real.pi : ℂ) ^ (s - 1 / 2) *
      (Real.pi : ℂ) ^ (-(s + a) / 2) := by
    rw [← Complex.cpow_add _ _ hpi]; congr 1; ring
  have hcp0 : (Real.pi : ℂ) ^ (-(s + a) / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have hN : (N : ℂ) ^ (1 - s - 1 / 2) = (N : ℂ) ^ (1 / 2 - s) := by congr 1; ring
  rw [hN, hcp]
  have hG : Complex.Gamma ((s + a) / 2) = Real.pi / Complex.sin (Real.pi * ((s + a) / 2)) /
      Complex.Gamma (1 - (s + a) / 2) := by
    rw [← hrefl, mul_div_cancel_right₀ _ hΓ1]
  rw [hG]
  field_simp

private lemma logDeriv_left_alg (c A B X1 X2 S L dL d1 d2 lN lπ co pp : ℂ) (hc : c ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (h1 : X1 ≠ 0) (h2 : X2 ≠ 0) (hS : S ≠ 0) (hL : L ≠ 0) :
    (c * (A * lN * -1 * (B * (X1 * (X2 * (S * L)))) +
        A * (B * lπ * 1 * (X1 * (X2 * (S * L))) +
          B * (d1 * X1 * (-1 / 2) * (X2 * (S * L)) +
            X1 * (d2 * X2 * (-1 / 2) * (S * L) +
              X2 * (co * (pp * (1 / 2)) * L + S * -dL)))))) /
        (c * (A * (B * (X1 * (X2 * (S * L)))))) =
      -lN + lπ - d1 / 2 - d2 / 2 + pp / 2 * (co / S) - dL / L := by
  field_simp
  ring

/-- **`L'/L` on the left half-plane.** For primitive `χ` mod `N` of parity `a` (gamma factors
`Γℝ(s + a)` for `χ` and `χ⁻¹`, `0 ≤ a ≤ 1`), `Re s < 0` and `sin (π(s+a)/2) ≠ 0`: `L(s, χ) ≠ 0`
and `L'/L(s, χ) = -log N + log π - ψ((1-s+a)/2)/2 - ψ(1-(s+a)/2)/2 + (π/2) cot(π(s+a)/2)
- L'/L(1-s, χ⁻¹)`, with `ψ` the digamma function. -/
theorem LFunction_ne_zero_and_logDeriv_eq_of_re_neg {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {a : ℝ}
    (hgf : ∀ w, χ.gammaFactor w = Complex.Gammaℝ (w + a))
    (hgf' : ∀ w, χ⁻¹.gammaFactor w = Complex.Gammaℝ (w + a)) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {s : ℂ} (hs : s.re < 0) (hsin : Complex.sin (Real.pi * ((s + a) / 2)) ≠ 0) :
    LFunction χ s ≠ 0 ∧
    deriv (LFunction χ) s / LFunction χ s =
      -Complex.log N + Complex.log Real.pi - Complex.digamma ((1 - s + a) / 2) / 2
        - Complex.digamma (1 - (s + a) / 2) / 2
        + Real.pi / 2 * (Complex.cos (Real.pi * ((s + a) / 2)) /
            Complex.sin (Real.pi * ((s + a) / 2)))
        - deriv (LFunction χ⁻¹) (1 - s) / LFunction χ⁻¹ (1 - s) := by
  set c : ℂ := χ.rootNumber / Real.pi with hc
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hc0 : c ≠ 0 := div_ne_zero hχ.rootNumber_ne_zero hpi
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hUo : IsOpen {w : ℂ | w.re < 0 ∧ Complex.sin (Real.pi * ((w + a) / 2)) ≠ 0} :=
    (isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_ne_fun (by fun_prop) continuous_const)
  have hev : LFunction χ =ᶠ[𝓝 s] fun w => c * ((N : ℂ) ^ (1 / 2 - w) *
      ((Real.pi : ℂ) ^ (w - 1 / 2) * (Complex.Gamma ((1 - w + a) / 2) *
        (Complex.Gamma (1 - (w + a) / 2) * (Complex.sin (Real.pi * ((w + a) / 2)) *
          LFunction χ⁻¹ (1 - w)))))) :=
    eventually_of_mem (hUo.mem_nhds ⟨hs, hsin⟩) fun w hw =>
      LFunction_eq_rootNumber_mul_of_re_neg hχ hgf hgf' ha0 hw.1 hw.2
  have hu1 : 0 < ((1 - s + a) / 2).re := by simp; linarith
  have hu2 : 0 < (1 - (s + a) / 2).re := by simp; linarith
  have hΓd : ∀ u : ℂ, 0 < u.re → DifferentiableAt ℂ Complex.Gamma u := fun u hu =>
    Complex.differentiableAt_Gamma u (fun m hm => by
      rw [hm] at hu; simp at hu; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  have hA : HasDerivAt (fun w : ℂ => (N : ℂ) ^ (1 / 2 - w))
      ((N : ℂ) ^ (1 / 2 - s) * Complex.log N * (-1)) s :=
    ((hasDerivAt_id s).const_sub (1 / 2 : ℂ)).const_cpow (Or.inl hN0)
  have hB : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) ^ (w - 1 / 2))
      ((Real.pi : ℂ) ^ (s - 1 / 2) * Complex.log Real.pi * 1) s :=
    ((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).const_cpow (Or.inl hpi)
  have hl1 : HasDerivAt (fun w : ℂ => (1 - w + a) / 2) (-1 / 2) s := by
    have := (((hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_id s)).add_const (a : ℂ)).div_const 2
    simpa using this
  have hl2 : HasDerivAt (fun w : ℂ => 1 - (w + a) / 2) (-1 / 2) s := by
    have := (((hasDerivAt_id s).add_const (a : ℂ)).div_const 2).const_sub (1 : ℂ)
    simpa [neg_div] using this
  have hl3 : HasDerivAt (fun w : ℂ => Real.pi * ((w + a) / 2)) (Real.pi * (1 / 2)) s := by
    have := (((hasDerivAt_id s).add_const (a : ℂ)).div_const 2).const_mul (Real.pi : ℂ)
    simpa using this
  have hC : HasDerivAt (fun w : ℂ => Complex.Gamma ((1 - w + a) / 2))
      (deriv Complex.Gamma ((1 - s + a) / 2) * (-1 / 2)) s :=
    (hΓd _ hu1).hasDerivAt.comp s hl1
  have hD : HasDerivAt (fun w : ℂ => Complex.Gamma (1 - (w + a) / 2))
      (deriv Complex.Gamma (1 - (s + a) / 2) * (-1 / 2)) s :=
    (hΓd _ hu2).hasDerivAt.comp s hl2
  have hE : HasDerivAt (fun w : ℂ => Complex.sin (Real.pi * ((w + a) / 2)))
      (Complex.cos (Real.pi * ((s + a) / 2)) * (Real.pi * (1 / 2))) s :=
    (Complex.hasDerivAt_sin _).comp s hl3
  have h1s : 1 ≤ (1 - s).re := by simp; linarith
  have h1s' : 1 - s ≠ 1 := fun h => by
    have : s = 0 := by linear_combination -h
    rw [this] at hs; simp at hs
  have hLd : DifferentiableAt ℂ (LFunction χ⁻¹) (1 - s) :=
    differentiableAt_LFunction _ _ (Or.inl h1s')
  have hG : HasDerivAt (fun w : ℂ => LFunction χ⁻¹ (1 - w)) (-deriv (LFunction χ⁻¹) (1 - s)) s :=
    hLd.hasDerivAt.comp_const_sub 1 s
  have hP := (hA.fun_mul (hB.fun_mul (hC.fun_mul (hD.fun_mul (hE.fun_mul hG))))).const_mul c
  have hAs : (N : ℂ) ^ (1 / 2 - s) ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have hBs : (Real.pi : ℂ) ^ (s - 1 / 2) ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have hCs := Complex.Gamma_ne_zero_of_re_pos hu1
  have hDs := Complex.Gamma_ne_zero_of_re_pos hu2
  have hGs : LFunction χ⁻¹ (1 - s) ≠ 0 := LFunction_ne_zero_of_one_le_re _ (Or.inr h1s') h1s
  have hLs : LFunction χ s ≠ 0 := by
    rw [hev.eq_of_nhds]
    exact mul_ne_zero hc0 (mul_ne_zero hAs (mul_ne_zero hBs (mul_ne_zero hCs
      (mul_ne_zero hDs (mul_ne_zero hsin hGs)))))
  refine ⟨hLs, ?_⟩
  have hψ : ∀ u : ℂ, Complex.Gamma u ≠ 0 →
      deriv Complex.Gamma u = Complex.digamma u * Complex.Gamma u := by
    intro u hu
    rw [Complex.digamma_def, logDeriv_apply]; field_simp
  rw [hev.deriv_eq, hP.deriv, hev.eq_of_nhds, hψ _ hCs, hψ _ hDs]
  exact logDeriv_left_alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc0 hAs hBs hCs hDs hsin hGs

/-! ### Bounds for `L'/L` to the right of `2` and to the left of `-1` -/

/-- `‖L'/L(s, χ)‖ ≤ ∑ Λ(n) / n²` on `Re s ≥ 2`, uniformly in `χ`. -/
theorem norm_logDeriv_LFunction_le_of_two_le_re {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 2 ≤ s.re) :
    ‖deriv (LFunction χ) s / LFunction χ s‖ ≤
      ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 2 n‖ := by
  open LSeries.notation in
  have hs1 : 1 < s.re := by linarith
  have hLS : -(deriv (LFunction χ) s / LFunction χ s) = LSeries (↗χ * ↗Λ) s := by
    rw [LSeries_twist_vonMangoldt_eq χ hs1, deriv_LFunction_eq_deriv_LSeries χ hs1,
      LFunction_eq_LSeries χ hs1, neg_div]
  have hnorm : ∀ n, ‖term (↗χ * ↗Λ) s n‖ ≤ ‖term (fun n => (Λ n : ℂ)) 2 n‖ := by
    intro n
    refine (norm_term_le (g := fun n => (Λ n : ℂ)) s ?_).trans ?_
    · simp only [Pi.mul_apply, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (norm_le_one χ _)
    · exact norm_term_le_of_re_le_re _ (by simpa using hs) n
  have hsum2 : Summable fun n => ‖term (fun n => (Λ n : ℂ)) 2 n‖ :=
    (LSeriesSummable_vonMangoldt (s := 2) (by norm_num)).norm
  have hsw := hsum2.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm
  rw [← norm_neg, hLS]
  exact (norm_tsum_le_tsum_norm hsw).trans (hsw.tsum_le_tsum hnorm hsum2)

/-- `L'/L(s, χ)` is bounded on `Re s ≥ 2`, uniformly in `χ`. -/
theorem exists_norm_logDeriv_LFunction_le_of_two_le_re :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 2 ≤ s.re →
      ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ K₀ :=
  ⟨_, tsum_nonneg fun _ => norm_nonneg _,
    fun χ _ hs => norm_logDeriv_LFunction_le_of_two_le_re χ hs⟩

/-- **`‖L'/L‖` on `Re s ≤ -1`, with explicit constants.** Given the digamma bound with constant
`Cd` and the bound `K₀` on `Re s ≥ 2`, for primitive `χ` mod `N` of parity `a`, `Re s ≤ -1` and
`‖cos (π(s+a)/2)‖ ≤ 2 ‖sin (π(s+a)/2)‖ ≠ 0`: `L(s, χ) ≠ 0` and
`‖L'/L(s, χ)‖ ≤ log N + log (‖s‖ + 2) + (7 + |Cd| + K₀)`. -/
theorem norm_logDeriv_LFunction_le_of_re_le_neg_one {Cd : ℝ}
    (hCd : ∀ v : ℂ, 0 < v.re → 1 ≤ ‖v‖ → ‖Complex.digamma v‖ ≤ Real.log ‖v‖ + Cd) {K₀ : ℝ}
    (hK₀ : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 2 ≤ s.re →
      ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ K₀)
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {a : ℝ}
    (hgf : ∀ w, χ.gammaFactor w = Complex.Gammaℝ (w + a))
    (hgf' : ∀ w, χ⁻¹.gammaFactor w = Complex.Gammaℝ (w + a)) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {s : ℂ} (hs : s.re ≤ -1) (hsin : Complex.sin (Real.pi * ((s + a) / 2)) ≠ 0)
    (hcot : ‖Complex.cos (Real.pi * ((s + a) / 2))‖ ≤
      2 * ‖Complex.sin (Real.pi * ((s + a) / 2))‖) :
    LFunction χ s ≠ 0 ∧
    ‖deriv (LFunction χ) s / LFunction χ s‖ ≤
      Real.log N + Real.log (‖s‖ + 2) + (7 + |Cd| + K₀) := by
  obtain ⟨hL, hEq⟩ :=
    LFunction_ne_zero_and_logDeriv_eq_of_re_neg hχ hgf hgf' ha0 ha1 (by linarith) hsin
  refine ⟨hL, ?_⟩
  rw [hEq]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlogN : ‖-Complex.log (N : ℂ)‖ = Real.log N := by
    rw [norm_neg, ← Complex.ofReal_natCast, ← Complex.ofReal_log (by positivity),
      Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hN1)]
  have hlogπ : ‖Complex.log (Real.pi : ℂ)‖ ≤ 3 := by
    rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real,
      Real.norm_of_nonneg (Real.log_nonneg (by linarith [Real.two_le_pi]))]
    have := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_le_four]
  have hns : 0 ≤ ‖s‖ := norm_nonneg _
  have hre1 : 1 ≤ ((1 - s + a) / 2).re := by simp; linarith
  have hre2 : 1 ≤ (1 - (s + a) / 2).re := by simp; linarith
  have hn1 : 1 ≤ ‖(1 - s + a) / 2‖ := hre1.trans (Complex.re_le_norm _)
  have hn2 : 1 ≤ ‖1 - (s + a) / 2‖ := hre2.trans (Complex.re_le_norm _)
  have hu1 : ‖(1 - s + a) / 2‖ ≤ ‖s‖ + 2 := by
    rw [norm_div, Complex.norm_two]
    have := norm_add_le (1 - s) (a : ℂ)
    have := norm_sub_le (1 : ℂ) s
    rw [Complex.norm_real, Real.norm_of_nonneg ha0] at *
    simp only [norm_one] at this
    linarith
  have hu2 : ‖1 - (s + a) / 2‖ ≤ ‖s‖ + 2 := by
    have h1 := norm_sub_le (1 : ℂ) ((s + a) / 2)
    rw [norm_div, Complex.norm_two, norm_one] at h1
    have := norm_add_le s (a : ℂ)
    rw [Complex.norm_real, Real.norm_of_nonneg ha0] at this
    linarith
  have hd1 := hCd _ (by linarith) hn1
  have hd2 := hCd _ (by linarith) hn2
  have hl1 := Real.log_le_log (by linarith) hu1
  have hl2 := Real.log_le_log (by linarith) hu2
  have hcot' : ‖(Real.pi : ℂ) / 2 * (Complex.cos (Real.pi * ((s + a) / 2)) /
      Complex.sin (Real.pi * ((s + a) / 2)))‖ ≤ 4 := by
    rw [norm_mul, norm_div, norm_div, Complex.norm_real, Complex.norm_two,
      Real.norm_of_nonneg Real.pi_pos.le]
    have hsn : 0 < ‖Complex.sin (Real.pi * ((s + a) / 2))‖ := norm_pos_iff.mpr hsin
    have : ‖Complex.cos (Real.pi * ((s + a) / 2))‖ /
        ‖Complex.sin (Real.pi * ((s + a) / 2))‖ ≤ 2 := (div_le_iff₀ hsn).mpr hcot
    have := Real.pi_le_four
    calc Real.pi / 2 * (‖Complex.cos (Real.pi * ((s + a) / 2))‖ /
          ‖Complex.sin (Real.pi * ((s + a) / 2))‖) ≤ Real.pi / 2 * 2 := by gcongr
      _ ≤ 4 := by linarith
  have hK := hK₀ χ⁻¹ (1 - s) (by simp; linarith)
  have hCd' := le_abs_self Cd
  have tri : ∀ a b c d e f : ℂ,
      ‖a + b - c - d + e - f‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
    intro a b c d e f
    have e1 := norm_sub_le (a + b - c - d + e) f
    have e2 := norm_add_le (a + b - c - d) e
    have e3 := norm_sub_le (a + b - c) d
    have e4 := norm_sub_le (a + b) c
    have e5 := norm_add_le a b
    linarith
  refine (tri _ _ _ _ _ _).trans ?_
  rw [hlogN, norm_div, norm_div, Complex.norm_two]
  linarith

/-- **`‖L'/L‖ ≪ log q + log (‖s‖ + 2)` on `Re s ≤ -1`** away from the trivial zeros: there is an
absolute `C ≥ 0` such that for every primitive `χ` mod `N` of parity `a`, every `s` with
`Re s ≤ -1` and `‖cos (π(s+a)/2)‖ ≤ 2 ‖sin (π(s+a)/2)‖ ≠ 0`, `L(s, χ) ≠ 0` and
`‖L'/L(s, χ)‖ ≤ log N + log (‖s‖ + 2) + C`. -/
theorem exists_norm_logDeriv_LFunction_le_of_re_le_neg_one :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ a : ℝ, (∀ w, χ.gammaFactor w = Complex.Gammaℝ (w + a)) →
      (∀ w, χ⁻¹.gammaFactor w = Complex.Gammaℝ (w + a)) → 0 ≤ a → a ≤ 1 →
      ∀ s : ℂ, s.re ≤ -1 → Complex.sin (Real.pi * ((s + a) / 2)) ≠ 0 →
      ‖Complex.cos (Real.pi * ((s + a) / 2))‖ ≤ 2 * ‖Complex.sin (Real.pi * ((s + a) / 2))‖ →
      LFunction χ s ≠ 0 ∧
      ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ Real.log N + Real.log (‖s‖ + 2) + C := by
  obtain ⟨Cd, hCd⟩ := Complex.exists_norm_digamma_le_log_add
  obtain ⟨K₀, hK₀0, hK₀⟩ := exists_norm_logDeriv_LFunction_le_of_two_le_re
  exact ⟨7 + |Cd| + K₀, by positivity, fun χ hχ a hgf hgf' ha0 ha1 s hs hsin hcot =>
    norm_logDeriv_LFunction_le_of_re_le_neg_one hCd hK₀ hχ hgf hgf' ha0 ha1 hs hsin hcot⟩

end DirichletCharacter
