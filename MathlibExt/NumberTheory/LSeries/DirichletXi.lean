/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.HadamardProduct
public import MathlibExt.NumberTheory.LSeries.DirichletNontrivialZeros
import MathlibExt.NumberTheory.LSeries.CompletedLFunctionGrowth
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.ZetaValues

/-!
# The completed Dirichlet `L`-function `ξ(s, χ)` and its Hadamard product

For a Dirichlet character `χ` modulo `q` with parity `a = (1 - χ(-1)) / 2`, the function
`ξ(s, χ) = (q / π) ^ ((s + a) / 2) Γ((s + a) / 2) L(s, χ)` is written as
`q ^ ((s + a) / 2) · Λ(s, χ)`, where `Λ = DirichletCharacter.completedLFunction`. For primitive
nonprincipal `χ` it is entire of order exactly `1`, its zeros are the nontrivial zeros of
`L(s, χ)`, and it has a Hadamard product.

## Main definitions

* `DirichletCharacter.xi χ`: the function `ξ(s, χ)`.

## Main statements

* `DirichletCharacter.differentiable_xi`: `ξ(s, χ)` is entire for `χ ≠ 1`.
* `DirichletCharacter.xi_eq_zero_iff`: for primitive `χ ≠ 1`, the zeros of `ξ(s, χ)` are the
  nontrivial zeros of `L(s, χ)`.
* `DirichletCharacter.conj_LFunction_conj`, `DirichletCharacter.conj_completedLFunction_conj`:
  `conj (L(conj s, χ)) = L(s, χ⁻¹)`, and the same for the completed `L`-function.
* `DirichletCharacter.xi_one_sub`: the functional equation `ξ(1 - s, χ) = W(χ) ξ(s, χ⁻¹)`.
* `DirichletCharacter.hasGrowthOrder_xi`: `ξ(s, χ)` has order `1`.
* `DirichletCharacter.nontrivialZeros_infinite`: `L(s, χ)` has infinitely many nontrivial zeros.
* `DirichletCharacter.exists_xi_eq_exp_mul_tprod`: the Hadamard product
  `ξ(s, χ) = exp (A + B s) ∏_ρ (1 - s / ρ) exp (s / ρ)`.
* `DirichletCharacter.exp_eq_xi_zero_of_xi_eq_exp_mul_tprod`: `exp A = ξ(0, χ)`.
* `DirichletCharacter.hasSum_re_one_div_of_xi_eq_exp_mul_tprod`: `∑_ρ Re (1 / ρ) = -Re B`.
-/

@[expose] public section

open Filter Asymptotics Bornology ComplexConjugate

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

/-- The completed Dirichlet `L`-function
`ξ(s, χ) = q ^ ((s + a) / 2) Λ(s, χ) = (q / π) ^ ((s + a) / 2) Γ((s + a) / 2) L(s, χ)`, where
`a = (1 - χ(-1)) / 2` is `0` for even and `1` for odd `χ`. Written through the total function
`completedLFunction`, so it has no junk values at the poles of the Gamma factor. -/
noncomputable def xi (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  (q : ℂ) ^ ((s + (1 - χ (-1)) / 2) / 2) * completedLFunction χ s

variable {χ : DirichletCharacter ℂ q}

/-- `ξ(s, χ)` is entire for nonprincipal `χ`. -/
theorem differentiable_xi (hχ1 : χ ≠ 1) : Differentiable ℂ (xi χ) := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  intro s
  refine DifferentiableAt.mul ?_ (differentiable_completedLFunction hχ1 s)
  exact DifferentiableAt.const_cpow (by fun_prop) (Or.inl hq)

/-- The factor `q ^ ((s + a) / 2)` does not vanish. -/
private lemma natCast_cpow_xi_ne_zero (χ : DirichletCharacter ℂ q) (s : ℂ) :
    (q : ℂ) ^ ((s + (1 - χ (-1)) / 2) / 2) ≠ 0 := by
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h => NeZero.ne q (by exact_mod_cast h.1)

/-- **The zeros of `ξ(s, χ)` are the nontrivial zeros of `L(s, χ)`** for primitive `χ ≠ 1`: the
trivial zeros of `L(s, χ)` are cancelled by the poles of `Γ((s + a) / 2)`. -/
theorem xi_eq_zero_iff (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (s : ℂ) :
    xi χ s = 0 ↔ s ∈ χ.nontrivialZeros := by
  -- on `Re w ≥ 1` the completed `L`-function of a nonprincipal character does not vanish
  have hgood : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ∀ w : ℂ, 1 ≤ w.re →
      completedLFunction ψ w ≠ 0 := by
    intro ψ hψ w hw h
    have hw0 : w ≠ 0 := by
      rintro rfl
      simp at hw
      linarith
    have hL := LFunction_eq_completed_div_gammaFactor ψ w (Or.inl hw0)
    rw [h, zero_div] at hL
    exact LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ) hw hL
  have hprim' : (χ⁻¹).IsPrimitive := by
    rw [IsPrimitive, conductor_inv]
    exact hχ
  -- on `Re s ≤ 0`, by the functional equation for `χ⁻¹`
  have hneg : ∀ s : ℂ, s.re ≤ 0 → completedLFunction χ s ≠ 0 := by
    intro s hs h
    have hfe := hprim'.completedLFunction_one_sub s
    rw [inv_inv, h, mul_zero] at hfe
    exact hgood χ⁻¹ (inv_ne_one.mpr hχ1) (1 - s) (by simp; linarith) hfe
  rw [xi, mul_eq_zero, or_iff_right (natCast_cpow_xi_ne_zero χ s), mem_nontrivialZeros]
  constructor
  · intro h
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact hneg 0 (by simp) h
    have hL := LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)
    rw [h, zero_div] at hL
    refine ⟨hL, ?_, ?_⟩
    · by_contra h0
      exact hneg s (by linarith [not_lt.mp h0]) h
    · by_contra h1
      exact hgood χ hχ1 s (by linarith [not_lt.mp h1]) h
  · rintro ⟨hL, h0, -⟩
    have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl _ h0
    rw [LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0), div_eq_zero_iff] at hL
    refine hL.resolve_right ?_
    rcases χ.even_or_odd with hχe | hχo
    · rw [hχe.gammaFactor_def]
      exact Complex.Gammaℝ_ne_zero_of_re_pos h0
    · rw [hχo.gammaFactor_def]
      exact Complex.Gammaℝ_ne_zero_of_re_pos (by rw [Complex.add_re, Complex.one_re]; linarith)

/-- `ξ(0, χ) ≠ 0` for primitive `χ ≠ 1`. -/
theorem xi_zero_ne_zero (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) : xi χ 0 ≠ 0 := by
  rw [Ne, xi_eq_zero_iff hχ hχ1]
  exact fun h => ne_zero_of_mem_nontrivialZeros h rfl

/-! ### Conjugation and the functional equation -/

/-- **Conjugation of Dirichlet `L`-functions:** `conj (L(conj s, χ)) = L(s, χ⁻¹)` for `χ ≠ 1`. -/
theorem conj_LFunction_conj (hχ1 : χ ≠ 1) (s : ℂ) :
    conj (LFunction χ (conj s)) = LFunction χ⁻¹ s := by
  have hLS : ∀ w : ℂ, 1 < w.re → conj (LFunction χ (conj w)) = LFunction χ⁻¹ w := by
    intro w hw
    rw [LFunction_eq_LSeries χ (by simpa using hw), LFunction_eq_LSeries χ⁻¹ hw, LSeries, LSeries,
      Complex.conj_tsum]
    congr 1
    funext n
    rw [LSeries.term_def, LSeries.term_def]
    split_ifs with hn
    · simp
    · have hna : (n : ℂ).arg ≠ Real.pi := by
        rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
      rw [map_div₀, show conj (χ n) = χ⁻¹ n from MulChar.star_apply' χ _,
        Complex.cpow_conj _ _ hna, Complex.conj_conj, Complex.conj_natCast]
  have hd1 : Differentiable ℂ (fun s => conj (LFunction χ (conj s))) := by
    intro s
    have := ((differentiable_LFunction hχ1) (conj s)).conj_conj
    rw [Complex.conj_conj] at this
    exact this
  have hd2 := differentiable_LFunction (inv_ne_one.mpr hχ1)
  have heq := AnalyticOnNhd.eq_of_eventuallyEq (fun w _ => hd1.analyticAt w)
    (fun w _ => hd2.analyticAt w) (z₀ := 2) (by
      have hopen : IsOpen {w : ℂ | 1 < w.re} :=
        isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with w hw
      exact hLS w hw)
  exact congrFun heq s

omit [NeZero q] in
/-- `χ⁻¹(-1) = χ(-1)`. -/
theorem inv_apply_neg_one (χ : DirichletCharacter ℂ q) : χ⁻¹ (-1) = χ (-1) := by
  rw [MulChar.inv_apply_eq_inv']
  rcases χ.even_or_odd with h | h <;> rw [h] <;> norm_num

omit [NeZero q] in
/-- `χ(-1)` is real. -/
theorem conj_apply_neg_one (χ : DirichletCharacter ℂ q) : conj (χ (-1)) = χ (-1) := by
  rcases χ.even_or_odd with h | h <;> rw [h] <;> simp

/-- **Conjugation of completed Dirichlet `L`-functions:**
`conj (Λ(conj s, χ)) = Λ(s, χ⁻¹)` for `χ ≠ 1`. -/
theorem conj_completedLFunction_conj (hχ1 : χ ≠ 1) (s : ℂ) :
    conj (completedLFunction χ (conj s)) = completedLFunction χ⁻¹ s := by
  have hχi1 : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ1
  have hm1i := inv_apply_neg_one χ
  have hargπ : (Real.pi : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_ne_zero.symm
  have hGR : ∀ w, conj (Complex.Gammaℝ (conj w)) = Complex.Gammaℝ w := by
    intro w
    rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, map_mul]
    have h1 : -conj w / 2 = conj (-w / 2) := by simp [map_div₀, map_ofNat]
    have h2 : conj w / 2 = conj (w / 2) := by simp [map_div₀, map_ofNat]
    rw [h1, h2, Complex.cpow_conj _ _ hargπ, Complex.conj_conj, Complex.conj_ofReal,
      Complex.Gamma_conj, Complex.conj_conj]
  have hgf : ∀ w, conj (gammaFactor χ (conj w)) = gammaFactor χ⁻¹ w := by
    intro w
    rcases χ.even_or_odd with h | h
    · have h' : (χ⁻¹).Even := by
        change χ⁻¹ (-1) = 1
        rw [hm1i]; exact h
      rw [h.gammaFactor_def, h'.gammaFactor_def, hGR]
    · have h' : (χ⁻¹).Odd := by
        change χ⁻¹ (-1) = -1
        rw [hm1i]; exact h
      rw [h.gammaFactor_def, h'.gammaFactor_def, show conj w + 1 = conj (w + 1) by simp, hGR]
  have hcomp : ∀ ψ : DirichletCharacter ℂ q, ∀ w : ℂ, 1 < w.re →
      completedLFunction ψ w = gammaFactor ψ w * LFunction ψ w := by
    intro ψ w hw
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw; linarith
    have hg : gammaFactor ψ w ≠ 0 := by
      rcases ψ.even_or_odd with h | h
      · rw [h.gammaFactor_def]; exact Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
      · rw [h.gammaFactor_def]
        exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    rw [LFunction_eq_completed_div_gammaFactor ψ w (Or.inl hw0), mul_div_cancel₀ _ hg]
  have hd1 : Differentiable ℂ (fun s => conj (completedLFunction χ (conj s))) := by
    intro s
    have := ((differentiable_completedLFunction hχ1) (conj s)).conj_conj
    rw [Complex.conj_conj] at this
    exact this
  have hd2 := differentiable_completedLFunction hχi1
  have heq := AnalyticOnNhd.eq_of_eventuallyEq (fun w _ => hd1.analyticAt w)
    (fun w _ => hd2.analyticAt w) (z₀ := 2) (by
      have hopen : IsOpen {w : ℂ | 1 < w.re} :=
        isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with w hw
      have hw' : 1 < (conj w).re := by simpa using hw
      rw [hcomp χ _ hw', hcomp χ⁻¹ w hw, map_mul, hgf, conj_LFunction_conj hχ1 w])
  exact congrFun heq s

/-- `conj (ξ(conj s, χ)) = ξ(s, χ⁻¹)` for `χ ≠ 1`. -/
theorem conj_xi_conj (hχ1 : χ ≠ 1) (s : ℂ) : conj (xi χ (conj s)) = xi χ⁻¹ s := by
  have hargq : (q : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
  rw [xi, xi, map_mul, conj_completedLFunction_conj hχ1, inv_apply_neg_one]
  congr 1
  have he : (conj s + (1 - χ (-1)) / 2) / 2 = conj ((s + (1 - χ (-1)) / 2) / 2) := by
    simp [map_div₀, conj_apply_neg_one, map_ofNat]
  rw [he, Complex.cpow_conj _ _ hargq, Complex.conj_conj, Complex.conj_natCast]

/-- **The functional equation of `ξ(s, χ)`:** `ξ(1 - s, χ) = W(χ) ξ(s, χ⁻¹)` for primitive `χ`,
with `W(χ) = rootNumber χ`. -/
theorem xi_one_sub (hχ : χ.IsPrimitive) (s : ℂ) : xi χ (1 - s) = rootNumber χ * xi χ⁻¹ s := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  rw [xi, xi, hχ.completedLFunction_one_sub s, inv_apply_neg_one]
  have : (q : ℂ) ^ ((1 - s + (1 - χ (-1)) / 2) / 2) * (q : ℂ) ^ (s - 1 / 2) =
      (q : ℂ) ^ ((s + (1 - χ (-1)) / 2) / 2) := by
    rw [← Complex.cpow_add _ _ hq0]; congr 1; ring
  rw [← this]; ring

/-- `ξ(s, χ) = W(χ) conj (ξ(1 - conj s, χ))` for primitive `χ ≠ 1`. -/
theorem xi_eq_rootNumber_mul_conj (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (s : ℂ) :
    xi χ s = rootNumber χ * conj (xi χ (1 - conj s)) := by
  have := xi_one_sub hχ (1 - s)
  rw [sub_sub_cancel, ← conj_xi_conj hχ1] at this
  rw [this, map_sub, map_one]

/-! ### Growth -/

/-- The parity `a ∈ {0, 1}` of `χ`, with `(1 - χ(-1)) / 2 = a` and `Λ(s, χ) = Γℝ(s + a) L(s, χ)`
for `Re s > 0`. -/
private lemma exists_parity (hχ1 : χ ≠ 1) : ∃ a : ℕ, (1 - χ (-1)) / 2 = (a : ℂ) ∧ a ≤ 1 ∧
    ∀ s : ℂ, 0 < s.re → completedLFunction χ s = Complex.Gammaℝ (s + a) * LFunction χ s := by
  have hq1 : q ≠ 1 := by
    rintro rfl; exact hχ1 (level_one' χ rfl)
  rcases χ.even_or_odd with he | ho
  · refine ⟨0, by rw [show χ (-1) = 1 from he]; simp, by norm_num, fun s hs => ?_⟩
    have hL := LFunction_eq_completed_div_gammaFactor χ s (Or.inr hq1)
    rw [he.gammaFactor_def] at hL
    have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs
    rw [hL, Nat.cast_zero, add_zero]; field_simp
  · refine ⟨1, by rw [show χ (-1) = -1 from ho]; norm_num, le_refl _, fun s hs => ?_⟩
    have hL := LFunction_eq_completed_div_gammaFactor χ s (Or.inr hq1)
    rw [ho.gammaFactor_def] at hL
    have hG : Complex.Gammaℝ (s + 1) ≠ 0 :=
      Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    rw [hL]; push_cast; field_simp

/-- `ξ(s, χ)` is of factorial type for `χ ≠ 1`: `‖ξ(s, χ)‖ ≤ A Bᴺ N!` whenever `‖s‖ + 1 ≤ N`. -/
theorem exists_norm_xi_le_mul_pow_mul_factorial (hχ1 : χ ≠ 1) :
    ∃ A B : ℝ, 0 ≤ A ∧ 1 ≤ B ∧ ∀ (s : ℂ) (N : ℕ),
      ‖s‖ + 1 ≤ N → ‖xi χ s‖ ≤ A * B ^ N * N.factorial := by
  have hq1 : q ≠ 1 := by
    rintro rfl; exact hχ1 (level_one' χ rfl)
  have hχ0 : χ 0 = 0 := by
    have : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr hq1
    exact MulChar.map_zero χ
  have hχsum : ∑ j, χ j = 0 := MulChar.sum_eq_zero_of_ne_one hχ1
  have hΛeq : ∀ s, completedLFunction χ s = ZMod.completedLFunction₀ (fun j => χ j) s := by
    intro s
    rw [completedLFunction, ZMod.completedLFunction_eq, hχ0, hχsum]
    simp
  obtain ⟨A, B, hA, hB, h⟩ := ZMod.exists_norm_completedLFunction₀_le_mul_pow_mul_factorial
    (fun j => χ j)
  obtain ⟨a, ha, ha1, -⟩ := exists_parity hχ1
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  refine ⟨A, q * B, hA, one_le_mul_of_one_le_of_one_le hq1' hB, fun s N hN => ?_⟩
  have hre := abs_le.1 (Complex.abs_re_le_norm s)
  have hqw : ‖(q : ℂ) ^ ((s + (1 - χ (-1)) / 2) / 2)‖ ≤ (q : ℝ) ^ N := by
    rw [ha, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (NeZero.ne q)),
      ← Real.rpow_natCast]
    have ha1' : (a : ℝ) ≤ 1 := by exact_mod_cast ha1
    exact Real.rpow_le_rpow_of_exponent_le hq1' (by simp; linarith)
  rw [xi, norm_mul, hΛeq, mul_pow]
  calc _ ≤ (q : ℝ) ^ N * (A * B ^ N * N.factorial) :=
        mul_le_mul hqw (h s N hN) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- `‖ξ(s, χ)‖ ≤ exp (4 ‖s‖ log ‖s‖)` for large `‖s‖`, for `χ ≠ 1`. -/
theorem eventually_norm_xi_le_exp (hχ1 : χ ≠ 1) :
    ∀ᶠ s in cobounded ℂ, ‖xi χ s‖ ≤ Real.exp (4 * ‖s‖ * Real.log ‖s‖) := by
  obtain ⟨A, B, -, hB, h⟩ := exists_norm_xi_le_mul_pow_mul_factorial hχ1
  filter_upwards [eventually_norm_le_rpow_of_le_mul_pow_mul_factorial (by linarith) h,
    tendsto_norm_cobounded_atTop.eventually_gt_atTop 0] with s hs hs0
  rwa [Real.rpow_def_of_pos hs0, show Real.log ‖s‖ * (4 * ‖s‖) = 4 * ‖s‖ * Real.log ‖s‖ by
    ring] at hs

/-- `ξ(s, χ)` has order of growth at most `1` for `χ ≠ 1`. -/
theorem hasGrowthOrderLE_xi (hχ1 : χ ≠ 1) : Complex.HasGrowthOrderLE (xi χ) 1 :=
  Complex.hasGrowthOrderLE_one_of_eventually_norm_le_exp_mul_log (eventually_norm_xi_le_exp hχ1)

/-- `‖L(k, χ)‖ ≥ 1 / 2` for every natural number `k ≥ 5`. -/
theorem one_half_le_norm_LSeries_natCast (χ : DirichletCharacter ℂ q) {k : ℕ} (hk : 5 ≤ k) :
    (1 / 2 : ℝ) ≤ ‖LSeries (fun n : ℕ => χ n) (k : ℂ)‖ := by
  have hs : LSeriesSummable (fun n : ℕ => χ n) (k : ℂ) :=
    ZMod.LSeriesSummable_of_one_lt_re (fun j => χ j)
      (by simp only [Complex.natCast_re]; exact_mod_cast (show 1 < k by omega))
  set f := LSeries.term (fun n : ℕ => χ n) (k : ℂ) with hf
  have hsplit := hs.sum_add_tsum_nat_add 2
  have hf0 : f 0 = 0 := LSeries.term_zero _ _
  have hf1 : f 1 = 1 := by simp [hf, LSeries.term_of_ne_zero]
  have hb : ∀ m : ℕ, ‖f (m + 2)‖ ≤ 1 / 8 * (1 / ((m : ℝ) + 2) ^ 2) := by
    intro m
    rw [hf, LSeries.term_of_ne_zero (by omega), norm_div, Complex.cpow_natCast, norm_pow,
      Complex.norm_natCast]
    have hm : (2 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ m + 2 by omega)
    have hpow : 8 * ((m + 2 : ℕ) : ℝ) ^ 2 ≤ ((m + 2 : ℕ) : ℝ) ^ k := by
      have h3 : ((m + 2 : ℕ) : ℝ) ^ k =
          ((m + 2 : ℕ) : ℝ) ^ 2 * ((m + 2 : ℕ) : ℝ) ^ (k - 2) := by
        rw [← pow_add]; congr 1; omega
      have h4 : (2 : ℝ) ^ 3 ≤ ((m + 2 : ℕ) : ℝ) ^ (k - 2) :=
        (pow_le_pow_left₀ (by norm_num) hm 3).trans
          (pow_le_pow_right₀ (by linarith) (by omega))
      rw [h3]; nlinarith [pow_pos (show (0 : ℝ) < ((m + 2 : ℕ) : ℝ) by linarith) 2]
    have hχm := norm_le_one χ ((m + 2 : ℕ) : ZMod q)
    have hcast : ((m : ℝ) + 2) = ((m + 2 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast, div_le_iff₀ (by positivity)]
    calc ‖χ ((m + 2 : ℕ) : ZMod q)‖ ≤ 1 := hχm
      _ ≤ 1 / 8 * (1 / ((m + 2 : ℕ) : ℝ) ^ 2) * ((m + 2 : ℕ) : ℝ) ^ k := by
        rw [show 1 / 8 * (1 / ((m + 2 : ℕ) : ℝ) ^ 2) * ((m + 2 : ℕ) : ℝ) ^ k =
          ((m + 2 : ℕ) : ℝ) ^ k / (8 * ((m + 2 : ℕ) : ℝ) ^ 2) by field_simp]
        rw [le_div_iff₀ (by positivity)]; linarith
  have hz := hasSum_zeta_two.summable.sum_add_tsum_nat_add 2
  rw [hasSum_zeta_two.tsum_eq] at hz
  have hgs : Summable (fun m : ℕ => 1 / ((m : ℝ) + 2) ^ 2) := by
    have := (summable_nat_add_iff 2).mpr hasSum_zeta_two.summable
    refine this.congr fun m => ?_
    push_cast; ring
  have htail : ∑' m : ℕ, 1 / ((m : ℝ) + 2) ^ 2 ≤ 3 := by
    have e : ∑' m : ℕ, 1 / ((m : ℝ) + 2) ^ 2 = ∑' i : ℕ, (((i : ℝ) + 2) ^ 2)⁻¹ := by
      simp only [one_div]
    rw [e]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hz
    norm_num at hz
    have := Real.pi_le_four
    have hpi := Real.pi_pos
    nlinarith
  have hrest : ‖∑' m : ℕ, f (m + 2)‖ ≤ 3 / 8 := by
    have hfs : Summable (fun m : ℕ => ‖f (m + 2)‖) :=
      Summable.of_nonneg_of_le (fun m => norm_nonneg _) hb (hgs.mul_left _)
    calc ‖∑' m : ℕ, f (m + 2)‖ ≤ ∑' m : ℕ, ‖f (m + 2)‖ := norm_tsum_le_tsum_norm hfs
      _ ≤ ∑' m : ℕ, 1 / 8 * (1 / ((m : ℝ) + 2) ^ 2) :=
        hfs.tsum_le_tsum hb (hgs.mul_left _)
      _ = 1 / 8 * ∑' m : ℕ, 1 / ((m : ℝ) + 2) ^ 2 := tsum_mul_left
      _ ≤ 3 / 8 := by linarith
  have hL : LSeries (fun n : ℕ => χ n) (k : ℂ) = 1 + ∑' m : ℕ, f (m + 2) := by
    rw [← hf] at hsplit
    rw [LSeries, ← hf, ← hsplit, Finset.sum_range_succ, Finset.sum_range_one, hf0, hf1,
      zero_add]
  rw [hL]
  have := norm_sub_norm_le (1 : ℂ) (-(∑' m : ℕ, f (m + 2)))
  rw [sub_neg_eq_add, norm_neg, norm_one] at this
  linarith

/-- `ξ(s, χ)` is not of exponential type, for `χ ≠ 1`: it grows factorially along
`s = 2 (n + 1) - a`. -/
theorem not_isBigO_xi_exp_mul_norm (hχ1 : χ ≠ 1) (b : ℝ) :
    ¬ xi χ =O[cobounded ℂ] fun s => Real.exp (b * ‖s‖) := by
  obtain ⟨a, ha, ha1, hgam⟩ := exists_parity hχ1
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hval : ∀ n : ℕ, 2 ≤ n →
      (n.factorial : ℝ) / Real.pi ^ (n + 1) / 2 ≤ ‖xi χ ((2 * (n + 1) - a : ℕ) : ℂ)‖ := by
    intro n hn
    set k : ℕ := 2 * (n + 1) - a with hkdef
    have hk : k + a = 2 * (n + 1) := by omega
    have hLn := one_half_le_norm_LSeries_natCast χ (show 5 ≤ k by omega)
    have hkre : 1 < ((k : ℂ)).re := by
      simp only [Complex.natCast_re]; exact_mod_cast (show 1 < k by omega)
    have hka : (k : ℂ) + (a : ℂ) = ((2 * (n + 1) : ℕ) : ℂ) := by exact_mod_cast hk
    rw [xi, ha, hgam (k : ℂ) (by linarith), LFunction_eq_LSeries χ hkre, hka]
    have hw : ((2 * (n + 1) : ℕ) : ℂ) / 2 = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hw, Complex.cpow_natCast]
    have hGv : Complex.Gammaℝ ((2 * (n + 1) : ℕ) : ℂ) =
        ((Real.pi ^ (n + 1))⁻¹ * n.factorial : ℝ) := by
      rw [Complex.Gammaℝ_def]
      have : ((2 * (n + 1) : ℕ) : ℂ) / 2 = ((n : ℂ) + 1) := by push_cast; ring
      rw [this, Complex.Gamma_nat_eq_factorial]
      have : -((2 * (n + 1) : ℕ) : ℂ) / 2 = ((-(n + 1 : ℕ) : ℤ) : ℂ) := by push_cast; ring
      rw [this, Complex.cpow_intCast]
      push_cast
      norm_cast
    rw [hGv, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow,
      Complex.norm_natCast]
    have hpos : 0 < (Real.pi ^ (n + 1))⁻¹ * n.factorial := by positivity
    rw [abs_of_pos hpos]
    have hq1n : 1 ≤ (q : ℝ) ^ (n + 1) := one_le_pow₀ hq1'
    calc (n.factorial : ℝ) / Real.pi ^ (n + 1) / 2
        = 1 * (((Real.pi ^ (n + 1))⁻¹ * n.factorial) * (1 / 2)) := by ring
      _ ≤ (q : ℝ) ^ (n + 1) * (((Real.pi ^ (n + 1))⁻¹ * n.factorial) *
          ‖LSeries (fun n : ℕ => χ n) (k : ℂ)‖) := by gcongr
  refine Complex.not_isBigO_exp_mul_norm_of_factorial_le
    (s := fun n => ((2 * (n + 1) - a : ℕ) : ℂ)) (a := 2) (C := 2 * Real.pi) (K := Real.pi)
    ?_ (fun n => ?_) ?_ b
  · rw [← tendsto_norm_atTop_iff_cobounded]
    simp only [Complex.norm_natCast]
    exact tendsto_natCast_atTop_atTop.comp
      (tendsto_atTop_mono (fun n => show n ≤ 2 * (n + 1) - a by omega) tendsto_id)
  · rw [Complex.norm_natCast]
    have : 2 * (n + 1) - a ≤ 2 * (n + 1) := Nat.sub_le _ _
    exact_mod_cast this
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have h := hval n hn
    rw [div_div, div_le_iff₀ (by positivity)] at h
    calc (n.factorial : ℝ) ≤ _ := h
      _ = 2 * Real.pi * Real.pi ^ n * ‖xi χ ((2 * (n + 1) - a : ℕ) : ℂ)‖ := by ring

/-- **`ξ(s, χ)` has order `1`** for `χ ≠ 1`. -/
theorem hasGrowthOrder_xi (hχ1 : χ ≠ 1) : Complex.HasGrowthOrder (xi χ) 1 := by
  refine Complex.hasGrowthOrder_one_of_not_isBigO_exp_norm (hasGrowthOrderLE_xi hχ1) ?_
  simpa using not_isBigO_xi_exp_mul_norm hχ1 1

/-- **`L(s, χ)` has infinitely many nontrivial zeros** for primitive `χ ≠ 1`. -/
theorem nontrivialZeros_infinite (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    χ.nontrivialZeros.Infinite := by
  have h := Complex.setOf_eq_zero_infinite_of_hasGrowthOrderLE_one (differentiable_xi hχ1)
    (hasGrowthOrderLE_xi hχ1) (xi_zero_ne_zero hχ hχ1) (not_isBigO_xi_exp_mul_norm hχ1)
  convert h using 1
  ext s
  exact (xi_eq_zero_iff hχ hχ1 s).symm

/-! ### The Hadamard product -/

/-- **The Hadamard product of `ξ(s, χ)`.** For primitive `χ ≠ 1` and any family `z` listing the
zeros of `ξ(s, χ)` with multiplicity (that is, the nontrivial zeros of `L(s, χ)`), there are
constants `A`, `B` with `ξ(s, χ) = exp (A + B s) ∏ₙ (1 - s / zₙ) exp (s / zₙ)`. -/
theorem exists_xi_eq_exp_mul_tprod (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {ι : Type*} {z : ι → ℂ}
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w) :
    ∃ A B : ℂ, ∀ s, xi χ s =
      Complex.exp (A + B * s) * ∏' n, (1 - s / z n) * Complex.exp (s / z n) :=
  Complex.exists_eq_exp_mul_tprod_of_hasGrowthOrderLE_one (differentiable_xi hχ1)
    (hasGrowthOrderLE_xi hχ1) (xi_zero_ne_zero hχ hχ1) hz

/-- The constant term of the Hadamard product of `ξ(s, χ)` satisfies `exp A = ξ(0, χ)`. -/
theorem exp_eq_xi_zero_of_xi_eq_exp_mul_tprod {ι : Type*} {z : ι → ℂ} {A B : ℂ}
    (hAB : ∀ s, xi χ s =
      Complex.exp (A + B * s) * ∏' n, (1 - s / z n) * Complex.exp (s / z n)) :
    Complex.exp A = xi χ 0 :=
  Complex.exp_eq_apply_zero_of_eq_exp_mul_tprod hAB

/-- In the Hadamard product of `ξ(s, χ)` for primitive `χ ≠ 1`, `∑_ρ Re (1 / ρ) = -Re B`, the sum
running over the nontrivial zeros of `L(s, χ)` with multiplicity (and converging). -/
theorem hasSum_re_one_div_of_xi_eq_exp_mul_tprod (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    {ι : Type*} {z : ι → ℂ} (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w)
    {A B : ℂ} (hAB : ∀ s, xi χ s =
      Complex.exp (A + B * s) * ∏' n, (1 - s / z n) * Complex.exp (s / z n)) :
    HasSum (fun n => (1 / z n).re) (-B.re) :=
  Complex.hasSum_re_one_div_of_eq_exp_mul_tprod (differentiable_xi hχ1) (hasGrowthOrderLE_xi hχ1)
    (xi_zero_ne_zero hχ hχ1) hz (xi_eq_rootNumber_mul_conj hχ hχ1)
    (fun w hw => by
      obtain ⟨-, h0, h1⟩ := (xi_eq_zero_iff hχ hχ1 w).mp hw
      exact ⟨h0.le, h1.le⟩) hAB

end DirichletCharacter
