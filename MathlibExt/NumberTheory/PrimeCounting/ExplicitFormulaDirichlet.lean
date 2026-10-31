/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LSeries.DirichletLogDerivZeros
public import MathlibExt.NumberTheory.PrimeCounting.DirichletChebyshevPsi
import MathlibExt.Analysis.Complex.RectangleResidueDoublePole
import MathlibExt.Analysis.PerronKernel
import MathlibExt.Analysis.SpecialFunctions.Trigonometric.CotBound
import MathlibExt.NumberTheory.LSeries.DirichletLeftHalfPlane
import MathlibExt.NumberTheory.LSeries.RiemannZetaLogDerivZeros
import MathlibExt.NumberTheory.LSeries.VerticalLine
import MathlibExt.NumberTheory.PrimeCounting.ExplicitFormula
import MathlibExt.NumberTheory.PrimeCounting.ExplicitFormulaContour
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The explicit formula for `ψ(x, χ)`

For a primitive nonprincipal Dirichlet character `χ` modulo `q` of parity
`a = (1 - χ(-1))/2`, we prove the explicit formula
`ψ(x, χ) = -∑_ρ x^ρ/ρ - (1 - a)(log x + b(χ)) - a L'(0, χ)/L(0, χ) + ∑_{m ≥ 1} x^{a - 2m}/(2m - a)`
for every real `x > 1` that is not a prime power, the sum over the zeros being the limit of its
truncations to `|γ| < R`, and its truncated form
`ψ(x, χ) = -∑_{|γ| < R} x^ρ/ρ - (1 - a)(log x + b(χ)) - a L'(0, χ)/L(0, χ)
  + ∑_{m ≥ 1} x^{a - 2m}/(2m - a) + O(x log² (q x R) / R)`
uniformly in `χ`, for `x - 1/2` a positive integer. We deduce that the generalized Riemann
hypothesis for `L(s, χ)` gives `ψ(x, χ) = O(√x log² (q x))`.

Both formulas come from the residue theorem for `-L'/L(s, χ) x^s / s` on the rectangle
`[-(2M + 1 - a), c] × [-T, T]` at a good height `T`, letting `M → ∞`.

## Main statements

* `DirichletCharacter.mem_nontrivialZeros_or_eq_of_LFunction_eq_zero`: the zeros of `L(s, χ)` are
  the nontrivial zeros and the trivial zeros `-a - 2n`.
* `DirichletCharacter.integral_rectangle_neg_logDeriv_LFunction_mul_cpow_div`: the residue
  theorem for `-L'/L(s, χ) x^s / s` on the rectangle.
* `DirichletCharacter.exists_good_height_norm_logDeriv_LFunction_le`: in every window `[R, R + 1]`
  there is a height `T` at which `L'/L(σ ± iT, χ) = O(log² (q R))` for `-1 ≤ σ ≤ 2`.
* `DirichletCharacter.exists_truncated_explicit_formula_chebyshevPsi`: the truncated explicit
  formula for `ψ(x, χ)`.
* `DirichletCharacter.tendsto_tsum_cpow_div_zeros_explicit_formula`: the explicit formula for
  `ψ(x, χ)`.
* `DirichletCharacter.exists_norm_chebyshevPsi_le_of_forall_re_eq_half`: under the generalized
  Riemann hypothesis for `L(s, χ)`, `‖ψ(x, χ)‖ ≤ C √x log² (q x)` for `x ≥ 2`.
-/

@[expose] public section

universe u

open Complex Filter Topology Set ArithmeticFunction RiemannXi

namespace DirichletCharacter

/-! ### Moving the truncation height -/

/-- Moving the truncation height of the zero sum from `R` to `T ∈ [R, R + 1]` costs
`O(log (q R) x / R)`. -/
private lemma norm_tsum_cpow_div_sub_tsum_cpow_div_le {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {ι : Type u} (z : ι → ℂ)
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w) {x : ℝ} (hx : 1 < x)
    {R T C₁ : ℝ} (hR : 2 ≤ R) (hRT : R ≤ T) (hT : T ≤ R + 1)
    (hC₁ : ∀ t : ℝ, ∀ F : Finset ι, (∀ n ∈ F, |t - (z n).im| < 1) →
      (F.card : ℝ) ≤ C₁ * Real.log (q * (|t| + 2))) :
    ‖(∑' n, (if |(z n).im| < T then (x : ℂ) ^ z n / z n else 0)) -
        ∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0)‖ ≤
      2 * (|C₁| * Real.log (q * (R + 3))) * (x / R) := by
  classical
  have hmin : min R T = R := min_eq_left hRT
  have hmax : max R T = T := max_eq_right hRT
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set t₀ : ℝ := R + 1 / 2 with ht₀
  have hlog : Real.log (q * (|t₀| + 2)) ≤ Real.log (q * (R + 3)) := by
    rw [abs_of_pos (by linarith)]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hlog' : Real.log (q * (|-t₀| + 2)) ≤ Real.log (q * (R + 3)) := by rwa [abs_neg]
  have hlog0 : 0 ≤ Real.log (q * (|t₀| + 2)) := Real.log_nonneg (by nlinarith [abs_nonneg t₀])
  have hlog0' : 0 ≤ Real.log (q * (|-t₀| + 2)) :=
    Real.log_nonneg (by nlinarith [abs_nonneg (-t₀)])
  have hc1 : C₁ * Real.log (q * (|t₀| + 2)) ≤ |C₁| * Real.log (q * (R + 3)) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hlog0).trans
      (mul_le_mul_of_nonneg_left hlog (abs_nonneg _))
  have hc2 : C₁ * Real.log (q * (|-t₀| + 2)) ≤ |C₁| * Real.log (q * (R + 3)) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hlog0').trans
      (mul_le_mul_of_nonneg_left hlog' (abs_nonneg _))
  have h := norm_tsum_ite_cpow_div_sub_tsum_ite_cpow_div_le z
    (fun n => (re_mem_Icc_of_card_eq_analyticOrderAt hχ hz n).2) hx (R := R) (T := T)
    (by rw [hmin]; linarith)
    (by rw [hmax]; exact finite_setOf_abs_im_lt_of_card_eq_analyticOrderAt hχ hχ1 hz T)
    (B := 2 * (|C₁| * Real.log (q * (R + 3)))) (fun D hD => by
      rw [hmin, hmax] at hD
      have hDP := hC₁ t₀ (D.filter (fun n => 0 ≤ (z n).im)) (by
        intro n hn
        rw [Finset.mem_filter] at hn
        obtain ⟨h1, h2⟩ := hD n hn.1
        rw [abs_of_nonneg hn.2] at h1 h2
        rw [abs_lt]; constructor <;> linarith)
      have hDM := hC₁ (-t₀) (D.filter (fun n => ¬ 0 ≤ (z n).im)) (by
        intro n hn
        rw [Finset.mem_filter] at hn
        obtain ⟨h1, h2⟩ := hD n hn.1
        rw [abs_of_neg (not_le.mp hn.2)] at h1 h2
        rw [abs_lt]; constructor <;> linarith)
      have hcard := Finset.card_filter_add_card_filter_not (s := D) (fun n => 0 ≤ (z n).im)
      have : (D.card : ℝ) = (D.filter (fun n => 0 ≤ (z n).im)).card +
          (D.filter (fun n => ¬ 0 ≤ (z n).im)).card := by exact_mod_cast hcard.symm
      linarith)
  rw [hmin] at h
  rwa [norm_sub_rev]

/-! ### The residues of `-L'/L(s, χ) x^s / s` -/

/-- On the lines `Re z = π/2 + kπ`, `sin z ≠ 0` and `|cos z| ≤ 2 |sin z|`. -/
private lemma sin_ne_zero_and_norm_cos_le_of_cos_eq_zero (x y : ℝ) (hx : Real.cos x = 0) :
    Complex.sin (x + y * I) ≠ 0 ∧
      ‖Complex.cos (x + y * I)‖ ≤ 2 * ‖Complex.sin (x + y * I)‖ := by
  have hre : Real.cos ((x : ℂ) + y * I).re = 0 := by simpa using hx
  exact ⟨Complex.sin_ne_zero_of_cos_re_eq_zero hre,
    (Complex.norm_cos_le_norm_sin_of_cos_re_eq_zero hre).trans
      (by linarith [norm_nonneg (Complex.sin ((x : ℂ) + y * I))])⟩

/-- **The pole at `s = 0` for a simple zero of `L(s, χ)`.** If `L(s, χ) = s E(s)` near `0` with
`E` analytic and nonzero at `0`, then `-L'/L(s, χ) x^s/s + 1/s²` has a simple pole at `0` with
residue `-(log x + b(χ))`, `b(χ) = DirichletCharacter.logDerivConstAtZero χ`. -/
theorem exists_neg_logDeriv_LFunction_mul_cpow_div_add_eq_of_eq_mul {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} {x : ℝ} (hx : 0 < x) {E : ℂ → ℂ} (hE : AnalyticAt ℂ E 0)
    (hE0 : E 0 ≠ 0) (hf : ∀ᶠ s in 𝓝[≠] (0 : ℂ), LFunction χ s = s * E s) :
    ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ 0 ∧ ∀ᶠ s in 𝓝[≠] (0 : ℂ),
      -(deriv (LFunction χ) s / LFunction χ s) * ((x : ℂ) ^ s / s) + 1 / s ^ 2 =
        (-((Real.log x : ℂ) + χ.logDerivConstAtZero)) / (s - 0) + φ s := by
  obtain ⟨φ, hφ, hφe⟩ :=
    Complex.exists_eventually_neg_logDeriv_mul_cpow_div_eq_of_eq_mul hx hE hE0 hf
  have hb : χ.logDerivConstAtZero = deriv E 0 / E 0 := by
    rw [logDerivConstAtZero_eq_logDeriv hE hE0 hf, logDeriv_apply]
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hφe] with s hs
  rw [hs, sub_zero, hb]
  ring

/-- **`L(s, χ)` near a zero of `ξ(s, χ)`.** Near a zero `p` of `ξ(s, χ)` of order `m` that is not
a pole of `Γ((s + a)/2)`, `L(s, χ) = (s - p)^m E(s)` with `E` analytic and nonzero at `p`. -/
theorem exists_LFunction_eventually_eq_pow_mul_of_analyticOrderAt_xi {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : q ≠ 1) {a : ℝ} (hapar : (1 - χ (-1)) / 2 = (a : ℂ))
    (hgf : ∀ w, χ.gammaFactor w = Complex.Gammaℝ (w + a))
    (hxid : Differentiable ℂ (xi χ)) {p : ℂ} {m : ℕ} (hm : analyticOrderAt (xi χ) p = m)
    (hp : ∀ n : ℕ, (p + a) / 2 ≠ -(n : ℂ)) :
    ∃ E : ℂ → ℂ, AnalyticAt ℂ E p ∧ E p ≠ 0 ∧
      ∀ᶠ s in 𝓝 p, LFunction χ s = (s - p) ^ m * E s := by
  obtain ⟨ξ₁, hξ₁a, hξ₁0, hξ₁e⟩ := (hxid.analyticAt p).analyticOrderAt_eq_natCast.mp hm
  refine ⟨fun s => ξ₁ s * ((q : ℂ) ^ (-((s + a) / 2)) *
      ((Real.pi : ℂ) ^ ((s + a) / 2) * (Complex.Gamma ((s + a) / 2))⁻¹)), ?_, ?_, ?_⟩
  · exact hξ₁a.mul ((differentiable_xi_cofactor q a).analyticAt p)
  · exact mul_ne_zero hξ₁0 (xi_cofactor_ne_zero q a hp)
  · filter_upwards [hξ₁e] with s hs
    rw [LFunction_eq_xi_mul_cofactor χ hq hapar hgf s, hs, smul_eq_mul]
    ring

/-- **The trivial zeros of `L(s, χ)` are simple.** At a pole `p = -a - 2n` of `Γ((s + a)/2)`
with `ξ(p, χ) ≠ 0`, `L(s, χ) = (s - p) E(s)` with `E` analytic and nonzero at `p`. -/
theorem exists_LFunction_eventually_eq_mul_of_xi_ne_zero {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : q ≠ 1) {a : ℝ} (hapar : (1 - χ (-1)) / 2 = (a : ℂ))
    (hgf : ∀ w, χ.gammaFactor w = Complex.Gammaℝ (w + a))
    (hxid : Differentiable ℂ (xi χ)) (n : ℕ) (hxi : xi χ (-(a : ℂ) - 2 * n) ≠ 0) :
    ∃ E : ℂ → ℂ, AnalyticAt ℂ E (-(a : ℂ) - 2 * n) ∧ E (-(a : ℂ) - 2 * n) ≠ 0 ∧
      ∀ᶠ s in 𝓝 (-(a : ℂ) - 2 * n), LFunction χ s = (s - (-(a : ℂ) - 2 * n)) * E s := by
  set p : ℂ := -(a : ℂ) - 2 * n with hpdef
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  obtain ⟨G, hGa, hG0, hGe⟩ := (Complex.differentiable_one_div_Gamma.analyticAt
    (-(n : ℂ))).analyticOrderAt_eq_natCast (n := 1) |>.mp
      ((Complex.analyticOrderAt_inv_Gamma_neg_natCast n).trans Nat.cast_one.symm)
  have hpn : (p + a) / 2 = -(n : ℂ) := by rw [hpdef]; ring
  have hl : AnalyticAt ℂ (fun s : ℂ => (s + a) / 2) p :=
    (analyticAt_id.add analyticAt_const).div_const
  have ht : Tendsto (fun s : ℂ => (s + a) / 2) (𝓝 p) (𝓝 (-(n : ℂ))) := by
    rw [← hpn]; exact hl.continuousAt.tendsto
  have hGe' := ht.eventually hGe
  have hGa' : AnalyticAt ℂ (fun s : ℂ => G ((s + a) / 2)) p := by
    have hGa2 : AnalyticAt ℂ G ((p + a) / 2) := by rw [hpn]; exact hGa
    exact AnalyticAt.comp (g := G) (f := fun s : ℂ => (s + a) / 2) hGa2 hl
  have hld : Differentiable ℂ (fun s : ℂ => (s + a) / 2) := by fun_prop
  have hA : Differentiable ℂ (fun s : ℂ => (q : ℂ) ^ (-((s + a) / 2))) :=
    fun s => (hld s).neg.const_cpow (Or.inl hq0)
  have hB : Differentiable ℂ (fun s : ℂ => (Real.pi : ℂ) ^ ((s + a) / 2)) :=
    fun s => (hld s).const_cpow (Or.inl hpi)
  refine ⟨fun s => xi χ s * ((q : ℂ) ^ (-((s + a) / 2)) *
      ((Real.pi : ℂ) ^ ((s + a) / 2) * (G ((s + a) / 2) / 2))), ?_, ?_, ?_⟩
  · exact (hxid.analyticAt p).mul ((hA.analyticAt p).mul ((hB.analyticAt p).mul hGa'.div_const))
  · have hGp : G ((p + a) / 2) ≠ 0 := by rw [hpn]; exact hG0
    refine mul_ne_zero hxi (mul_ne_zero (by rw [Ne, Complex.cpow_eq_zero_iff]; tauto)
      (mul_ne_zero (by rw [Ne, Complex.cpow_eq_zero_iff]; tauto) (div_ne_zero hGp two_ne_zero)))
  · filter_upwards [hGe'] with s hs
    rw [LFunction_eq_xi_mul_cofactor χ hq hapar hgf s, hs, pow_one, smul_eq_mul, hpdef]
    ring

/-- **The zeros of `L(s, χ)`.** For primitive `χ ≠ 1` of parity `a`, every zero of `L(s, χ)` is a
nontrivial zero or a trivial zero `-a - 2n`. -/
theorem mem_nontrivialZeros_or_eq_of_LFunction_eq_zero {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {a : ℝ}
    (hapar : (1 - χ (-1)) / 2 = (a : ℂ)) (hgf : ∀ w, χ.gammaFactor w = Complex.Gammaℝ (w + a))
    {s : ℂ} (hs : LFunction χ s = 0) :
    s ∈ χ.nontrivialZeros ∨ ∃ n : ℕ, s = -(a : ℂ) - 2 * n := by
  have hq : q ≠ 1 := fun h => hχ1 (level_one' χ h)
  rw [LFunction_eq_xi_mul_cofactor χ hq hapar hgf s, mul_eq_zero] at hs
  rcases hs with h | h
  · exact Or.inl ((xi_eq_zero_iff hχ hχ1 s).mp h)
  · right
    by_contra hne
    push Not at hne
    exact xi_cofactor_ne_zero q a (fun n hn => hne n (by linear_combination 2 * hn)) h

/-- **The residue theorem for `-L'/L(s, χ) x^s / s`.** For primitive `χ ≠ 1` of parity `a`,
`x > 1`, `M ≥ 1`, `U = 2M + 1 - a`, `c > 1` and `T > 0` not the absolute value of the ordinate of
a zero, the boundary integral of `F(s) = -L'/L(s, χ) x^s/s` over `[-U, c] × [-T, T]`, divided by
`2πi`, is
`-∑_{|γ| < T} x^ρ/ρ - (1 - a)(log x + b(χ)) - a L'(0, χ)/L(0, χ) + ∑_{m=1}^{M} x^{a-2m}/(2m-a)`,
with `b(χ) = DirichletCharacter.logDerivConstAtZero χ`. -/
theorem integral_rectangle_neg_logDeriv_LFunction_mul_cpow_div {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {a : ℝ}
    (ha : a = 0 ∨ a = 1) (hapar : (1 - χ (-1)) / 2 = (a : ℂ))
    (hgf : ∀ w, χ.gammaFactor w = Complex.Gammaℝ (w + a))
    {ι : Type u} (z : ι → ℂ) (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w)
    {x : ℝ} (hx : 1 < x) {M : ℕ} (hM : 1 ≤ M) {T : ℝ} (hT : 0 < T)
    (hTz : ∀ n, |(z n).im| ≠ T) {c : ℝ} (hc : 1 < c)
    {U : ℝ} (hU : U = 2 * M + 1 - a) {F : ℂ → ℂ}
    (hF : F = fun s => -(deriv (LFunction χ) s / LFunction χ s) * ((x : ℂ) ^ s / s)) :
    (1 / (2 * Real.pi * I)) *
        ((∫ t in (-T)..T, F (c + t * I) * I) + (∫ σ in c..(-U), F (σ + T * I)) +
          (∫ t in T..(-T), F (-(U : ℂ) + t * I) * I) + ∫ σ in (-U)..c, F (σ - T * I)) =
      -(∑' n, (if |(z n).im| < T then (x : ℂ) ^ z n / z n else 0)) -
        (1 - (a : ℂ)) * ((Real.log x : ℂ) + χ.logDerivConstAtZero) -
        (a : ℂ) * (deriv (LFunction χ) 0 / LFunction χ 0) +
        ∑ m ∈ Finset.Icc 1 M, (x : ℂ) ^ ((a : ℂ) - 2 * m) / (2 * m - (a : ℂ)) := by
  classical
  have hq : q ≠ 1 := fun h => hχ1 (level_one' χ h)
  have hxid := differentiable_xi hχ1
  have hLd : Differentiable ℂ (LFunction χ) := fun s =>
    differentiableAt_LFunction χ s (Or.inr hχ1)
  have hx0 : 0 < x := by linarith
  have hc1 : 1 < c := hc
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hU2 : 2 ≤ U := by rcases ha with h | h <;> rw [hU, h] <;> linarith
  -- facts about `ξ(s, χ)` and the zeros
  have hxi0 : xi χ 0 ≠ 0 := xi_zero_ne_zero hχ hχ1
  have hord_top := analyticOrderAt_xi_ne_top hχ hχ1
  have hmem_of := mem_nontrivialZeros_of_card_eq_analyticOrderAt hχ hχ1 hz
  have hexists : ∀ p, xi χ p = 0 → ∃ n, z n = p := fun p hxi =>
    exists_eq_of_card_eq_analyticOrderAt hχ hχ1 hz ((xi_eq_zero_iff hχ hχ1 p).mp hxi)
  have hfib := finite_of_card_eq_analyticOrderAt hχ hχ1 hz
  have hNfin := finite_setOf_abs_im_lt_of_card_eq_analyticOrderAt hχ hχ1 hz T
  set NF := hNfin.toFinset with hNF
  set Z : Finset ℂ := NF.image z with hZ
  set Tr : Finset ℂ := (Finset.Icc 1 M).image (fun m : ℕ => (a : ℂ) - 2 * m) with hTr
  set S : Finset ℂ := insert 0 (Z ∪ Tr) with hS
  have hZmem : ∀ p, p ∈ Z ↔ p ∈ χ.nontrivialZeros ∧ |p.im| < T := by
    intro p; constructor
    · intro hp
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨hmem_of n, by simpa [NF] using hn⟩
    · rintro ⟨hp, hpR⟩
      obtain ⟨n, hn⟩ := hexists p ((xi_eq_zero_iff hχ hχ1 p).mpr hp)
      exact Finset.mem_image.mpr ⟨n, by simp [NF, hn, hpR], hn⟩
  have hTrmem : ∀ p, p ∈ Tr ↔ ∃ m : ℕ, 1 ≤ m ∧ m ≤ M ∧ p = (a : ℂ) - 2 * m := by
    intro p
    simp only [Tr, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨m, ⟨h1, h2⟩, rfl⟩; exact ⟨m, h1, h2, rfl⟩
    · rintro ⟨m, h1, h2, rfl⟩; exact ⟨m, ⟨h1, h2⟩, rfl⟩
  have hZprop : ∀ p ∈ Z, p ≠ 0 ∧ 0 ≤ p.re ∧ p.re ≤ 1 ∧ |p.im| < T := by
    intro p hp
    obtain ⟨hnt, hpR⟩ := (hZmem p).mp hp
    exact ⟨ne_zero_of_mem_nontrivialZeros hnt, hnt.2.1.le, hnt.2.2.le, hpR⟩
  have hTrprop : ∀ p ∈ Tr, p.re < 0 ∧ -U < p.re ∧ p.im = 0 := by
    intro p hp
    obtain ⟨m, h1, h2, rfl⟩ := (hTrmem p).mp hp
    have h1' : (1 : ℝ) ≤ m := by exact_mod_cast h1
    have h2' : (m : ℝ) ≤ M := by exact_mod_cast h2
    have ha1 : a ≤ 1 := by rcases ha with h | h <;> simp [h]
    have ha0 : 0 ≤ a := by rcases ha with h | h <;> simp [h]
    rw [hU]
    simp only [sub_re, ofReal_re, mul_re, re_ofNat, natCast_re, im_ofNat, natCast_im, mul_zero,
      sub_zero, neg_sub, sub_im, ofReal_im, mul_im, zero_mul, add_zero, sub_self, and_true]
    constructor <;> linarith
  have h0Z : (0 : ℂ) ∉ Z := fun h => (hZprop 0 h).1 rfl
  have h0Tr : (0 : ℂ) ∉ Tr := fun h => by have := (hTrprop 0 h).1; simp at this
  have hZTr : ∀ p ∈ Tr, p ∉ Z := fun p hp hpZ => by
    linarith [(hTrprop p hp).1, (hZprop p hpZ).2.1]
  -- residues
  let mo : ℂ → ℕ := fun p => (analyticOrderAt (xi χ) p).toNat
  let kf : ℂ → ℕ := fun p => if p ∈ Z then mo p else 1
  let r : ℂ → ℂ := fun p =>
    if p = 0 then -(1 - (a : ℂ)) * ((Real.log x : ℂ) + χ.logDerivConstAtZero) -
      (a : ℂ) * (deriv (LFunction χ) 0 / LFunction χ 0)
    else -(kf p : ℂ) * ((x : ℂ) ^ p / p)
  let h2 : ℂ → ℂ := fun s => (1 - (a : ℂ)) * (1 / s ^ 2)
  let Ft : ℂ → ℂ := F + h2
  have hh2d : ∀ s : ℂ, s ≠ 0 → DifferentiableAt ℂ h2 s := fun s hs =>
    (differentiableAt_const _).mul ((differentiableAt_const _).div
      (differentiableAt_id.pow 2) (pow_ne_zero 2 hs))
  have hloc : ∀ p ∈ S, ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ p ∧
      ∀ᶠ s in 𝓝[≠] p, Ft s = r p / (s - p) + φ s := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · -- the origin
      have hr0 : r 0 = -(1 - (a : ℂ)) * ((Real.log x : ℂ) + χ.logDerivConstAtZero) -
          (a : ℂ) * (deriv (LFunction χ) 0 / LFunction χ 0) := by simp [r]
      rw [hr0]
      rcases ha with rfl | rfl
      · obtain ⟨E, hEa, hE0, hEe⟩ := exists_LFunction_eventually_eq_mul_of_xi_ne_zero hq hapar hgf
          hxid 0 (by simpa using hxi0)
        have hp0 : (-(((0 : ℝ)) : ℂ) - 2 * ((0 : ℕ) : ℂ)) = 0 := by simp
        rw [hp0] at hEa hE0 hEe
        have hf : ∀ᶠ s in 𝓝[≠] (0 : ℂ), LFunction χ s = s * E s := by
          filter_upwards [nhdsWithin_le_nhds hEe] with s hs
          rw [hs, sub_zero]
        obtain ⟨φ, hφ, hφe⟩ :=
          exists_neg_logDeriv_LFunction_mul_cpow_div_add_eq_of_eq_mul hx0 hEa hE0 hf
        refine ⟨φ, hφ, ?_⟩
        filter_upwards [hφe] with s hs
        simp only [Ft, h2, hF, Pi.add_apply]
        push_cast
        linear_combination hs
      · have hL0 : LFunction χ 0 ≠ 0 := by
          rw [LFunction_eq_xi_mul_cofactor χ hq hapar hgf 0]
          refine mul_ne_zero hxi0 (xi_cofactor_ne_zero q 1 fun n h => ?_)
          have := congrArg Complex.re h
          simp at this
          linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
        obtain ⟨φ, hφ, hφe⟩ := Complex.exists_eventually_neg_logDeriv_mul_cpow_div_eq_of_ne_zero
          hx0 (hLd.analyticAt 0) hL0
        refine ⟨φ, hφ, ?_⟩
        filter_upwards [hφe] with s hs
        simp only [Ft, h2, hF, Pi.add_apply]
        push_cast
        linear_combination hs
    rcases Finset.mem_union.mp hp with hpZ | hpT
    · obtain ⟨hp0, hpre, -, -⟩ := hZprop p hpZ
      have hm : analyticOrderAt (xi χ) p = (mo p : ℕ) :=
        (ENat.natCast_toNat (hord_top p)).symm
      have hHp : ∀ n : ℕ, (p + a) / 2 ≠ -(n : ℂ) := by
        intro n h
        have hpe : p = -(a : ℂ) - 2 * n := by linear_combination 2 * h
        have hre : p.re = -a - 2 * n := by rw [hpe]; simp
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have ha0 : 0 ≤ a := by rcases ha with h | h <;> simp [h]
        have ha' : a = 0 := by linarith
        have hn' : (n : ℝ) = 0 := by linarith
        apply hp0
        rw [hpe, ha', show ((n : ℕ) : ℂ) = ((n : ℝ) : ℂ) by simp, hn']
        simp
      obtain ⟨E, hEa, hE0, hEe⟩ := exists_LFunction_eventually_eq_pow_mul_of_analyticOrderAt_xi hq
        hapar hgf hxid hm hHp
      have hf : ∀ᶠ s in 𝓝[≠] p, LFunction χ s = (s - p) ^ ((mo p : ℕ) : ℤ) * E s := by
        filter_upwards [nhdsWithin_le_nhds hEe] with s hs
        rw [hs, zpow_natCast]
      obtain ⟨φ, hφ, hφe⟩ :=
        Complex.exists_eventually_neg_logDeriv_mul_cpow_div_eq_of_zpow hx0 hp0 hEa hE0 hf
      refine ⟨fun s => φ s + h2 s, hφ.add (hh2d p hp0), ?_⟩
      have hr : r p = -((mo p : ℕ) : ℂ) * ((x : ℂ) ^ p / p) := by
        simp [r, kf, hp0, hpZ]
      filter_upwards [hφe] with s hs
      rw [hr]
      simp only [Ft, hF, Pi.add_apply]
      push_cast at hs ⊢
      linear_combination hs
    · obtain ⟨m, hm1, hmM, rfl⟩ := (hTrmem p).mp hpT
      obtain ⟨hre, -, -⟩ := hTrprop _ hpT
      have hp0 : (a : ℂ) - 2 * m ≠ 0 := fun h => by rw [h] at hre; simp at hre
      have hxi : xi χ ((a : ℂ) - 2 * m) ≠ 0 := by
        rw [Ne, xi_eq_zero_iff hχ hχ1]
        intro h; linarith [h.2.1]
      obtain ⟨n, hn⟩ : ∃ n : ℕ, (a : ℂ) - 2 * m = -(a : ℂ) - 2 * n := by
        rcases ha with rfl | rfl
        · exact ⟨m, by simp⟩
        · refine ⟨m - 1, ?_⟩
          rw [Nat.cast_sub hm1]; push_cast; ring
      obtain ⟨E, hEa, hE0, hEe⟩ := exists_LFunction_eventually_eq_mul_of_xi_ne_zero hq hapar hgf
        hxid n (hn ▸ hxi)
      rw [← hn] at hEa hE0 hEe
      have hf : ∀ᶠ s in 𝓝[≠] ((a : ℂ) - 2 * m), LFunction χ s =
          (s - ((a : ℂ) - 2 * m)) ^ (1 : ℤ) * E s := by
        filter_upwards [nhdsWithin_le_nhds hEe] with s hs
        rw [hs, zpow_one]
      obtain ⟨φ, hφ, hφe⟩ :=
        Complex.exists_eventually_neg_logDeriv_mul_cpow_div_eq_of_zpow hx0 hp0 hEa hE0 hf
      refine ⟨fun s => φ s + h2 s, hφ.add (hh2d _ hp0), ?_⟩
      have hr : r ((a : ℂ) - 2 * m) = -((1 : ℕ) : ℂ) *
          ((x : ℂ) ^ ((a : ℂ) - 2 * m) / ((a : ℂ) - 2 * m)) := by
        simp only [r, kf, hp0, hZTr _ hpT, ite_false]
      filter_upwards [hφe] with s hs
      rw [hr]
      simp only [Ft, hF, Pi.add_apply]
      push_cast at hs ⊢
      linear_combination hs
  -- the rectangle
  set rect := RectilinearRectangle.ofBounds (-U) c (-T) T with hrect
  have hKre : ∀ s ∈ rect.carrier, -U ≤ s.re ∧ s.re ≤ c ∧ -T ≤ s.im ∧ s.im ≤ T := by
    intro s hs
    obtain ⟨h1, h2⟩ := Complex.mem_reProdIm.mp hs
    simp only [hrect, RectilinearRectangle.ofBounds_first_re,
      RectilinearRectangle.ofBounds_second_re, RectilinearRectangle.ofBounds_first_im,
      RectilinearRectangle.ofBounds_second_im] at h1 h2
    rw [Set.uIcc_of_le (by linarith)] at h1 h2
    exact ⟨h1.1, h1.2, h2.1, h2.2⟩
  have hFd : ∀ s ∈ rect.carrier, s ∉ S → DifferentiableAt ℂ F s := by
    intro s hsK hsS
    obtain ⟨k1, k2, k3, k4⟩ := hKre s hsK
    have hs0 : s ≠ 0 := fun h => hsS (by simp [S, h])
    have hLs : LFunction χ s ≠ 0 := by
      intro h0
      rcases mem_nontrivialZeros_or_eq_of_LFunction_eq_zero hχ hχ1 hapar hgf h0 with hnt | ⟨n, hse⟩
      · obtain ⟨n, hn⟩ := hexists s ((xi_eq_zero_iff hχ hχ1 s).mpr hnt)
        have hIm : |s.im| < T := lt_of_le_of_ne (abs_le.mpr ⟨k3, k4⟩) (hn ▸ hTz n)
        exact hsS (by simp [S, (hZmem s).mpr ⟨hnt, hIm⟩])
      · have hre : s.re = -a - 2 * n := by rw [hse]; simp
        have hk1 : -(2 * (M : ℝ) + 1 - a) ≤ -a - 2 * n := by rw [← hre, ← hU]; exact k1
        apply hsS
        refine Finset.mem_insert_of_mem (Finset.mem_union_right _ ((hTrmem s).mpr ?_))
        rcases ha with rfl | rfl
        · have hn1 : 1 ≤ n := by
            rcases Nat.eq_zero_or_pos n with h | h
            · exact absurd (by rw [hse, h]; simp) hs0
            · exact h
          have hnM : n ≤ M := by
            have h1 : (2 * n : ℝ) ≤ 2 * M + 1 := by linarith
            have h2 : 2 * n ≤ 2 * M + 1 := by exact_mod_cast h1
            omega
          exact ⟨n, hn1, hnM, by rw [hse]; simp⟩
        · have hnM : (n : ℝ) + 1 ≤ M := by
            have h1 : (n : ℝ) < M := by linarith
            have h2 : n < M := by exact_mod_cast h1
            have h3 : n + 1 ≤ M := h2
            exact_mod_cast h3
          refine ⟨n + 1, by omega, by exact_mod_cast hnM, ?_⟩
          rw [hse]; push_cast; ring
    have hx0' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    rw [hF]
    exact (((hLd.analyticAt s).deriv.differentiableAt.div (hLd s) hLs).neg).mul
      ((differentiableAt_id.const_cpow (Or.inl hx0')).div differentiableAt_id hs0)
  -- the double pole of `h2` at `0` moves to `F`
  let d : ℂ → ℂ := fun p => if p = 0 then -(1 - (a : ℂ)) else 0
  have hlocF : ∀ p ∈ S, ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ p ∧
      ∀ᶠ s in 𝓝[≠] p, F s = r p / (s - p) + d p / (s - p) ^ 2 + φ s := by
    intro p hp
    obtain ⟨φ, hφ, hφe⟩ := hloc p hp
    by_cases hp0 : p = 0
    · subst hp0
      refine ⟨φ, hφ, ?_⟩
      filter_upwards [hφe] with s hs
      simp only [Ft, h2, Pi.add_apply, d, ite_true, sub_zero] at hs ⊢
      linear_combination hs
    · refine ⟨fun s => φ s - h2 s, hφ.sub (hh2d p hp0), ?_⟩
      filter_upwards [hφe] with s hs
      simp only [Ft, Pi.add_apply, d, hp0, ite_false] at hs ⊢
      linear_combination hs
  obtain ⟨g, hg, hfg⟩ := Complex.exists_differentiableOn_eq_add_sum_div_sub_add_div_sub_sq _ S r d
    F hlocF (fun s hs h => (hFd s hs h).differentiableWithinAt)
  have hin : ∀ p ∈ S, rect.first.re < p.re ∧ p.re < rect.second.re ∧ rect.first.im < p.im ∧
      p.im < rect.second.im := by
    intro p hp
    simp only [hrect, RectilinearRectangle.ofBounds_first_re,
      RectilinearRectangle.ofBounds_second_re, RectilinearRectangle.ofBounds_first_im,
      RectilinearRectangle.ofBounds_second_im]
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simp only [zero_re, zero_im, Left.neg_neg_iff]
      exact ⟨by linarith, by linarith, hT, hT⟩
    rcases Finset.mem_union.mp hp with hpZ | hpT
    · obtain ⟨-, h1, h2, h3⟩ := hZprop p hpZ
      exact ⟨by linarith, by linarith, (abs_lt.mp h3).1, (abs_lt.mp h3).2⟩
    · obtain ⟨h1, h2, h3⟩ := hTrprop p hpT
      exact ⟨h2, by linarith, by rw [h3]; linarith, by rw [h3]; exact hT⟩
  have hRS := RectilinearRectangle.boundaryIntegral_eq_two_pi_mul_I_mul_sum_of_double rect S r d
    F g hin hg hfg
  simp only [hrect, RectilinearRectangle.boundaryIntegral, RectilinearRectangle.ofBounds_first_re,
    RectilinearRectangle.ofBounds_second_re, RectilinearRectangle.ofBounds_first_im,
    RectilinearRectangle.ofBounds_second_im, smul_eq_mul] at hRS
  simp only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg] at hRS
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_symm (-U) c, intervalIntegral.integral_symm (-T) T]
  -- the residue sum
  have hcard : ∀ p ∈ Z, (NF.filter (fun n => z n = p)).card = mo p := by
    intro p hp
    have hpR := (hZprop p hp).2.2.2
    have := hfib p
    have h := hz p
    rw [ENat.card_eq_coe_natCard, Nat.subtype_card (NF.filter (fun n => z n = p)) (by
      intro n
      simp only [NF, Finset.mem_filter, Set.Finite.mem_toFinset, mem_ofPred_eq]
      exact ⟨And.right, fun h => ⟨h ▸ hpR, h⟩⟩), ← ENat.natCast_toNat (hord_top p)] at h
    exact_mod_cast h
  have htsum : ∑' n, (if |(z n).im| < T then (x : ℂ) ^ z n / z n else 0) =
      ∑ p ∈ Z, (mo p : ℂ) * ((x : ℂ) ^ p / p) := by
    rw [tsum_eq_sum (s := NF) (fun n hn => ite_eq_right (by simpa [NF] using hn))]
    rw [Finset.sum_congr rfl (fun n hn => ite_eq_left (by simpa [NF] using hn))]
    rw [Finset.sum_comp (fun p => (x : ℂ) ^ p / p) z]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hcard p hp, nsmul_eq_mul]
  have hinj : Set.InjOn (fun m : ℕ => (a : ℂ) - 2 * m) (Finset.Icc 1 M : Set ℕ) := by
    intro m₁ _ m₂ _ h
    simp only [sub_right_inj, mul_eq_mul_left_iff, two_ne_zero, or_false, Nat.cast_inj] at h
    exact h
  have hsumS : ∑ p ∈ S, r p =
      -(∑' n, (if |(z n).im| < T then (x : ℂ) ^ z n / z n else 0)) -
        (1 - (a : ℂ)) * ((Real.log x : ℂ) + χ.logDerivConstAtZero) -
        (a : ℂ) * (deriv (LFunction χ) 0 / LFunction χ 0) +
        ∑ m ∈ Finset.Icc 1 M, (x : ℂ) ^ ((a : ℂ) - 2 * m) / (2 * m - (a : ℂ)) := by
    have hdisj : Disjoint Z Tr := Finset.disjoint_right.mpr hZTr
    rw [Finset.sum_insert (by simp [h0Z, h0Tr]), Finset.sum_union hdisj, htsum,
      Finset.sum_image hinj]
    have hr0 : r 0 = -(1 - (a : ℂ)) * ((Real.log x : ℂ) + χ.logDerivConstAtZero) -
        (a : ℂ) * (deriv (LFunction χ) 0 / LFunction χ 0) := by simp [r]
    have hrZ : ∑ p ∈ Z, r p = -∑ p ∈ Z, (mo p : ℂ) * ((x : ℂ) ^ p / p) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun p hp => ?_
      obtain ⟨hp0, -⟩ := hZprop p hp
      simp [r, kf, hp0, hp]
    have hrT : ∑ m ∈ Finset.Icc 1 M, r ((a : ℂ) - 2 * m) =
        ∑ m ∈ Finset.Icc 1 M, (x : ℂ) ^ ((a : ℂ) - 2 * m) / (2 * m - (a : ℂ)) := by
      refine Finset.sum_congr rfl fun m hm => ?_
      have hpT : (a : ℂ) - 2 * m ∈ Tr := Finset.mem_image.mpr ⟨m, hm, rfl⟩
      have hre := (hTrprop _ hpT).1
      have hp0 : (a : ℂ) - 2 * m ≠ 0 := fun h => by rw [h] at hre; simp at hre
      simp only [r, kf, hp0, hZTr _ hpT, ite_false]
      rw [show (2 * (m : ℂ) - a) = -((a : ℂ) - 2 * m) by ring, div_neg]
      push_cast
      ring
    rw [hr0, hrZ, hrT]
    ring
  rw [← hsumS]
  have hpi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [div_mul_eq_mul_div, one_mul, div_eq_iff hpi]
  linear_combination hRS


/-! ### Good heights and the edges of the rectangle -/

private lemma finite_setOf_abs_sub_im_lt_of_card_le {ι : Type u} (z : ι → ℂ) (t B : ℝ)
    (hB : ∀ F : Finset ι, (∀ n ∈ F, |t - (z n).im| < 1) → (F.card : ℝ) ≤ B) :
    {n | |t - (z n).im| < 1}.Finite := by
  by_contra hinf
  obtain ⟨F, hFsub, hFcard⟩ := Set.Infinite.exists_subset_card_eq hinf (⌈B⌉₊ + 1)
  have h1 := hB F (fun n hn => hFsub hn)
  rw [hFcard] at h1
  push_cast at h1
  linarith [Nat.le_ceil B]

private lemma exists_far_from_finset (G : Finset ℝ) (R : ℝ) :
    ∃ T : ℝ, R ≤ T ∧ T ≤ R + 1 ∧ ∀ γ ∈ G, 1 / (2 * ((G.card : ℝ) + 1)) ≤ |γ - T| := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = G.card := ⟨_, rfl⟩
  rw [← hm]
  have hmpos : (0 : ℝ) < m + 1 := by positivity
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / ((m : ℝ) + 1) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hgood : ∃ j ∈ Finset.range (m + 1), ∀ γ ∈ G, δ / 2 ≤ |γ - (R + j * δ)| := by
    by_contra hcon
    push Not at hcon
    choose! g hgG hgd using hcon
    have hinj : Set.InjOn g (Finset.range (m + 1) : Set ℕ) := by
      intro j hj k hk hjk
      by_contra hne
      have h1 := hgd j hj
      have h2 := hgd k hk
      rw [hjk] at h1
      have h3 : |(R + j * δ) - (R + k * δ)| < δ := by
        have := abs_sub_le (R + j * δ) (g k) (R + k * δ)
        rw [abs_sub_comm (R + j * δ) (g k)] at this
        linarith
      have h4 : δ ≤ |(R + j * δ) - (R + k * δ)| := by
        have hjk' : (1 : ℝ) ≤ |(j : ℝ) - k| := by
          rcases lt_or_gt_of_ne hne with h | h
          · have : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
            rw [abs_sub_comm, abs_of_pos (by linarith)]
            linarith
          · have : (k : ℝ) + 1 ≤ j := by exact_mod_cast h
            rw [abs_of_pos (by linarith)]
            linarith
        have : (R + j * δ) - (R + k * δ) = ((j : ℝ) - k) * δ := by ring
        rw [this, abs_mul, abs_of_pos hδpos]
        nlinarith
      linarith
    have := Finset.card_le_card_of_injOn g (fun j hj => hgG j hj) hinj
    simp only [Finset.card_range] at this
    omega
  obtain ⟨j, hj, hjG⟩ := hgood
  have hjm : (j : ℝ) ≤ m := by
    have := Finset.mem_range.mp hj
    exact_mod_cast Nat.lt_succ_iff.mp this
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hjδ : (j : ℝ) * δ ≤ 1 := by
    have : (j : ℝ) * δ = j / ((m : ℝ) + 1) := by rw [hδ]; ring
    rw [this, div_le_iff₀ hmpos]; linarith
  refine ⟨R + j * δ, by nlinarith, by linarith, fun γ hγ => ?_⟩
  have := hjG γ hγ
  have e : 1 / (2 * ((m : ℝ) + 1)) = δ / 2 := by rw [hδ]; field_simp
  rw [e]; exact this

private lemma norm_logDeriv_LFunction_le_of_far {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {ι : Type u} (z : ι → ℂ) (R ℓ A₁ A₂ δ : ℝ) (hδ : 0 < δ)
    (hC₂ : ∀ s : ℂ, -3 / 2 ≤ s.re → s.re ≤ 5 / 2 → 2 ≤ |s.im| → |s.im| ≤ R + 1 →
      (∀ n, (z n).im ≠ s.im) →
      ‖deriv (LFunction χ) s / LFunction χ s
          - ∑' n, (if |s.im - (z n).im| < 1 then 1 / (s - z n) else 0)‖ ≤ A₂ * ℓ)
    (hcnt : ∀ t : ℝ, |t| ≤ R + 1 → ∀ F : Finset ι, (∀ n ∈ F, |t - (z n).im| < 1) →
      (F.card : ℝ) ≤ A₁ * ℓ)
    (σ y : ℝ) (hσ1 : -1 ≤ σ) (hσ2 : σ ≤ 2) (hy1 : 2 ≤ |y|) (hy2 : |y| ≤ R + 1)
    (hfy : ∀ n, δ ≤ |y - (z n).im|) :
    ‖deriv (LFunction χ) ((σ : ℂ) + y * I) /
        LFunction χ ((σ : ℂ) + y * I)‖ ≤ A₂ * ℓ + A₁ * ℓ / δ := by
  classical
  set s : ℂ := (σ : ℂ) + y * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = y := by simp [hs]
  have hzim : ∀ n, (z n).im ≠ s.im := by
    intro n h
    have := hfy n
    rw [hsim] at h
    rw [← h, sub_self, abs_zero] at this
    linarith
  have h1 := hC₂ s (by rw [hsre]; linarith) (by rw [hsre]; linarith) (by rw [hsim]; exact hy1)
    (by rw [hsim]; exact hy2) hzim
  have hfin := finite_setOf_abs_sub_im_lt_of_card_le z y (A₁ * ℓ) (hcnt y hy2)
  set B := hfin.toFinset with hB
  have hsum_eq : ∑' n, (if |s.im - (z n).im| < 1 then 1 / (s - z n) else 0) =
      ∑ n ∈ B, (if |s.im - (z n).im| < 1 then 1 / (s - z n) else 0) := by
    refine tsum_eq_sum fun n hn => ite_eq_right ?_
    rw [hsim]
    simpa [B] using hn
  have hBcard : (B.card : ℝ) ≤ A₁ * ℓ := hcnt y hy2 B (fun n hn => by simpa [B] using hn)
  have hterm : ∀ n ∈ B, ‖(if |s.im - (z n).im| < 1 then 1 / (s - z n) else 0)‖ ≤ 1 / δ := by
    intro n _
    split_ifs
    · have hd : δ ≤ ‖s - z n‖ := by
        refine (hfy n).trans ?_
        have := Complex.abs_im_le_norm (s - z n)
        rwa [Complex.sub_im, hsim] at this
      rw [norm_div, norm_one]
      exact one_div_le_one_div_of_le hδ hd
    · rw [norm_zero]; positivity
  have hsum_le : ‖∑' n, (if |s.im - (z n).im| < 1 then 1 / (s - z n) else 0)‖ ≤
      A₁ * ℓ / δ := by
    rw [hsum_eq]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_one_div (A₁ * ℓ)]
    exact mul_le_mul_of_nonneg_right hBcard (by positivity)
  have htri := norm_le_norm_sub_add (deriv (LFunction χ) s /
    LFunction χ s)
    (∑' n, (if |s.im - (z n).im| < 1 then 1 / (s - z n) else 0))
  linarith

/-- **Good heights for `L'/L(s, χ)`.** There is an absolute constant `K` such that for every
primitive Dirichlet character `χ` modulo `q`, every family `z` listing the zeros of `ξ(s, χ)` with
multiplicity and every `R ≥ 2`, some `T ∈ [R, R + 1]` is not the absolute value of the ordinate of
a zero and satisfies `‖L'/L(σ ± iT, χ)‖ ≤ K log² (q (R + 3))` for `-1 ≤ σ ≤ 2`. -/
theorem exists_good_height_norm_logDeriv_LFunction_le :
    ∃ K : ℝ, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ {ι : Type u} (z : ι → ℂ),
        (∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w) →
        ∀ R : ℝ, 2 ≤ R → ∃ T : ℝ, R ≤ T ∧ T ≤ R + 1 ∧ (∀ n, |(z n).im| ≠ T) ∧
          ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
            ‖deriv (LFunction χ) ((σ : ℂ) + T * I) /
                LFunction χ ((σ : ℂ) + T * I)‖ ≤
                K * Real.log (q * (R + 3)) ^ 2 ∧
            ‖deriv (LFunction χ) ((σ : ℂ) - T * I) /
                LFunction χ ((σ : ℂ) - T * I)‖ ≤
                K * Real.log (q * (R + 3)) ^ 2 := by
  classical
  obtain ⟨C₁, hC₁⟩ := exists_card_le_log_of_abs_sub_im_lt.{u}
  obtain ⟨C₂, hC₂⟩ := exists_norm_logDeriv_LFunction_sub_tsum_le_log.{u}
  obtain ⟨A₁, hA₁⟩ : ∃ A, A = |C₁| := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂⟩ : ∃ A, A = |C₂| := ⟨_, rfl⟩
  have hA₁0 : 0 ≤ A₁ := by rw [hA₁]; exact abs_nonneg _
  have hA₂0 : 0 ≤ A₂ := by rw [hA₂]; exact abs_nonneg _
  refine ⟨A₂ + 2 * A₁ * (2 * A₁ + 1), ?_⟩
  intro q _ χ hχ ι z hz R hR
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = Real.log (q * (R + 3)) := ⟨_, rfl⟩
  rw [← hℓ]
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    nlinarith
  have hcnt : ∀ t : ℝ, |t| ≤ R + 1 → ∀ F : Finset ι, (∀ n ∈ F, |t - (z n).im| < 1) →
      (F.card : ℝ) ≤ A₁ * ℓ := by
    intro t ht F hF
    have h := hC₁ χ hχ z hz t F hF
    have hlog : Real.log (q * (|t| + 2)) ≤ ℓ := by
      rw [hℓ]; exact Real.log_le_log (by positivity) (by nlinarith)
    have hlog0 : 0 ≤ Real.log (q * (|t| + 2)) := Real.log_nonneg (by nlinarith [abs_nonneg t])
    calc (F.card : ℝ) ≤ C₁ * Real.log (q * (|t| + 2)) := h
      _ ≤ A₁ * Real.log (q * (|t| + 2)) := by
          rw [hA₁]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hlog0
      _ ≤ A₁ * ℓ := mul_le_mul_of_nonneg_left hlog hA₁0
  have hC₂' : ∀ s : ℂ, -3 / 2 ≤ s.re → s.re ≤ 5 / 2 → 2 ≤ |s.im| → |s.im| ≤ R + 1 →
      (∀ n, (z n).im ≠ s.im) →
      ‖deriv (LFunction χ) s / LFunction χ s
          - ∑' n, (if |s.im - (z n).im| < 1 then 1 / (s - z n) else 0)‖ ≤ A₂ * ℓ := by
    intro s h1 h2 h3 h4 h5
    have h := hC₂ χ hχ z hz s h1 h2 h3 h5
    have hlog : Real.log (q * (|s.im| + 2)) ≤ ℓ := by
      rw [hℓ]; exact Real.log_le_log (by positivity) (by nlinarith)
    have hlog0 : 0 ≤ Real.log (q * (|s.im| + 2)) := Real.log_nonneg (by nlinarith)
    refine h.trans ?_
    calc C₂ * Real.log (q * (|s.im| + 2)) ≤ A₂ * Real.log (q * (|s.im| + 2)) := by
          rw [hA₂]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hlog0
      _ ≤ A₂ * ℓ := mul_le_mul_of_nonneg_left hlog hA₂0
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, t₀ = R + 1 / 2 := ⟨_, rfl⟩
  have ht₀a : |t₀| ≤ R + 1 := by rw [abs_of_pos (by linarith)]; linarith
  have ht₀b : |-t₀| ≤ R + 1 := by rw [abs_neg]; exact ht₀a
  have hfinP := finite_setOf_abs_sub_im_lt_of_card_le z t₀ (A₁ * ℓ) (hcnt t₀ ht₀a)
  have hfinM := finite_setOf_abs_sub_im_lt_of_card_le z (-t₀) (A₁ * ℓ) (hcnt (-t₀) ht₀b)
  obtain ⟨G, hG⟩ : ∃ G : Finset ℝ,
      G = (hfinP.toFinset ∪ hfinM.toFinset).image (fun n => |(z n).im|) := ⟨_, rfl⟩
  have hGcard : (G.card : ℝ) ≤ 2 * A₁ * ℓ := by
    have h1 : G.card ≤ (hfinP.toFinset ∪ hfinM.toFinset).card := by
      rw [hG]; exact Finset.card_image_le
    have h2 := Finset.card_union_le hfinP.toFinset hfinM.toFinset
    have h3 := hcnt t₀ ht₀a hfinP.toFinset (fun n hn => by simpa using hn)
    have h4 := hcnt (-t₀) ht₀b hfinM.toFinset (fun n hn => by simpa using hn)
    have : (G.card : ℝ) ≤ hfinP.toFinset.card + hfinM.toFinset.card := by
      exact_mod_cast h1.trans h2
    linarith
  obtain ⟨T, hT1, hT2, hTG⟩ := exists_far_from_finset G R
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / (2 * ((G.card : ℝ) + 1)) := ⟨_, rfl⟩
  rw [← hδ] at hTG
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδ1 : δ ≤ 1 / 2 := by
    rw [hδ]
    apply one_div_le_one_div_of_le (by norm_num)
    linarith [(Nat.cast_nonneg G.card : (0 : ℝ) ≤ G.card)]
  have hTpos : 0 < T := by linarith
  have hTt₀ : |T - t₀| ≤ 1 / 2 := by
    rw [abs_le, ht₀]; constructor <;> linarith
  have hfar : ∀ n, δ ≤ |T - (z n).im| ∧ δ ≤ |-T - (z n).im| := by
    intro n
    by_cases hnA : n ∈ hfinP.toFinset ∪ hfinM.toFinset
    · have hγ : |(z n).im| ∈ G := by rw [hG]; exact Finset.mem_image.mpr ⟨n, hnA, rfl⟩
      have h1 := hTG _ hγ
      have e1 : |(|(z n).im| - T)| ≤ |T - (z n).im| := by
        rw [abs_sub_comm]
        have := abs_abs_sub_abs_le_abs_sub T (z n).im
        rwa [abs_of_pos hTpos] at this
      have e2 : |(|(z n).im| - T)| ≤ |-T - (z n).im| := by
        rw [abs_sub_comm, show -T - (z n).im = -(T + (z n).im) by ring, abs_neg]
        have := abs_abs_sub_abs_le_abs_sub T (-(z n).im)
        rwa [abs_of_pos hTpos, abs_neg, sub_neg_eq_add] at this
      exact ⟨h1.trans e1, h1.trans e2⟩
    · rw [Finset.mem_union, not_or] at hnA
      have hP : 1 ≤ |t₀ - (z n).im| := by
        by_contra h; push Not at h; exact hnA.1 (by simpa using h)
      have hM : 1 ≤ |-t₀ - (z n).im| := by
        by_contra h; push Not at h; exact hnA.2 (by simpa using h)
      constructor
      · have := abs_sub_abs_le_abs_sub (t₀ - (z n).im) (t₀ - T)
        have e : t₀ - (z n).im - (t₀ - T) = T - (z n).im := by ring
        rw [e] at this
        have : |t₀ - T| ≤ 1 / 2 := by rw [abs_sub_comm]; exact hTt₀
        linarith
      · have := abs_sub_abs_le_abs_sub (-t₀ - (z n).im) (-t₀ + T)
        have e : -t₀ - (z n).im - (-t₀ + T) = -T - (z n).im := by ring
        rw [e] at this
        have : |-t₀ + T| ≤ 1 / 2 := by
          rw [show -t₀ + T = T - t₀ by ring]; exact hTt₀
        linarith
  have hord : ∀ n, |(z n).im| ≠ T := by
    intro n h
    have h1 := (hfar n).1
    have h2 := (hfar n).2
    rcases (abs_eq hTpos.le).mp h with h' | h'
    · rw [h', sub_self, abs_zero] at h1; linarith
    · rw [h', sub_neg_eq_add, neg_add_cancel, abs_zero] at h2; linarith
  have hinvδ : A₁ * ℓ / δ ≤ 2 * A₁ * (2 * A₁ + 1) * ℓ ^ 2 := by
    have e : A₁ * ℓ / δ = A₁ * ℓ * (2 * ((G.card : ℝ) + 1)) := by
      rw [hδ]; field_simp
    rw [e]
    have : (2 * ((G.card : ℝ) + 1)) ≤ 2 * (2 * A₁ + 1) * ℓ := by nlinarith
    calc A₁ * ℓ * (2 * ((G.card : ℝ) + 1)) ≤ A₁ * ℓ * (2 * (2 * A₁ + 1) * ℓ) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * A₁ * (2 * A₁ + 1) * ℓ ^ 2 := by ring
  have hℓ2 : A₂ * ℓ ≤ A₂ * ℓ ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hA₂0
  have hTabs : |T| = T := abs_of_pos hTpos
  refine ⟨T, hT1, hT2, hord, fun σ hσ1 hσ2 => ⟨?_, ?_⟩⟩
  · have := norm_logDeriv_LFunction_le_of_far χ z R ℓ A₁ A₂ δ hδpos hC₂' hcnt σ T hσ1 hσ2
      (by rw [hTabs]; linarith) (by rw [hTabs]; exact hT2) (fun n => (hfar n).1)
    linarith
  · have := norm_logDeriv_LFunction_le_of_far χ z R ℓ A₁ A₂ δ hδpos hC₂' hcnt σ (-T) hσ1 hσ2
      (by rw [abs_neg, hTabs]; linarith) (by rw [abs_neg, hTabs]; exact hT2)
      (fun n => (hfar n).2)
    have e : ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) = (σ : ℂ) - T * I := by push_cast; ring
    rw [e] at this
    linarith

private lemma one_div_log_le_three {x : ℝ} (hx : 3 / 2 ≤ x) : 1 / Real.log x ≤ 3 := by
  have hl : 1 / 3 < Real.log x := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have h3 : Real.exp (1 / 3) ^ 3 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have he := Real.exp_one_lt_d9
    have hp := Real.exp_pos (1 / 3)
    nlinarith [sq_nonneg (Real.exp (1 / 3) - 3 / 2), sq_nonneg (Real.exp (1 / 3))]
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- On a horizontal line `Im s = y`, `|y| = T ≥ 2`, where `‖L'/L(σ + iy, χ)‖ ≤ B` for
`-1 ≤ σ ≤ 2`: for `σ ≤ c`, `‖-L'/L(s, χ) x^s/s‖ ≤ (Φ - σ) x^σ / T` with
`Φ = log q + log (T + 2) + 7 + |C_d| + 2 K₀ + 2c + B`. -/
private lemma norm_integrand_le_of_abs_im_eq (Cd : ℝ)
    (hCd : ∀ v : ℂ, 0 < v.re → 1 ≤ ‖v‖ → ‖Complex.digamma v‖ ≤ Real.log ‖v‖ + Cd) (K₀ : ℝ)
    (hK₀0 : 0 ≤ K₀)
    (hK₀ : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 2 ≤ s.re →
      ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ K₀)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (a : ℝ)
    (hgf : ∀ w, χ.gammaFactor w = Complex.Gammaℝ (w + a))
    (hgf' : ∀ w, χ⁻¹.gammaFactor w = Complex.Gammaℝ (w + a)) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (x : ℝ) (hx : 1 < x) (c : ℝ) (hc : 1 ≤ c) (T y B : ℝ) (hT : 2 ≤ T) (hy : |y| = T)
    (hB0 : 0 ≤ B)
    (hB : ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
      ‖deriv (LFunction χ) ((σ : ℂ) + y * I) /
        LFunction χ ((σ : ℂ) + y * I)‖ ≤ B)
    (σ : ℝ) (hσ : σ ≤ c) :
    ‖-(deriv (LFunction χ) ((σ : ℂ) + y * I) /
        LFunction χ ((σ : ℂ) + y * I)) *
      ((x : ℂ) ^ ((σ : ℂ) + y * I) / ((σ : ℂ) + y * I))‖ ≤
      (Real.log q + Real.log (T + 2) + (7 + |Cd| + K₀) + 2 * c + B + K₀ - σ) * x ^ σ / T := by
  set s : ℂ := (σ : ℂ) + y * I with hs
  have hx0 : 0 < x := by linarith
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = y := by simp [hs]
  have hsT : T ≤ ‖s‖ := by rw [← hy, ← hsim]; exact Complex.abs_im_le_norm s
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlT : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
  have hCd0 := abs_nonneg Cd
  set Φ := Real.log q + Real.log (T + 2) + (7 + |Cd| + K₀) + 2 * c + B + K₀ with hΦ
  have hLD : ‖deriv (LFunction χ) s / LFunction χ s‖ ≤
      Φ - σ := by
    rcases le_or_gt σ (-1) with h1 | h1
    · have hz : 1 ≤ |((Real.pi : ℂ) * ((s + a) / 2)).im| := by
        have : ((Real.pi : ℂ) * ((s + a) / 2)).im = Real.pi * y / 2 := by
          simp [hs]; ring
        rw [this, abs_div, abs_mul, hy, abs_of_pos Real.pi_pos, abs_two]
        have := Real.pi_gt_three
        nlinarith
      have hsin := Complex.sin_ne_zero_of_one_le_abs_im hz
      have hcot := Complex.norm_cos_le_two_mul_norm_sin_of_one_le_abs_im hz
      obtain ⟨-, hb⟩ := norm_logDeriv_LFunction_le_of_re_le_neg_one hCd hK₀ hχ hgf hgf'
        ha0 ha1 (by rw [hsre]; exact h1) hsin hcot
      have hns : ‖s‖ ≤ -σ + T := by
        calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
          _ = -σ + T := by rw [hsre, hsim, hy, abs_of_neg (by linarith)]
      have hlg : Real.log (‖s‖ + 2) ≤ Real.log (T + 2) + -σ := by
        have h2 : ‖s‖ + 2 ≤ (T + 2) * Real.exp (-σ) := by
          have := Real.add_one_le_exp (-σ)
          nlinarith
        calc Real.log (‖s‖ + 2) ≤ Real.log ((T + 2) * Real.exp (-σ)) :=
              Real.log_le_log (by positivity) h2
          _ = Real.log (T + 2) + -σ := by
              rw [Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp]
      rw [hΦ]
      linarith
    · rcases le_or_gt σ 2 with h2 | h2
      · have := hB σ h1.le h2
        rw [hΦ]
        linarith
      · have := hK₀ χ s (by rw [hsre]; linarith)
        rw [hΦ]
        linarith
  have hΦσ : 0 ≤ Φ - σ := (norm_nonneg _).trans hLD
  have hTpos : 0 < T := by linarith
  rw [norm_mul, norm_neg, norm_div ((x : ℂ) ^ s) s, Complex.norm_cpow_eq_rpow_re_of_pos hx0, hsre]
  have he := Real.rpow_pos_of_pos hx0 σ
  calc ‖deriv (LFunction χ) s / LFunction χ s‖ * (x ^ σ / ‖s‖) ≤ (Φ - σ) * (x ^ σ / T) := by
        apply mul_le_mul hLD _ (by positivity) hΦσ
        exact div_le_div_of_nonneg_left he.le hTpos hsT
    _ = (Φ - σ) * x ^ σ / T := by ring

private lemma cos_pi_mul_neg_half_eq_zero (a : ℝ) (ha : a = 0 ∨ a = 1) (M : ℕ) :
    Real.cos (Real.pi * ((-(2 * (M : ℝ) + 1 - a) + a) / 2)) = 0 := by
  rcases ha with rfl | rfl
  · have : Real.pi * ((-(2 * (M : ℝ) + 1 - 0) + 0) / 2) = -((M : ℝ) * Real.pi + Real.pi / 2) := by
      ring
    rw [this, Real.cos_neg, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero]
  · have : Real.pi * ((-(2 * (M : ℝ) + 1 - 1) + 1) / 2) = Real.pi / 2 - (M : ℝ) * Real.pi := by
      ring
    rw [this, Real.cos_pi_div_two_sub, Real.sin_nat_mul_pi]

private lemma norm_integral_vertical_le (Cd : ℝ)
    (hCd : ∀ v : ℂ, 0 < v.re → 1 ≤ ‖v‖ → ‖Complex.digamma v‖ ≤ Real.log ‖v‖ + Cd) (K₀ : ℝ)
    (hK₀ : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 2 ≤ s.re →
      ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ K₀)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (a : ℝ)
    (ha : a = 0 ∨ a = 1)
    (hgf : ∀ w, χ.gammaFactor w = Complex.Gammaℝ (w + a))
    (hgf' : ∀ w, χ⁻¹.gammaFactor w = Complex.Gammaℝ (w + a))
    (x : ℝ) (hx : 1 < x) (T : ℝ) (hT : 0 < T) (M : ℕ) (hM : 1 ≤ M) :
    ‖∫ t in T..(-T), -(deriv (LFunction χ)
        (-((2 * M + 1 - a : ℝ) : ℂ) + t * I) /
        LFunction χ (-((2 * M + 1 - a : ℝ) : ℂ) + t * I)) *
      ((x : ℂ) ^ (-((2 * M + 1 - a : ℝ) : ℂ) + t * I) /
        (-((2 * M + 1 - a : ℝ) : ℂ) + t * I)) * I‖ ≤
      (Real.log q + T + 2 + (7 + |Cd| + K₀) + (2 * M + 1 - a)) *
        Real.exp (-(2 * M + 1 - a) * Real.log x) * (2 * T) := by
  have ha0 : 0 ≤ a := by rcases ha with h | h <;> simp [h]
  have ha1 : a ≤ 1 := by rcases ha with h | h <;> simp [h]
  have hx0 : 0 < x := by linarith
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = 2 * M + 1 - a := ⟨_, rfl⟩
  rw [← hU]
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hU2 : 2 ≤ U := by rw [hU]; linarith
  have hb : ∀ t ∈ Set.uIoc T (-T), ‖-(deriv (LFunction χ)
        (-(U : ℂ) + t * I) / LFunction χ (-(U : ℂ) + t * I)) *
      ((x : ℂ) ^ (-(U : ℂ) + t * I) / (-(U : ℂ) + t * I)) * I‖ ≤
      (Real.log q + T + 2 + (7 + |Cd| + K₀) + U) * Real.exp (-U * Real.log x) := by
    intro t ht
    have ht' : |t| ≤ T := by
      rw [Set.uIoc_of_ge (by linarith)] at ht
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    set s : ℂ := -(U : ℂ) + t * I with hs
    have hsre : s.re = -U := by simp [hs]
    have hsim : s.im = t := by simp [hs]
    have hzeq : (Real.pi : ℂ) * ((s + a) / 2) =
        ((Real.pi * ((-U + a) / 2) : ℝ) : ℂ) + ((Real.pi * t / 2 : ℝ) : ℂ) * I := by
      rw [hs]; push_cast; ring
    have hcos : Real.cos (Real.pi * ((-U + a) / 2)) = 0 := by
      rw [hU]; exact cos_pi_mul_neg_half_eq_zero a ha M
    obtain ⟨hsin, hcot⟩ := sin_ne_zero_and_norm_cos_le_of_cos_eq_zero _ (Real.pi * t / 2) hcos
    rw [← hzeq] at hsin hcot
    obtain ⟨-, hbd⟩ := norm_logDeriv_LFunction_le_of_re_le_neg_one hCd hK₀ hχ hgf hgf'
      ha0 ha1 (by rw [hsre]; linarith) hsin hcot
    have hns : ‖s‖ ≤ U + T := by
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ ≤ U + T := by rw [hsre, hsim, abs_neg, abs_of_pos (by linarith)]; linarith
    have hns1 : 1 ≤ ‖s‖ := by
      have := Complex.abs_re_le_norm s
      rw [hsre, abs_neg, abs_of_pos (by linarith)] at this
      linarith
    have hlg : Real.log (‖s‖ + 2) ≤ U + T + 2 := by
      have := Real.log_le_sub_one_of_pos (show 0 < ‖s‖ + 2 by positivity)
      linarith
    rw [norm_mul, Complex.norm_I, mul_one, norm_mul, norm_neg, norm_div ((x : ℂ) ^ s) s,
      Complex.norm_cpow_eq_rpow_re_of_pos hx0, hsre, Real.rpow_def_of_pos hx0,
      mul_comm (Real.log x) (-U)]
    have he := Real.exp_pos (-U * Real.log x)
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have h1 : Real.exp (-U * Real.log x) / ‖s‖ ≤ Real.exp (-U * Real.log x) :=
      div_le_self he.le hns1
    have hK₀0 : 0 ≤ K₀ := (norm_nonneg _).trans (hK₀ χ 2 (by simp))
    have hA : ‖deriv (LFunction χ) s / LFunction χ s‖ ≤
        Real.log q + T + 2 + (7 + abs Cd + K₀) + U := by
      linarith [Real.log_nonneg hq1, abs_nonneg Cd, hbd, hlg]
    have hA0 : 0 ≤ Real.log q + T + 2 + (7 + abs Cd + K₀) + U := by
      linarith [Real.log_nonneg hq1, abs_nonneg Cd]
    exact mul_le_mul hA h1 (by positivity) hA0
  have e2 : abs (-T - T) = 2 * T := by rw [abs_of_neg (by linarith)]; ring
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans (le_of_eq ?_)
  rw [e2]

private lemma tendsto_vertical_bound (W T ℓ a : ℝ) (hℓ : 0 < ℓ) :
    Filter.Tendsto (fun M : ℕ => (W + (2 * M + 1 - a)) * Real.exp (-(2 * M + 1 - a) * ℓ) *
      (2 * T)) Filter.atTop (𝓝 0) := by
  have hu : Filter.Tendsto (fun M : ℕ => (2 * (M : ℝ) + 1 - a) * ℓ) Filter.atTop
      Filter.atTop := by
    refine Filter.Tendsto.atTop_mul_const hℓ ?_
    refine Filter.tendsto_atTop_add_const_right _ _ ?_
    refine Filter.tendsto_atTop_add_const_right _ _ ?_
    exact Filter.Tendsto.const_mul_atTop two_pos tendsto_natCast_atTop_atTop
  have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hu
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hu
  have hlim := ((h0.const_mul W).add (h1.const_mul (1 / ℓ))).mul_const (2 * T)
  simp only [mul_zero, add_zero, zero_mul] at hlim
  refine hlim.congr fun M => ?_
  simp only [Function.comp, pow_zero, pow_one, one_mul]
  have : -(2 * (M : ℝ) + 1 - a) * ℓ = -((2 * (M : ℝ) + 1 - a) * ℓ) := by ring
  rw [this]
  field_simp

private lemma log_bounds (q x R : ℝ) (hq : 1 ≤ q) (hx : 3 / 2 ≤ x) (hR : 2 ≤ R) :
    1 ≤ Real.log (q * x * R) ∧ Real.log x ≤ Real.log (q * x * R) ∧
      Real.log q ≤ Real.log (q * x * R) ∧
      Real.log (q * (R + 3)) ≤ 2 * Real.log (q * x * R) := by
  have hx0 : 0 < x := by linarith
  have hqR : 1 ≤ q * R := by nlinarith
  have hqxR : 3 ≤ q * x * R := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  · apply Real.log_le_log hx0
    have : x ≤ x * (q * R) := le_mul_of_one_le_right hx0.le hqR
    linarith [show q * x * R = x * (q * R) by ring]
  · apply Real.log_le_log (by positivity)
    have : q ≤ q * (x * R) := le_mul_of_one_le_right (by positivity) (by nlinarith)
    linarith [show q * x * R = q * (x * R) by ring]
  · have h1 : q * (R + 3) ≤ (q * x * R) * (5 / 3) := by nlinarith
    have h2 : Real.log (q * (R + 3)) ≤ Real.log (q * x * R) + Real.log (5 / 3) := by
      rw [← Real.log_mul (by positivity) (by norm_num)]
      exact Real.log_le_log (by positivity) h1
    have h3 : Real.log (5 / 3 : ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 / 3 by norm_num)
      linarith
    have h4 : 1 ≤ Real.log (q * x * R) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have := Real.exp_one_lt_d9
      linarith
    linarith

private lemma phi_le (lq lT K₁ K₀ c B Kg ℒ : ℝ) (hℒ1 : 1 ≤ ℒ) (hlq : lq ≤ ℒ)
    (hlT : lT ≤ 2 * ℒ) (hK₁ : 0 ≤ K₁) (hK₀ : 0 ≤ K₀) (hc : c ≤ 4) (hB : B ≤ 4 * |Kg| * ℒ ^ 2) :
    lq + lT + K₁ + 2 * c + B + K₀ ≤ (11 + K₁ + K₀ + 4 * |Kg|) * ℒ ^ 2 := by
  have hℒ2 : ℒ ≤ ℒ ^ 2 := by nlinarith
  have e1 : K₁ ≤ K₁ * ℒ ^ 2 := le_mul_of_one_le_right hK₁ (by nlinarith)
  have e2 : K₀ ≤ K₀ * ℒ ^ 2 := le_mul_of_one_le_right hK₀ (by nlinarith)
  have e3 : (8 : ℝ) ≤ 8 * ℒ ^ 2 := by nlinarith
  nlinarith

private lemma norm_sub_le_of_rectangle (ψ P H₁ V H₂ ST SR Pm Sinf Bc Ac : ℂ) (e₁ Hb v e₃ : ℝ)
    (hrect : (1 / (2 * Real.pi * I)) * (P + H₁ + V + H₂) = -ST - Bc - Ac + Pm)
    (hP : ‖ψ - (1 / (2 * Real.pi * I)) * P‖ ≤ e₁) (h1 : ‖H₁‖ ≤ Hb) (h2 : ‖H₂‖ ≤ Hb)
    (h3 : ‖V‖ ≤ v) (hZ : ‖ST - SR‖ ≤ e₃) :
    ‖ψ - (-SR - Bc - Ac + Sinf)‖ ≤ e₁ + 2 * Hb + e₃ + v + ‖Pm - Sinf‖ := by
  have hid : ψ - (-SR - Bc - Ac + Sinf) =
      (ψ - (1 / (2 * Real.pi * I)) * P) -
        (1 / (2 * Real.pi * I)) * (H₁ + V + H₂) + (Pm - Sinf) - (ST - SR) := by
    have h2 : (1 / (2 * Real.pi * I)) * P =
        -ST - Bc - Ac + Pm - (1 / (2 * Real.pi * I)) * (H₁ + V + H₂) := by
      rw [← hrect]; ring
    rw [h2]; ring
  have hnk : ‖(1 / (2 * Real.pi * I) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Complex.norm_two, Real.norm_of_nonneg Real.pi_pos.le]
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hW3 : ‖(1 / (2 * Real.pi * I)) * (H₁ + V + H₂)‖ ≤ ‖H₁‖ + ‖V‖ + ‖H₂‖ := by
    rw [norm_mul]
    have := norm_add₃_le (a := H₁) (b := V) (c := H₂)
    have := mul_le_mul_of_nonneg_right hnk (norm_nonneg (H₁ + V + H₂))
    linarith
  rw [hid]
  have t1 := norm_sub_le ((ψ - (1 / (2 * Real.pi * I)) * P) -
    (1 / (2 * Real.pi * I)) * (H₁ + V + H₂) + (Pm - Sinf)) (ST - SR)
  have t2 := norm_add_le ((ψ - (1 / (2 * Real.pi * I)) * P) -
    (1 / (2 * Real.pi * I)) * (H₁ + V + H₂)) (Pm - Sinf)
  have t3 := norm_sub_le (ψ - (1 / (2 * Real.pi * I)) * P)
    ((1 / (2 * Real.pi * I)) * (H₁ + V + H₂))
  linarith

private lemma final_bound (Cp C₁ Kφ Φ x ℓ T R ℒ lR xc : ℝ) (hx0 : 0 < x) (hR : 2 ≤ R)
    (hT1 : R ≤ T) (hℓ : 0 < ℓ) (hℓ3 : 1 / ℓ ≤ 3) (hlx : ℓ ≤ ℒ) (hℒ1 : 1 ≤ ℒ)
    (hlR : lR ≤ 2 * ℒ) (hΦ0 : 0 ≤ Φ) (hΦK : Φ ≤ Kφ * ℒ ^ 2) (hexp : xc ≤ 3 * x) :
    Cp * (x * ℓ ^ 2 / T) + 2 * (xc * (Φ / ℓ + 1 / ℓ ^ 2) / T) + 2 * (|C₁| * lR) * (x / R) ≤
      (|Cp| + 6 * (3 * Kφ + 9) + 4 * |C₁|) * (x * ℒ ^ 2 / R) := by
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = x * ℒ ^ 2 / R := ⟨_, rfl⟩
  rw [← hQ]
  have hRpos : 0 < R := by linarith
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have hxT : x / T ≤ x / R := div_le_div_of_nonneg_left hx0.le hRpos hT1
  have e1 : Cp * (x * ℓ ^ 2 / T) ≤ |Cp| * Q := by
    have h1 : x * ℓ ^ 2 / T ≤ Q := by
      rw [hQ]
      have : ℓ ^ 2 ≤ ℒ ^ 2 := pow_le_pow_left₀ hℓ.le hlx 2
      calc x * ℓ ^ 2 / T = ℓ ^ 2 * (x / T) := by ring
        _ ≤ ℒ ^ 2 * (x / R) := mul_le_mul this hxT (div_nonneg hx0.le (by linarith))
            (sq_nonneg _)
        _ = x * ℒ ^ 2 / R := by ring
    have hT0 : 0 < T := by linarith
    calc Cp * (x * ℓ ^ 2 / T) ≤ |Cp| * (x * ℓ ^ 2 / T) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |Cp| * Q := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have e2 : xc * (Φ / ℓ + 1 / ℓ ^ 2) / T ≤ 3 * (3 * Kφ + 9) * Q := by
    have hin : Φ / ℓ + 1 / ℓ ^ 2 ≤ 3 * Φ + 9 := by
      have h1 : Φ / ℓ ≤ 3 * Φ := by
        rw [div_eq_mul_one_div]
        calc Φ * (1 / ℓ) ≤ Φ * 3 := mul_le_mul_of_nonneg_left hℓ3 hΦ0
          _ = 3 * Φ := by ring
      have h2 : 1 / ℓ ^ 2 ≤ 9 := by
        rw [show 1 / ℓ ^ 2 = (1 / ℓ) ^ 2 by ring]
        have := one_div_pos.mpr hℓ
        nlinarith
      linarith
    have hin0 : 0 ≤ Φ / ℓ + 1 / ℓ ^ 2 := by positivity
    have h3 : 3 * Φ + 9 ≤ (3 * Kφ + 9) * ℒ ^ 2 := by nlinarith
    have hT0 : 0 < T := by linarith
    calc xc * (Φ / ℓ + 1 / ℓ ^ 2) / T = xc * (Φ / ℓ + 1 / ℓ ^ 2) * (1 / T) := by ring
      _ ≤ (3 * x) * ((3 * Kφ + 9) * ℒ ^ 2) * (1 / R) := by
          apply mul_le_mul (mul_le_mul hexp (hin.trans h3) hin0 (by linarith))
            (one_div_le_one_div_of_le hRpos hT1) (one_div_pos.mpr hT0).le
            (mul_nonneg (by linarith) (le_trans (by linarith) h3))
      _ = 3 * (3 * Kφ + 9) * Q := by rw [hQ]; ring
  have e3 : 2 * (|C₁| * lR) * (x / R) ≤ 4 * |C₁| * Q := by
    rw [hQ]
    have hℒ2 : ℒ ≤ ℒ ^ 2 := by nlinarith
    have : |C₁| * lR ≤ |C₁| * (2 * ℒ ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    calc 2 * (|C₁| * lR) * (x / R) ≤ 2 * (|C₁| * (2 * ℒ ^ 2)) * (x / R) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 4 * |C₁| * (x * ℒ ^ 2 / R) := by ring
  linarith


/-! ### The explicit formula at one height -/

/-- **The explicit formula at one height**, with the Perron integral left in. For `x > 1`,
`c > 1` and a height `T ≥ 2` that is not the absolute value of the ordinate of a zero, at which
`‖L'/L(σ ± iT, χ)‖ ≤ B` for `-1 ≤ σ ≤ 2`, the explicit formula truncated at `T` differs from
`ψ(x, χ)` by at most the error of the truncated Perron integral on `Re s = c` plus twice the
bound `x^c (Φ / log x + 1 / log² x) / T` for a horizontal side of the rectangle. -/
private lemma norm_chebyshevPsi_sub_le_of_height (Cd : ℝ)
    (hCd : ∀ v : ℂ, 0 < v.re → 1 ≤ ‖v‖ → ‖Complex.digamma v‖ ≤ Real.log ‖v‖ + Cd) (K₀ : ℝ)
    (hK₀0 : 0 ≤ K₀)
    (hK₀ : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 2 ≤ s.re →
      ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ K₀)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {a : ℝ}
    (ha : a = 0 ∨ a = 1) (hapar : (1 - χ (-1)) / 2 = (a : ℂ))
    (hgf : ∀ w, χ.gammaFactor w = Complex.Gammaℝ (w + a))
    (hgf' : ∀ w, χ⁻¹.gammaFactor w = Complex.Gammaℝ (w + a))
    {ι : Type u} (z : ι → ℂ) (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w)
    {x : ℝ} (hx : 1 < x) {c : ℝ} (hc : 1 < c) {T : ℝ} (hT : 2 ≤ T)
    (hTz : ∀ n, |(z n).im| ≠ T) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
      ‖deriv (LFunction χ) ((σ : ℂ) + T * I) / LFunction χ ((σ : ℂ) + T * I)‖ ≤ B ∧
      ‖deriv (LFunction χ) ((σ : ℂ) - T * I) / LFunction χ ((σ : ℂ) - T * I)‖ ≤ B) :
    ‖χ.chebyshevPsi x -
        (-(∑' n, (if |(z n).im| < T then (x : ℂ) ^ z n / z n else 0))
          - (1 - (a : ℂ)) * ((Real.log x : ℂ) + χ.logDerivConstAtZero)
          - (a : ℂ) * (deriv (LFunction χ) 0 / LFunction χ 0)
          + ∑' m : ℕ, (x : ℂ) ^ ((a : ℂ) - 2 * ((m : ℂ) + 1)) /
              (2 * ((m : ℂ) + 1) - (a : ℂ)))‖ ≤
      ‖χ.chebyshevPsi x - (1 / (2 * Real.pi)) * ∫ t in (-T)..T,
          -(deriv (LFunction χ) (c + t * I) / LFunction χ (c + t * I)) *
            ((x : ℂ) ^ (c + t * I) / (c + t * I))‖ +
        2 * (x ^ c * ((Real.log q + Real.log (T + 2) + (7 + |Cd| + K₀) + 2 * c + B + K₀) /
          Real.log x + 1 / Real.log x ^ 2) / T) := by
  classical
  have ha0 : 0 ≤ a := by rcases ha with h | h <;> simp [h]
  have ha1 : a ≤ 1 := by rcases ha with h | h <;> simp [h]
  have hℓ : 0 < Real.log x := Real.log_pos hx
  have hTpos : 0 < T := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set e₁ : ℝ := ‖χ.chebyshevPsi x - (1 / (2 * Real.pi)) * ∫ t in (-T)..T,
      -(deriv (LFunction χ) (c + t * I) / LFunction χ (c + t * I)) *
        ((x : ℂ) ^ (c + t * I) / (c + t * I))‖ with he₁
  obtain ⟨F, hF⟩ : ∃ F : ℂ → ℂ, F = fun s => -(deriv (LFunction χ) s /
      LFunction χ s) * ((x : ℂ) ^ s / s) := ⟨_, rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ,
      Φ = Real.log q + Real.log (T + 2) + (7 + |Cd| + K₀) + 2 * c + B + K₀ := ⟨_, rfl⟩
  rw [← hΦ]
  have hΦ0 : 0 ≤ Φ := by
    have := Real.log_nonneg hq1
    have := Real.log_nonneg (show (1 : ℝ) ≤ T + 2 by linarith)
    rw [hΦ]
    linarith [abs_nonneg Cd]
  obtain ⟨Hb, hHb⟩ : ∃ Hb : ℝ, Hb = x ^ c * (Φ / Real.log x + 1 / Real.log x ^ 2) / T :=
    ⟨_, rfl⟩
  rw [← hHb]
  -- the horizontal sides
  have hptw : ∀ y : ℝ, |y| = T → (∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
      ‖deriv (LFunction χ) ((σ : ℂ) + y * I) / LFunction χ ((σ : ℂ) + y * I)‖ ≤ B) →
      ∀ U : ℝ, 0 ≤ U → ‖∫ σ in (-U)..c, F ((σ : ℂ) + y * I)‖ ≤ Hb := by
    intro y hy hBy U hU
    rw [hHb]
    refine norm_intervalIntegral_le_of_norm_le_sub_mul_rpow hx hTpos zero_le_one (by linarith)
      (by linarith) (by linarith) fun σ hσ => ?_
    rw [one_mul, hF, hΦ]
    exact norm_integrand_le_of_abs_im_eq Cd hCd K₀ hK₀0 hK₀ χ hχ a hgf hgf' ha0 ha1 x hx c hc.le
      T y B hT hy hB0 hBy σ hσ.2
  have hemT : ∀ σ : ℝ, (σ : ℂ) - T * I = (σ : ℂ) + ((-T : ℝ) : ℂ) * I := by
    intro σ; push_cast; ring
  have hBT' : ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
      ‖deriv (LFunction χ) ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) /
        LFunction χ ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ B := by
    intro σ h1 h2
    rw [← hemT]
    exact (hB σ h1 h2).2
  have hTabs : |T| = T := abs_of_pos hTpos
  have hH1 : ∀ M : ℕ, 1 ≤ M →
      ‖∫ σ in c..(-(2 * M + 1 - a : ℝ)), F ((σ : ℂ) + T * I)‖ ≤ Hb := by
    intro M hM
    have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
    rw [intervalIntegral.integral_symm, norm_neg]
    exact hptw T hTabs (fun σ h1 h2 => (hB σ h1 h2).1) _ (by linarith)
  have hH2 : ∀ M : ℕ, 1 ≤ M →
      ‖∫ σ in (-(2 * M + 1 - a : ℝ))..c, F ((σ : ℂ) - T * I)‖ ≤ Hb := by
    intro M hM
    have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
    simp only [hemT]
    exact hptw (-T) (by rw [abs_neg, hTabs]) hBT' _ (by linarith)
  -- the left side
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = Real.log q + T + 2 + (7 + |Cd| + K₀) := ⟨_, rfl⟩
  have hV : ∀ M : ℕ, 1 ≤ M →
      ‖∫ t in T..(-T), F (-((2 * M + 1 - a : ℝ) : ℂ) + t * I) * I‖ ≤
        (W + (2 * M + 1 - a)) * Real.exp (-(2 * M + 1 - a) * Real.log x) * (2 * T) := by
    intro M hM
    simp only [hF]
    rw [hW]
    exact norm_integral_vertical_le Cd hCd K₀ hK₀ χ hχ a ha hgf hgf' x hx T hTpos M hM
  have hVt := tendsto_vertical_bound W T (Real.log x) a hℓ
  -- the right side
  have hPeq : (1 / (2 * Real.pi * I)) * ∫ t in (-T)..T, F ((c : ℂ) + t * I) * I =
      (1 / (2 * Real.pi)) * ∫ t in (-T)..T,
        -(deriv (LFunction χ) (c + t * I) / LFunction χ (c + t * I)) *
          ((x : ℂ) ^ (c + t * I) / (c + t * I)) := by
    rw [intervalIntegral.integral_mul_const]
    simp only [hF]
    have hI : I ≠ 0 := Complex.I_ne_zero
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hX : ∀ X : ℂ, 1 / (2 * Real.pi * I) * (X * I) = 1 / (2 * (Real.pi : ℂ)) * X := by
      intro X; field_simp
    exact hX _
  have hP : ‖χ.chebyshevPsi x -
      (1 / (2 * Real.pi * I)) * ∫ t in (-T)..T, F ((c : ℂ) + t * I) * I‖ ≤ e₁ := by
    rw [hPeq]
  -- the trivial zeros
  have hS := tendsto_sum_cpow_sub_two_mul_div_two_mul_sub hx ha1
  -- the estimate for each `M`
  have hstep : ∀ M : ℕ, 1 ≤ M →
      ‖χ.chebyshevPsi x -
          (-(∑' n, (if |(z n).im| < T then (x : ℂ) ^ z n / z n else 0))
            - (1 - (a : ℂ)) * ((Real.log x : ℂ) + χ.logDerivConstAtZero)
            - (a : ℂ) * (deriv (LFunction χ) 0 / LFunction χ 0)
            + ∑' m : ℕ, (x : ℂ) ^ ((a : ℂ) - 2 * ((m : ℂ) + 1)) /
                (2 * ((m : ℂ) + 1) - (a : ℂ)))‖ ≤
        e₁ + 2 * Hb + 0 +
          (W + (2 * M + 1 - a)) * Real.exp (-(2 * M + 1 - a) * Real.log x) * (2 * T) +
          ‖(∑ m ∈ Finset.Icc 1 M, (x : ℂ) ^ ((a : ℂ) - 2 * m) / (2 * m - (a : ℂ))) -
            ∑' m : ℕ, (x : ℂ) ^ ((a : ℂ) - 2 * ((m : ℂ) + 1)) / (2 * ((m : ℂ) + 1) - a)‖ := by
    intro M hM
    have hrect := integral_rectangle_neg_logDeriv_LFunction_mul_cpow_div hχ hχ1 ha hapar hgf z hz
      hx hM hTpos hTz hc rfl hF
    exact norm_sub_le_of_rectangle _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrect hP (hH1 M hM) (hH2 M hM)
      (hV M hM) (by rw [sub_self, norm_zero])
  -- the limit `M → ∞`
  have hlim := (hVt.const_add (e₁ + 2 * Hb + 0)).add (tendsto_iff_norm_sub_tendsto_zero.mp hS)
  have hmain := ge_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨1, hstep⟩)
  simpa only [add_zero] using hmain

/-! ### The truncated explicit formula -/

/-- **The truncated explicit formula for `ψ(x, χ)`.** There is an absolute constant `C` such that
for every primitive Dirichlet character `χ ≠ 1` modulo `q`, with parity `a = (1 - χ(-1))/2`, every
family `z` listing the zeros of `ξ(s, χ)` with multiplicity (the nontrivial zeros `ρ = β + iγ` of
`L(s, χ)`), every `x` with `x - 1/2` a positive integer and every `R ≥ 2`,
`ψ(x, χ) = -∑_{|γ| < R} x^ρ/ρ - (1 - a)(log x + b(χ)) - a L'(0, χ)/L(0, χ)
  + ∑_{m ≥ 1} x^{a - 2m}/(2m - a) + O(x log² (q x R) / R)`,
with `b(χ) = DirichletCharacter.logDerivConstAtZero χ`. The term `-a L'(0, χ)/L(0, χ)` is the
residue at `s = 0` for odd `χ`. -/
theorem exists_truncated_explicit_formula_chebyshevPsi :
    ∃ C : ℝ, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∀ {ι : Type u} (z : ι → ℂ),
        (∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w) →
        ∀ x : ℝ, (∃ n : ℕ, 0 < n ∧ x = n + 1 / 2) →
        ∀ R : ℝ, 2 ≤ R →
          ‖χ.chebyshevPsi x -
              (-(∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0))
                - (1 - (1 - χ (-1)) / 2) * ((Real.log x : ℂ) + χ.logDerivConstAtZero)
                - (1 - χ (-1)) / 2 * (deriv (LFunction χ) 0 / LFunction χ 0)
                + ∑' m : ℕ, (x : ℂ) ^ ((1 - χ (-1)) / 2 - 2 * ((m : ℂ) + 1)) /
                    (2 * ((m : ℂ) + 1) - (1 - χ (-1)) / 2))‖
            ≤ C * (x * Real.log (q * x * R) ^ 2 / R) := by
  classical
  obtain ⟨Cd, hCd⟩ := Complex.exists_norm_digamma_le_log_add
  obtain ⟨K₀, hK₀0, hK₀⟩ := exists_norm_logDeriv_LFunction_le_of_two_le_re
  obtain ⟨Kg, hKg⟩ := exists_good_height_norm_logDeriv_LFunction_le.{u}
  obtain ⟨Cp, hCp⟩ := exists_norm_chebyshevPsi_sub_truncated_integral_le_log_sq
  obtain ⟨C₁, hC₁⟩ := exists_card_le_log_of_abs_sub_im_lt.{u}
  refine ⟨|Cp| + 6 * (3 * (11 + (7 + |Cd| + K₀) + K₀ + 4 * |Kg|) + 9) + 4 * |C₁|, ?_⟩
  intro q _ χ hχ hχ1 ι z hz x hxn R hR
  obtain ⟨a, ha, hapar, hgf, hgf'⟩ := exists_parity_gammaFactor_eq χ
  rw [hapar]
  -- facts about `x`
  obtain ⟨n₀, hn₀, hxn₀⟩ := hxn
  have hx32 : 3 / 2 ≤ x := by
    have : (1 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
    rw [hxn₀]; linarith
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hℓ : 0 < Real.log x := Real.log_pos hx1
  have hℓ3 : 1 / Real.log x ≤ 3 := one_div_log_le_three hx32
  have hc4 : 1 + 1 / Real.log x ≤ 4 := by linarith
  have hc0 : 0 < 1 / Real.log x := one_div_pos.mpr hℓ
  have hc1 : 1 < 1 + 1 / Real.log x := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  obtain ⟨hℒ1, hlx, hlq, hlR⟩ := log_bounds q x R hq1 hx32 hR
  have hlR0 : 0 ≤ Real.log (q * (R + 3)) := Real.log_nonneg (by nlinarith)
  -- the good height
  obtain ⟨T, hT1, hT2, hTz, hTb⟩ := hKg χ hχ z hz R hR
  have hTpos : 0 < T := by linarith
  have hT2' : 2 ≤ T := by linarith
  obtain ⟨B, hB⟩ : ∃ B, B = |Kg| * Real.log (q * (R + 3)) ^ 2 := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hKgB : Kg * Real.log (q * (R + 3)) ^ 2 ≤ B := by
    rw [hB]; exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have hB4 : B ≤ 4 * |Kg| * Real.log (q * x * R) ^ 2 := by
    rw [hB]
    have : Real.log (q * (R + 3)) ^ 2 ≤ (2 * Real.log (q * x * R)) ^ 2 :=
      pow_le_pow_left₀ hlR0 hlR 2
    have h4 := mul_le_mul_of_nonneg_left this (abs_nonneg Kg)
    linarith
  -- the explicit formula at height `T`
  have hstep := norm_chebyshevPsi_sub_le_of_height Cd hCd K₀ hK₀0 hK₀ hχ hχ1 ha hapar hgf hgf'
    z hz hx1 hc1 hT2' hTz hB0
    (fun σ h1 h2 => ⟨(hTb σ h1 h2).1.trans hKgB, (hTb σ h1 h2).2.trans hKgB⟩)
  -- Perron
  have hP := hCp χ x T ⟨n₀, hn₀, hxn₀⟩ hTpos
  -- the zeros between `R` and `T`
  have hZd := norm_tsum_cpow_div_sub_tsum_cpow_div_le hχ hχ1 z hz hx1 hR hT1 hT2 (hC₁ χ hχ z hz)
  -- the size of the horizontal sides
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ, Φ = Real.log q + Real.log (T + 2) + (7 + |Cd| + K₀) +
      2 * (1 + 1 / Real.log x) + B + K₀ := ⟨_, rfl⟩
  rw [← hΦ] at hstep
  have hlT : Real.log (T + 2) ≤ 2 * Real.log (q * x * R) := by
    refine (Real.log_le_log (by linarith) ?_).trans hlR
    have : T + 2 ≤ R + 3 := by linarith
    nlinarith
  have hlT0 : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hΦ0 : 0 ≤ Φ := by
    rw [hΦ]; linarith [abs_nonneg Cd]
  have hΦK : Φ ≤ (11 + (7 + |Cd| + K₀) + K₀ + 4 * |Kg|) * Real.log (q * x * R) ^ 2 := by
    rw [hΦ]
    exact phi_le _ _ _ _ _ _ _ _ hℒ1 hlq hlT (by linarith [abs_nonneg Cd]) hK₀0 hc4 hB4
  have hexp : x ^ (1 + 1 / Real.log x) ≤ 3 * x := by
    rw [Real.rpow_add hx0, Real.rpow_one, Real.rpow_def_of_pos hx0,
      mul_one_div_cancel hℓ.ne']
    have := Real.exp_one_lt_d9
    nlinarith
  -- moving from `T` to `R`
  set SR := ∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0) with hSR
  set ST := ∑' n, (if |(z n).im| < T then (x : ℂ) ^ z n / z n else 0) with hST
  set Bc := (1 - (a : ℂ)) * ((Real.log x : ℂ) + χ.logDerivConstAtZero) with hBc
  set Ac := (a : ℂ) * (deriv (LFunction χ) 0 / LFunction χ 0) with hAc
  set Sinf := ∑' m : ℕ, (x : ℂ) ^ ((a : ℂ) - 2 * ((m : ℂ) + 1)) /
    (2 * ((m : ℂ) + 1) - (a : ℂ)) with hSinf
  have hid : χ.chebyshevPsi x - (-SR - Bc - Ac + Sinf) =
      (χ.chebyshevPsi x - (-ST - Bc - Ac + Sinf)) - (ST - SR) := by ring
  rw [hid]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add (hstep.trans (add_le_add hP le_rfl)) hZd).trans ?_
  exact final_bound Cp C₁ _ Φ x (Real.log x) T R (Real.log (q * x * R)) _ _ hx0 hR hT1 hℓ hℓ3
    hlx hℒ1 hlR hΦ0 hΦK hexp

/-- Zeros whose ordinate has integer part `k` number at most `2 |C₁| log (q (k + 3))`. -/
private lemma card_le_of_floor_abs_im_eq {q : ℕ} [NeZero q] {ι : Type u} (z : ι → ℂ) (C₁ : ℝ)
    (hC₁ : ∀ t : ℝ, ∀ F : Finset ι, (∀ n ∈ F, |t - (z n).im| < 1) →
      (F.card : ℝ) ≤ C₁ * Real.log (q * (|t| + 2)))
    (k : ℕ) (D : Finset ι) (hD : ∀ n ∈ D, ⌊|(z n).im|⌋₊ = k) :
    (D.card : ℝ) ≤ 2 * (|C₁| * Real.log (q * (k + 3))) := by
  classical
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hwin : ∀ n ∈ D, (k : ℝ) ≤ |(z n).im| ∧ |(z n).im| < k + 1 := by
    intro n hn
    have h := (Nat.floor_eq_iff (abs_nonneg _)).mp (hD n hn)
    exact h
  set t₀ : ℝ := k + 1 / 2 with ht₀
  have hlog : Real.log (q * (|t₀| + 2)) ≤ Real.log (q * (k + 3)) := by
    rw [abs_of_pos (by linarith)]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hlog' : Real.log (q * (|-t₀| + 2)) ≤ Real.log (q * (k + 3)) := by rwa [abs_neg]
  have hlog0 : 0 ≤ Real.log (q * (|t₀| + 2)) := Real.log_nonneg (by nlinarith [abs_nonneg t₀])
  have hlog0' : 0 ≤ Real.log (q * (|-t₀| + 2)) :=
    Real.log_nonneg (by nlinarith [abs_nonneg (-t₀)])
  have hDP := hC₁ t₀ (D.filter (fun n => 0 ≤ (z n).im)) (by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨h1, h2⟩ := hwin n hn.1
    rw [abs_of_nonneg hn.2] at h1 h2
    rw [abs_lt]; constructor <;> linarith)
  have hDM := hC₁ (-t₀) (D.filter (fun n => ¬ 0 ≤ (z n).im)) (by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨h1, h2⟩ := hwin n hn.1
    rw [abs_of_neg (not_le.mp hn.2)] at h1 h2
    rw [abs_lt]; constructor <;> linarith)
  have hcard := Finset.card_filter_add_card_filter_not (s := D) (fun n => 0 ≤ (z n).im)
  have hc1 : C₁ * Real.log (q * (|t₀| + 2)) ≤ |C₁| * Real.log (q * (k + 3)) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hlog0).trans
      (mul_le_mul_of_nonneg_left hlog (abs_nonneg _))
  have hc2 : C₁ * Real.log (q * (|-t₀| + 2)) ≤ |C₁| * Real.log (q * (k + 3)) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hlog0').trans
      (mul_le_mul_of_nonneg_left hlog' (abs_nonneg _))
  have : (D.card : ℝ) = (D.filter (fun n => 0 ≤ (z n).im)).card +
      (D.filter (fun n => ¬ 0 ≤ (z n).im)).card := by exact_mod_cast hcard.symm
  linarith

/-- Under GRH, `∑_{|γ| < R} 1/|ρ| ≤ 4 |C₁| log (q (⌈R⌉ + 2)) (1 + log ⌈R⌉)`. -/
private lemma sum_one_div_norm_le_of_re_eq_half {q : ℕ} [NeZero q] {ι : Type u} (z : ι → ℂ) (C₁ : ℝ)
    (hC₁ : ∀ t : ℝ, ∀ F : Finset ι, (∀ n ∈ F, |t - (z n).im| < 1) →
      (F.card : ℝ) ≤ C₁ * Real.log (q * (|t| + 2)))
    (hre : ∀ n, (z n).re = 1 / 2) (R : ℝ) (N : Finset ι) (hN : ∀ n ∈ N, |(z n).im| < R) :
    ∑ n ∈ N, 1 / ‖z n‖ ≤
      4 * (|C₁| * Real.log (q * ((⌈R⌉₊ : ℝ) + 2))) * (1 + Real.log ⌈R⌉₊) := by
  classical
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set K := ⌈R⌉₊ with hK
  have hmaps : ∀ n ∈ N, (fun n => ⌊|(z n).im|⌋₊) n ∈ Finset.range K := by
    intro n hn
    simp only [Finset.mem_range]
    have h1 := hN n hn
    have h2 : R ≤ (K : ℝ) := Nat.le_ceil R
    exact Nat.floor_lt (abs_nonneg _) |>.mpr (by linarith)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  set ℓ := |C₁| * Real.log (q * ((K : ℝ) + 2)) with hℓ
  have hfib : ∀ k ∈ Finset.range K,
      ∑ n ∈ N with ⌊|(z n).im|⌋₊ = k, 1 / ‖z n‖ ≤ 4 * ℓ * (1 / ((k : ℝ) + 1)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hkK : (k : ℝ) + 3 ≤ (K : ℝ) + 2 := by
      have : (k : ℝ) + 1 ≤ K := by exact_mod_cast hk
      linarith
    have hterm : ∀ n ∈ N.filter (fun n => ⌊|(z n).im|⌋₊ = k),
        1 / ‖z n‖ ≤ 2 * (1 / ((k : ℝ) + 1)) := by
      intro n hn
      rw [Finset.mem_filter] at hn
      have hw := (Nat.floor_eq_iff (abs_nonneg _)).mp hn.2
      have h1 : (k : ℝ) ≤ ‖z n‖ := hw.1.trans (Complex.abs_im_le_norm _)
      have h2 : (1 / 2 : ℝ) ≤ ‖z n‖ := by
        have := Complex.abs_re_le_norm (z n)
        rw [hre n] at this
        norm_num at this ⊢
        linarith
      have h3 : ((k : ℝ) + 1) / 2 ≤ ‖z n‖ := by
        rcases Nat.eq_zero_or_pos k with h | h
        · rw [h]; norm_num; linarith
        · have : (1 : ℝ) ≤ k := by exact_mod_cast h
          linarith
      calc 1 / ‖z n‖ ≤ 1 / (((k : ℝ) + 1) / 2) := one_div_le_one_div_of_le (by positivity) h3
        _ = 2 * (1 / ((k : ℝ) + 1)) := by field_simp
    have hcard := card_le_of_floor_abs_im_eq z C₁ hC₁ k (N.filter fun n => ⌊|(z n).im|⌋₊ = k)
      (fun n hn => (Finset.mem_filter.mp hn).2)
    have hlog : |C₁| * Real.log (q * (k + 3)) ≤ ℓ :=
      mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by nlinarith)) (abs_nonneg _)
    calc ∑ n ∈ N with ⌊|(z n).im|⌋₊ = k, 1 / ‖z n‖
        ≤ ∑ n ∈ N with ⌊|(z n).im|⌋₊ = k, 2 * (1 / ((k : ℝ) + 1)) := Finset.sum_le_sum hterm
      _ = ((N.filter fun n => ⌊|(z n).im|⌋₊ = k).card : ℝ) * (2 * (1 / ((k : ℝ) + 1))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * ℓ) * (2 * (1 / ((k : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 4 * ℓ * (1 / ((k : ℝ) + 1)) := by ring
  refine (Finset.sum_le_sum hfib).trans ?_
  rw [← Finset.mul_sum]
  have hℓ0 : 0 ≤ ℓ := mul_nonneg (abs_nonneg _) (Real.log_nonneg (by nlinarith))
  have hH : ∑ k ∈ Finset.range K, 1 / ((k : ℝ) + 1) ≤ 1 + Real.log K := by
    have := harmonic_le_one_add_log K
    have he : ((harmonic K : ℚ) : ℝ) = ∑ k ∈ Finset.range K, 1 / ((k : ℝ) + 1) := by
      simp [harmonic, one_div]
    linarith
  exact mul_le_mul_of_nonneg_left hH (by positivity)

/-- Under GRH, `‖∑_{|γ| < R} y^ρ/ρ‖ ≤ √y ∑_{|γ| < R} 1/|ρ|`. -/
private lemma norm_tsum_cpow_div_le_of_re_eq_half {ι : Type u} (z : ι → ℂ)
    (hre : ∀ n, (z n).re = 1 / 2) (R y : ℝ)
    (hy : 0 < y) (N : Finset ι) (hN : ∀ n, n ∈ N ↔ |(z n).im| < R) :
    ‖∑' n, (if |(z n).im| < R then (y : ℂ) ^ z n / z n else 0)‖ ≤
      Real.sqrt y * ∑ n ∈ N, 1 / ‖z n‖ := by
  rw [tsum_eq_sum (s := N) (fun n hn => ite_eq_right (by rwa [hN] at hn))]
  rw [Finset.sum_congr rfl (fun n hn => ite_eq_left ((hN n).mp hn)), Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy, hre n, Real.sqrt_eq_rpow]
  rw [div_eq_mul_one_div]

/-- The trivial-zero series is bounded by `2` for `y ≥ 3/2`. -/
private lemma norm_tsum_trivial_zeros_le (y : ℝ) (hy : 3 / 2 ≤ y) (A : ℂ) (hA : A = 0 ∨ A = 1) :
    ‖∑' m : ℕ, (y : ℂ) ^ (A - 2 * ((m : ℂ) + 1)) / (2 * ((m : ℂ) + 1) - A)‖ ≤ 2 := by
  have hy0 : 0 < y := by linarith
  obtain ⟨a, ha0, ha1, rfl⟩ : ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ A = (a : ℂ) := by
    rcases hA with h | h
    · exact ⟨0, le_refl _, zero_le_one, by simp [h]⟩
    · exact ⟨1, zero_le_one, le_refl _, by simp [h]⟩
  refine tsum_of_norm_bounded hasSum_geometric_two fun m => ?_
  have hden : 1 ≤ ‖(2 * ((m : ℂ) + 1) - a)‖ := by
    have h := Complex.re_le_norm (2 * ((m : ℂ) + 1) - a)
    have : (2 * ((m : ℂ) + 1) - a).re = 2 * ((m : ℝ) + 1) - a := by simp
    rw [this] at h
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
  have hre : ((a : ℂ) - 2 * ((m : ℂ) + 1)).re = a - 2 * ((m : ℝ) + 1) := by simp
  rw [hre]
  have hr : y ^ (-2 : ℝ) ≤ 1 / 2 := by
    rw [Real.rpow_neg hy0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  have h1 : y ^ (a - 2 * ((m : ℝ) + 1)) ≤ (y ^ (-2 : ℝ)) ^ m := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  calc y ^ (a - 2 * ((m : ℝ) + 1)) / ‖(2 * ((m : ℂ) + 1) - a)‖
      ≤ y ^ (a - 2 * ((m : ℝ) + 1)) := div_le_self (by positivity) hden
    _ ≤ (y ^ (-2 : ℝ)) ^ m := h1
    _ ≤ (1 / 2) ^ m := pow_le_pow_left₀ (by positivity) hr m

private lemma norm_le_of_two_explicit_formulas (ψ Z1 Z2 A L1 L2 b D S1 S2 : ℂ)
    (e1 e2 z1 z2 l s1 s2 : ℝ)
    (h1 : ‖ψ - (-Z1 - (1 - A) * (L1 + b) - A * D + S1)‖ ≤ e1)
    (h2 : ‖0 - (-Z2 - (1 - A) * (L2 + b) - A * D + S2)‖ ≤ e2)
    (hZ1 : ‖Z1‖ ≤ z1) (hZ2 : ‖Z2‖ ≤ z2) (hl : ‖(1 - A) * (L1 - L2)‖ ≤ l)
    (hS1 : ‖S1‖ ≤ s1) (hS2 : ‖S2‖ ≤ s2) :
    ‖ψ‖ ≤ e1 + e2 + z1 + z2 + l + s1 + s2 := by
  have heq : ψ = (ψ - (-Z1 - (1 - A) * (L1 + b) - A * D + S1)) -
      (0 - (-Z2 - (1 - A) * (L2 + b) - A * D + S2)) - Z1 + Z2 - (1 - A) * (L1 - L2) + S1 - S2 := by
    ring
  rw [heq]
  generalize ψ - (-Z1 - (1 - A) * (L1 + b) - A * D + S1) = u1 at h1 ⊢
  generalize 0 - (-Z2 - (1 - A) * (L2 + b) - A * D + S2) = u2 at h2 ⊢
  generalize (1 - A) * (L1 - L2) = W at hl ⊢
  have t1 := norm_sub_le (u1 - u2 - Z1 + Z2 - W + S1) S2
  have t2 := norm_add_le (u1 - u2 - Z1 + Z2 - W) S1
  have t3 := norm_sub_le (u1 - u2 - Z1 + Z2) W
  have t4 := norm_add_le (u1 - u2 - Z1) Z2
  have t5 := norm_sub_le (u1 - u2) Z1
  have t6 := norm_sub_le u1 u2
  linarith

private lemma final_bound_of_re_eq_half (C₇ C₁ q x x' R K Sig : ℝ) (hq1 : 1 ≤ q) (hx : 2 ≤ x)
    (hx'1 : x - 1 / 2 ≤ x') (hx'2 : x' ≤ x + 1 / 2) (hx'3 : 5 / 2 ≤ x') (hR1 : x' ≤ R)
    (hR2 : R ≤ x' + 1)
    (hK1 : 1 ≤ K) (hKR : K ≤ R + 1)
    (hSig : Sig ≤ 4 * (|C₁| * Real.log (q * (K + 2))) * (1 + Real.log K)) (hSum0 : 0 ≤ Sig) :
    C₇ * (x' * Real.log (q * x' * R) ^ 2 / R) + C₇ * (3 / 2 * Real.log (q * (3 / 2) * R) ^ 2 / R) +
        Real.sqrt x' * Sig + Real.sqrt (3 / 2) * Sig + Real.log x' + 2 + 2 ≤
      (32 * |C₇| + 180 * |C₁| + 20) * Real.sqrt x * Real.log (q * x) ^ 2 := by
  have hK0 : (0 : ℝ) < K := by linarith
  have hlK1 : 0 ≤ 1 + Real.log K := by linarith [Real.log_nonneg hK1]
  have hR2' : 2 ≤ R := by linarith
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (q * x) := ⟨_, rfl⟩
  rw [← hL]
  have hxqx : x ≤ q * x := le_mul_of_one_le_left (by linarith) hq1
  have hqx2 : 2 ≤ q * x := by linarith
  have hL12 : 1 / 2 ≤ L := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ L := hL ▸ Real.log_le_log (by norm_num) hqx2
    linarith
  -- logs of polynomial expressions in `q x`
  have hlogpow : ∀ (k : ℕ) (u : ℝ), 0 < u → u ≤ (q * x) ^ k → Real.log u ≤ k * L := by
    intro k u hu huk
    rw [hL, ← Real.log_pow]
    exact Real.log_le_log hu huk
  have hsx : 1 ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = Real.sqrt x * L ^ 2 := ⟨_, rfl⟩
  have hLP : L ^ 2 ≤ P := by rw [hP]; nlinarith [sq_nonneg L]
  have hP1 : 1 ≤ 4 * P := by nlinarith
  have hx'4 : x' ≤ 4 * x := by linarith
  -- the two error terms
  have hx'0 : 0 < x' := by linarith
  have hqxR : q * x' * R ≤ (q * x) ^ 4 := by
    have h1 : x' ≤ 2 * x := by linarith
    have h2 : R ≤ 2 * x := by linarith
    have h3 : q * x' * R ≤ q * (2 * x) * (2 * x) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 (by linarith)) h2 (by linarith) (by positivity)
    have hy2 : 4 ≤ (q * x) ^ 2 := by nlinarith
    have h4 : 4 * (q * x) ^ 2 ≤ (q * x) ^ 4 := by
      calc 4 * (q * x) ^ 2 ≤ (q * x) ^ 2 * (q * x) ^ 2 :=
            mul_le_mul_of_nonneg_right hy2 (sq_nonneg _)
        _ = (q * x) ^ 4 := by ring
    have h5 : q * (2 * x) * (2 * x) ≤ 4 * (q * x) ^ 2 := by nlinarith
    linarith
  have hlog4 : ∀ u : ℝ, 0 < u → u ≤ (q * x) ^ 4 → Real.log u ≤ 4 * L := by
    intro u hu huq
    calc Real.log u ≤ Real.log ((q * x) ^ 4) := Real.log_le_log hu huq
      _ = 4 * L := by rw [Real.log_pow, hL]; push_cast; ring
  have hl1 : Real.log (q * x' * R) ≤ 4 * L := hlog4 _ (by positivity) hqxR
  have hl1' : 0 ≤ Real.log (q * x' * R) := Real.log_nonneg
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hq1 (by linarith))
      (by linarith))
  have hl2 : Real.log (q * (3 / 2) * R) ≤ 4 * L :=
    hlog4 _ (by positivity)
      ((by gcongr; linarith : q * (3 / 2) * R ≤ q * x' * R).trans hqxR)
  have hl2' : 0 ≤ Real.log (q * (3 / 2) * R) := Real.log_nonneg
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hq1 (by norm_num))
      (by linarith))
  have he1 : C₇ * (x' * Real.log (q * x' * R) ^ 2 / R) ≤ 16 * (|C₇| * P) := by
    have ha : x' * Real.log (q * x' * R) ^ 2 / R ≤ (4 * L) ^ 2 := by
      rw [div_le_iff₀ (by linarith)]
      have : Real.log (q * x' * R) ^ 2 ≤ (4 * L) ^ 2 := pow_le_pow_left₀ hl1' hl1 2
      nlinarith
    have hb : 0 ≤ x' * Real.log (q * x' * R) ^ 2 / R := by
      apply div_nonneg _ (by linarith); have : 0 < x' := by linarith
      positivity
    calc C₇ * (x' * Real.log (q * x' * R) ^ 2 / R)
        ≤ |C₇| * (x' * Real.log (q * x' * R) ^ 2 / R) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hb
      _ ≤ |C₇| * (16 * P) := mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _)
      _ = 16 * (|C₇| * P) := by ring
  have he2 : C₇ * (3 / 2 * Real.log (q * (3 / 2) * R) ^ 2 / R) ≤ 16 * (|C₇| * P) := by
    have ha : 3 / 2 * Real.log (q * (3 / 2) * R) ^ 2 / R ≤ (4 * L) ^ 2 := by
      rw [div_le_iff₀ (by linarith)]
      have : Real.log (q * (3 / 2) * R) ^ 2 ≤ (4 * L) ^ 2 := pow_le_pow_left₀ hl2' hl2 2
      nlinarith
    have hb : 0 ≤ 3 / 2 * Real.log (q * (3 / 2) * R) ^ 2 / R := by
      apply div_nonneg _ (by linarith); positivity
    calc C₇ * (3 / 2 * Real.log (q * (3 / 2) * R) ^ 2 / R)
        ≤ |C₇| * (3 / 2 * Real.log (q * (3 / 2) * R) ^ 2 / R) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hb
      _ ≤ |C₇| * (16 * P) := mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _)
      _ = 16 * (|C₇| * P) := by ring
  -- the zero sum
  have hsq : 2 * (q * x) ≤ (q * x) ^ 2 := by
    rw [sq]; exact mul_le_mul_of_nonneg_right hqx2 (by linarith)
  have hcube : 4 * (q * x) ≤ (q * x) ^ 3 := by
    have h4 : 4 ≤ (q * x) ^ 2 := by linarith
    calc 4 * (q * x) ≤ (q * x) ^ 2 * (q * x) := mul_le_mul_of_nonneg_right h4 (by linarith)
      _ = (q * x) ^ 3 := by ring
  have hK4 : K + 2 ≤ 4 * x := by linarith
  have hlK : Real.log (q * (K + 2)) ≤ 3 * L := by
    have h1 : q * (K + 2) ≤ q * (4 * x) := mul_le_mul_of_nonneg_left hK4 (by positivity)
    have := hlogpow 3 (q * (K + 2)) (by positivity) (by linarith)
    push_cast at this; linarith
  have hlK0 : 0 ≤ Real.log (q * (K + 2)) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq1 (by linarith))
  have hlK' : 1 + Real.log K ≤ 5 * L := by
    have := hlogpow 3 K hK0 (by linarith)
    push_cast at this; linarith
  have hSum : Sig ≤ 60 * (|C₁| * L ^ 2) := by
    refine hSig.trans ?_
    calc 4 * (|C₁| * Real.log (q * (K + 2))) * (1 + Real.log K)
        ≤ 4 * (|C₁| * (3 * L)) * (5 * L) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlK (abs_nonneg _))
            (by norm_num)) hlK' hlK1 (by positivity)
      _ = 60 * (|C₁| * L ^ 2) := by ring
  have hsx' : Real.sqrt x' ≤ 2 * Real.sqrt x := by
    rw [show 2 * Real.sqrt x = Real.sqrt (4 * x) by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx'4
  have hs32 : Real.sqrt (3 / 2) ≤ Real.sqrt x := Real.sqrt_le_sqrt (by linarith)
  have hz1 : Real.sqrt x' * Sig ≤ 120 * (|C₁| * P) := by
    calc Real.sqrt x' * Sig ≤ (2 * Real.sqrt x) * (60 * (|C₁| * L ^ 2)) :=
          mul_le_mul hsx' hSum hSum0 (by positivity)
      _ = 120 * (|C₁| * P) := by rw [hP]; ring
  have hz2 : Real.sqrt (3 / 2) * Sig ≤ 60 * (|C₁| * P) := by
    calc Real.sqrt (3 / 2) * Sig ≤ Real.sqrt x * (60 * (|C₁| * L ^ 2)) :=
          mul_le_mul hs32 hSum hSum0 (by positivity)
      _ = 60 * (|C₁| * P) := by rw [hP]; ring
  -- the logarithm
  have hlx : Real.log x' ≤ 4 * P := by
    have := hlogpow 2 x' (by linarith) (by linarith)
    push_cast at this
    have h := mul_le_mul_of_nonneg_left hL12 (show (0 : ℝ) ≤ 4 * L by linarith)
    have he : 4 * L * L = 4 * L ^ 2 := by ring
    linarith
  have hfin : (32 * |C₇| + 180 * |C₁| + 20) * Real.sqrt x * L ^ 2 =
      32 * (|C₇| * P) + 180 * (|C₁| * P) + 20 * P := by rw [hP]; ring
  rw [hfin]
  linarith

/-! ### The generalized Riemann hypothesis and `ψ(x, χ)` -/

/-- **The generalized Riemann hypothesis for `L(s, χ)` gives `ψ(x, χ) = O(√x log² (q x))`.** There
is an absolute constant `C` such that for every primitive Dirichlet character `χ ≠ 1` modulo `q`
all of whose nontrivial zeros lie on the line `Re s = 1/2`, and every `x ≥ 2`,
`‖ψ(x, χ)‖ ≤ C √x log² (q x)`. -/
theorem exists_norm_chebyshevPsi_le_of_forall_re_eq_half :
    ∃ C : ℝ, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      (∀ ρ ∈ χ.nontrivialZeros, ρ.re = 1 / 2) → ∀ x : ℝ, 2 ≤ x →
        ‖χ.chebyshevPsi x‖ ≤ C * Real.sqrt x * Real.log (q * x) ^ 2 := by
  classical
  obtain ⟨C₇, hC₇⟩ := exists_truncated_explicit_formula_chebyshevPsi.{0}
  obtain ⟨C₁, hC₁⟩ := exists_card_le_log_of_abs_sub_im_lt.{0}
  refine ⟨32 * |C₇| + 180 * |C₁| + 20, ?_⟩
  intro q _ χ hχ hχ1 hGRH x hx
  -- an enumeration of the zeros
  let z : (Σ w : ℂ, Fin (analyticOrderAt (xi χ) w).toNat) → ℂ := fun n => n.1
  have hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w :=
    Complex.card_sigma_fin_analyticOrderAt (differentiable_xi hχ1) (xi_zero_ne_zero hχ hχ1)
  have hre : ∀ n, (z n).re = 1 / 2 := fun n =>
    hGRH _ (mem_nontrivialZeros_of_card_eq_analyticOrderAt hχ hχ1 hz n)
  have hC₁' := hC₁ χ hχ z hz
  -- replace `x` by `x' = ⌊x⌋ + 1/2`
  have hx0 : 0 < x := by linarith
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, n₀ = ⌊x⌋₊ := ⟨_, rfl⟩
  have hn₀2 : 2 ≤ n₀ := by rw [hn₀]; exact Nat.le_floor (by exact_mod_cast hx)
  have hn₀x : (n₀ : ℝ) ≤ x := by rw [hn₀]; exact Nat.floor_le hx0.le
  have hxn₀ : x < n₀ + 1 := by rw [hn₀]; exact Nat.lt_floor_add_one x
  have hn₀2' : (2 : ℝ) ≤ n₀ := by exact_mod_cast hn₀2
  obtain ⟨x', hx'⟩ : ∃ x' : ℝ, x' = n₀ + 1 / 2 := ⟨_, rfl⟩
  have hψ : χ.chebyshevPsi x = χ.chebyshevPsi x' := by
    have hfl : ⌊x'⌋₊ = n₀ := by
      rw [Nat.floor_eq_iff (by rw [hx']; positivity)]
      constructor <;> rw [hx'] <;> linarith
    simp only [chebyshevPsi, hfl, hn₀]
  have hψ0 : χ.chebyshevPsi (3 / 2) = 0 := by
    have hfl : ⌊(3 / 2 : ℝ)⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by norm_num)]; norm_num
    simp [chebyshevPsi, hfl]
  obtain ⟨R, hR1, hR2⟩ : ∃ R : ℝ, x' ≤ R ∧ R ≤ x' + 1 := ⟨x', le_rfl, by linarith⟩
  have hR2' : 2 ≤ R := by linarith
  have hE1 := hC₇ χ hχ hχ1 z hz x' ⟨n₀, by omega, hx'⟩ R hR2'
  have hE2 := hC₇ χ hχ hχ1 z hz (3 / 2) ⟨1, one_pos, by norm_num⟩ R hR2'
  rw [hψ0] at hE2
  -- the zero sum
  set N := (finite_setOf_abs_im_lt_of_card_eq_analyticOrderAt hχ hχ1 hz R).toFinset with hN
  have hmemN : ∀ n, n ∈ N ↔ |(z n).im| < R := fun n => by simp [N]
  have hSig := sum_one_div_norm_le_of_re_eq_half z C₁ hC₁' hre R N (fun n hn => (hmemN n).mp hn)
  have hZ1 := norm_tsum_cpow_div_le_of_re_eq_half z hre R x' (by linarith) N hmemN
  have hZ2 := norm_tsum_cpow_div_le_of_re_eq_half z hre R (3 / 2) (by norm_num) N hmemN
  have hA : (1 - χ (-1)) / 2 = 0 ∨ (1 - χ (-1)) / 2 = 1 := by
    rcases χ.even_or_odd with h | h
    · left; rw [show χ (-1) = 1 from h]; ring
    · right; rw [show χ (-1) = -1 from h]; ring
  have hS1 := norm_tsum_trivial_zeros_le x' (by linarith) _ hA
  have hS2 := norm_tsum_trivial_zeros_le (3 / 2) le_rfl _ hA
  rw [hψ]
  refine (norm_le_of_two_explicit_formulas _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Real.log x') _ _ hE1 hE2
    hZ1 hZ2 ?_
    hS1 hS2).trans ?_
  · rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have h1 : ‖1 - (1 - χ (-1)) / 2‖ ≤ 1 := by rcases hA with h | h <;> rw [h] <;> norm_num
    have hl0 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
    have hl1 : Real.log (3 / 2) ≤ Real.log x' := Real.log_le_log (by norm_num) (by linarith)
    have h2 : |Real.log x' - Real.log (3 / 2)| ≤ Real.log x' := by
      rw [abs_of_nonneg (by linarith)]; linarith
    calc ‖1 - (1 - χ (-1)) / 2‖ * |Real.log x' - Real.log (3 / 2)| ≤ 1 * Real.log x' :=
          mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = Real.log x' := one_mul _
  -- the final estimate
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hSum0 : 0 ≤ ∑ n ∈ N, 1 / ‖z n‖ := Finset.sum_nonneg fun n _ => by positivity
  have hK1 : (1 : ℝ) ≤ (⌈R⌉₊ : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by linarith)).ne'
  have hKR : (⌈R⌉₊ : ℝ) ≤ R + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  exact final_bound_of_re_eq_half C₇ C₁ q x x' R ⌈R⌉₊ _ hq1 hx (by linarith) (by linarith)
    (by linarith) hR1 hR2 hK1 hKR
    hSig hSum0


/-! ### The explicit formula -/

/-- `log² (q (R + 3)) / R → 0` as `R → ∞`. -/
private lemma tendsto_log_sq_div (q : ℕ) [NeZero q] :
    Tendsto (fun R : ℝ => Real.log (q * (R + 3)) ^ 2 / R) atTop (𝓝 0) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have h := Real.tendsto_pow_log_div_mul_add_atTop (1 / (q : ℝ)) (-3) 2 (by positivity)
  have hg : Tendsto (fun R : ℝ => (q : ℝ) * (R + 3)) atTop atTop :=
    (tendsto_atTop_add_const_right _ 3 tendsto_id).const_mul_atTop hq
  refine (h.comp hg).congr fun R => ?_
  simp only [Function.comp]
  congr 1
  field_simp
  ring

/-- **The explicit formula for `ψ(x, χ)`.** For a primitive Dirichlet character `χ ≠ 1` modulo
`q` with parity `a = (1 - χ(-1))/2`, a family `z` listing the zeros of `ξ(s, χ)` with
multiplicity (the nontrivial zeros `ρ = β + iγ` of `L(s, χ)`), and real `x > 1` not a prime power,
`∑_ρ x^ρ/ρ = -ψ(x, χ) - (1 - a)(log x + b(χ)) - a L'(0, χ)/L(0, χ) + ∑_{m ≥ 1} x^{a-2m}/(2m - a)`,
where `b(χ) = DirichletCharacter.logDerivConstAtZero χ`. The sum over the zeros converges only
conditionally: it is the limit as `R → ∞` of its truncations to `|γ| < R`, each with finite
support. -/
theorem tendsto_tsum_cpow_div_zeros_explicit_formula {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {ι : Type u} (z : ι → ℂ)
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w) {x : ℝ} (hx : 1 < x)
    (hpp : ∀ n : ℕ, (n : ℝ) = x → ¬ IsPrimePow n) :
    Tendsto (fun R : ℝ => ∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0)) atTop
      (𝓝 (-χ.chebyshevPsi x
        - (1 - (1 - χ (-1)) / 2) * ((Real.log x : ℂ) + χ.logDerivConstAtZero)
        - (1 - χ (-1)) / 2 * (deriv (LFunction χ) 0 / LFunction χ 0)
        + ∑' m : ℕ, (x : ℂ) ^ ((1 - χ (-1)) / 2 - 2 * ((m : ℂ) + 1)) /
            (2 * ((m : ℂ) + 1) - (1 - χ (-1)) / 2))) := by
  classical
  obtain ⟨Cd, hCd⟩ := Complex.exists_norm_digamma_le_log_add
  obtain ⟨K₀, hK₀0, hK₀⟩ := exists_norm_logDeriv_LFunction_le_of_two_le_re
  obtain ⟨Kg, hKg⟩ := exists_good_height_norm_logDeriv_LFunction_le.{u}
  obtain ⟨C₁, hC₁⟩ := exists_card_le_log_of_abs_sub_im_lt.{u}
  obtain ⟨a, ha, hapar, hgf, hgf'⟩ := exists_parity_gammaFactor_eq χ
  rw [hapar]
  have hx0 : 0 < x := by linarith
  have hℓ : 0 < Real.log x := Real.log_pos hx
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hPer := tendsto_truncated_integral_chebyshevPsi χ hx hpp (c := 2) one_lt_two
  -- the error terms are `O(log² (q (R + 3)) / R)`
  set D₁ : ℝ := 2 + (7 + |Cd| + K₀) + 4 + K₀ + |Kg| with hD₁
  have hD₁0 : 0 ≤ D₁ := by positivity
  set D : ℝ := 2 * (x ^ (2 : ℝ) * (D₁ / Real.log x + 1 / Real.log x ^ 2)) + 2 * |C₁| * x
    with hD
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hPer (ε / 2) hε2
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (((tendsto_log_sq_div q).const_mul D).eventually
    (gt_mem_nhds (by rw [mul_zero]; exact hε2)))
  refine ⟨max 2 (max N₁ N₂), fun R hR => ?_⟩
  have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
  have hRN₁ : N₁ ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hR
  have hRN₂ : N₂ ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hR
  have hR0 : 0 < R := by linarith
  -- the good height
  obtain ⟨T, hT1, hT2, hTz, hTb⟩ := hKg χ hχ z hz R hR2
  have hZd := norm_tsum_cpow_div_sub_tsum_cpow_div_le hχ hχ1 z hz hx hR2 hT1 hT2 (hC₁ χ hχ z hz)
  set L := Real.log (q * (R + 3)) with hL
  have hqR : R + 3 ≤ q * (R + 3) := le_mul_of_one_le_left (by linarith) hq1
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    linarith [Real.exp_one_lt_d9]
  have hL2 : L ≤ L ^ 2 := le_self_pow₀ hL1 two_ne_zero
  have hL2' : 1 ≤ L ^ 2 := hL1.trans hL2
  obtain ⟨B, hB⟩ : ∃ B, B = |Kg| * L ^ 2 := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hKgB : Kg * L ^ 2 ≤ B := by
    rw [hB]; exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have hstep := norm_chebyshevPsi_sub_le_of_height Cd hCd K₀ hK₀0 hK₀ hχ hχ1 ha hapar hgf hgf'
    z hz hx (c := 2) one_lt_two (by linarith) hTz hB0
    (fun σ h1 h2 => ⟨(hTb σ h1 h2).1.trans hKgB, (hTb σ h1 h2).2.trans hKgB⟩)
  have hP := hN₁ T (by linarith)
  rw [dist_eq_norm, norm_sub_rev] at hP
  have h2 := hN₂ R hRN₂
  -- the horizontal sides
  have hlq : Real.log q ≤ L := by
    rw [hL]
    exact Real.log_le_log (by positivity) (le_mul_of_one_le_right (by positivity) (by linarith))
  have hlT : Real.log (T + 2) ≤ L := by
    rw [hL]; exact Real.log_le_log (by linarith) (by linarith)
  have hΦ : Real.log q + Real.log (T + 2) + (7 + |Cd| + K₀) + 2 * 2 + B + K₀ ≤ D₁ * L ^ 2 := by
    have h1 : 7 + |Cd| + K₀ ≤ (7 + |Cd| + K₀) * L ^ 2 :=
      le_mul_of_one_le_right (by positivity) hL2'
    have h2 : K₀ ≤ K₀ * L ^ 2 := le_mul_of_one_le_right hK₀0 hL2'
    have e : D₁ * L ^ 2 = 2 * L ^ 2 + (7 + |Cd| + K₀) * L ^ 2 + 4 * L ^ 2 + K₀ * L ^ 2 +
        |Kg| * L ^ 2 := by rw [hD₁]; ring
    rw [e, hB]
    linarith
  have hΦ0 : 0 ≤ Real.log q + Real.log (T + 2) + (7 + |Cd| + K₀) + 2 * 2 + B + K₀ := by
    have := Real.log_nonneg hq1
    have := Real.log_nonneg (show (1 : ℝ) ≤ T + 2 by linarith)
    positivity
  have hHb : 2 * (x ^ (2 : ℝ) * ((Real.log q + Real.log (T + 2) + (7 + |Cd| + K₀) + 2 * 2 + B +
      K₀) / Real.log x + 1 / Real.log x ^ 2) / T) ≤
      2 * (x ^ (2 : ℝ) * (D₁ / Real.log x + 1 / Real.log x ^ 2)) * (L ^ 2 / R) := by
    have hx2 : 0 < x ^ (2 : ℝ) := by positivity
    have e1 : (Real.log q + Real.log (T + 2) + (7 + |Cd| + K₀) + 2 * 2 + B + K₀) / Real.log x +
        1 / Real.log x ^ 2 ≤ (D₁ / Real.log x + 1 / Real.log x ^ 2) * L ^ 2 := by
      have h3 : 1 / Real.log x ^ 2 ≤ 1 / Real.log x ^ 2 * L ^ 2 :=
        le_mul_of_one_le_right (by positivity) (by nlinarith)
      have h4 : (Real.log q + Real.log (T + 2) + (7 + |Cd| + K₀) + 2 * 2 + B + K₀) / Real.log x ≤
          D₁ * L ^ 2 / Real.log x := div_le_div_of_nonneg_right hΦ hℓ.le
      have e : (D₁ / Real.log x + 1 / Real.log x ^ 2) * L ^ 2 =
          D₁ * L ^ 2 / Real.log x + 1 / Real.log x ^ 2 * L ^ 2 := by ring
      linarith
    have e0 : 0 ≤ (D₁ / Real.log x + 1 / Real.log x ^ 2) * L ^ 2 :=
      mul_nonneg (add_nonneg (div_nonneg hD₁0 hℓ.le) (by positivity)) (sq_nonneg _)
    calc 2 * (x ^ (2 : ℝ) * ((Real.log q + Real.log (T + 2) + (7 + |Cd| + K₀) + 2 * 2 + B + K₀) /
          Real.log x + 1 / Real.log x ^ 2) / T)
        ≤ 2 * (x ^ (2 : ℝ) * ((D₁ / Real.log x + 1 / Real.log x ^ 2) * L ^ 2) / R) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact div_le_div₀ (mul_nonneg hx2.le e0) (mul_le_mul_of_nonneg_left e1 hx2.le) hR0 hT1
      _ = 2 * (x ^ (2 : ℝ) * (D₁ / Real.log x + 1 / Real.log x ^ 2)) * (L ^ 2 / R) := by ring
  -- the zeros between `R` and `T`
  have hw : 2 * (|C₁| * L) * (x / R) ≤ 2 * |C₁| * x * (L ^ 2 / R) := by
    have := mul_le_mul_of_nonneg_left hL2 (abs_nonneg C₁)
    calc 2 * (|C₁| * L) * (x / R) ≤ 2 * (|C₁| * L ^ 2) * (x / R) := by gcongr
      _ = 2 * |C₁| * x * (L ^ 2 / R) := by ring
  -- combine
  rw [dist_eq_norm]
  set SR := ∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0) with hSR
  set ST := ∑' n, (if |(z n).im| < T then (x : ℂ) ^ z n / z n else 0) with hST
  set Bc := (1 - (a : ℂ)) * ((Real.log x : ℂ) + χ.logDerivConstAtZero) with hBc
  set Ac := (a : ℂ) * (deriv (LFunction χ) 0 / LFunction χ 0) with hAc
  set Sinf := ∑' m : ℕ, (x : ℂ) ^ ((a : ℂ) - 2 * ((m : ℂ) + 1)) /
    (2 * ((m : ℂ) + 1) - (a : ℂ)) with hSinf
  have hid : SR - (-χ.chebyshevPsi x - Bc - Ac + Sinf) =
      -(ST - SR) + (χ.chebyshevPsi x - (-ST - Bc - Ac + Sinf)) := by ring
  rw [hid]
  refine (norm_add_le _ _).trans_lt ?_
  rw [norm_neg]
  have hDe : D * (L ^ 2 / R) = 2 * (x ^ (2 : ℝ) * (D₁ / Real.log x + 1 / Real.log x ^ 2)) *
      (L ^ 2 / R) + 2 * |C₁| * x * (L ^ 2 / R) := by rw [hD]; ring
  have h2' : D * (L ^ 2 / R) < ε / 2 := h2
  linarith [hstep]

end DirichletCharacter
