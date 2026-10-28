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
import MathlibExt.NumberTheory.LSeries.VerticalLine
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The explicit formula for `ψ(x, χ)`, `χ` odd

For a primitive odd Dirichlet character `χ` modulo `q` and real `x > 1` not a prime power,
`ψ(x, χ) = -∑_ρ x^ρ/ρ - L'(0, χ)/L(0, χ) + ∑_{m ≥ 0} x^{-(2m+1)}/(2m+1)`,
the sum running over the nontrivial zeros `ρ = β + iγ` of `L(s, χ)` with multiplicity, as the limit
of the truncated sums over `|γ| < R`. The proof integrates `-L'/L(s, χ) x^s / s` over the boundary
of the rectangle `[-2k, 2] × [-T, T]` at good heights `T`, lets `k → ∞`, and compares with
Perron's formula `DirichletCharacter.tendsto_truncated_integral_chebyshevPsi`.

## Main statements

* `DirichletCharacter.tendsto_tsum_cpow_div_zeros_explicit_formula_of_odd`: the explicit formula
  for `ψ(x, χ)`, `χ` odd.
-/

@[expose] public section

universe u

open Complex Filter Topology Set ArithmeticFunction

namespace DirichletCharacter

/-! ### `L(s, χ)` for odd `χ` -/

section Odd

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

private lemma odd_facts (hodd : χ (-1) = -1) : χ ≠ 1 ∧ q ≠ 1 ∧ χ⁻¹ (-1) = -1 := by
  have hu : IsUnit (-1 : ZMod q) := isUnit_one.neg
  refine ⟨?_, ?_, by rw [inv_apply_neg_one, hodd]⟩
  · rintro rfl
    rw [MulChar.one_apply hu] at hodd
    norm_num at hodd
  · rintro rfl
    have : (-1 : ZMod 1) = 1 := Subsingleton.elim _ _
    rw [this, map_one] at hodd
    norm_num at hodd

omit [NeZero q] in
private lemma gammaFactor_eq_of_odd {ψ : DirichletCharacter ℂ q} (hψ : ψ (-1) = -1) (w : ℂ) :
    ψ.gammaFactor w = Complex.Gammaℝ (w + ((1 : ℝ) : ℂ)) := by
  rw [Odd.gammaFactor_def hψ]; simp

/-- `L(s, χ) = ξ(s, χ) H(s)` for odd `χ` of modulus `≠ 1`, at every `s`. -/
private lemma LFunction_eq_xi_mul_of_odd (hodd : χ (-1) = -1) (hq : q ≠ 1) (s : ℂ) :
    LFunction χ s = xi χ s * ((q : ℂ) ^ (-((s + 1) / 2)) *
      ((Real.pi : ℂ) ^ ((s + 1) / 2) * (Complex.Gamma ((s + 1) / 2))⁻¹)) := by
  simpa only [Complex.ofReal_one] using LFunction_eq_xi_mul_cofactor χ hq (a := 1)
    (by rw [hodd]; norm_num) (gammaFactor_eq_of_odd hodd) s

/-- `log ‖v‖ ≤ -σ + log (|t| + 2)` for `1 ≤ ‖v‖ ≤ ‖s‖ + 2`, `σ = Re s ≤ 0`. -/
private lemma log_norm_le (s v : ℂ) (hs : s.re ≤ 0) (hv1 : 1 ≤ ‖v‖) (hv : ‖v‖ ≤ ‖s‖ + 2) :
    Real.log ‖v‖ ≤ -s.re + Real.log (|s.im| + 2) := by
  have h1 : ‖s‖ ≤ -s.re + |s.im| := by
    have := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_nonpos hs] at this; exact this
  have h2 : ‖v‖ ≤ (|s.im| + 2) * Real.exp (-s.re) := by
    have he := Real.add_one_le_exp (-s.re)
    have hp : 0 ≤ -s.re := by linarith
    have : -s.re + |s.im| + 2 ≤ (|s.im| + 2) * (-s.re + 1) := by
      nlinarith [abs_nonneg s.im]
    calc ‖v‖ ≤ -s.re + |s.im| + 2 := by linarith
      _ ≤ (|s.im| + 2) * (-s.re + 1) := this
      _ ≤ (|s.im| + 2) * Real.exp (-s.re) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc Real.log ‖v‖ ≤ Real.log ((|s.im| + 2) * Real.exp (-s.re)) :=
        Real.log_le_log (by linarith) h2
    _ = -s.re + Real.log (|s.im| + 2) := by
        rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]; ring

/-- `L'/L(s, χ)` on the left: on `Re s ≤ -1`, along the lines `|Im s| ≥ 2` and `Re s = -2k`,
`L(s, χ) ≠ 0` and `‖L'/L(s, χ)‖ ≤ K (-Re s + log (|Im s| + 2) + 1)`. -/
private lemma exists_norm_logDeriv_le_left (hχ : χ.IsPrimitive) (hodd : χ (-1) = -1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, s.re ≤ -1 → (2 ≤ |s.im| ∨ ∃ k : ℕ, s.re = -2 * k) →
      LFunction χ s ≠ 0 ∧
      ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ K * (-s.re + Real.log (|s.im| + 2) + 1) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_logDeriv_LFunction_le_of_re_le_neg_one
  obtain ⟨-, -, hinv⟩ := odd_facts hodd
  have hlq : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  refine ⟨Real.log q + C + 1, by positivity, fun s hs hline => ?_⟩
  set z : ℂ := Real.pi * ((s + ((1 : ℝ) : ℂ)) / 2) with hz
  have hsc : Complex.sin z ≠ 0 ∧ ‖Complex.cos z‖ ≤ 2 * ‖Complex.sin z‖ := by
    rcases hline with h | ⟨k, hk⟩
    · have him : 1 ≤ |z.im| := by
        have : z.im = Real.pi * s.im / 2 := by simp [hz]; ring
        rw [this, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]
        nlinarith [Real.two_le_pi]
      exact ⟨Complex.sin_ne_zero_of_one_le_abs_im him,
        Complex.norm_cos_le_two_mul_norm_sin_of_one_le_abs_im him⟩
    · have hre : Real.cos z.re = 0 := by
        have : z.re = Real.pi / 2 - k * Real.pi := by simp [hz, hk]; ring
        rw [this, Real.cos_pi_div_two_sub, Real.sin_nat_mul_pi]
      exact ⟨Complex.sin_ne_zero_of_cos_re_eq_zero hre,
        (Complex.norm_cos_le_norm_sin_of_cos_re_eq_zero hre).trans
          (by linarith [norm_nonneg (Complex.sin z)])⟩
  obtain ⟨hLs, hb⟩ := hC χ hχ 1 (gammaFactor_eq_of_odd hodd) (gammaFactor_eq_of_odd hinv)
    zero_le_one le_rfl s hs hsc.1 hsc.2
  refine ⟨hLs, hb.trans ?_⟩
  have hv : ‖(((‖s‖ + 2 : ℝ)) : ℂ)‖ = ‖s‖ + 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hlog := log_norm_le s _ (by linarith) (by rw [hv]; linarith [norm_nonneg s]) hv.le
  rw [hv] at hlog
  have hX : 1 ≤ -s.re + Real.log (|s.im| + 2) + 1 := by
    linarith [Real.log_nonneg (by linarith [abs_nonneg s.im] : (1 : ℝ) ≤ |s.im| + 2)]
  nlinarith [mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ Real.log q + C)]

/-- The zeros of `L(s, χ)`, `χ` odd primitive: the nontrivial zeros and `-(2n + 1)`. -/
private lemma mem_nontrivialZeros_or_of_LFunction_eq_zero (hχ : χ.IsPrimitive)
    (hodd : χ (-1) = -1) {s : ℂ} (hs : LFunction χ s = 0) :
    s ∈ χ.nontrivialZeros ∨ ∃ n : ℕ, s = -(2 * (n : ℂ) + 1) := by
  obtain ⟨hχ1, hq, -⟩ := odd_facts hodd
  have hqc : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [LFunction_eq_xi_mul_of_odd hodd hq s] at hs
  rcases mul_eq_zero.mp hs with h | h
  · left; exact (xi_eq_zero_iff hχ hχ1 s).mp h
  · right
    have hA : (q : ℂ) ^ (-((s + 1) / 2)) ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hqc]
    have hB : (Real.pi : ℂ) ^ ((s + 1) / 2) ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hpi]
    have hG : Complex.Gamma ((s + 1) / 2) = 0 := by
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h hA
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h hB
      · exact inv_eq_zero.mp h
    obtain ⟨m, hm⟩ := (Complex.Gamma_eq_zero_iff _).mp hG
    exact ⟨m, by linear_combination 2 * hm⟩

private lemma LFunction_zero_ne_zero_of_odd (hχ : χ.IsPrimitive) (hodd : χ (-1) = -1) :
    LFunction χ 0 ≠ 0 := by
  intro h
  rcases mem_nontrivialZeros_or_of_LFunction_eq_zero hχ hodd h with h | ⟨n, hn⟩
  · exact h.2.2.2 rfl
  · have := congrArg Complex.re hn
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- The principal part of `-L'/L(s, χ) x^s/s` at a nontrivial zero `p` of multiplicity `m`. -/
private lemma exists_local_pole_zero (hodd : χ (-1) = -1) {x : ℝ}
    (hx : 0 < x) {p : ℂ} (hp : p ∈ χ.nontrivialZeros) {m : ℕ} (hm : analyticOrderAt (xi χ) p = m) :
    ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ p ∧ ∀ᶠ s in 𝓝[≠] p,
      -(deriv (LFunction χ) s / LFunction χ s) * ((x : ℂ) ^ s / s) =
        (-(((m : ℤ)) : ℂ) * ((x : ℂ) ^ p / p)) / (s - p) + φ s := by
  obtain ⟨hχ1, hq, -⟩ := odd_facts hodd
  have hp0 : p ≠ 0 := hp.2.2.2
  obtain ⟨ξ₁, hξ₁a, hξ₁0, hξ₁e⟩ :=
    ((differentiable_xi hχ1).analyticAt p).analyticOrderAt_eq_natCast.mp hm
  have hHd : Differentiable ℂ (fun w : ℂ => (q : ℂ) ^ (-((w + 1) / 2)) *
      ((Real.pi : ℂ) ^ ((w + 1) / 2) * (Complex.Gamma ((w + 1) / 2))⁻¹)) := by
    simpa only [Complex.ofReal_one] using differentiable_xi_cofactor q 1
  have hwp : ∀ m' : ℕ, (p + ((1 : ℝ) : ℂ)) / 2 ≠ -(m' : ℂ) := by
    intro m' h
    have := congrArg Complex.re h
    simp at this
    linarith [hp.2.1, (Nat.cast_nonneg m' : (0 : ℝ) ≤ m')]
  have hHp := xi_cofactor_ne_zero q 1 hwp
  simp only [Complex.ofReal_one] at hHp
  refine Complex.exists_eventually_neg_logDeriv_mul_cpow_div_eq_of_zpow hx hp0
    (E := fun s => ξ₁ s * ((q : ℂ) ^ (-((s + 1) / 2)) *
      ((Real.pi : ℂ) ^ ((s + 1) / 2) * (Complex.Gamma ((s + 1) / 2))⁻¹)))
    (hξ₁a.mul (hHd.analyticAt p)) (mul_ne_zero hξ₁0 hHp) ?_
  filter_upwards [nhdsWithin_le_nhds hξ₁e] with s hse
  rw [LFunction_eq_xi_mul_of_odd hodd hq s, hse, zpow_natCast, smul_eq_mul]
  ring

/-- The principal part of `-L'/L(s, χ) x^s/s` at the trivial zero `-(2n + 1)`. -/
private lemma exists_local_pole_trivial (hχ : χ.IsPrimitive) (hodd : χ (-1) = -1) {x : ℝ}
    (hx : 0 < x) (n : ℕ) :
    ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ (-(2 * (n : ℂ) + 1)) ∧
      ∀ᶠ s in 𝓝[≠] (-(2 * (n : ℂ) + 1)),
      -(deriv (LFunction χ) s / LFunction χ s) * ((x : ℂ) ^ s / s) =
        (-(((1 : ℤ)) : ℂ) * ((x : ℂ) ^ (-(2 * (n : ℂ) + 1)) / (-(2 * (n : ℂ) + 1)))) /
          (s - (-(2 * (n : ℂ) + 1))) + φ s := by
  obtain ⟨hχ1, hq, -⟩ := odd_facts hodd
  have hqc : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  set p : ℂ := -(2 * (n : ℂ) + 1) with hpdef
  have hpre : p.re < 0 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp [p]; linarith
  have hp0 : p ≠ 0 := fun h => by rw [h] at hpre; simp at hpre
  obtain ⟨G, hGa, hG0, hGe⟩ := (Complex.differentiable_one_div_Gamma.analyticAt
    (-(n : ℂ))).analyticOrderAt_eq_natCast (n := 1) |>.mp
      ((Complex.analyticOrderAt_inv_Gamma_neg_natCast n).trans Nat.cast_one.symm)
  have ht : Tendsto (fun s : ℂ => (s + 1) / 2) (𝓝 p) (𝓝 (-(n : ℂ))) := by
    have h : -(n : ℂ) = (p + 1) / 2 := by rw [hpdef]; ring
    rw [h]
    exact ((continuous_id.add continuous_const).div_const (2 : ℂ)).tendsto p
  have hGe' := ht.eventually hGe
  have hGa' := ht.eventually hGa.eventually_analyticAt
  have hξd := differentiable_xi hχ1
  set E : ℂ → ℂ := fun s => xi χ s * ((q : ℂ) ^ (-((s + 1) / 2)) *
      ((Real.pi : ℂ) ^ ((s + 1) / 2) * (G ((s + 1) / 2) / 2))) with hEdef
  have hE : AnalyticAt ℂ E p := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [hGa'] with s hsa
    have h1 : DifferentiableAt ℂ (fun w : ℂ => (q : ℂ) ^ (-((w + 1) / 2))) s :=
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => -((w + 1) / 2)) s).const_cpow (Or.inl hqc)
    have h2 : DifferentiableAt ℂ (fun w : ℂ => (Real.pi : ℂ) ^ ((w + 1) / 2)) s :=
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => (w + 1) / 2) s).const_cpow (Or.inl hpi)
    have h3 : DifferentiableAt ℂ (fun w : ℂ => G ((w + 1) / 2)) s :=
      hsa.differentiableAt.comp s (by fun_prop)
    exact (hξd s).mul (h1.mul (h2.mul (h3.div_const 2)))
  have hE0 : E p ≠ 0 := by
    have hxi : xi χ p ≠ 0 := by
      rw [Ne, xi_eq_zero_iff hχ hχ1]
      intro h; linarith [h.2.1]
    have hGp : G ((p + 1) / 2) ≠ 0 := by
      have : (p + 1) / 2 = -(n : ℂ) := by rw [hpdef]; ring
      rw [this]; exact hG0
    have hA : (q : ℂ) ^ (-((p + 1) / 2)) ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hqc]
    have hB : (Real.pi : ℂ) ^ ((p + 1) / 2) ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hpi]
    exact mul_ne_zero hxi (mul_ne_zero hA (mul_ne_zero hB (div_ne_zero hGp two_ne_zero)))
  have hζ : ∀ᶠ s in 𝓝[≠] p, LFunction χ s = (s - p) ^ ((1 : ℤ)) * E s := by
    filter_upwards [nhdsWithin_le_nhds hGe'] with s hse
    rw [LFunction_eq_xi_mul_of_odd hodd hq s, hse, zpow_one, pow_one, smul_eq_mul]
    simp only [E, p]
    ring
  exact Complex.exists_eventually_neg_logDeriv_mul_cpow_div_eq_of_zpow hx hp0 hE hE0 hζ

/-- The principal part of `-L'/L(s, χ) x^s/s` at `s = 0`. -/
private lemma exists_local_pole_origin (hχ : χ.IsPrimitive) (hodd : χ (-1) = -1) {x : ℝ}
    (hx : 0 < x) :
    ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ 0 ∧ ∀ᶠ s in 𝓝[≠] (0 : ℂ),
      -(deriv (LFunction χ) s / LFunction χ s) * ((x : ℂ) ^ s / s) =
        (-(deriv (LFunction χ) 0 / LFunction χ 0)) / (s - 0) + φ s :=
  Complex.exists_eventually_neg_logDeriv_mul_cpow_div_eq_of_ne_zero hx
    ((differentiable_LFunction (odd_facts hodd).1).analyticAt 0)
    (LFunction_zero_ne_zero_of_odd hχ hodd)

end Odd

/-! ### The residue theorem on `[-2k, 2] × [-T, T]` -/

section Rectangle

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- **The residues of `-L'/L(s, χ) x^s / s`, `χ` odd.** For `x > 1`, `k ≥ 1` and `T > 0` not the
ordinate of a nontrivial zero, the boundary integral of `-L'/L(s, χ) x^s / s` over
`[-2k, 2] × [-T, T]` is
`2πi (-L'/L(0, χ) - ∑_{|γ| < T} x^ρ/ρ + ∑_{m < k} x^{-(2m+1)}/(2m+1))`. -/
private lemma boundaryIntegral_neg_logDeriv_mul_cpow_div (hχ : χ.IsPrimitive)
    (hodd : χ (-1) = -1) {ι : Type u} (z : ι → ℂ)
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w)
    {x : ℝ} (hx : 1 < x) {k : ℕ} (hk : 1 ≤ k) {T : ℝ} (hT : 0 < T)
    (hTz : ∀ ρ ∈ χ.nontrivialZeros, |ρ.im| ≠ T) :
    (RectilinearRectangle.ofBounds (-(2 * k : ℝ)) 2 (-T) T).boundaryIntegral
        (fun s => -(deriv (LFunction χ) s / LFunction χ s) * ((x : ℂ) ^ s / s)) =
      2 * (Real.pi : ℂ) * I * (-(deriv (LFunction χ) 0 / LFunction χ 0) -
        ∑' n, (if |(z n).im| < T then (x : ℂ) ^ z n / z n else 0) +
        ∑ m ∈ Finset.range k, (x : ℂ) ^ (-(2 * (m : ℂ) + 1)) / (2 * (m : ℂ) + 1)) := by
  classical
  set F : ℂ → ℂ := fun s => -(deriv (LFunction χ) s / LFunction χ s) * ((x : ℂ) ^ s / s)
    with hF
  obtain ⟨hχ1, hq, -⟩ := odd_facts hodd
  have hx0 : 0 < x := by linarith
  have hkpos : (0 : ℝ) < 2 * k := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hord_top := analyticOrderAt_xi_ne_top hχ hχ1
  have hmem_of := mem_nontrivialZeros_of_card_eq_analyticOrderAt hχ hχ1 hz
  have hfib := finite_of_card_eq_analyticOrderAt hχ hχ1 hz
  have hNfin := finite_setOf_abs_im_lt_of_card_eq_analyticOrderAt hχ hχ1 hz T
  set NF := hNfin.toFinset with hNF
  set Z : Finset ℂ := NF.image z with hZ
  set Tr : Finset ℂ := (Finset.range k).image (fun m : ℕ => -(2 * (m : ℂ) + 1)) with hTr
  set S : Finset ℂ := insert 0 (Z ∪ Tr) with hS
  have hZmem : ∀ p, p ∈ Z ↔ p ∈ χ.nontrivialZeros ∧ |p.im| < T := by
    intro p; constructor
    · intro hp
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨hmem_of n, by simpa [NF] using hn⟩
    · rintro ⟨hp, hpR⟩
      obtain ⟨n, hn⟩ := exists_eq_of_card_eq_analyticOrderAt hχ hχ1 hz hp
      exact Finset.mem_image.mpr ⟨n, by simp [NF, hn, hpR], hn⟩
  have hTrmem : ∀ p, p ∈ Tr ↔ ∃ m : ℕ, m < k ∧ p = -(2 * (m : ℂ) + 1) := by
    intro p
    simp only [Tr, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨m, h1, rfl⟩; exact ⟨m, h1, rfl⟩
    · rintro ⟨m, h1, rfl⟩; exact ⟨m, h1, rfl⟩
  have hZprop : ∀ p ∈ Z, p ≠ 0 ∧ 0 ≤ p.re ∧ p.re ≤ 1 ∧ |p.im| < T := by
    intro p hp
    obtain ⟨hnt, hpR⟩ := (hZmem p).mp hp
    exact ⟨hnt.2.2.2, hnt.2.1, hnt.2.2.1, hpR⟩
  have hTrprop : ∀ p ∈ Tr, p.re < 0 ∧ -(2 * k : ℝ) < p.re ∧ p.im = 0 := by
    intro p hp
    obtain ⟨m, h1, rfl⟩ := (hTrmem p).mp hp
    have h1' : (m : ℝ) + 1 ≤ k := by exact_mod_cast h1
    have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    simp
    constructor <;> linarith
  -- residues
  let mo : ℂ → ℕ := fun p => (analyticOrderAt (xi χ) p).toNat
  let kf : ℂ → ℤ := fun p => if p ∈ Z then (mo p : ℤ) else 1
  let r : ℂ → ℂ := fun p =>
    if p = 0 then -(deriv (LFunction χ) 0 / LFunction χ 0)
    else -(kf p : ℂ) * ((x : ℂ) ^ p / p)
  have h0Z : (0 : ℂ) ∉ Z := fun h => (hZprop 0 h).1 rfl
  have h0Tr : (0 : ℂ) ∉ Tr := fun h => by have := (hTrprop 0 h).1; simp at this
  have hZTr : ∀ p ∈ Tr, p ∉ Z := fun p hp hpZ => by
    linarith [(hTrprop p hp).1, (hZprop p hpZ).2.1]
  have hloc : ∀ p ∈ S, ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ p ∧
      ∀ᶠ s in 𝓝[≠] p, F s = r p / (s - p) + φ s := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · obtain ⟨φ, h1, h2⟩ := exists_local_pole_origin hχ hodd hx0
      refine ⟨φ, h1, ?_⟩
      have hr : r 0 = -(deriv (LFunction χ) 0 / LFunction χ 0) := by simp [r]
      rw [hr]; exact h2
    rcases Finset.mem_union.mp hp with hpZ | hpT
    · obtain ⟨hp0, -⟩ := hZprop p hpZ
      have hm : analyticOrderAt (xi χ) p = (mo p : ℕ) :=
        (ENat.natCast_toNat (hord_top p)).symm
      obtain ⟨φ, h1, h2⟩ := exists_local_pole_zero hodd hx0 ((hZmem p).mp hpZ).1 hm
      refine ⟨φ, h1, ?_⟩
      have hr : r p = -(((mo p : ℕ) : ℤ) : ℂ) * ((x : ℂ) ^ p / p) := by
        simp [r, kf, hp0, hpZ]
      rw [hr]; exact h2
    · obtain ⟨m, -, rfl⟩ := (hTrmem p).mp hpT
      obtain ⟨φ, h1, h2⟩ := exists_local_pole_trivial hχ hodd hx0 m
      refine ⟨φ, h1, ?_⟩
      have hre := (hTrprop _ hpT).1
      have hp0 : -(2 * (m : ℂ) + 1) ≠ 0 := fun h => by rw [h] at hre; simp at hre
      have hr : r (-(2 * (m : ℂ) + 1)) = -(((1 : ℤ)) : ℂ) *
          ((x : ℂ) ^ (-(2 * (m : ℂ) + 1)) / (-(2 * (m : ℂ) + 1))) := by
        simp only [r, kf, hp0, hZTr _ hpT, ite_false]
      rw [hr]; exact h2
  set rect := RectilinearRectangle.ofBounds (-(2 * k : ℝ)) 2 (-T) T with hrect
  have hKre : ∀ s ∈ rect.carrier, -(2 * k : ℝ) ≤ s.re ∧ s.re ≤ 2 ∧ -T ≤ s.im ∧ s.im ≤ T := by
    intro s hs
    obtain ⟨h1, h2⟩ := Complex.mem_reProdIm.mp hs
    simp only [hrect, RectilinearRectangle.ofBounds_first_re,
      RectilinearRectangle.ofBounds_second_re, RectilinearRectangle.ofBounds_first_im,
      RectilinearRectangle.ofBounds_second_im] at h1 h2
    rw [Set.uIcc_of_le (by linarith)] at h1
    rw [Set.uIcc_of_le (by linarith)] at h2
    exact ⟨h1.1, h1.2, h2.1, h2.2⟩
  have hdiff : ∀ s ∈ rect.carrier, s ∉ S → DifferentiableAt ℂ F s := by
    intro s hsK hsS
    obtain ⟨k1, k2, k3, k4⟩ := hKre s hsK
    have hs0 : s ≠ 0 := fun h => hsS (by simp [S, h])
    have hLs : LFunction χ s ≠ 0 := by
      intro h0
      rcases mem_nontrivialZeros_or_of_LFunction_eq_zero hχ hodd h0 with hnt | ⟨n, rfl⟩
      · have hIm : |s.im| < T := lt_of_le_of_ne (abs_le.mpr ⟨k3, k4⟩) (hTz s hnt)
        exact hsS (Finset.mem_insert_of_mem (Finset.mem_union_left _ ((hZmem s).mpr ⟨hnt, hIm⟩)))
      · have hle : (2 * n + 1 : ℝ) ≤ 2 * k := by simp at k1; linarith
        have hlt : n < k := by
          have : (n : ℝ) < k := by linarith
          exact_mod_cast this
        have hT' : -(2 * (n : ℂ) + 1) ∈ Tr := (hTrmem _).mpr ⟨n, hlt, rfl⟩
        exact hsS (Finset.mem_insert_of_mem (Finset.mem_union_right _ hT'))
    have hLa : AnalyticAt ℂ (LFunction χ) s := (differentiable_LFunction hχ1).analyticAt s
    have hx0' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    exact ((hLa.deriv.differentiableAt.div hLa.differentiableAt hLs).neg).mul
      ((differentiableAt_id.const_cpow (Or.inl hx0')).div differentiableAt_id hs0)
  obtain ⟨g, hg, hfg⟩ := Complex.exists_differentiableOn_eq_add_sum_div_sub _ S r F hloc
    (fun s hs h => (hdiff s hs h).differentiableWithinAt)
  have hin : ∀ p ∈ S, rect.first.re < p.re ∧ p.re < rect.second.re ∧ rect.first.im < p.im ∧
      p.im < rect.second.im := by
    intro p hp
    simp only [hrect, RectilinearRectangle.ofBounds_first_re,
      RectilinearRectangle.ofBounds_second_re, RectilinearRectangle.ofBounds_first_im,
      RectilinearRectangle.ofBounds_second_im]
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simp only [Complex.zero_re, Complex.zero_im]
      exact ⟨by linarith, by norm_num, by linarith, hT⟩
    rcases Finset.mem_union.mp hp with hpZ | hpT
    · obtain ⟨-, h1, h2, h3⟩ := hZprop p hpZ
      exact ⟨by linarith, by linarith, (abs_lt.mp h3).1, (abs_lt.mp h3).2⟩
    · obtain ⟨h1, h2, h3⟩ := hTrprop p hpT
      exact ⟨h2, by linarith, by rw [h3]; linarith, by rw [h3]; exact hT⟩
  rw [RectilinearRectangle.boundaryIntegral_eq_two_pi_mul_I_mul_sum rect S r F g hin hg hfg]
  congr 1
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
  have hinj : Set.InjOn (fun m : ℕ => -(2 * (m : ℂ) + 1)) (Finset.range k : Set ℕ) := by
    intro a _ b _ h
    simp only [neg_inj, add_left_inj, mul_eq_mul_left_iff, two_ne_zero, or_false,
      Nat.cast_inj] at h
    exact h
  have hdisj : Disjoint Z Tr := Finset.disjoint_right.mpr hZTr
  rw [Finset.sum_insert (by simp [h0Z, h0Tr]), Finset.sum_union hdisj, htsum,
    Finset.sum_image hinj]
  have hr0 : r 0 = -(deriv (LFunction χ) 0 / LFunction χ 0) := by simp [r]
  have hrZ : ∑ p ∈ Z, r p = -∑ p ∈ Z, (mo p : ℂ) * ((x : ℂ) ^ p / p) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hp0, -⟩ := hZprop p hp
    simp [r, kf, hp0, hp]
  have hrT : ∑ m ∈ Finset.range k, r (-(2 * (m : ℂ) + 1)) =
      ∑ m ∈ Finset.range k, (x : ℂ) ^ (-(2 * (m : ℂ) + 1)) / (2 * (m : ℂ) + 1) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hpT : -(2 * (m : ℂ) + 1) ∈ Tr := Finset.mem_image.mpr ⟨m, hm, rfl⟩
    have hre := (hTrprop _ hpT).1
    have hp0 : -(2 * (m : ℂ) + 1) ≠ 0 := fun h => by rw [h] at hre; simp at hre
    simp only [r, kf, hp0, hZTr _ hpT, ite_false]
    rw [div_neg]
    push_cast
    ring
  rw [hr0, hrZ, hrT]
  ring

end Rectangle

/-! ### Good heights and the zero sums -/

section Heights

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- The zeros near a height `t`: finitely many, at most `C log (q (|t| + 2))` of them. -/
private lemma exists_card_near_le (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {ι : Type u} (z : ι → ℂ)
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, {n | |t - (z n).im| < 1}.Finite ∧
      ∀ F : Finset ι, (∀ n ∈ F, |t - (z n).im| < 1) →
        (F.card : ℝ) ≤ C * Real.log (q * (|t| + 2)) := by
  obtain ⟨C₂, hC₂⟩ := exists_card_le_log_of_abs_sub_im_lt.{u}
  refine ⟨|C₂|, abs_nonneg _, fun t => ⟨?_, fun F hF => ?_⟩⟩
  · refine (finite_setOf_abs_im_lt_of_card_eq_analyticOrderAt hχ hχ1 hz (|t| + 1)).subset ?_
    intro n hn
    have h1 : |t - (z n).im| < 1 := hn
    have := abs_sub_abs_le_abs_sub (z n).im t
    rw [abs_sub_comm] at h1
    change |(z n).im| < |t| + 1
    linarith
  · have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hl0 : 0 ≤ Real.log (q * (|t| + 2)) := Real.log_nonneg (by
      have := abs_nonneg t; nlinarith)
    exact (hC₂ χ hχ z hz t F hF).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hl0)

/-- **Good heights for `L'/L(s, χ)`.** Within `1` of any `R ≥ 3` there is a height `T`, avoiding
the ordinates `±γ`, on which `‖L'/L(σ ± iT, χ)‖ ≤ K log² (q (R + 4))` for `-3/2 ≤ σ ≤ 2`. -/
private lemma exists_good_height (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {ι : Type u} (z : ι → ℂ)
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 3 ≤ R → ∃ T : ℝ, |T - R| ≤ 1 ∧ 2 ≤ T ∧
      (∀ n, |(z n).im| ≠ T) ∧ ∀ σ τ : ℝ, -3 / 2 ≤ σ → σ ≤ 2 → |τ| = T →
        ‖deriv (LFunction χ) (σ + τ * I) / LFunction χ (σ + τ * I)‖ ≤
          K * Real.log (q * (R + 4)) ^ 2 := by
  classical
  obtain ⟨C₁, hC₁⟩ := exists_norm_logDeriv_LFunction_sub_tsum_le_log.{u}
  obtain ⟨C₂, hC₂0, hcnt⟩ := exists_card_near_le hχ hχ1 z hz
  refine ⟨|C₁| + 4 * C₂ ^ 2 + 4 * C₂, by positivity, fun R hR => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set ℓ := Real.log (q * (R + 4)) with hℓ
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    nlinarith
  -- the zeros near height `±R`
  set Ap : Finset ι := (hcnt R).1.toFinset with hAp
  set Am : Finset ι := (hcnt (-R)).1.toFinset with hAm
  set A : Finset ι := Ap ∪ Am with hA
  set G : Finset ℝ := A.image (fun n => |(z n).im|) with hG
  have hlR : Real.log (q * (R + 2)) ≤ ℓ :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hGcard : (G.card : ℝ) ≤ 2 * C₂ * ℓ := by
    have h1 : (G.card : ℝ) ≤ A.card := by exact_mod_cast Finset.card_image_le
    have h2 : (A.card : ℝ) ≤ Ap.card + Am.card := by exact_mod_cast Finset.card_union_le _ _
    have h3 := (hcnt R).2 Ap (fun n hn => by simpa [hAp] using hn)
    have h4 := (hcnt (-R)).2 Am (fun n hn => by simpa [hAm] using hn)
    rw [abs_neg, abs_of_pos (by linarith)] at h4
    rw [abs_of_pos (by linarith)] at h3
    have h5 : C₂ * Real.log (q * (R + 2)) ≤ C₂ * ℓ := mul_le_mul_of_nonneg_left hlR hC₂0
    linarith
  set m : ℕ := ⌈2 * C₂ * ℓ⌉₊ with hm
  have hmG : G.card ≤ m := by
    have : (G.card : ℝ) ≤ m := hGcard.trans (Nat.le_ceil _)
    exact_mod_cast this
  have hm1 : (m : ℝ) + 1 ≤ 2 * C₂ * ℓ + 2 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 2 * C₂ * ℓ by positivity)
    rw [← hm] at this
    linarith
  have hmpos : (0 : ℝ) < m + 1 := by positivity
  set δ : ℝ := 1 / ((m : ℝ) + 1) with hδ
  have hδpos : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one hmpos]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  let t : ℕ → ℝ := fun j => R - 1 / 2 + j * δ
  -- pigeonhole: some grid point is far from every `|γ| ∈ G`
  have hgood : ∃ j ∈ Finset.range (m + 1), ∀ γ ∈ G, δ / 2 ≤ |γ - t j| := by
    by_contra hcon
    push Not at hcon
    choose! g hgG hgd using hcon
    have hinj : Set.InjOn g (Finset.range (m + 1) : Set ℕ) := by
      intro j hj k hk hjk
      by_contra hne
      have h1 := hgd j hj
      have h2 := hgd k hk
      rw [hjk] at h1
      have h3 : |t j - t k| < δ := by
        have := abs_sub_le (t j) (g k) (t k)
        rw [abs_sub_comm (t j) (g k)] at this
        linarith
      have h4 : δ ≤ |t j - t k| := by
        have hjk' : (1 : ℝ) ≤ |(j : ℝ) - k| := by
          rcases lt_or_gt_of_ne hne with h | h
          · have : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
            rw [abs_sub_comm, abs_of_pos (by linarith)]
            linarith
          · have : (k : ℝ) + 1 ≤ j := by exact_mod_cast h
            rw [abs_of_pos (by linarith)]
            linarith
        have : t j - t k = ((j : ℝ) - k) * δ := by simp only [t]; ring
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
    have : (j : ℝ) * δ = j / ((m : ℝ) + 1) := by simp only [hδ]; ring
    rw [this, div_le_one hmpos]; linarith
  have hjδ0 : 0 ≤ (j : ℝ) * δ := by positivity
  have htR : |t j - R| ≤ 1 / 2 := by
    simp only [t]; rw [abs_le]; constructor <;> linarith
  set T := t j with hTdef
  have hT2 : 2 ≤ T := by rw [abs_le] at htR; linarith
  have hfar : ∀ n, δ / 2 ≤ abs (T - |(z n).im|) := by
    intro n
    by_cases hn : n ∈ A
    · have := hjG _ (Finset.mem_image_of_mem _ hn)
      rwa [abs_sub_comm] at this
    · have h1 : ¬ |R - (z n).im| < 1 := fun h =>
        hn (Finset.mem_union_left _ (by simpa [hAp] using h))
      have h2 : ¬ |-R - (z n).im| < 1 := fun h =>
        hn (Finset.mem_union_right _ (by simpa [hAm] using h))
      push Not at h1 h2
      have h3 : 1 ≤ abs (R - |(z n).im|) := by
        rcases le_total 0 (z n).im with h | h
        · rwa [abs_of_nonneg h]
        · rw [abs_of_nonpos h, show R - -(z n).im = -(-R - (z n).im) by ring, abs_neg]
          exact h2
      have h4 := abs_sub_abs_le_abs_sub (R - |(z n).im|) (R - T)
      have h5 : |R - T| ≤ 1 / 2 := by rw [abs_sub_comm]; exact htR
      have h6 : R - |(z n).im| - (R - T) = T - |(z n).im| := by ring
      rw [h6] at h4
      linarith
  refine ⟨T, by linarith, hT2, fun n h => ?_, ?_⟩
  · have := hfar n
    rw [h, sub_self, abs_zero] at this
    linarith
  intro σ τ hσ1 hσ2 hτ
  set s : ℂ := σ + τ * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = τ := by simp [hs]
  have hfar' : ∀ n, δ / 2 ≤ |τ - (z n).im| := by
    intro n
    have h1 := abs_abs_sub_abs_le_abs_sub τ (z n).im
    rw [hτ] at h1
    exact (hfar n).trans h1
  have key := hC₁ χ hχ z hz s (by rw [hsre]; linarith) (by rw [hsre]; linarith)
    (by rw [hsim, hτ]; exact hT2) (fun n h => by
      have := hfar' n
      rw [← hsim, ← h, sub_self, abs_zero] at this
      linarith)
  rw [hsim, hτ] at key
  have hlT : Real.log (q * (T + 2)) ≤ ℓ :=
    Real.log_le_log (by positivity) (by
      have : T + 2 ≤ R + 4 := by rw [abs_le] at htR; linarith
      nlinarith)
  have hlT0 : 0 ≤ Real.log (q * (T + 2)) := Real.log_nonneg (by nlinarith)
  set f : ι → ℂ := fun n => if |s.im - (z n).im| < 1 then 1 / (s - z n) else 0 with hf
  set B : Finset ι := (hcnt τ).1.toFinset with hB
  have hzero : ∀ n ∉ B, f n = 0 := by
    intro n hn
    simp only [hf]
    rw [ite_eq_right]
    intro hlt
    apply hn
    rw [hsim] at hlt
    simpa [hB] using hlt
  have hterm : ∀ n ∈ B, ‖f n‖ ≤ 2 / δ := by
    intro n _
    simp only [hf]
    split_ifs with hlt
    · rw [norm_div, norm_one]
      have hn1 : |τ - (z n).im| ≤ ‖s - z n‖ := by
        have := Complex.abs_im_le_norm (s - z n)
        simpa [Complex.sub_im, hsim] using this
      have hpos : 0 < |τ - (z n).im| := lt_of_lt_of_le (by positivity) (hfar' n)
      rw [div_le_div_iff₀ (lt_of_lt_of_le hpos hn1) hδpos]
      nlinarith [hfar' n]
    · rw [norm_zero]; positivity
  have hBcard : (B.card : ℝ) ≤ C₂ * Real.log (q * (T + 2)) := by
    have := (hcnt τ).2 B (fun n hn => by simpa [hB] using hn)
    rwa [hτ] at this
  have hsumle : ‖∑' n, f n‖ ≤ C₂ * ℓ * (2 * (2 * C₂ * ℓ + 2)) := by
    rw [tsum_eq_sum hzero]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
    have h2δ : 2 / δ ≤ 2 * (2 * C₂ * ℓ + 2) := by
      rw [hδ, div_div_eq_mul_div, div_one]; linarith
    have hc1 : (B.card : ℝ) ≤ C₂ * ℓ :=
      hBcard.trans (mul_le_mul_of_nonneg_left hlT hC₂0)
    exact mul_le_mul hc1 h2δ (by positivity) (by positivity)
  have htri : ‖deriv (LFunction χ) s / LFunction χ s‖ ≤
      ‖deriv (LFunction χ) s / LFunction χ s - ∑' n, f n‖ + ‖∑' n, f n‖ := by
    have := norm_add_le (deriv (LFunction χ) s / LFunction χ s - ∑' n, f n) (∑' n, f n)
    simpa using this
  have hℓℓ : ℓ ≤ ℓ ^ 2 := le_self_pow₀ hℓ1 (by norm_num)
  have h1 : C₁ * Real.log (q * (T + 2)) ≤ |C₁| * ℓ ^ 2 := by
    have : C₁ * Real.log (q * (T + 2)) ≤ |C₁| * Real.log (q * (T + 2)) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hlT0
    have h2 : |C₁| * Real.log (q * (T + 2)) ≤ |C₁| * ℓ ^ 2 :=
      mul_le_mul_of_nonneg_left (hlT.trans hℓℓ) (abs_nonneg _)
    linarith
  have h2 : C₂ * ℓ * (2 * (2 * C₂ * ℓ + 2)) ≤ (4 * C₂ ^ 2 + 4 * C₂) * ℓ ^ 2 := by
    have h3 : C₂ * ℓ ≤ C₂ * ℓ ^ 2 := mul_le_mul_of_nonneg_left hℓℓ hC₂0
    have e1 : C₂ * ℓ * (2 * (2 * C₂ * ℓ + 2)) = 4 * C₂ ^ 2 * ℓ ^ 2 + 4 * (C₂ * ℓ) := by ring
    have e2 : (4 * C₂ ^ 2 + 4 * C₂) * ℓ ^ 2 = 4 * C₂ ^ 2 * ℓ ^ 2 + 4 * (C₂ * ℓ ^ 2) := by ring
    rw [e1, e2]
    linarith only [h3]
  have key' : ‖deriv (LFunction χ) s / LFunction χ s - ∑' n, f n‖ ≤
      C₁ * Real.log (q * (T + 2)) := by
    simpa [hf, hsim] using key
  linarith

/-- Moving the truncation height by at most `1` changes the zero sum by
`O(log (q R) x / R)`. -/
private lemma exists_norm_tsum_sub_tsum_le (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {ι : Type u}
    (z : ι → ℂ) (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w)
    {x : ℝ} (hx : 1 < x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R T : ℝ, 3 ≤ R → |T - R| ≤ 1 →
      ‖(∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0)) -
        ∑' n, (if |(z n).im| < T then (x : ℂ) ^ z n / z n else 0)‖ ≤
        C * Real.log (q * (R + 4)) * x / (R - 1) := by
  classical
  obtain ⟨C₂, hC₂0, hcnt⟩ := exists_card_near_le hχ hχ1 z hz
  refine ⟨2 * C₂, by positivity, fun R T hR hTR => ?_⟩
  have hx0 : 0 < x := by linarith
  have hTR' := abs_le.mp hTR
  set U := max R T with hU
  set NF := (finite_setOf_abs_im_lt_of_card_eq_analyticOrderAt hχ hχ1 hz U).toFinset with hNF
  have hsupp : ∀ V : ℝ, V ≤ U → ∑' n, (if |(z n).im| < V then (x : ℂ) ^ z n / z n else 0) =
      ∑ n ∈ NF, (if |(z n).im| < V then (x : ℂ) ^ z n / z n else 0) := by
    intro V hV
    refine tsum_eq_sum fun n hn => ite_eq_right ?_
    intro h
    apply hn
    simp only [hNF, Set.Finite.mem_toFinset, mem_ofPred_eq]
    linarith
  rw [hsupp R (le_max_left _ _), hsupp T (le_max_right _ _), ← Finset.sum_sub_distrib]
  set d : ι → ℂ := fun n => (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0) -
    (if |(z n).im| < T then (x : ℂ) ^ z n / z n else 0) with hd
  set c0 : ℝ := (R + T) / 2 with hc0
  have hc0pos : 0 < c0 := by rw [hc0]; linarith
  have hdz : ∀ n, d n ≠ 0 → min R T ≤ |(z n).im| ∧ |(z n).im| < max R T := by
    intro n hn
    by_contra hc
    apply hn
    simp only [hd]
    rcases not_and_or.mp hc with h | h
    · push Not at h
      rw [ite_eq_left (lt_of_lt_of_le h (min_le_left _ _)),
        ite_eq_left (lt_of_lt_of_le h (min_le_right _ _)), sub_self]
    · push Not at h
      rw [ite_eq_right (not_lt.mpr ((le_max_left _ _).trans h)),
        ite_eq_right (not_lt.mpr ((le_max_right _ _).trans h)), sub_self]
  have hdnorm : ∀ n, ‖d n‖ ≤ x / (R - 1) := by
    intro n
    by_cases hn : d n = 0
    · rw [hn, norm_zero]; exact div_nonneg hx0.le (by linarith)
    obtain ⟨h1, h2⟩ := hdz n hn
    have hmin : R - 1 ≤ min R T := le_min (by linarith) (by linarith)
    have hzn : R - 1 ≤ ‖z n‖ := (hmin.trans h1).trans (Complex.abs_im_le_norm _)
    have hmem := mem_nontrivialZeros_of_card_eq_analyticOrderAt hχ hχ1 hz n
    have hpow : ‖(x : ℂ) ^ z n‖ ≤ x := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      calc x ^ (z n).re ≤ x ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx.le hmem.2.2.1
        _ = x := Real.rpow_one x
    have hval : ‖(x : ℂ) ^ z n / z n‖ ≤ x / (R - 1) := by
      rw [norm_div]
      exact div_le_div₀ hx0.le hpow (by linarith) hzn
    simp only [hd] at hn ⊢
    split_ifs at hn ⊢ with ha hb hb
    · simp at hn
    · rwa [sub_zero]
    · rwa [zero_sub, norm_neg]
    · simp at hn
  set W : Finset ι := NF.filter (fun n => d n ≠ 0) with hW
  have hsum_eq : ∑ n ∈ NF, d n = ∑ n ∈ W, d n := by
    rw [hW, Finset.sum_filter_ne_zero]
  set Wp : Finset ι := W.filter (fun n => 0 ≤ (z n).im) with hWp
  set Wm : Finset ι := W.filter (fun n => ¬ 0 ≤ (z n).im) with hWm
  have hWcard : (W.card : ℝ) ≤ 2 * C₂ * Real.log (q * (R + 4)) := by
    have hsplit : W.card = Wp.card + Wm.card := (Finset.card_filter_add_card_filter_not _).symm
    have hnear : ∀ n ∈ W, |(|(z n).im| - c0)| < 1 := by
      intro n hn
      obtain ⟨h1, h2⟩ := hdz n (Finset.mem_filter.mp hn).2
      rw [abs_lt]
      constructor
      · have : min R T ≥ c0 - 1 / 2 := by
          rcases le_total R T with h | h
          · rw [min_eq_left h, hc0]; linarith
          · rw [min_eq_right h, hc0]; linarith
        linarith
      · have : max R T ≤ c0 + 1 / 2 := by
          rcases le_total R T with h | h
          · rw [max_eq_right h, hc0]; linarith
          · rw [max_eq_left h, hc0]; linarith
        linarith
    have hlog : Real.log (q * (|c0| + 2)) ≤ Real.log (q * (R + 4)) := by
      have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
      rw [abs_of_pos hc0pos]
      exact Real.log_le_log (mul_pos hq0 (by linarith)) (by
        have : c0 + 2 ≤ R + 4 := by rw [hc0]; linarith
        nlinarith)
    have hp := (hcnt c0).2 Wp (by
      intro n hn
      obtain ⟨hnW, h0⟩ := Finset.mem_filter.mp hn
      have := hnear n hnW
      rw [abs_of_nonneg h0] at this
      rwa [abs_sub_comm])
    have hm := (hcnt (-c0)).2 Wm (by
      intro n hn
      obtain ⟨hnW, h0⟩ := Finset.mem_filter.mp hn
      have := hnear n hnW
      rw [abs_of_neg (not_le.mp h0)] at this
      rw [show -c0 - (z n).im = -(z n).im - c0 by ring]
      exact this)
    rw [abs_neg] at hm
    have h1 : C₂ * Real.log (q * (|c0| + 2)) ≤ C₂ * Real.log (q * (R + 4)) :=
      mul_le_mul_of_nonneg_left hlog hC₂0
    rw [hsplit]
    push_cast
    linarith
  rw [hsum_eq]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun n _ => hdnorm n).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hR1 : 0 < R - 1 := by linarith
  calc (W.card : ℝ) * (x / (R - 1)) ≤ (2 * C₂ * Real.log (q * (R + 4))) * (x / (R - 1)) :=
        mul_le_mul_of_nonneg_right hWcard (by positivity)
    _ = 2 * C₂ * Real.log (q * (R + 4)) * x / (R - 1) := by ring

end Heights


/-! ### The sides of the rectangle -/

section Sides

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- The horizontal sides: a bound uniform in `k`, decaying like `1 / T`. -/
private lemma norm_integral_horizontal_le {KL : ℝ} (hKL0 : 0 ≤ KL)
    (hKL : ∀ s : ℂ, s.re ≤ -1 → (2 ≤ |s.im| ∨ ∃ k : ℕ, s.re = -2 * k) →
      LFunction χ s ≠ 0 ∧
      ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ KL * (-s.re + Real.log (|s.im| + 2) + 1))
    {x : ℝ} (hx : 1 < x) {M : ℝ} (hM0 : 0 ≤ M) {T τ : ℝ} (hT : 2 ≤ T) (hτ : |τ| = T)
    (hM : ∀ σ : ℝ, -3 / 2 ≤ σ → σ ≤ 2 →
      ‖deriv (LFunction χ) (σ + τ * I) / LFunction χ (σ + τ * I)‖ ≤ M)
    {k : ℕ} (hk : 1 ≤ k) :
    ‖∫ σ in (-(2 * k : ℝ))..(2 : ℝ), -(deriv (LFunction χ) (σ + τ * I) /
        LFunction χ (σ + τ * I)) * ((x : ℂ) ^ ((σ : ℂ) + τ * I) / ((σ : ℂ) + τ * I))‖ ≤
      x ^ 2 * ((M + KL * (Real.log (T + 2) + 3)) / Real.log x + KL / Real.log x ^ 2) / T := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx
  have hT0 : 0 < T := by linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set c' : ℝ := Real.log (T + 2) + 5 with hc'
  have hlog0 : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
  set a : ℝ := M + KL * c' with ha
  set g : ℝ → ℝ := fun σ => (a - KL * σ) * x ^ σ / T with hg
  set Φ : ℝ → ℝ := fun σ => x ^ σ * ((a - KL * σ) / Real.log x + KL / Real.log x ^ 2) / T
    with hΦ
  have hderiv : ∀ σ : ℝ, HasDerivAt Φ (g σ) σ := by
    intro σ
    have h1 : HasDerivAt (fun σ : ℝ => x ^ σ) (x ^ σ * Real.log x) σ :=
      (Real.hasStrictDerivAt_const_rpow hx0 σ).hasDerivAt
    have h2 : HasDerivAt (fun σ : ℝ => (a - KL * σ) / Real.log x + KL / Real.log x ^ 2)
        (-KL / Real.log x) σ := by
      have := (((hasDerivAt_id σ).const_mul KL).const_sub a).div_const (Real.log x)
      simpa using this.add_const (KL / Real.log x ^ 2)
    have h3 := (h1.mul h2).div_const T
    refine h3.congr_deriv ?_
    change _ = (a - KL * σ) * x ^ σ / T
    field_simp
    ring
  have hgc : Continuous g := by
    have : Continuous (fun σ : ℝ => x ^ σ) :=
      continuous_const.rpow continuous_id (fun _ => Or.inl hx0.ne')
    simp only [hg]
    fun_prop
  have hint : ∫ σ in (-(2 * k : ℝ))..(2 : ℝ), g σ = Φ 2 - Φ (-(2 * k : ℝ)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun σ _ => hderiv σ)
      (hgc.intervalIntegrable _ _)
  have hΦa : 0 ≤ Φ (-(2 * k : ℝ)) := by
    simp only [hΦ]
    have : 0 ≤ a - KL * -(2 * k : ℝ) := by
      have : 0 ≤ KL * c' := mul_nonneg hKL0 (by linarith)
      nlinarith
    positivity
  have hΦ2 : Φ 2 = x ^ 2 * ((M + KL * (Real.log (T + 2) + 3)) / Real.log x +
      KL / Real.log x ^ 2) / T := by
    simp only [hΦ, ha, hc']
    rw [show ((2 : ℝ) : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  have hle : ∀ σ ∈ Set.Ioc (-(2 * k : ℝ)) 2,
      ‖-(deriv (LFunction χ) (σ + τ * I) / LFunction χ (σ + τ * I)) *
        ((x : ℂ) ^ ((σ : ℂ) + τ * I) / ((σ : ℂ) + τ * I))‖ ≤ g σ := by
    rintro σ ⟨hσ1, hσ2⟩
    set s : ℂ := (σ : ℂ) + τ * I with hs
    have hsre : s.re = σ := by simp [hs]
    have hsim : s.im = τ := by simp [hs]
    have hsT : T ≤ ‖s‖ := by
      rw [← hτ, ← hsim]; exact Complex.abs_im_le_norm s
    have hxs : ‖(x : ℂ) ^ s‖ = x ^ σ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, hsre]
    have hxσ : 0 < x ^ σ := Real.rpow_pos_of_pos hx0 σ
    have hnorm : ‖-(deriv (LFunction χ) s / LFunction χ s) * ((x : ℂ) ^ s / s)‖ ≤
        ‖deriv (LFunction χ) s / LFunction χ s‖ * (x ^ σ / T) := by
      rw [norm_mul, norm_neg, norm_div ((x : ℂ) ^ s), hxs]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hxσ.le hT0 hsT) (norm_nonneg _)
    refine hnorm.trans ?_
    have hgσ : g σ = (M + KL * (c' - σ)) * (x ^ σ / T) := by
      simp only [hg, ha]; ring
    rw [hgσ]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have hc0 : 0 ≤ KL * (c' - σ) := mul_nonneg hKL0 (by linarith)
    by_cases hσ : -3 / 2 ≤ σ
    · have := hM σ hσ hσ2
      linarith
    · push Not at hσ
      have h := (hKL s (by rw [hsre]; linarith) (Or.inl (by rw [hsim, hτ]; exact hT))).2
      rw [hsre, hsim, hτ] at h
      have : KL * (-σ + Real.log (T + 2) + 1) ≤ KL * (c' - σ) :=
        mul_le_mul_of_nonneg_left (by linarith) hKL0
      linarith
  have hmain := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume)
    (by linarith) (Filter.Eventually.of_forall (fun σ hσ => hle σ hσ))
    (hgc.intervalIntegrable _ _)
  rw [hint, ← hΦ2] at *
  linarith

/-- The left side `Re s = -2k` contributes nothing in the limit `k → ∞`. -/
private lemma tendsto_integral_left_side {KL : ℝ} (hKL0 : 0 ≤ KL)
    (hKL : ∀ s : ℂ, s.re ≤ -1 → (2 ≤ |s.im| ∨ ∃ k : ℕ, s.re = -2 * k) →
      LFunction χ s ≠ 0 ∧
      ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ KL * (-s.re + Real.log (|s.im| + 2) + 1))
    {x : ℝ} (hx : 1 < x) {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun k : ℕ => ∫ t in (-T)..T,
      -(deriv (LFunction χ) (((-(2 * k : ℝ) : ℝ) : ℂ) + t * I) /
        LFunction χ (((-(2 * k : ℝ) : ℝ) : ℂ) + t * I)) *
        ((x : ℂ) ^ (((-(2 * k : ℝ) : ℝ) : ℂ) + t * I) / (((-(2 * k : ℝ) : ℝ) : ℂ) + t * I)))
      atTop (𝓝 0) := by
  have hx0 : 0 < x := by linarith
  set r : ℝ := (x ^ 2)⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  set c : ℝ := Real.log (T + 2) + 1 with hc
  have hc0 : 0 ≤ c := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ T + 2 by linarith); linarith
  set B : ℕ → ℝ := fun k => KL * ((2 * k + c) * r ^ k) * (2 * T) with hB
  have hBt : Tendsto B atTop (𝓝 0) := by
    have h1 := tendsto_self_mul_const_pow_of_lt_one hr0 hr1
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    have h3 : Tendsto (fun k : ℕ => (2 * k + c) * r ^ k) atTop (𝓝 0) := by
      have := (h1.const_mul 2).add (h2.const_mul c)
      simp only [mul_zero, add_zero] at this
      refine this.congr fun k => ?_
      ring
    have := (h3.const_mul KL).mul_const (2 * T)
    simpa [hB] using this
  refine squeeze_zero_norm' ?_ hBt
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hbound : ∀ t ∈ Set.uIoc (-T) T,
      ‖-(deriv (LFunction χ) (((-(2 * k : ℝ) : ℝ) : ℂ) + t * I) /
        LFunction χ (((-(2 * k : ℝ) : ℝ) : ℂ) + t * I)) *
        ((x : ℂ) ^ (((-(2 * k : ℝ) : ℝ) : ℂ) + t * I) /
          (((-(2 * k : ℝ) : ℝ) : ℂ) + t * I))‖ ≤ KL * ((2 * k + c) * r ^ k) := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    have htT : |t| ≤ T := abs_le.mpr ⟨ht.1.le, ht.2⟩
    set s : ℂ := (((-(2 * k : ℝ) : ℝ) : ℂ) + t * I) with hs
    have hsre : s.re = -(2 * k) := by simp [hs]
    have hsim : s.im = t := by simp [hs]
    have h1s : 1 ≤ ‖s‖ := by
      calc (1 : ℝ) ≤ |s.re| := by rw [hsre, abs_neg, abs_of_pos (by linarith)]; linarith
        _ ≤ ‖s‖ := Complex.abs_re_le_norm s
    have hxs : ‖(x : ℂ) ^ s‖ = r ^ k := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, hsre, hr, inv_pow, ← pow_mul,
        Real.rpow_neg hx0.le]
      congr 1
      rw [← Real.rpow_natCast]
      push_cast
      ring_nf
    have h := (hKL s (by rw [hsre]; linarith) (Or.inr ⟨k, by rw [hsre]; ring⟩)).2
    rw [hsre, hsim] at h
    have hlt : Real.log (|t| + 2) ≤ Real.log (T + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have hL : ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ KL * (2 * k + c) := by
      refine h.trans (mul_le_mul_of_nonneg_left ?_ hKL0)
      rw [hc]; linarith
    rw [norm_mul, norm_neg, norm_div ((x : ℂ) ^ s), hxs]
    have hrk : 0 ≤ r ^ k := pow_nonneg hr0 k
    have : r ^ k / ‖s‖ ≤ r ^ k := div_le_self hrk h1s
    calc _ ≤ KL * (2 * k + c) * (r ^ k / ‖s‖) :=
          mul_le_mul_of_nonneg_right hL (by positivity)
      _ ≤ KL * (2 * k + c) * r ^ k :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = KL * ((2 * k + c) * r ^ k) := by ring
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [show |T - -T| = 2 * T by rw [abs_of_nonneg (by linarith)]; ring] at this
  simpa [hB] using this

/-- The sum over the trivial zeros: `∑_{m < k} x^{-(2m+1)}/(2m+1)` converges. -/
private lemma tendsto_sum_cpow_neg_odd_div {x : ℝ} (hx : 1 < x) :
    Tendsto (fun k : ℕ => ∑ m ∈ Finset.range k,
        (x : ℂ) ^ (-(2 * (m : ℂ) + 1)) / (2 * (m : ℂ) + 1))
      atTop (𝓝 (((∑' m : ℕ, x ^ (-(2 * (m : ℤ) + 1)) / (2 * m + 1) : ℝ) : ℂ))) := by
  have hx0 : 0 < x := by linarith
  set a : ℕ → ℝ := fun m => x ^ (-(2 * (m : ℤ) + 1)) / (2 * m + 1) with ha
  have hxi0 : 0 ≤ x⁻¹ := by positivity
  have hxi1 : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
  have hzp : ∀ m : ℕ, x ^ (-(2 * (m : ℤ) + 1)) = x⁻¹ ^ (2 * m + 1) := by
    intro m
    rw [show -(2 * (m : ℤ) + 1) = -((2 * m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
      zpow_natCast, inv_pow]
  have ha0 : ∀ m, 0 ≤ a m := fun m => by
    simp only [ha, hzp]; positivity
  have hale : ∀ m, a m ≤ x⁻¹ ^ m := by
    intro m
    simp only [ha, hzp]
    have h1 : x⁻¹ ^ (2 * m + 1) ≤ x⁻¹ ^ m := pow_le_pow_of_le_one hxi0 hxi1.le (by omega)
    have h2 : (1 : ℝ) ≤ 2 * m + 1 := by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
    exact (div_le_self (by positivity) h2).trans h1
  have hsum : Summable a :=
    Summable.of_nonneg_of_le ha0 hale (summable_geometric_of_lt_one hxi0 hxi1)
  have h := (Complex.continuous_ofReal.tendsto _).comp hsum.hasSum.tendsto_sum_nat
  refine h.congr fun k => ?_
  simp only [Function.comp_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [ha]
  push_cast
  rw [← Complex.cpow_intCast]
  push_cast
  ring_nf

end Sides


/-! ### The explicit formula -/

section Formula

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- At a good height `T`, the zero sum is within `‖P(T) - ψ(x, χ)‖ + Hb(T)/π` of its limit,
where `P(T)` is the truncated Perron integral on `Re s = 2`. -/
private lemma norm_tsum_sub_le_of_good_height (hχ : χ.IsPrimitive) (hodd : χ (-1) = -1)
    {ι : Type u} (z : ι → ℂ) (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w)
    {KL : ℝ} (hKL0 : 0 ≤ KL)
    (hKL : ∀ s : ℂ, s.re ≤ -1 → (2 ≤ |s.im| ∨ ∃ k : ℕ, s.re = -2 * k) →
      LFunction χ s ≠ 0 ∧
      ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ KL * (-s.re + Real.log (|s.im| + 2) + 1))
    {x : ℝ} (hx : 1 < x) {M : ℝ} (hM0 : 0 ≤ M) {T : ℝ} (hT : 2 ≤ T)
    (hTz : ∀ n, |(z n).im| ≠ T)
    (hM : ∀ σ τ : ℝ, -3 / 2 ≤ σ → σ ≤ 2 → |τ| = T →
      ‖deriv (LFunction χ) (σ + τ * I) / LFunction χ (σ + τ * I)‖ ≤ M) :
    ‖∑' n, (if |(z n).im| < T then (x : ℂ) ^ z n / z n else 0) -
        (-(deriv (LFunction χ) 0 / LFunction χ 0) +
          ((∑' m : ℕ, x ^ (-(2 * (m : ℤ) + 1)) / (2 * m + 1) : ℝ) : ℂ) - χ.chebyshevPsi x)‖ ≤
      ‖(1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
          -(deriv (LFunction χ) ((2 : ℝ) + t * I) / LFunction χ ((2 : ℝ) + t * I)) *
            ((x : ℂ) ^ ((2 : ℝ) + t * I) / ((2 : ℝ) + t * I))) - χ.chebyshevPsi x‖ +
        x ^ 2 * ((M + KL * (Real.log (T + 2) + 3)) / Real.log x + KL / Real.log x ^ 2) / T /
          Real.pi := by
  set F : ℂ → ℂ := fun s => -(deriv (LFunction χ) s / LFunction χ s) * ((x : ℂ) ^ s / s)
    with hF
  set A := -(deriv (LFunction χ) 0 / LFunction χ 0) with hA
  set Sinf : ℂ := ((∑' m : ℕ, x ^ (-(2 * (m : ℤ) + 1)) / (2 * m + 1) : ℝ) : ℂ) with hSinf
  set ST := ∑' n, (if |(z n).im| < T then (x : ℂ) ^ z n / z n else 0) with hST
  set ψ := χ.chebyshevPsi x with hψ
  set P : ℂ := (1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T, F ((2 : ℝ) + t * I)) with hP
  set Hb : ℝ := x ^ 2 * ((M + KL * (Real.log (T + 2) + 3)) / Real.log x +
    KL / Real.log x ^ 2) / T with hHb
  set Sk : ℕ → ℂ := fun k =>
    ∑ m ∈ Finset.range k, (x : ℂ) ^ (-(2 * (m : ℂ) + 1)) / (2 * (m : ℂ) + 1) with hSk
  set Lk : ℕ → ℂ := fun k => ∫ t in (-T)..T, F (((-(2 * k : ℝ) : ℝ) : ℂ) + t * I) with hLk
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi' : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hTz' : ∀ ρ ∈ χ.nontrivialZeros, |ρ.im| ≠ T := by
    intro ρ hρ
    obtain ⟨n, rfl⟩ := exists_eq_of_card_eq_analyticOrderAt hχ (odd_facts hodd).1 hz hρ
    exact hTz n
  have hnorm2pi : ‖(1 / (2 * Real.pi * I) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_two,
      Complex.norm_real, Real.norm_of_nonneg hpi.le]
  -- the bound for every `k ≥ 1`
  have hk : ∀ k : ℕ, 1 ≤ k →
      ‖ST - (A + Sinf - ψ)‖ ≤
        ‖Sk k - Sinf‖ + ‖P - ψ‖ + Hb / Real.pi + ‖(1 / (2 * Real.pi * I)) * (I * Lk k)‖ := by
    intro k hk1
    have hrect := boundaryIntegral_neg_logDeriv_mul_cpow_div hχ hodd z hz hx hk1
      (by linarith) hTz'
    simp only [RectilinearRectangle.boundaryIntegral, RectilinearRectangle.ofBounds_first_re,
      RectilinearRectangle.ofBounds_first_im, RectilinearRectangle.ofBounds_second_re,
      RectilinearRectangle.ofBounds_second_im, smul_eq_mul] at hrect
    have htop := norm_integral_horizontal_le hKL0 hKL hx hM0 hT (abs_of_pos (by linarith))
      (fun σ h1 h2 => hM σ T h1 h2 (abs_of_pos (by linarith))) hk1
    have hbot := norm_integral_horizontal_le hKL0 hKL hx hM0 hT
      (by rw [abs_neg, abs_of_pos (by linarith)])
      (fun σ h1 h2 => hM σ (-T) h1 h2 (by rw [abs_neg, abs_of_pos (by linarith)])) hk1
    set Htop := ∫ σ in (-(2 * k : ℝ))..(2 : ℝ), F (σ + T * I) with hHtop
    set Hbot := ∫ σ in (-(2 * k : ℝ))..(2 : ℝ), F (σ + ((-T : ℝ) : ℂ) * I) with hHbot
    set Rint := ∫ t in (-T)..T, F ((2 : ℝ) + t * I) with hRint
    have hrect' : Hbot - Htop + I * Rint - I * Lk k = 2 * (Real.pi : ℂ) * I * (A - ST + Sk k) :=
      hrect
    have hc : (1 / (2 * Real.pi * I)) * I = (1 / (2 * Real.pi) : ℂ) := by field_simp
    have hX : A - ST + Sk k = (1 / (2 * Real.pi * I)) * (Hbot - Htop + I * Rint - I * Lk k) := by
      rw [hrect']; field_simp
    have hid : ST - (A + Sinf - ψ) = (Sk k - Sinf) - (P - ψ) -
        (1 / (2 * Real.pi * I)) * (Hbot - Htop) + (1 / (2 * Real.pi * I)) * (I * Lk k) := by
      rw [hP]
      linear_combination (-1 : ℂ) * hX - Rint * hc
    rw [hid]
    have hE : ‖(1 / (2 * Real.pi * I)) * (Hbot - Htop)‖ ≤ Hb / Real.pi := by
      rw [norm_mul, hnorm2pi]
      have := norm_sub_le Hbot Htop
      calc 1 / (2 * Real.pi) * ‖Hbot - Htop‖ ≤ 1 / (2 * Real.pi) * (Hb + Hb) :=
            mul_le_mul_of_nonneg_left (this.trans (add_le_add hbot htop)) (by positivity)
        _ = Hb / Real.pi := by field_simp; ring
    have t1 := norm_add_le ((Sk k - Sinf) - (P - ψ) - (1 / (2 * Real.pi * I)) * (Hbot - Htop))
      ((1 / (2 * Real.pi * I)) * (I * Lk k))
    have t2 := norm_sub_le ((Sk k - Sinf) - (P - ψ)) ((1 / (2 * Real.pi * I)) * (Hbot - Htop))
    have t3 := norm_sub_le (Sk k - Sinf) (P - ψ)
    linarith
  -- the limit `k → ∞`
  have hlim1 : Tendsto (fun k => ‖Sk k - Sinf‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).mp (tendsto_sum_cpow_neg_odd_div hx)
  have hlim2 : Tendsto (fun k => ‖(1 / (2 * Real.pi * I)) * (I * Lk k)‖) atTop (𝓝 0) := by
    have := (((tendsto_integral_left_side hKL0 hKL hx (T := T) (by linarith)).const_mul I).const_mul
      (1 / (2 * Real.pi * I))).norm
    simpa [hLk, hF] using this
  have hlim := (hlim1.add_const (‖P - ψ‖ + Hb / Real.pi)).add hlim2
  simp only [zero_add, add_zero] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop 1] with k hk1
  have := hk k hk1
  linarith

private lemma tendsto_log_pow_div (c : ℝ) (hc : 0 < c) (n : ℕ) :
    Tendsto (fun R : ℝ => Real.log (c * (R + 4)) ^ n / (R - 1)) atTop (𝓝 0) := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop (1 / c) (-5) n (by positivity)
  have hg : Tendsto (fun R : ℝ => c * (R + 4)) atTop atTop :=
    (tendsto_atTop_add_const_right _ 4 tendsto_id).const_mul_atTop hc
  refine (h.comp hg).congr fun R => ?_
  simp only [Function.comp_apply]
  congr 1
  field_simp
  ring

private lemma tendsto_one_div_sub_one : Tendsto (fun R : ℝ => 1 / (R - 1)) atTop (𝓝 0) := by
  have h : Tendsto (fun R : ℝ => R - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_id.atTop_add (tendsto_const_nhds (x := (-1 : ℝ)))
  refine h.inv_tendsto_atTop.congr fun R => ?_
  simp [one_div]

/-- **The explicit formula for `ψ(x, χ)`, `χ` odd.** For a primitive odd Dirichlet character `χ`
modulo `q`, a family `z` listing the zeros of `ξ(s, χ)` with multiplicity (the nontrivial zeros
`ρ = β + iγ` of `L(s, χ)`), and real `x > 1` not a prime power,
`∑_{|γ| < R} x^ρ/ρ → -L'(0, χ)/L(0, χ) + ∑_{m ≥ 0} x^{-(2m+1)}/(2m+1) - ψ(x, χ)` as `R → ∞`.
Each truncated sum has finite support. -/
theorem tendsto_tsum_cpow_div_zeros_explicit_formula_of_odd (hχ : χ.IsPrimitive) (hodd : χ.Odd)
    {ι : Type u} (z : ι → ℂ) (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w)
    {x : ℝ} (hx : 1 < x) (hpp : ∀ n : ℕ, (n : ℝ) = x → ¬ IsPrimePow n) :
    Tendsto (fun R : ℝ => ∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0)) atTop
      (𝓝 (-(deriv (LFunction χ) 0 / LFunction χ 0) +
        ((∑' m : ℕ, x ^ (-(2 * (m : ℤ) + 1)) / (2 * m + 1) : ℝ) : ℂ) - χ.chebyshevPsi x)) := by
  have hodd' : χ (-1) = -1 := hodd
  have hχ1 := (odd_facts hodd').1
  obtain ⟨KL, hKL0, hKL⟩ := exists_norm_logDeriv_le_left hχ hodd'
  obtain ⟨Kg, hKg0, hgood⟩ := exists_good_height hχ hχ1 z hz
  obtain ⟨Cw, hCw0, hwin⟩ := exists_norm_tsum_sub_tsum_le hχ hχ1 z hz hx
  have hPer := tendsto_truncated_integral_chebyshevPsi χ hx hpp (c := 2) (by norm_num)
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  set V : ℂ := -(deriv (LFunction χ) 0 / LFunction χ 0) +
    ((∑' m : ℕ, x ^ (-(2 * (m : ℤ) + 1)) / (2 * m + 1) : ℝ) : ℂ) - χ.chebyshevPsi x with hV
  -- the error terms
  set hb : ℝ → ℝ := fun R => x ^ 2 * ((Kg * Real.log (q * (R + 4)) ^ 2 +
      KL * (Real.log (R + 3) + 3)) / Real.log x + KL / Real.log x ^ 2) / (R - 1) / Real.pi
    with hhb
  set zw : ℝ → ℝ := fun R => Cw * Real.log (q * (R + 4)) * x / (R - 1) with hzw
  have hhbt : Tendsto hb atTop (𝓝 0) := by
    have h1 := tendsto_log_pow_div q hq0 2
    have h2 : Tendsto (fun R : ℝ => Real.log (R + 3) / (R - 1)) atTop (𝓝 0) := by
      have h := Real.tendsto_pow_log_div_mul_add_atTop 1 (-4) 1 one_ne_zero
      have hg : Tendsto (fun R : ℝ => R + 3) atTop atTop :=
        tendsto_atTop_add_const_right _ 3 tendsto_id
      refine (h.comp hg).congr fun R => ?_
      simp only [Function.comp_apply, pow_one, one_mul]
      congr 1
      ring
    have h3 := tendsto_one_div_sub_one
    have := ((((h1.const_mul Kg).add ((h2.add (h3.const_mul 3)).const_mul KL)).const_mul
      (x ^ 2 / Real.log x / Real.pi)).add (h3.const_mul (x ^ 2 * (KL / Real.log x ^ 2) /
        Real.pi)))
    simp only [mul_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
    have hR1 : R - 1 ≠ 0 := by linarith
    simp only [hhb]
    field_simp
  have hzwt : Tendsto zw atTop (𝓝 0) := by
    have := (tendsto_log_pow_div q hq0 1).const_mul (Cw * x)
    simp only [mul_zero, pow_one] at this
    refine this.congr fun R => ?_
    simp only [hzw]
    ring
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    ((tendsto_iff_norm_sub_tendsto_zero.mp hPer).eventually (gt_mem_nhds hε3))
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hhbt.eventually (gt_mem_nhds hε3))
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.mp (hzwt.eventually (gt_mem_nhds hε3))
  refine ⟨max (max 3 (N₁ + 1)) (max N₂ N₃), fun R hR => ?_⟩
  have hR3 : 3 ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hRN₁ : N₁ + 1 ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hRN₂ : N₂ ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hR
  have hRN₃ : N₃ ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hR
  obtain ⟨T, hTR, hT2, hTz, hM⟩ := hgood R hR3
  have hTR' := abs_le.mp hTR
  have hM0 : 0 ≤ Kg * Real.log (q * (R + 4)) ^ 2 := by positivity
  have hat := norm_tsum_sub_le_of_good_height hχ hodd' z hz hKL0 hKL hx hM0 hT2 hTz hM
  have hw := hwin R T hR3 hTR
  have h1 := hN₁ T (by linarith)
  have h2 := hN₂ R hRN₂
  have h3 := hN₃ R hRN₃
  -- compare the error at `T` with `hb R`
  have hHb : x ^ 2 * ((Kg * Real.log (q * (R + 4)) ^ 2 + KL * (Real.log (T + 2) + 3)) /
      Real.log x + KL / Real.log x ^ 2) / T / Real.pi ≤ hb R := by
    simp only [hhb]
    have hlog : Real.log (T + 2) ≤ Real.log (R + 3) :=
      Real.log_le_log (by linarith) (by linarith)
    have hnum : x ^ 2 * ((Kg * Real.log (q * (R + 4)) ^ 2 + KL * (Real.log (T + 2) + 3)) /
        Real.log x + KL / Real.log x ^ 2) ≤ x ^ 2 * ((Kg * Real.log (q * (R + 4)) ^ 2 +
        KL * (Real.log (R + 3) + 3)) / Real.log x + KL / Real.log x ^ 2) := by
      gcongr
    have hpos : 0 ≤ x ^ 2 * ((Kg * Real.log (q * (R + 4)) ^ 2 + KL * (Real.log (T + 2) + 3)) /
        Real.log x + KL / Real.log x ^ 2) := by
      have : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
      positivity
    have hposR : 0 ≤ x ^ 2 * ((Kg * Real.log (q * (R + 4)) ^ 2 + KL * (Real.log (R + 3) + 3)) /
        Real.log x + KL / Real.log x ^ 2) := by
      have : 0 ≤ Real.log (R + 3) := Real.log_nonneg (by linarith)
      positivity
    have hTR1 : R - 1 ≤ T := by linarith
    have hR1 : 0 < R - 1 := by linarith
    gcongr
  rw [dist_eq_norm]
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0))
    (∑' n, (if |(z n).im| < T then (x : ℂ) ^ z n / z n else 0)) V
  have hzwR : zw R = Cw * Real.log (q * (R + 4)) * x / (R - 1) := rfl
  have h1' : ‖(1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
      -(deriv (LFunction χ) ((2 : ℝ) + t * I) / LFunction χ ((2 : ℝ) + t * I)) *
        ((x : ℂ) ^ ((2 : ℝ) + t * I) / ((2 : ℝ) + t * I))) - χ.chebyshevPsi x‖ < ε / 3 := h1
  linarith

end Formula

end DirichletCharacter
