/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LSeries.DirichletLogDerivZeros
public import MathlibExt.NumberTheory.PrimeCounting.DirichletChebyshevPsi
import MathlibExt.NumberTheory.LSeries.DirichletLeftHalfPlane
import MathlibExt.NumberTheory.PrimeCounting.ExplicitFormulaDirichlet
import MathlibExt.NumberTheory.LSeries.RiemannZetaResidues
import MathlibExt.NumberTheory.LSeries.VerticalLine
import MathlibExt.Analysis.Complex.RectangleResidueDoublePole
import MathlibExt.Analysis.SpecialFunctions.Trigonometric.CotBound
import MathlibExt.Analysis.PerronKernel
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The explicit formula for `ψ(x, χ)`, `χ` even

For a primitive even nonprincipal Dirichlet character `χ` and `x > 1` not a prime power,
`ψ(x, χ) = -∑_ρ x^ρ/ρ - log x - b(χ) - ½ log (1 - x⁻²)`, where `ρ` runs over the nontrivial zeros of
`L(s, χ)` with multiplicity and `b(χ)` is the constant term of `L'/L(s, χ)` at `s = 0`. The zero sum
converges conditionally, as the limit of its truncations to `|Im ρ| < R`.

The proof integrates `-L'/L(s, χ) x^s / s` around the rectangle `[-U, 2] × [-T, T]` with `U` odd:
the residues are `-x^ρ/ρ` at the nontrivial zeros, `x^{-2m}/(2m)` at the trivial zeros `-2m`, and a
double pole at `0` (the trivial zero of `L(s, χ)` meets the pole of `x^s / s`) with residue
`-(log x + b(χ))`.

## Main statements

* `DirichletCharacter.tendsto_tsum_cpow_div_zeros_explicit_formula_of_even`: the explicit formula
  for `ψ(x, χ)`, `χ` even.
-/

@[expose] public section

universe u

open Complex Filter Topology Set ArithmeticFunction

namespace DirichletCharacter

section Even

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

private lemma ne_one_of_ne_one (hχ1 : χ ≠ 1) : q ≠ 1 := by
  rintro rfl
  exact hχ1 (level_one χ)

/-- `L(s, χ) = ξ(s, χ) q^{-s/2} π^{s/2} Γ(s/2)⁻¹` for even `χ ≠ 1`. -/
private lemma LFunction_eq_xi_mul_of_even (hχ1 : χ ≠ 1) (heven : χ.Even) (s : ℂ) :
    LFunction χ s = xi χ s *
      ((q : ℂ) ^ (-s / 2) * (Real.pi : ℂ) ^ (s / 2) * (Complex.Gamma (s / 2))⁻¹) := by
  rw [LFunction_eq_xi_mul_cofactor χ (ne_one_of_ne_one hχ1) (a := 0)
    (by rw [show χ (-1) = 1 from heven]; norm_num)
    (fun w => by rw [heven.gammaFactor_def]; simp) s]
  simp only [Complex.ofReal_zero, add_zero, neg_div, mul_assoc]

private lemma differentiable_cofactor (q : ℕ) [NeZero q] :
    Differentiable ℂ (fun s : ℂ =>
      (q : ℂ) ^ (-s / 2) * (Real.pi : ℂ) ^ (s / 2) * (Complex.Gamma (s / 2))⁻¹) := by
  simpa only [Complex.ofReal_zero, add_zero, neg_div, mul_assoc] using
    differentiable_xi_cofactor q 0

private lemma cofactor_ne_zero (q : ℕ) [NeZero q] {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(2 * (n : ℂ))) :
    (q : ℂ) ^ (-s / 2) * (Real.pi : ℂ) ^ (s / 2) * (Complex.Gamma (s / 2))⁻¹ ≠ 0 := by
  have h := xi_cofactor_ne_zero q 0 (s := s) fun n h => hs n (by
    rw [Complex.ofReal_zero, add_zero] at h; linear_combination 2 * h)
  simpa only [Complex.ofReal_zero, add_zero, neg_div, mul_assoc] using h

/-- Near a zero `p = -2n` of the gamma factor, `L(s, χ) = (s - p) E(s)` with `E(p) ≠ 0`. -/
private lemma exists_LFunction_eventually_eq_mul (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    (heven : χ.Even) (n : ℕ) :
    ∃ E : ℂ → ℂ, AnalyticAt ℂ E (-(2 * (n : ℂ))) ∧ E (-(2 * (n : ℂ))) ≠ 0 ∧
      ∀ᶠ s in 𝓝 (-(2 * (n : ℂ))), LFunction χ s = (s - (-(2 * (n : ℂ)))) * E s := by
  set p : ℂ := -(2 * (n : ℂ)) with hpdef
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hord : analyticOrderAt (fun s => (Complex.Gamma s)⁻¹) (-(n : ℂ)) = (1 : ℕ) := by
    rw [Complex.analyticOrderAt_inv_Gamma_neg_natCast]; simp
  obtain ⟨G, hGa, hG0, hGe⟩ :=
    (Complex.differentiable_one_div_Gamma.analyticAt (-(n : ℂ))).analyticOrderAt_eq_natCast.mp
      hord
  have ht : Tendsto (fun s : ℂ => s / 2) (𝓝 p) (𝓝 (-(n : ℂ))) := by
    have h : -(n : ℂ) = p / 2 := by rw [hpdef]; ring
    rw [h]
    exact (continuous_id.div_const (2 : ℂ)).tendsto p
  have hGe' := ht.eventually hGe
  have hGa' := ht.eventually hGa.eventually_analyticAt
  have hξd := differentiable_xi hχ1
  refine ⟨fun s => xi χ s * ((q : ℂ) ^ (-s / 2) * (Real.pi : ℂ) ^ (s / 2) * (G (s / 2) / 2)),
    ?_, ?_, ?_⟩
  · rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [hGa'] with s hsa
    have h1 : DifferentiableAt ℂ (fun s : ℂ => (q : ℂ) ^ (-s / 2)) s :=
      ((differentiableAt_id.neg).div_const (2 : ℂ)).const_cpow (Or.inl hq)
    have h2 : DifferentiableAt ℂ (fun s : ℂ => (Real.pi : ℂ) ^ (s / 2)) s :=
      (differentiableAt_id.div_const (2 : ℂ)).const_cpow (Or.inl hpi)
    have h3 : DifferentiableAt ℂ (fun s : ℂ => G (s / 2)) s :=
      hsa.differentiableAt.comp s (differentiableAt_id.div_const (2 : ℂ))
    exact (hξd s).mul ((h1.mul h2).mul (h3.div_const 2))
  · have hxi : xi χ p ≠ 0 := by
      rw [Ne, xi_eq_zero_iff hχ hχ1]
      intro h
      rcases Nat.eq_zero_or_pos n with hn | hn
      · exact h.2.2.2 (by rw [hpdef, hn]; simp)
      · have h0 := h.2.1
        rw [hpdef] at h0
        simp at h0
        have : (0 : ℝ) < n := by exact_mod_cast hn
        linarith
    have hGp : G (p / 2) ≠ 0 := by
      rw [show p / 2 = -(n : ℂ) by rw [hpdef]; ring]; exact hG0
    refine mul_ne_zero hxi (mul_ne_zero (mul_ne_zero ?_ ?_) (div_ne_zero hGp two_ne_zero))
    · simp [Complex.cpow_eq_zero_iff, hq]
    · simp [Complex.cpow_eq_zero_iff, hpi]
  · filter_upwards [hGe'] with s hse
    rw [LFunction_eq_xi_mul_of_even hχ1 heven s, hse, pow_one, smul_eq_mul, hpdef]
    ring

/-- The zeros of `L(s, χ)`: the nontrivial zeros and the trivial zeros `-2n`. -/
private lemma mem_nontrivialZeros_or_of_LFunction_eq_zero (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    (heven : χ.Even) {s : ℂ} (hs : LFunction χ s = 0) :
    s ∈ χ.nontrivialZeros ∨ ∃ n : ℕ, s = -(2 * (n : ℂ)) := by
  rw [LFunction_eq_xi_mul_of_even hχ1 heven s, mul_eq_zero] at hs
  rcases hs with h | h
  · exact Or.inl ((xi_eq_zero_iff hχ hχ1 s).mp h)
  · right
    by_contra hne
    push Not at hne
    exact cofactor_ne_zero q hne h

/-- **The residue theorem for `-L'/L(s, χ) x^s / s`** on the rectangle `[-U, 2] × [-R, R]`,
`U = 2j + 1`. -/
private lemma boundaryIntegral_eq (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (heven : χ.Even)
    {ι : Type*} (z : ι → ℂ) (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w)
    {x : ℝ} (hx : 1 < x) (j : ℕ) {R : ℝ} (hR : 0 < R) (hRz : ∀ n, |(z n).im| ≠ R)
    (F : ℂ → ℂ) (hF : ∀ s, F s = -(deriv (LFunction χ) s / LFunction χ s) * ((x : ℂ) ^ s / s)) :
    (RectilinearRectangle.ofBounds (-((2 * j + 1 : ℕ) : ℝ)) 2 (-R) R).boundaryIntegral F =
      2 * (Real.pi : ℂ) * I *
        (-(∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0)) -
          ((Real.log x : ℂ) + χ.logDerivConstAtZero) +
          ∑ m ∈ Finset.Icc 1 j, (x : ℂ) ^ (-(2 * (m : ℂ))) / (2 * (m : ℂ))) := by
  classical
  set L := LFunction χ with hLdef
  set U : ℕ := 2 * j + 1 with hU
  have hx0 : 0 < x := by linarith
  have hUpos : (0 : ℝ) < U := by positivity
  have hξd := differentiable_xi hχ1
  have hLd : Differentiable ℂ L := differentiable_LFunction hχ1
  have hord_top := analyticOrderAt_xi_ne_top hχ hχ1
  have hmem_of := mem_nontrivialZeros_of_card_eq_analyticOrderAt hχ hχ1 hz
  have hfib := finite_of_card_eq_analyticOrderAt hχ hχ1 hz
  have hNfin := finite_setOf_abs_im_lt_of_card_eq_analyticOrderAt hχ hχ1 hz R
  set NF := hNfin.toFinset with hNF
  set Z : Finset ℂ := NF.image z with hZ
  set T : Finset ℂ := (Finset.Icc 1 j).image (fun m : ℕ => -(2 * (m : ℂ))) with hT
  set S : Finset ℂ := insert 0 (Z ∪ T) with hS
  have hZmem : ∀ p, p ∈ Z ↔ p ∈ χ.nontrivialZeros ∧ |p.im| < R := by
    intro p; constructor
    · intro hp
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨hmem_of n, by simpa [NF] using hn⟩
    · rintro ⟨hp, hpR⟩
      obtain ⟨n, hn⟩ := exists_eq_of_card_eq_analyticOrderAt hχ hχ1 hz hp
      exact Finset.mem_image.mpr ⟨n, by simp [NF, hn, hpR], hn⟩
  have hRz' : ∀ ρ ∈ χ.nontrivialZeros, |ρ.im| ≠ R := by
    intro ρ hρ
    obtain ⟨n, rfl⟩ := exists_eq_of_card_eq_analyticOrderAt hχ hχ1 hz hρ
    exact hRz n
  have hTmem : ∀ p, p ∈ T ↔ ∃ m : ℕ, 0 < m ∧ m ≤ j ∧ p = -(2 * (m : ℂ)) := by
    intro p
    simp only [T, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨m, ⟨h1, h2⟩, rfl⟩; exact ⟨m, h1, h2, rfl⟩
    · rintro ⟨m, h1, h2, rfl⟩; exact ⟨m, ⟨h1, h2⟩, rfl⟩
  have hZprop : ∀ p ∈ Z, p ≠ 0 ∧ 0 ≤ p.re ∧ p.re ≤ 1 ∧ |p.im| < R := by
    intro p hp
    obtain ⟨hnt, hpR⟩ := (hZmem p).mp hp
    exact ⟨hnt.2.2.2, hnt.2.1, hnt.2.2.1, hpR⟩
  have hTprop : ∀ p ∈ T, p.re < 0 ∧ -(U : ℝ) < p.re ∧ p.im = 0 := by
    intro p hp
    obtain ⟨m, h1, h2, rfl⟩ := (hTmem p).mp hp
    have h1' : (0 : ℝ) < m := by exact_mod_cast h1
    have h2' : (m : ℝ) ≤ j := by exact_mod_cast h2
    simp only [hU]
    push_cast
    simp
    constructor <;> linarith
  -- the residue at `0`
  obtain ⟨E₀, hE₀a, hE₀0, hE₀e⟩ := exists_LFunction_eventually_eq_mul hχ hχ1 heven 0
  simp only [Nat.cast_zero, mul_zero, neg_zero] at hE₀a hE₀0 hE₀e
  have hE₀e' : ∀ᶠ s in 𝓝[≠] (0 : ℂ), L s = s * E₀ s := by
    filter_upwards [nhdsWithin_le_nhds hE₀e] with s hs
    rw [hLdef, hs, sub_zero]
  have hb : χ.logDerivConstAtZero = logDeriv E₀ 0 :=
    logDerivConstAtZero_eq_logDeriv hE₀a hE₀0 hE₀e'
  rw [logDeriv_apply] at hb
  -- the residues
  let mo : ℂ → ℕ := fun p => (analyticOrderAt (xi χ) p).toNat
  let kf : ℂ → ℤ := fun p => if p ∈ Z then (mo p : ℤ) else 1
  let r : ℂ → ℂ := fun p =>
    if p = 0 then -(Real.log x : ℂ) - χ.logDerivConstAtZero else -(kf p : ℂ) * ((x : ℂ) ^ p / p)
  let d : ℂ → ℂ := fun p => if p = 0 then -1 else 0
  have h0Z : (0 : ℂ) ∉ Z := fun h => (hZprop 0 h).1 rfl
  have h0T : (0 : ℂ) ∉ T := fun h => by have := (hTprop 0 h).1; simp at this
  have hZT : ∀ p ∈ T, p ∉ Z := fun p hp hpZ => by
    linarith [(hTprop p hp).1, (hZprop p hpZ).2.1]
  have hloc : ∀ p ∈ S, ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ p ∧
      ∀ᶠ s in 𝓝[≠] p, F s = r p / (s - p) + d p / (s - p) ^ 2 + φ s := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · obtain ⟨φ, h1, h2⟩ :=
        Complex.exists_eventually_neg_logDeriv_mul_cpow_div_eq_of_eq_mul hx0 hE₀a hE₀0 hE₀e'
      refine ⟨φ, h1, ?_⟩
      have hr : r 0 = -(Real.log x : ℂ) - deriv E₀ 0 / E₀ 0 := by simp [r, hb]
      have hd : d 0 = -1 := by simp [d]
      filter_upwards [h2] with s hs
      rw [hF, hs, hr, hd]
    rcases Finset.mem_union.mp hp with hpZ | hpT
    · obtain ⟨hp0, hpre, -⟩ := hZprop p hpZ
      have hm : analyticOrderAt (xi χ) p = (mo p : ℕ) :=
        (ENat.natCast_toNat (hord_top p)).symm
      obtain ⟨ξ₁, hξ₁a, hξ₁0, hξ₁e⟩ := (hξd.analyticAt p).analyticOrderAt_eq_natCast.mp hm
      have hEp : (q : ℂ) ^ (-p / 2) * (Real.pi : ℂ) ^ (p / 2) * (Complex.Gamma (p / 2))⁻¹ ≠ 0 := by
        apply cofactor_ne_zero q
        intro n hn
        rcases Nat.eq_zero_or_pos n with h | h
        · exact hp0 (by rw [hn, h]; simp)
        · have := congrArg Complex.re hn
          simp at this
          have : (0 : ℝ) < n := by exact_mod_cast h
          linarith
      have hEa : AnalyticAt ℂ (fun s => ξ₁ s * ((q : ℂ) ^ (-s / 2) * (Real.pi : ℂ) ^ (s / 2) *
          (Complex.Gamma (s / 2))⁻¹)) p :=
        hξ₁a.mul ((differentiable_cofactor q).analyticAt p)
      have hLf : ∀ᶠ s in 𝓝[≠] p, L s = (s - p) ^ ((mo p : ℕ) : ℤ) *
          (ξ₁ s * ((q : ℂ) ^ (-s / 2) * (Real.pi : ℂ) ^ (s / 2) * (Complex.Gamma (s / 2))⁻¹)) := by
        filter_upwards [nhdsWithin_le_nhds hξ₁e] with s hs
        rw [hLdef, LFunction_eq_xi_mul_of_even hχ1 heven s, hs, zpow_natCast, smul_eq_mul]
        ring
      obtain ⟨φ, h1, h2⟩ := Complex.exists_eventually_neg_logDeriv_mul_cpow_div_eq_of_zpow hx0 hp0
        hEa (mul_ne_zero hξ₁0 hEp) hLf
      refine ⟨φ, h1, ?_⟩
      have hr : r p = -(((mo p : ℕ) : ℤ) : ℂ) * ((x : ℂ) ^ p / p) := by
        simp [r, kf, hp0, hpZ]
      have hd : d p = 0 := by simp [d, hp0]
      filter_upwards [h2] with s hs
      rw [hF, hs, hr, hd, zero_div, add_zero]
    · obtain ⟨m, hm0, -, rfl⟩ := (hTmem p).mp hpT
      obtain ⟨E', hE'a, hE'0, hE'e⟩ := exists_LFunction_eventually_eq_mul hχ hχ1 heven m
      have hp0 : -(2 * (m : ℂ)) ≠ 0 := fun h => h0T (h ▸ hpT)
      have hLf : ∀ᶠ s in 𝓝[≠] (-(2 * (m : ℂ))),
          L s = (s - (-(2 * (m : ℂ)))) ^ (1 : ℤ) * E' s := by
        filter_upwards [nhdsWithin_le_nhds hE'e] with s hs
        rw [zpow_one]; exact hs
      obtain ⟨φ, h1, h2⟩ :=
        Complex.exists_eventually_neg_logDeriv_mul_cpow_div_eq_of_zpow hx0 hp0 hE'a hE'0 hLf
      refine ⟨φ, h1, ?_⟩
      have hr : r (-(2 * (m : ℂ))) = -(((1 : ℤ)) : ℂ) *
          ((x : ℂ) ^ (-(2 * (m : ℂ))) / (-(2 * (m : ℂ)))) := by
        simp only [r, kf, hp0, hZT _ hpT, ite_false]
      have hd : d (-(2 * (m : ℂ))) = 0 := by simp only [d, hp0, ite_false]
      filter_upwards [h2] with s hs
      rw [hF, hs, hr, hd, zero_div, add_zero]
  set rect := RectilinearRectangle.ofBounds (-(U : ℝ)) 2 (-R) R with hrect
  have hKre : ∀ s ∈ rect.carrier, -(U : ℝ) ≤ s.re ∧ s.re ≤ 2 ∧ -R ≤ s.im ∧ s.im ≤ R := by
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
    rw [show F = fun s => -(deriv L s / L s) * ((x : ℂ) ^ s / s) from funext hF]
    obtain ⟨k1, k2, k3, k4⟩ := hKre s hsK
    have hs0 : s ≠ 0 := fun h => hsS (by simp [S, h])
    have hLs : L s ≠ 0 := by
      intro h0
      rcases mem_nontrivialZeros_or_of_LFunction_eq_zero hχ hχ1 heven h0 with hnt | ⟨n, rfl⟩
      · have hIm : |s.im| < R := lt_of_le_of_ne (abs_le.mpr ⟨k3, k4⟩) (hRz' s hnt)
        exact hsS (by simp [S, (hZmem s).mpr ⟨hnt, hIm⟩])
      · rcases Nat.eq_zero_or_pos n with hn | hn
        · exact hs0 (by rw [hn]; simp)
        · have hle : (2 * n : ℝ) ≤ U := by simp at k1; linarith
          have hle' : 2 * n ≤ U := by exact_mod_cast hle
          have hT' : -(2 * (n : ℂ)) ∈ T := (hTmem _).mpr ⟨n, hn, by omega, rfl⟩
          exact hsS (by simp [S, hT'])
    have hLa : AnalyticAt ℂ L s := hLd.analyticAt s
    have hx0' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    exact ((hLa.deriv.differentiableAt.div hLa.differentiableAt hLs).neg).mul
      ((differentiableAt_id.const_cpow (Or.inl hx0')).div differentiableAt_id hs0)
  obtain ⟨g, hg, hfg⟩ := Complex.exists_differentiableOn_eq_add_sum_div_sub_add_div_sub_sq _ S r d
    F hloc (fun s hs h => (hdiff s hs h).differentiableWithinAt)
  have hin : ∀ p ∈ S, rect.first.re < p.re ∧ p.re < rect.second.re ∧ rect.first.im < p.im ∧
      p.im < rect.second.im := by
    intro p hp
    simp only [hrect, RectilinearRectangle.ofBounds_first_re,
      RectilinearRectangle.ofBounds_second_re, RectilinearRectangle.ofBounds_first_im,
      RectilinearRectangle.ofBounds_second_im]
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simp only [Complex.zero_re, Complex.zero_im]
      exact ⟨by linarith, by norm_num, by linarith, hR⟩
    rcases Finset.mem_union.mp hp with hpZ | hpT
    · obtain ⟨-, h1, h2, h3⟩ := hZprop p hpZ
      exact ⟨by linarith, by linarith, (abs_lt.mp h3).1, (abs_lt.mp h3).2⟩
    · obtain ⟨h1, h2, h3⟩ := hTprop p hpT
      exact ⟨h2, by linarith, by rw [h3]; linarith, by rw [h3]; exact hR⟩
  rw [RectilinearRectangle.boundaryIntegral_eq_two_pi_mul_I_mul_sum_of_double rect S r d F g hin
    hg hfg]
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
  have htsum : ∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0) =
      ∑ p ∈ Z, (mo p : ℂ) * ((x : ℂ) ^ p / p) := by
    rw [tsum_eq_sum (s := NF) (fun n hn => ite_eq_right (by simpa [NF] using hn))]
    rw [Finset.sum_congr rfl (fun n hn => ite_eq_left (by simpa [NF] using hn))]
    rw [Finset.sum_comp (fun p => (x : ℂ) ^ p / p) z]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hcard p hp, nsmul_eq_mul]
  have hinj : Set.InjOn (fun m : ℕ => -(2 * (m : ℂ))) (Finset.Icc 1 j : Set ℕ) := by
    intro a _ b _ h
    simp only [neg_inj, mul_eq_mul_left_iff, two_ne_zero, or_false, Nat.cast_inj] at h
    exact h
  have hdisj : Disjoint Z T := Finset.disjoint_right.mpr hZT
  rw [Finset.sum_insert (by simp [h0Z, h0T]), Finset.sum_union hdisj, htsum,
    Finset.sum_image hinj]
  have hr0 : r 0 = -(Real.log x : ℂ) - χ.logDerivConstAtZero := by simp [r]
  have hrZ : ∑ p ∈ Z, r p = -∑ p ∈ Z, (mo p : ℂ) * ((x : ℂ) ^ p / p) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hp0, -⟩ := hZprop p hp
    simp [r, kf, hp0, hp]
  have hrT : ∑ m ∈ Finset.Icc 1 j, r (-(2 * (m : ℂ))) =
      ∑ m ∈ Finset.Icc 1 j, (x : ℂ) ^ (-(2 * (m : ℂ))) / (2 * (m : ℂ)) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hpT : -(2 * (m : ℂ)) ∈ T := Finset.mem_image.mpr ⟨m, hm, rfl⟩
    have hp0 : -(2 * (m : ℂ)) ≠ 0 := fun h => h0T (h ▸ hpT)
    simp only [r, kf, hp0, hZT _ hpT, ite_false]
    rw [div_neg]
    push_cast
    ring
  rw [hr0, hrZ, hrT]
  ring

/-- The Perron error tends to `0` as the height grows. -/
private lemma tendsto_perron_error (x c : ℝ) :
    Tendsto (fun R : ℝ => 1 / Real.pi * ∑' n : ℕ, Λ n * (x / n) ^ c / (R * |Real.log (x / n)|))
      atTop (𝓝 0) := by
  have h : ∀ R : ℝ, 1 / Real.pi * ∑' n : ℕ, Λ n * (x / n) ^ c / (R * |Real.log (x / n)|) =
      R⁻¹ * (1 / Real.pi * ∑' n : ℕ, Λ n * (x / n) ^ c / |Real.log (x / n)|) := by
    intro R
    have e : ∀ n : ℕ, Λ n * (x / n) ^ c / (R * |Real.log (x / n)|) =
        R⁻¹ * (Λ n * (x / n) ^ c / |Real.log (x / n)|) := fun n => by
      rw [mul_comm R, ← div_div, div_eq_inv_mul]
    simp only [e, tsum_mul_left]
    ring
  simp only [h]
  simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).mul_const
    (1 / Real.pi * ∑' n : ℕ, Λ n * (x / n) ^ c / |Real.log (x / n)|)

/-! ### Good heights -/

/-- **Good heights.** Every `R ≥ 3` is within `1` of a height `T` that is not the ordinate of a
zero and on which `L'/L(σ ± iT, χ) = O(log² (q (R + 3)))` for `-1 ≤ σ ≤ 2`. -/
private lemma exists_good_height (hχ : χ.IsPrimitive) {ι : Type u} (z : ι → ℂ)
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w) :
    ∃ B : ℝ, ∀ R : ℝ, 3 ≤ R → ∃ T : ℝ, |T - R| ≤ 1 ∧ (∀ n, |(z n).im| ≠ T) ∧
      ∀ τ : ℝ, (τ = T ∨ τ = -T) → ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
        ‖deriv (LFunction χ) (σ + τ * I) / LFunction χ (σ + τ * I)‖ ≤
          B * Real.log (q * (R + 3)) ^ 2 := by
  obtain ⟨K, hK⟩ := exists_good_height_norm_logDeriv_LFunction_le.{u}
  refine ⟨K, fun R hR => ?_⟩
  obtain ⟨T, hRT, hTR, hTz, hT⟩ := hK χ hχ z hz R (by linarith)
  refine ⟨T, by rw [abs_le]; constructor <;> linarith, hTz, fun τ hτ σ hσ1 hσ2 => ?_⟩
  rcases hτ with rfl | rfl
  · exact (hT σ hσ1 hσ2).1
  · have := (hT σ hσ1 hσ2).2
    simpa [sub_eq_add_neg] using this

/-! ### The sides of the rectangle -/

/-- `L'/L(s, χ)` on `Re s ≤ -1`, where `|cot (πs/2)| ≤ 2`: `‖L'/L(s, χ)‖ ≤ C + log (‖s‖ + 2)`. -/
private lemma exists_norm_logDeriv_le_left (hχ : χ.IsPrimitive) (heven : χ.Even) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re ≤ -1 → Complex.sin (Real.pi * s / 2) ≠ 0 →
      ‖Complex.cos (Real.pi * s / 2) / Complex.sin (Real.pi * s / 2)‖ ≤ 2 →
      ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ C + Real.log (‖s‖ + 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_logDeriv_LFunction_le_of_re_le_neg_one
  have hlq : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hinv : χ⁻¹.Even := (inv_apply_neg_one χ).trans heven
  refine ⟨Real.log q + C, by positivity, fun s hs hsin hcot => ?_⟩
  have e : (Real.pi : ℂ) * ((s + ((0 : ℝ) : ℂ)) / 2) = Real.pi * s / 2 := by push_cast; ring
  rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hsin)] at hcot
  have h := (hC χ hχ 0 (fun w => by rw [heven.gammaFactor_def]; simp)
    (fun w => by rw [hinv.gammaFactor_def]; simp) le_rfl zero_le_one s hs (by rw [e]; exact hsin)
    (by rw [e]; exact hcot)).2
  linarith

/-- `|cot(πs/2)| ≤ 2` away from the real axis. -/
private lemma norm_cot_le_of_one_le_abs_im {s : ℂ} (hs : 1 ≤ |s.im|) :
    Complex.sin (Real.pi * s / 2) ≠ 0 ∧
      ‖Complex.cos (Real.pi * s / 2) / Complex.sin (Real.pi * s / 2)‖ ≤ 2 := by
  have hb : 1 ≤ |((Real.pi : ℂ) * s / 2).im| := by
    have : ((Real.pi : ℂ) * s / 2).im = Real.pi * s.im / 2 := by simp
    rw [this, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]
    nlinarith [Real.two_le_pi, abs_nonneg s.im]
  have h0 := Complex.sin_ne_zero_of_one_le_abs_im hb
  refine ⟨h0, ?_⟩
  rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr h0)]
  exact Complex.norm_cos_le_two_mul_norm_sin_of_one_le_abs_im hb

/-- `|cot(πs/2)| ≤ 1` on the vertical lines `Re s = -(2j + 1)`. -/
private lemma norm_cot_le_of_re_eq_odd (j : ℕ) {s : ℂ} (hs : s.re = -(2 * (j : ℝ) + 1)) :
    Complex.sin (Real.pi * s / 2) ≠ 0 ∧
      ‖Complex.cos (Real.pi * s / 2) / Complex.sin (Real.pi * s / 2)‖ ≤ 1 := by
  have hre : Real.cos ((Real.pi : ℂ) * s / 2).re = 0 := by
    have : ((Real.pi : ℂ) * s / 2).re = Real.pi * s.re / 2 := by simp
    rw [this, Real.cos_eq_zero_iff]
    refine ⟨-((j : ℤ) + 1), ?_⟩
    rw [hs]
    push_cast
    ring
  have h0 := Complex.sin_ne_zero_of_cos_re_eq_zero hre
  refine ⟨h0, ?_⟩
  rw [norm_div, div_le_one (norm_pos_iff.mpr h0)]
  exact Complex.norm_cos_le_norm_sin_of_cos_re_eq_zero hre

private lemma differentiableAt_integrand (hχ1 : χ ≠ 1) {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hLs : LFunction χ s ≠ 0) (hs0 : s ≠ 0) :
    DifferentiableAt ℂ (fun s => -(deriv (LFunction χ) s / LFunction χ s) * ((x : ℂ) ^ s / s))
      s := by
  have hLa : AnalyticAt ℂ (LFunction χ) s := (differentiable_LFunction hχ1).analyticAt s
  have hx0' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  exact ((hLa.deriv.differentiableAt.div hLa.differentiableAt hLs).neg).mul
    ((differentiableAt_id.const_cpow (Or.inl hx0')).div differentiableAt_id hs0)

private lemma norm_integrand (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ‖-(deriv (LFunction χ) s / LFunction χ s) * ((x : ℂ) ^ s / s)‖ =
      ‖deriv (LFunction χ) s / LFunction χ s‖ * (x ^ s.re / ‖s‖) := by
  rw [norm_mul, norm_neg, norm_div ((x : ℂ) ^ s) s, Complex.norm_cpow_eq_rpow_re_of_pos hx]

/-- The horizontal side at height `τ`, `|τ| = T`. -/
private lemma norm_integral_horizontal_le (hχ1 : χ ≠ 1) {x : ℝ} (hx : 1 < x) (U : ℕ) (hU : 1 ≤ U)
    {T τ : ℝ} (hT : 0 < T) (hτ : |τ| = T) (hL0 : ∀ σ : ℝ, LFunction χ (σ + τ * I) ≠ 0)
    {M K : ℝ}
    (hM : ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
      ‖deriv (LFunction χ) (σ + τ * I) / LFunction χ (σ + τ * I)‖ ≤ M)
    (hK : ∀ σ : ℝ, -(U : ℝ) ≤ σ → σ ≤ -1 →
      ‖deriv (LFunction χ) (σ + τ * I) / LFunction χ (σ + τ * I)‖ ≤ K)
    (F : ℂ → ℂ) (hF : ∀ s, F s = -(deriv (LFunction χ) s / LFunction χ s) * ((x : ℂ) ^ s / s)) :
    ‖∫ σ in (-(U : ℝ))..2, F (σ + τ * I)‖ ≤ (3 * M * x ^ 2 + K / Real.log x) / T := by
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx
  set f : ℝ → ℂ := fun σ => F (σ + τ * I) with hf
  have hne : ∀ σ : ℝ, (σ : ℂ) + τ * I ≠ 0 := by
    intro σ h
    have : τ = 0 := by simpa using congrArg Complex.im h
    rw [this, abs_zero] at hτ
    linarith
  have hnorm : ∀ σ : ℝ, T ≤ ‖(σ : ℂ) + τ * I‖ := by
    intro σ
    calc T = |((σ : ℂ) + τ * I).im| := by simp [hτ]
      _ ≤ _ := Complex.abs_im_le_norm _
  have hFf : F = fun s => -(deriv (LFunction χ) s / LFunction χ s) * ((x : ℂ) ^ s / s) :=
    funext hF
  have hcont : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro σ
    have hd := differentiableAt_integrand hχ1 hx0 (hL0 σ) (hne σ)
    rw [← hFf] at hd
    exact hd.continuousAt.comp (f := fun σ : ℝ => (σ : ℂ) + τ * I) (by fun_prop)
  have hpt : ∀ σ : ℝ, ∀ B : ℝ,
      ‖deriv (LFunction χ) (σ + τ * I) / LFunction χ (σ + τ * I)‖ ≤ B →
        ‖f σ‖ ≤ B * x ^ σ / T := by
    intro σ B hB
    simp only [hf, hF]
    rw [norm_integrand χ hx0]
    have hre : ((σ : ℂ) + τ * I).re = σ := by simp
    rw [hre]
    have hxs : 0 < x ^ σ := Real.rpow_pos_of_pos hx0 σ
    have h1 : x ^ σ / ‖(σ : ℂ) + τ * I‖ ≤ x ^ σ / T :=
      div_le_div_of_nonneg_left hxs.le hT (hnorm σ)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
    calc _ ≤ B * (x ^ σ / ‖(σ : ℂ) + τ * I‖) :=
          mul_le_mul_of_nonneg_right hB (by positivity)
      _ ≤ B * (x ^ σ / T) := mul_le_mul_of_nonneg_left h1 hB0
      _ = B * x ^ σ / T := by ring
  have hUle : -(U : ℝ) ≤ -1 := by
    have : (1 : ℝ) ≤ U := by exact_mod_cast hU
    linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := -1)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK (-1) hUle le_rfl)
  -- the left piece
  have h1 : ‖∫ σ in (-(U : ℝ))..(-1), f σ‖ ≤ K / (T * Real.log x) := by
    have hxc : Continuous fun σ : ℝ => x ^ σ :=
      continuous_const.rpow continuous_id fun _ => Or.inl hx0.ne'
    have hg : IntervalIntegrable (fun σ : ℝ => K / T * x ^ σ) MeasureTheory.volume
        (-(U : ℝ)) (-1) := (continuous_const.mul hxc).intervalIntegrable _ _
    refine (intervalIntegral.norm_integral_le_of_norm_le hUle ?_ hg).trans ?_
    · refine Filter.Eventually.of_forall fun σ hσ => ?_
      have := hpt σ K (hK σ hσ.1.le hσ.2)
      calc ‖f σ‖ ≤ K * x ^ σ / T := this
        _ = K / T * x ^ σ := by ring
    · rw [intervalIntegral.integral_const_mul]
      have hderiv : ∀ σ ∈ Set.uIcc (-(U : ℝ)) (-1),
          HasDerivAt (fun σ : ℝ => x ^ σ / Real.log x) (x ^ σ) σ := by
        intro σ _
        have := (Real.hasStrictDerivAt_const_rpow hx0 σ).hasDerivAt.div_const (Real.log x)
        exact this.congr_deriv (by field_simp)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hxc.intervalIntegrable _ _)]
      have hxU : 0 < x ^ (-(U : ℝ)) := Real.rpow_pos_of_pos hx0 _
      have hx1 : x ^ (-1 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by norm_num)
      rw [div_sub_div_same, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
      have : K / T * (x ^ (-1 : ℝ) - x ^ (-(U : ℝ))) ≤ K / T := by
        have : x ^ (-1 : ℝ) - x ^ (-(U : ℝ)) ≤ 1 := by linarith
        calc K / T * (x ^ (-1 : ℝ) - x ^ (-(U : ℝ))) ≤ K / T * 1 :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = K / T := mul_one _
      have hT' : K / T * T = K := by field_simp
      nlinarith [mul_le_mul_of_nonneg_right this (le_of_lt (mul_pos hT hlogx))]
  -- the right piece
  have h2 : ‖∫ σ in (-1 : ℝ)..2, f σ‖ ≤ 3 * M * x ^ 2 / T := by
    have hb : ∀ σ ∈ Set.uIoc (-1 : ℝ) 2, ‖f σ‖ ≤ M * x ^ 2 / T := by
      intro σ hσ
      rw [Set.uIoc_of_le (by norm_num)] at hσ
      refine (hpt σ M (hM σ hσ.1.le hσ.2)).trans ?_
      have : x ^ σ ≤ x ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le hσ.2
      rw [Real.rpow_two] at this
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by norm_num) (by norm_num))
      gcongr
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [show |(2 : ℝ) - -1| = 3 by norm_num] at this
    calc _ ≤ M * x ^ 2 / T * 3 := this
      _ = 3 * M * x ^ 2 / T := by ring
  calc ‖(∫ σ in (-(U : ℝ))..(-1), f σ) + ∫ σ in (-1 : ℝ)..2, f σ‖
      ≤ ‖∫ σ in (-(U : ℝ))..(-1), f σ‖ + ‖∫ σ in (-1 : ℝ)..2, f σ‖ := norm_add_le _ _
    _ ≤ K / (T * Real.log x) + 3 * M * x ^ 2 / T := add_le_add h1 h2
    _ = (3 * M * x ^ 2 + K / Real.log x) / T := by field_simp; ring

/-- The left side `Re s = -U`. -/
private lemma norm_integral_left_le (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 1 < x) (U : ℕ)
    (hU : 1 ≤ U) {R : ℝ} (hR : 0 ≤ R) {K : ℝ}
    (hK : ∀ t : ℝ, |t| ≤ R →
      ‖deriv (LFunction χ) (((-(U : ℝ) : ℝ) : ℂ) + t * I) /
        LFunction χ (((-(U : ℝ) : ℝ) : ℂ) + t * I)‖ ≤ K)
    (F : ℂ → ℂ) (hF : ∀ s, F s = -(deriv (LFunction χ) s / LFunction χ s) * ((x : ℂ) ^ s / s)) :
    ‖∫ t in (-R)..R, F (((-(U : ℝ) : ℝ) : ℂ) + t * I)‖ ≤ K * x ^ (-(U : ℝ)) / U * (2 * R) := by
  have hx0 : 0 < x := by linarith
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (by simpa using hR))
  have hb : ∀ t ∈ Set.uIoc (-R) R, ‖F (((-(U : ℝ) : ℝ) : ℂ) + t * I)‖ ≤
      K * x ^ (-(U : ℝ)) / U := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    have htR : |t| ≤ R := abs_le.mpr ⟨ht.1.le, ht.2⟩
    rw [hF, norm_integrand χ hx0]
    have hre : (((-(U : ℝ) : ℝ) : ℂ) + t * I).re = -(U : ℝ) := by simp
    rw [hre]
    have hn : (U : ℝ) ≤ ‖((-(U : ℝ) : ℝ) : ℂ) + t * I‖ := by
      calc (U : ℝ) = |(((-(U : ℝ) : ℝ) : ℂ) + t * I).re| := by
            rw [hre, abs_neg, abs_of_pos hU0]
        _ ≤ _ := Complex.abs_re_le_norm _
    have hxs : 0 < x ^ (-(U : ℝ)) := Real.rpow_pos_of_pos hx0 _
    have h1 : x ^ (-(U : ℝ)) / ‖((-(U : ℝ) : ℝ) : ℂ) + t * I‖ ≤ x ^ (-(U : ℝ)) / U :=
      div_le_div_of_nonneg_left hxs.le hU0 hn
    calc _ ≤ K * (x ^ (-(U : ℝ)) / ‖((-(U : ℝ) : ℝ) : ℂ) + t * I‖) :=
          mul_le_mul_of_nonneg_right (hK t htR) (by positivity)
      _ ≤ K * (x ^ (-(U : ℝ)) / U) := mul_le_mul_of_nonneg_left h1 hK0
      _ = K * x ^ (-(U : ℝ)) / U := by ring
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [show |R - -R| = 2 * R by rw [abs_of_nonneg (by linarith)]; ring] at this
  exact this

/-- Moving the truncation height by at most `1` changes the zero sum by `O(x log (qR) / R)`. -/
private lemma exists_norm_tsum_sub_tsum_le (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {ι : Type u}
    (z : ι → ℂ) (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w) {x : ℝ}
    (hx : 1 < x) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ R : ℝ, 3 ≤ R → ∀ T : ℝ, |T - R| ≤ 1 →
      ‖(∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0)) -
        ∑' n, (if |(z n).im| < T then (x : ℂ) ^ z n / z n else 0)‖ ≤
        C' * Real.log (q * (R + 3)) * x / (R - 1) := by
  classical
  obtain ⟨C₂, hC₂'⟩ := exists_tsum_one_div_one_add_sq_sub_im_le_log.{u}
  have hC₂ : ∀ t : ℝ, ∀ F : Finset ι,
      ∑ n ∈ F, 1 / (1 + (t - (z n).im) ^ 2) ≤ C₂ * Real.log (q * (|t| + 2)) := fun t F =>
    ((hC₂' χ hχ z hz t).1.sum_le_tsum F fun _ _ => by positivity).trans (hC₂' χ hχ z hz t).2
  refine ⟨10 * |C₂|, by positivity, fun R hR T hTR => ?_⟩
  have hx0 : 0 < x := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set ℓ := Real.log (q * (R + 3)) with hℓ
  have hl2 : Real.log (q * (R + 2)) ≤ ℓ := Real.log_le_log (by positivity) (by nlinarith)
  have hl20 : 0 ≤ Real.log (q * (R + 2)) := Real.log_nonneg (by nlinarith)
  have hfin := finite_setOf_abs_im_lt_of_card_eq_analyticOrderAt hχ hχ1 hz (R + 2)
  set F := hfin.toFinset with hF
  have hmemF : ∀ n, n ∈ F ↔ |(z n).im| < R + 2 := by
    intro n; simp [F]
  have hT1 : T ≤ R + 1 := by linarith [(abs_le.mp hTR).2]
  have hT2 : R - 1 ≤ T := by linarith [(abs_le.mp hTR).1]
  set f : ι → ℂ := fun n => (x : ℂ) ^ z n / z n with hf
  have h1 : ∑' n, (if |(z n).im| < R then f n else 0) =
      ∑ n ∈ F, (if |(z n).im| < R then f n else 0) := by
    refine tsum_eq_sum fun n hn => ite_eq_right ?_
    rw [hmemF] at hn; intro h; exact absurd (by linarith : |(z n).im| < R + 2) hn
  have h2 : ∑' n, (if |(z n).im| < T then f n else 0) =
      ∑ n ∈ F, (if |(z n).im| < T then f n else 0) := by
    refine tsum_eq_sum fun n hn => ite_eq_right ?_
    rw [hmemF] at hn; intro h; exact absurd (by linarith : |(z n).im| < R + 2) hn
  change ‖(∑' n, (if |(z n).im| < R then f n else 0)) -
      ∑' n, (if |(z n).im| < T then f n else 0)‖ ≤ _
  rw [h1, h2, ← Finset.sum_sub_distrib]
  have hR1 : 0 < R - 1 := by linarith
  -- each term
  have hterm : ∀ n ∈ F, ‖(if |(z n).im| < R then f n else 0) -
      (if |(z n).im| < T then f n else 0)‖ ≤ if R - 1 ≤ |(z n).im| then x / (R - 1) else 0 := by
    intro n _
    have hmem := mem_nontrivialZeros_of_card_eq_analyticOrderAt hχ hχ1 hz n
    by_cases hc : R - 1 ≤ |(z n).im|
    · rw [ite_eq_left hc]
      have hfn : ‖f n‖ ≤ x / (R - 1) := by
        simp only [hf]
        rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        have hpos : 0 < ‖z n‖ := lt_of_lt_of_le hR1 (hc.trans (Complex.abs_im_le_norm _))
        rw [div_le_div_iff₀ hpos hR1]
        have hxb : x ^ (z n).re ≤ x := by
          calc x ^ (z n).re ≤ x ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hx.le hmem.2.2.1
            _ = x := Real.rpow_one x
        have hn1 : R - 1 ≤ ‖z n‖ := hc.trans (Complex.abs_im_le_norm _)
        nlinarith [Real.rpow_pos_of_pos hx0 (z n).re]
      split_ifs <;> simp [hfn, div_nonneg hx0.le hR1.le]
    · push Not at hc
      rw [ite_eq_right (not_le.mpr hc), ite_eq_left (by linarith), ite_eq_left (by linarith),
        sub_self, norm_zero]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  -- counting
  have hcount : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      ((F.filter fun n => |ε * (z n).im - R| ≤ 2).card : ℝ) ≤ 5 * |C₂| * ℓ := by
    intro ε hε
    set N := F.filter fun n => |ε * (z n).im - R| ≤ 2 with hN
    have key := hC₂ (ε * R) N
    have habs : |ε * R| = R := by
      rcases hε with rfl | rfl <;> simp [abs_of_pos (by linarith : (0 : ℝ) < R)]
    rw [habs] at key
    have hterm : ∀ n ∈ N, (1 / 5 : ℝ) ≤ 1 / (1 + (ε * R - (z n).im) ^ 2) := by
      intro n hn
      simp only [N, Finset.mem_filter] at hn
      have h2 := hn.2
      have hsq : (ε * R - (z n).im) ^ 2 ≤ 4 := by
        have : (ε * R - (z n).im) ^ 2 = (ε * (z n).im - R) ^ 2 := by
          rcases hε with rfl | rfl <;> ring
        rw [this]
        have := abs_le.mp h2
        nlinarith
      apply one_div_le_one_div_of_le (by positivity); linarith
    have h1 := Finset.card_nsmul_le_sum N _ (1 / 5) hterm
    rw [nsmul_eq_mul] at h1
    have h2 : C₂ * Real.log (q * (R + 2)) ≤ |C₂| * ℓ :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) hl20).trans
        (mul_le_mul_of_nonneg_left hl2 (abs_nonneg _))
    linarith
  have hsub : F.filter (fun n => R - 1 ≤ |(z n).im|) ⊆
      (F.filter fun n => |1 * (z n).im - R| ≤ 2) ∪
        (F.filter fun n => |-1 * (z n).im - R| ≤ 2) := by
    intro n hn
    simp only [Finset.mem_filter] at hn
    obtain ⟨hnF, hn⟩ := hn
    have hlt := (hmemF n).mp hnF
    simp only [Finset.mem_union, Finset.mem_filter]
    rcases le_or_gt 0 (z n).im with h | h
    · left
      rw [abs_of_nonneg h] at hn hlt
      refine ⟨hnF, ?_⟩
      rw [abs_le]; constructor <;> linarith
    · right
      rw [abs_of_neg h] at hn hlt
      refine ⟨hnF, ?_⟩
      rw [abs_le]; constructor <;> linarith
  have hc1 := hcount 1 (Or.inl rfl)
  have hc2 := hcount (-1) (Or.inr rfl)
  have hcard : ((F.filter (fun n => R - 1 ≤ |(z n).im|)).card : ℝ) ≤ 10 * |C₂| * ℓ := by
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have : ((F.filter (fun n => R - 1 ≤ |(z n).im|)).card : ℝ) ≤
        (F.filter fun n => |1 * (z n).im - R| ≤ 2).card +
          (F.filter fun n => |-1 * (z n).im - R| ≤ 2).card := by exact_mod_cast this
    linarith
  calc ((F.filter (fun n => R - 1 ≤ |(z n).im|)).card : ℝ) * (x / (R - 1))
      ≤ 10 * |C₂| * ℓ * (x / (R - 1)) :=
        mul_le_mul_of_nonneg_right hcard (div_nonneg hx0.le hR1.le)
    _ = 10 * |C₂| * ℓ * x / (R - 1) := by ring

private lemma tendsto_log_sq_div (q : ℕ) [NeZero q] :
    Tendsto (fun R : ℝ => Real.log (q * (R + 3)) ^ 2 / (R - 1)) atTop (𝓝 0) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have h := Real.tendsto_pow_log_div_mul_add_atTop (1 / (q : ℝ)) (-4) 2 (by positivity)
  have hg : Tendsto (fun R : ℝ => (q : ℝ) * (R + 3)) atTop atTop :=
    (tendsto_atTop_add_const_right _ 3 tendsto_id).const_mul_atTop hq
  refine (h.comp hg).congr fun R => ?_
  simp only [Function.comp]
  congr 1
  field_simp
  ring

private lemma tendsto_sq_mul_exp_neg (x : ℝ) (hx : 1 < x) :
    Tendsto (fun R : ℝ => (R + 3) ^ 2 * Real.exp (-(2 * Real.log x) * R)) atTop (𝓝 0) := by
  have hc : 0 < 2 * Real.log x := by have := Real.log_pos hx; linarith
  set c := 2 * Real.log x with hcdef
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp
    ((tendsto_atTop_add_const_right _ 3 tendsto_id).const_mul_atTop hc)
  have h2 := h.const_mul (Real.exp (3 * c) / c ^ 2)
  rw [mul_zero] at h2
  refine h2.congr fun R => ?_
  simp only [Function.comp, id]
  rw [show -(c * (R + 3)) = -c * R + -(3 * c) by ring, Real.exp_add, Real.exp_neg (3 * c)]
  have hc0 : c ≠ 0 := hc.ne'
  have he0 : Real.exp (3 * c) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

/-- The horizontal sides at a good height `T` near `R`, with `U = 2⌈R⌉ + 1`. -/
private lemma norm_integral_horizontal_le_of_good (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    (heven : χ.Even) {ι : Type u} (z : ι → ℂ)
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w)
    {x : ℝ} (hx : 1 < x) {B Cl : ℝ} (hCl0 : 0 ≤ Cl)
    (hCl : ∀ s : ℂ, s.re ≤ -1 → Complex.sin (Real.pi * s / 2) ≠ 0 →
      ‖Complex.cos (Real.pi * s / 2) / Complex.sin (Real.pi * s / 2)‖ ≤ 2 →
      ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ Cl + Real.log (‖s‖ + 2))
    {R : ℝ} (hR : 3 ≤ R) {T : ℝ} (hTR : |T - R| ≤ 1) (hord : ∀ n, |(z n).im| ≠ T)
    {τ : ℝ} (hτ : τ = T ∨ τ = -T)
    (hbd : ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
      ‖deriv (LFunction χ) (σ + τ * I) / LFunction χ (σ + τ * I)‖ ≤
        B * Real.log (q * (R + 3)) ^ 2)
    (F : ℂ → ℂ) (hF : ∀ s, F s = -(deriv (LFunction χ) s / LFunction χ s) * ((x : ℂ) ^ s / s)) :
    ‖∫ σ in (-((2 * ⌈R⌉₊ + 1 : ℕ) : ℝ))..2, F (σ + τ * I)‖ ≤
      (3 * |B| * x ^ 2 + (Cl + 2) / Real.log x) * (Real.log (q * (R + 3)) ^ 2 / (R - 1)) := by
  set U : ℕ := 2 * ⌈R⌉₊ + 1 with hU
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hT1 : T ≤ R + 1 := by linarith [(abs_le.mp hTR).2]
  have hT2 : R - 1 ≤ T := by linarith [(abs_le.mp hTR).1]
  have hKR' : (⌈R⌉₊ : ℝ) < R + 1 := Nat.ceil_lt_add_one (by linarith)
  have hUR : (U : ℝ) = 2 * ⌈R⌉₊ + 1 := by rw [hU]; push_cast; ring
  have hU1 : 1 ≤ U := by omega
  set ℓ := Real.log (q * (R + 3)) with hℓ
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    nlinarith
  have hlogU : Real.log (U + T + 2) ≤ 2 * ℓ := by
    have e : 2 * ℓ = Real.log ((q * (R + 3)) ^ 2) := by
      rw [Real.log_pow, hℓ]; push_cast; ring
    rw [e]
    apply Real.log_le_log (by have : (0 : ℝ) ≤ U := Nat.cast_nonneg U; linarith)
    rw [hUR]
    have h1 : R + 3 ≤ q * (R + 3) := le_mul_of_one_le_left (by linarith) hq1
    have h2 : (R + 3) ^ 2 ≤ (q * (R + 3)) ^ 2 := by gcongr
    nlinarith
  have hτT : |τ| = T := by
    rcases hτ with rfl | rfl
    · exact abs_of_pos (by linarith)
    · rw [abs_neg]; exact abs_of_pos (by linarith)
  have hL0 : ∀ σ : ℝ, LFunction χ (σ + τ * I) ≠ 0 := by
    intro σ h0
    rcases mem_nontrivialZeros_or_of_LFunction_eq_zero hχ hχ1 heven h0 with hnt | ⟨n, hn⟩
    · obtain ⟨m, hm⟩ := exists_eq_of_card_eq_analyticOrderAt hχ hχ1 hz hnt
      apply hord m
      rw [hm]; simpa using hτT
    · have : τ = 0 := by simpa using congrArg Complex.im hn
      rw [this, abs_zero] at hτT
      linarith
  have h := norm_integral_horizontal_le hχ1 hx U hU1 (by linarith) hτT hL0
    (M := B * ℓ ^ 2) (K := Cl + 2 * ℓ) hbd
    (fun σ h1 h2 => by
      have hcot := norm_cot_le_of_one_le_abs_im (s := (σ : ℂ) + τ * I) (by simp [hτT]; linarith)
      have hs4 : ‖(σ : ℂ) + τ * I‖ ≤ U + T := by
        calc ‖(σ : ℂ) + τ * I‖ ≤ ‖(σ : ℂ)‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
          _ = |σ| + |τ| := by simp
          _ ≤ U + T := by
              rw [hτT, abs_of_nonpos (by linarith)]
              linarith
      have h3 := hCl _ (by simpa using h2) hcot.1 (by linarith [hcot.2])
      have h4 : Real.log (‖(σ : ℂ) + τ * I‖ + 2) ≤ Real.log (U + T + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      linarith) F hF
  refine h.trans ?_
  have hl1 : 1 ≤ ℓ ^ 2 := by nlinarith
  have hCl' : Cl + 2 * ℓ ≤ (Cl + 2) * ℓ ^ 2 := by
    have : Cl ≤ Cl * ℓ ^ 2 := le_mul_of_one_le_right hCl0 hl1
    have e : (Cl + 2) * ℓ ^ 2 = Cl * ℓ ^ 2 + 2 * ℓ ^ 2 := by ring
    nlinarith
  have hnum : 3 * (B * ℓ ^ 2) * x ^ 2 + (Cl + 2 * ℓ) / Real.log x ≤
      (3 * |B| * x ^ 2 + (Cl + 2) / Real.log x) * ℓ ^ 2 := by
    have h1 : (Cl + 2 * ℓ) / Real.log x ≤ (Cl + 2) * ℓ ^ 2 / Real.log x :=
      div_le_div_of_nonneg_right hCl' hlogx.le
    have hB' : B * ℓ ^ 2 ≤ |B| * ℓ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have h2 : 3 * (B * ℓ ^ 2) * x ^ 2 ≤ 3 * (|B| * ℓ ^ 2) * x ^ 2 := by gcongr
    have h3 : (3 * |B| * x ^ 2 + (Cl + 2) / Real.log x) * ℓ ^ 2 =
        3 * (|B| * ℓ ^ 2) * x ^ 2 + (Cl + 2) * ℓ ^ 2 / Real.log x := by ring
    linarith
  have hpos : 0 ≤ (3 * |B| * x ^ 2 + (Cl + 2) / Real.log x) * ℓ ^ 2 := by positivity
  calc _ ≤ (3 * |B| * x ^ 2 + (Cl + 2) / Real.log x) * ℓ ^ 2 / T :=
        div_le_div_of_nonneg_right hnum (by linarith)
    _ ≤ (3 * |B| * x ^ 2 + (Cl + 2) / Real.log x) * ℓ ^ 2 / (R - 1) :=
        div_le_div_of_nonneg_left hpos (by linarith) hT2
    _ = _ := by ring

/-- The left side of the rectangle, `Re s = -(2⌈R⌉ + 1)`. -/
private lemma norm_integral_left_le_of_good (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 1 < x)
    {Cl : ℝ} (hCl0 : 0 ≤ Cl)
    (hCl : ∀ s : ℂ, s.re ≤ -1 → Complex.sin (Real.pi * s / 2) ≠ 0 →
      ‖Complex.cos (Real.pi * s / 2) / Complex.sin (Real.pi * s / 2)‖ ≤ 2 →
      ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ Cl + Real.log (‖s‖ + 2))
    {R : ℝ} (hR : 3 ≤ R) {T : ℝ} (hTR : |T - R| ≤ 1)
    (F : ℂ → ℂ) (hF : ∀ s, F s = -(deriv (LFunction χ) s / LFunction χ s) * ((x : ℂ) ^ s / s)) :
    ‖∫ t in (-T)..T, F (((-((2 * ⌈R⌉₊ + 1 : ℕ) : ℝ) : ℝ) : ℂ) + t * I)‖ ≤
      2 * (Cl + 2) * q * ((R + 3) ^ 2 * Real.exp (-(2 * Real.log x) * R)) := by
  set U : ℕ := 2 * ⌈R⌉₊ + 1 with hU
  have hx0 : 0 < x := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hT1 : T ≤ R + 1 := by linarith [(abs_le.mp hTR).2]
  have hT2 : R - 1 ≤ T := by linarith [(abs_le.mp hTR).1]
  have hKR' : (⌈R⌉₊ : ℝ) < R + 1 := Nat.ceil_lt_add_one (by linarith)
  have hUR : (U : ℝ) = 2 * ⌈R⌉₊ + 1 := by rw [hU]; push_cast; ring
  have hU1 : 1 ≤ U := by omega
  set ℓ := Real.log (q * (R + 3)) with hℓ
  have hlogU : Real.log (U + T + 2) ≤ 2 * ℓ := by
    have e : 2 * ℓ = Real.log ((q * (R + 3)) ^ 2) := by
      rw [Real.log_pow, hℓ]; push_cast; ring
    rw [e]
    apply Real.log_le_log (by have : (0 : ℝ) ≤ U := Nat.cast_nonneg U; linarith)
    rw [hUR]
    have h1 : R + 3 ≤ q * (R + 3) := le_mul_of_one_le_left (by linarith) hq1
    have h2 : (R + 3) ^ 2 ≤ (q * (R + 3)) ^ 2 := by gcongr
    nlinarith
  have h := norm_integral_left_le χ hx U hU1 (R := T) (by linarith) (K := Cl + 2 * ℓ)
    (fun t ht => by
      have hre : (((-(U : ℝ) : ℝ) : ℂ) + t * I).re = -(2 * (⌈R⌉₊ : ℝ) + 1) := by simp [hUR]
      have hcot := norm_cot_le_of_re_eq_odd ⌈R⌉₊ hre
      have hs4 : ‖((-(U : ℝ) : ℝ) : ℂ) + t * I‖ ≤ U + T := by
        calc ‖((-(U : ℝ) : ℝ) : ℂ) + t * I‖ ≤ ‖((-(U : ℝ) : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ :=
              norm_add_le _ _
          _ = U + |t| := by simp
          _ ≤ U + T := by linarith
      have h3 := hCl _ (by rw [hre]; linarith [(Nat.cast_nonneg ⌈R⌉₊ : (0 : ℝ) ≤ ⌈R⌉₊)])
        hcot.1 (by linarith [hcot.2])
      have h4 : Real.log (‖((-(U : ℝ) : ℝ) : ℂ) + t * I‖ + 2) ≤ Real.log (U + T + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      linarith) F hF
  refine h.trans ?_
  have hℓq : ℓ ≤ q * (R + 3) := by
    have := Real.log_le_sub_one_of_pos (show 0 < (q : ℝ) * (R + 3) by positivity)
    linarith
  have hqR : 1 ≤ (q : ℝ) * (R + 3) := by nlinarith
  have hK1 : Cl + 2 * ℓ ≤ (Cl + 2) * (q * (R + 3)) := by
    have : Cl ≤ Cl * (q * (R + 3)) := le_mul_of_one_le_right hCl0 hqR
    have e : (Cl + 2) * (q * (R + 3)) = Cl * (q * (R + 3)) + 2 * (q * (R + 3)) := by ring
    linarith
  have hxU : x ^ (-(U : ℝ)) ≤ Real.exp (-(2 * Real.log x) * R) := by
    rw [Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.mpr
    rw [hUR]
    have := Real.log_pos hx
    have hKR : R ≤ ⌈R⌉₊ := Nat.le_ceil R
    nlinarith
  have hU1' : (1 : ℝ) ≤ U := by exact_mod_cast hU1
  have hxU0 : 0 < x ^ (-(U : ℝ)) := Real.rpow_pos_of_pos hx0 _
  have hK0 : 0 ≤ Cl + 2 * ℓ := by
    have : 0 ≤ ℓ := Real.log_nonneg (by nlinarith)
    linarith
  have hA0 : 0 ≤ (Cl + 2 * ℓ) * x ^ (-(U : ℝ)) * (2 * T) :=
    mul_nonneg (mul_nonneg hK0 hxU0.le) (by linarith)
  calc (Cl + 2 * ℓ) * x ^ (-(U : ℝ)) / U * (2 * T)
      = (Cl + 2 * ℓ) * x ^ (-(U : ℝ)) * (2 * T) / U := by ring
    _ ≤ (Cl + 2 * ℓ) * x ^ (-(U : ℝ)) * (2 * T) := div_le_self hA0 hU1'
    _ ≤ ((Cl + 2) * (q * (R + 3))) * Real.exp (-(2 * Real.log x) * R) * (2 * (R + 3)) :=
        mul_le_mul (mul_le_mul hK1 hxU hxU0.le (by positivity)) (by linarith) (by linarith)
          (by positivity)
    _ = 2 * (Cl + 2) * q * ((R + 3) ^ 2 * Real.exp (-(2 * Real.log x) * R)) := by ring

/-! ### The explicit formula -/

/-- The explicit formula at one height: all error terms at a good height `T` near `R`. -/
private lemma norm_tsum_sub_le_of_good (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (heven : χ.Even)
    {ι : Type u} (z : ι → ℂ) (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w)
    {x : ℝ} (hx : 1 < x) (hpp : ∀ n : ℕ, (n : ℝ) = x → ¬ IsPrimePow n) {B Cl C' : ℝ}
    (hCl0 : 0 ≤ Cl)
    (hCl : ∀ s : ℂ, s.re ≤ -1 → Complex.sin (Real.pi * s / 2) ≠ 0 →
      ‖Complex.cos (Real.pi * s / 2) / Complex.sin (Real.pi * s / 2)‖ ≤ 2 →
      ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ Cl + Real.log (‖s‖ + 2))
    (hC'0 : 0 ≤ C')
    (hC' : ∀ R : ℝ, 3 ≤ R → ∀ T : ℝ, |T - R| ≤ 1 →
      ‖(∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0)) -
        ∑' n, (if |(z n).im| < T then (x : ℂ) ^ z n / z n else 0)‖ ≤
        C' * Real.log (q * (R + 3)) * x / (R - 1))
    {R : ℝ} (hR : 3 ≤ R) {T : ℝ} (hTR : |T - R| ≤ 1) (hord : ∀ n, |(z n).im| ≠ T)
    (hbd : ∀ τ : ℝ, (τ = T ∨ τ = -T) → ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
      ‖deriv (LFunction χ) (σ + τ * I) / LFunction χ (σ + τ * I)‖ ≤
        B * Real.log (q * (R + 3)) ^ 2) :
    ‖(∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0)) -
      (-χ.chebyshevPsi x - (Real.log x : ℂ) - χ.logDerivConstAtZero -
        ((1 / 2 * Real.log (1 - x ^ (-2 : ℤ)) : ℝ) : ℂ))‖ ≤
      (C' * x + 2 * (3 * |B| * x ^ 2 + (Cl + 2) / Real.log x)) *
          (Real.log (q * (R + 3)) ^ 2 / (R - 1)) +
        2 * (Cl + 2) * q * ((R + 3) ^ 2 * Real.exp (-(2 * Real.log x) * R)) +
        1 / Real.pi * ∑' n : ℕ, Λ n * (x / n) ^ (2 : ℝ) / (T * |Real.log (x / n)|) +
        ‖(∑ m ∈ Finset.Icc 1 ⌈R⌉₊, (x : ℂ) ^ (-(2 * (m : ℂ))) / (2 * (m : ℂ))) -
          -(((1 / 2 * Real.log (1 - x ^ (-2 : ℤ))) : ℝ) : ℂ)‖ := by
  have hT1 : T ≤ R + 1 := by linarith [(abs_le.mp hTR).2]
  have hT2 : R - 1 ≤ T := by linarith [(abs_le.mp hTR).1]
  have hT0 : 0 < T := by linarith
  set F : ℂ → ℂ := fun s => -(deriv (LFunction χ) s / LFunction χ s) * ((x : ℂ) ^ s / s) with hF
  -- the residue theorem
  have hb := boundaryIntegral_eq hχ hχ1 heven z hz hx ⌈R⌉₊ hT0 hord F (fun s => rfl)
  simp only [RectilinearRectangle.boundaryIntegral, RectilinearRectangle.ofBounds_first_re,
    RectilinearRectangle.ofBounds_first_im, RectilinearRectangle.ofBounds_second_re,
    RectilinearRectangle.ofBounds_second_im, smul_eq_mul] at hb
  set J := ∫ t in (-T)..T, F (((2 : ℝ) : ℂ) + t * I) with hJ
  set I₁ := ∫ σ in (-((2 * ⌈R⌉₊ + 1 : ℕ) : ℝ))..2, F (σ + ((-T : ℝ) : ℂ) * I) with hI₁
  set I₂ := ∫ σ in (-((2 * ⌈R⌉₊ + 1 : ℕ) : ℝ))..2, F (σ + (T : ℂ) * I) with hI₂
  set I₃ := ∫ t in (-T)..T, F (((-((2 * ⌈R⌉₊ + 1 : ℕ) : ℝ) : ℝ) : ℂ) + t * I) with hI₃
  set S := fun R : ℝ => ∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0) with hS
  set St := ∑ m ∈ Finset.Icc 1 ⌈R⌉₊, (x : ℂ) ^ (-(2 * (m : ℂ))) / (2 * (m : ℂ)) with hSt
  set lim : ℂ := -(((1 / 2 * Real.log (1 - x ^ (-2 : ℤ))) : ℝ) : ℂ) with hlim
  set A : ℂ := -χ.chebyshevPsi x - (Real.log x : ℂ) - χ.logDerivConstAtZero -
    ((1 / 2 * Real.log (1 - x ^ (-2 : ℤ)) : ℝ) : ℂ) with hA
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hid : S T - A = (χ.chebyshevPsi x - (1 / (2 * Real.pi)) * J) -
      (1 / (2 * Real.pi * I)) * (I₁ - I₂ - I * I₃) + (St - lim) := by
    have h2πI : 2 * (Real.pi : ℂ) * I ≠ 0 := by simp [hpi, Complex.I_ne_zero]
    have hlim' : lim = -((1 / 2 * Real.log (1 - x ^ (-2 : ℤ)) : ℝ) : ℂ) := rfl
    rw [hA, hlim', show S T = ∑' n, (if |(z n).im| < T then (x : ℂ) ^ z n / z n else 0) from rfl]
    field_simp
    linear_combination hb
  -- the pieces
  obtain ⟨hbd1, hbd2⟩ := And.intro (hbd T (Or.inl rfl)) (hbd (-T) (Or.inr rfl))
  have hP := norm_chebyshevPsi_sub_truncated_integral_le χ hx hpp (c := 2) (by norm_num) hT0
  have hI₁' := norm_integral_horizontal_le_of_good hχ hχ1 heven z hz hx hCl0 hCl hR hTR hord
    (τ := -T) (Or.inr rfl) hbd2 F (fun s => rfl)
  have hI₂' := norm_integral_horizontal_le_of_good hχ hχ1 heven z hz hx hCl0 hCl hR hTR hord
    (τ := T) (Or.inl rfl) hbd1 F (fun s => rfl)
  have hI₃' := norm_integral_left_le_of_good χ hx hCl0 hCl hR hTR F (fun s => rfl)
  have hcmp := hC' R hR T hTR
  set ℓ := Real.log (q * (R + 3)) with hℓ
  have hℓ1 : 1 ≤ ℓ := by
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    rw [hℓ, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    nlinarith
  have hx0 : 0 < x := by linarith
  have hcmp' : C' * ℓ * x / (R - 1) ≤ C' * x * (ℓ ^ 2 / (R - 1)) := by
    rw [mul_div_assoc']
    apply div_le_div_of_nonneg_right _ (by linarith)
    have : ℓ ≤ ℓ ^ 2 := by nlinarith
    have : 0 ≤ C' * x := by positivity
    nlinarith
  have hpi1 : ‖1 / (2 * (Real.pi : ℂ) * I)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_two,
      Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    rw [div_le_one (by positivity)]
    linarith [Real.two_le_pi]
  have htri : ‖S R - A‖ ≤ ‖S R - S T‖ + ‖S T - A‖ := by
    have := norm_add_le (S R - S T) (S T - A)
    simpa using this
  have hST' : ‖S T - A‖ ≤ ‖χ.chebyshevPsi x - (1 / (2 * Real.pi)) * J‖ +
      (‖I₁‖ + ‖I₂‖ + ‖I₃‖) + ‖St - lim‖ := by
    rw [hid]
    refine (norm_add_le _ _).trans ?_
    gcongr
    refine (norm_sub_le _ _).trans ?_
    gcongr
    rw [norm_mul]
    calc ‖1 / (2 * (Real.pi : ℂ) * I)‖ * ‖I₁ - I₂ - I * I₃‖ ≤ 1 * ‖I₁ - I₂ - I * I₃‖ :=
          mul_le_mul_of_nonneg_right hpi1 (norm_nonneg _)
      _ ≤ ‖I₁‖ + ‖I₂‖ + ‖I₃‖ := by
          rw [one_mul]
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul, Complex.norm_I, one_mul]
          gcongr
          exact norm_sub_le _ _
  have hPJ : ‖χ.chebyshevPsi x - (1 / (2 * Real.pi)) * J‖ ≤
      1 / Real.pi * ∑' n : ℕ, Λ n * (x / n) ^ (2 : ℝ) / (T * |Real.log (x / n)|) := hP
  have hSRT : ‖S R - S T‖ ≤ C' * x * (ℓ ^ 2 / (R - 1)) := hcmp.trans hcmp'
  have hfinal : C' * x * (ℓ ^ 2 / (R - 1)) +
      2 * ((3 * |B| * x ^ 2 + (Cl + 2) / Real.log x) * (ℓ ^ 2 / (R - 1))) =
      (C' * x + 2 * (3 * |B| * x ^ 2 + (Cl + 2) / Real.log x)) * (ℓ ^ 2 / (R - 1)) := by ring
  linarith

end Even

/-- **The explicit formula for `ψ(x, χ)`, `χ` even.** For a primitive even nonprincipal Dirichlet
character `χ` modulo `q` and real `x > 1` not a prime power,
`∑_ρ x^ρ/ρ = -ψ(x, χ) - log x - b(χ) - ½ log (1 - x⁻²)`, where `b(χ)` is the constant term of
`L'/L(s, χ)` at `s = 0` (`DirichletCharacter.logDerivConstAtZero`). The sum over the nontrivial
zeros `ρ = β + iγ`, listed with multiplicity by any family `z` listing the zeros of `ξ(s, χ)`,
converges only conditionally: it is the limit as `R → ∞` of its truncations to `|γ| < R`, each
with finite support. -/
theorem tendsto_tsum_cpow_div_zeros_explicit_formula_of_even {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (heven : χ.Even)
    {ι : Type u} (z : ι → ℂ) (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w)
    {x : ℝ} (hx : 1 < x) (hpp : ∀ n : ℕ, (n : ℝ) = x → ¬ IsPrimePow n) :
    Tendsto (fun R : ℝ => ∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0)) atTop
      (𝓝 (-χ.chebyshevPsi x - (Real.log x : ℂ) - χ.logDerivConstAtZero -
        ((1 / 2 * Real.log (1 - x ^ (-2 : ℤ)) : ℝ) : ℂ))) := by
  classical
  obtain ⟨B, hB⟩ := exists_good_height hχ z hz
  obtain ⟨Cl, hCl0, hCl⟩ := exists_norm_logDeriv_le_left hχ heven
  obtain ⟨C', hC'0, hC'⟩ := exists_norm_tsum_sub_tsum_le hχ hχ1 z hz hx
  set H : ℝ := C' * x + 2 * (3 * |B| * x ^ 2 + (Cl + 2) / Real.log x) with hH
  set H' : ℝ := 2 * (Cl + 2) * q with hH'
  have htriv : Tendsto (fun k : ℕ => ∑ m ∈ Finset.Icc 1 k, (x : ℂ) ^ (-(2 * (m : ℂ))) /
      (2 * (m : ℂ))) atTop (𝓝 (-(((1 / 2 * Real.log (1 - x ^ (-2 : ℤ))) : ℝ) : ℂ))) := by
    have h := tendsto_sum_cpow_neg_two_mul_div_two_mul hx
    convert h using 2
    push_cast
    ring
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    (((tendsto_log_sq_div q).const_mul H).eventually (gt_mem_nhds (by rw [mul_zero]; exact hε4)))
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp
    (((tendsto_sq_mul_exp_neg x hx).const_mul H').eventually
      (gt_mem_nhds (by rw [mul_zero]; exact hε4)))
  obtain ⟨N₃, hN₃⟩ := Metric.tendsto_atTop.mp (tendsto_perron_error x 2) (ε / 4) hε4
  obtain ⟨N₄, hN₄⟩ := Metric.tendsto_atTop.mp htriv (ε / 4) hε4
  refine ⟨max (max 3 N₁) (max N₂ (max (N₃ + 1) (N₄ : ℝ))), fun R hR => ?_⟩
  have hR3 : 3 ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hRN₁ : N₁ ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hRN₂ : N₂ ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hR
  have hRN₃ : N₃ + 1 ≤ R :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hR
  have hRN₄ : (N₄ : ℝ) ≤ R :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hR
  obtain ⟨T, hTR, hord, hbd⟩ := hB R hR3
  have hT2 : R - 1 ≤ T := by linarith [(abs_le.mp hTR).1]
  have hKN₄ : N₄ ≤ ⌈R⌉₊ := by exact_mod_cast hRN₄.trans (Nat.le_ceil R)
  have hmain := norm_tsum_sub_le_of_good hχ hχ1 heven z hz hx hpp hCl0 hCl hC'0 hC' hR3 hTR
    hord hbd
  have hPT := hN₃ T (by linarith)
  rw [Real.dist_eq, sub_zero] at hPT
  have hSt := hN₄ ⌈R⌉₊ hKN₄
  rw [dist_eq_norm] at hSt
  have h1 := hN₁ R hRN₁
  have h2 := hN₂ R hRN₂
  rw [dist_eq_norm]
  have hPT' := lt_of_abs_lt hPT
  linarith

end DirichletCharacter
