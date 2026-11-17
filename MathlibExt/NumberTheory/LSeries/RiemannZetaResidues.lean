/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.RectangleResidue
import MathlibExt.Analysis.Complex.RectangleResidueDoublePole
public import MathlibExt.NumberTheory.LSeries.RiemannXiZeros
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The residues of `-ζ'/ζ(s) x^s / s`

The integrand of the explicit formula for `ψ(x)` has simple poles at `s = 1` (residue `x`), at
`s = 0` (residue `-ζ'(0)/ζ(0)`), at each nontrivial zero `ρ` (residue `-m_ρ x^ρ / ρ`, with `m_ρ`
the multiplicity) and at each trivial zero `-2m` (residue `x^{-2m} / (2m)`). We evaluate the
boundary integral over the rectangle `[-U, c] × [-R, R]` by the residue theorem, and sum the
contributions of the trivial zeros.

## Main statements

* `RiemannXi.boundaryIntegral_neg_logDeriv_riemannZeta_mul_cpow_div`: for `x > 0`, `c > 1`, `U`
  odd and `R > 0` not the ordinate of a zero, the boundary integral of `-ζ'/ζ(s) x^s/s` over
  `[-U, c] × [-R, R]` is `2πi (x - ∑_{|γ| < R} x^ρ/ρ - ζ'(0)/ζ(0) + ∑_{1 ≤ m ≤ U/2} x^{-2m}/(2m))`.
* `tendsto_sum_cpow_neg_two_mul_div_two_mul`: `∑_{m ≥ 1} x^{-2m}/(2m) = -½ log (1 - x⁻²)`.
* `norm_half_log_one_sub_zpow_neg_two_le`: `|½ log (1 - y⁻²)| ≤ ½` for `y ≥ 3/2`.
-/

@[expose] public section

open Complex Filter Topology Set

section Residues

private lemma pi_cpow_ne_zero (s : ℂ) : (Real.pi : ℂ) ^ s ≠ 0 := by
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h => Real.pi_ne_zero (by exact_mod_cast h.1)

private lemma differentiableAt_pi_cpow_half (s : ℂ) :
    DifferentiableAt ℂ (fun s : ℂ => (Real.pi : ℂ) ^ (s / 2)) s :=
  (differentiableAt_id.div_const (2 : ℂ)).const_cpow (Or.inl (by exact_mod_cast Real.pi_ne_zero))

/-- The pole at `s = 1`, with residue `x`. -/
private lemma exists_local_pole_one {x : ℝ} (hx : 0 < x) :
    ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ 1 ∧ ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      -(deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ s / s) =
        (-(((-1 : ℤ) : ℤ) : ℂ) * ((x : ℂ) ^ (1 : ℂ) / 1)) / (s - 1) + φ s := by
  let E : ℂ → ℂ := fun s =>
    2 * RiemannXi.riemannXi s * (Real.pi : ℂ) ^ (s / 2) * (Complex.Gamma (s / 2))⁻¹ / s
  have hEd : ∀ s : ℂ, s ≠ 0 → DifferentiableAt ℂ E s := fun s hs =>
    ((((RiemannXi.differentiable_riemannXi s).const_mul 2).mul
      (differentiableAt_pi_cpow_half s)).mul
      ((Complex.differentiable_one_div_Gamma.comp (differentiable_id.div_const (2 : ℂ))) s)).div
      differentiableAt_id hs
  have hE : AnalyticAt ℂ E 1 := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [isOpen_compl_singleton.mem_nhds (show (1 : ℂ) ∈ ({0}ᶜ : Set ℂ) by simp)]
      with s hs using hEd s hs
  have hE0 : E 1 ≠ 0 := by
    have hG : Complex.Gamma (2⁻¹) ≠ 0 := by
      refine Complex.Gamma_ne_zero fun m hm => ?_
      have := congrArg Complex.re hm
      simp at this
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    simp [E, RiemannXi.riemannXi_one, hG]
  refine Complex.exists_eventually_neg_logDeriv_mul_cpow_div_eq_of_zpow hx one_ne_zero hE hE0 ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds
      (show (1 : ℂ) ∈ ({0}ᶜ : Set ℂ) by simp))] with s hs1 hs0
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [RiemannXi.riemannZeta_eq_riemannXi_mul_div hs0 hs1, zpow_neg_one]
  simp only [E]
  field_simp

/-- The pole at a nontrivial zero `p` of multiplicity `m`, with residue `-m x^p / p`. -/
private lemma exists_local_pole_zero {x : ℝ} (hx : 0 < x) {p : ℂ}
    (hp : p ∈ riemannZetaNontrivialZeros) {m : ℕ}
    (hm : analyticOrderAt RiemannXi.riemannXi p = m) :
    ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ p ∧ ∀ᶠ s in 𝓝[≠] p,
      -(deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ s / s) =
        (-(((m : ℤ)) : ℂ) * ((x : ℂ) ^ p / p)) / (s - p) + φ s := by
  obtain ⟨E, hE, hE0, hζ⟩ := RiemannXi.exists_riemannZeta_eventually_eq_zpow_mul hp hm
  exact Complex.exists_eventually_neg_logDeriv_mul_cpow_div_eq_of_zpow hx
    (ne_zero_of_mem_riemannZetaNontrivialZeros hp) hE hE0 hζ

/-- The pole at a trivial zero `-2n`, with residue `x^{-2n} / (2n)`. -/
private lemma exists_local_pole_trivial {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 0 < n) :
    ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ (-(2 * (n : ℂ))) ∧ ∀ᶠ s in 𝓝[≠] (-(2 * (n : ℂ))),
      -(deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ s / s) =
        (-(((1 : ℤ)) : ℂ) * ((x : ℂ) ^ (-(2 * (n : ℂ))) / (-(2 * (n : ℂ))))) /
          (s - (-(2 * (n : ℂ)))) + φ s := by
  set p : ℂ := -(2 * (n : ℂ)) with hpdef
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hp0 : p ≠ 0 := by simp [p, hn']
  have hpre : p.re < 0 := by simpa [p] using hn
  have hp1 : p ≠ 1 := by
    intro h; have := congrArg Complex.re h; linarith [show p.re = 1 by simpa using this]
  obtain ⟨G, hGa, hG0, hGe⟩ := (Complex.differentiable_one_div_Gamma.analyticAt
    (-(n : ℂ))).analyticOrderAt_eq_natCast (n := 1) |>.mp
      ((Complex.analyticOrderAt_inv_Gamma_neg_natCast n).trans Nat.cast_one.symm)
  have ht : Tendsto (fun s : ℂ => s / 2) (𝓝 p) (𝓝 (-(n : ℂ))) := by
    have h : -(n : ℂ) = p / 2 := by rw [hpdef]; ring
    rw [h]
    exact (continuous_id.div_const (2 : ℂ)).tendsto p
  have hGe' := ht.eventually hGe
  have hGa' := ht.eventually hGa.eventually_analyticAt
  let E : ℂ → ℂ := fun s =>
    2 * RiemannXi.riemannXi s * (Real.pi : ℂ) ^ (s / 2) * (G (s / 2) / 2) / (s * (s - 1))
  have hE : AnalyticAt ℂ E p := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [isOpen_compl_singleton.mem_nhds (show p ∈ ({0}ᶜ : Set ℂ) from hp0),
      isOpen_compl_singleton.mem_nhds (show p ∈ ({1}ᶜ : Set ℂ) from hp1),
      hGa'] with s hs0 hs1 hsa
    have h2' : DifferentiableAt ℂ (fun s : ℂ => G (s / 2)) s :=
      hsa.differentiableAt.comp s (differentiableAt_id.div_const (2 : ℂ))
    have hden : s * (s - 1) ≠ 0 := mul_ne_zero hs0 (sub_ne_zero.mpr hs1)
    exact ((((RiemannXi.differentiable_riemannXi s).const_mul 2).mul
      (differentiableAt_pi_cpow_half s)).mul (h2'.div_const 2)).div (by fun_prop) hden
  have hE0 : E p ≠ 0 := by
    have hxi : RiemannXi.riemannXi p ≠ 0 := by
      rw [Ne, RiemannXi.riemannXi_eq_zero_iff]
      intro h; linarith [h.2.1]
    have hGp : G (p / 2) ≠ 0 := by
      rw [show p / 2 = -(n : ℂ) by rw [hpdef]; ring]; exact hG0
    have hden : p * (p - 1) ≠ 0 := mul_ne_zero hp0 (sub_ne_zero.mpr hp1)
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hxi)
      (pi_cpow_ne_zero _)) (div_ne_zero hGp two_ne_zero)) hden
  refine Complex.exists_eventually_neg_logDeriv_mul_cpow_div_eq_of_zpow hx hp0 hE hE0 ?_
  filter_upwards [nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds
      (show p ∈ ({0}ᶜ : Set ℂ) from hp0)),
    nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds (show p ∈ ({1}ᶜ : Set ℂ) from hp1)),
    nhdsWithin_le_nhds hGe'] with s hs0 hs1 hse
  rw [RiemannXi.riemannZeta_eq_riemannXi_mul_div hs0 hs1, hse, zpow_one, pow_one, smul_eq_mul]
  simp only [E, p]
  ring

/-- The pole at `s = 0`, with residue `-ζ'(0)/ζ(0)`. -/
private lemma exists_local_pole_origin {x : ℝ} (hx : 0 < x) :
    ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ 0 ∧ ∀ᶠ s in 𝓝[≠] (0 : ℂ),
      -(deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ s / s) =
        (-(deriv riemannZeta 0 / riemannZeta 0)) / (s - 0) + φ s := by
  have hζa : AnalyticAt ℂ riemannZeta 0 := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [isOpen_compl_singleton.mem_nhds (show (0 : ℂ) ∈ ({1}ᶜ : Set ℂ) by simp)]
      with s hs using differentiableAt_riemannZeta hs
  exact Complex.exists_eventually_neg_logDeriv_mul_cpow_div_eq_of_ne_zero hx hζa
    (by rw [riemannZeta_zero]; norm_num)

end Residues

namespace RiemannXi

/-- **The residues of `-ζ'/ζ(s) x^s/s` in a rectangle.** Let `x > 0`, `c > 1`, `U` an odd natural
number and `R > 0` not the ordinate of a nontrivial zero of `ζ`. The positively oriented boundary
integral of `-ζ'/ζ(s) x^s/s` over the rectangle `[-U, c] × [-R, R]` is
`2πi (x - ∑_{|γ| < R} x^ρ/ρ - ζ'(0)/ζ(0) + ∑_{1 ≤ m ≤ U/2} x^{-2m}/(2m))`, the sum over the
nontrivial zeros `ρ = β + iγ` counted with multiplicity (any family `z` listing the zeros of `ξ`
with multiplicity); it has finite support. -/
theorem boundaryIntegral_neg_logDeriv_riemannZeta_mul_cpow_div {ι : Type*} (z : ι → ℂ)
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w)
    {x : ℝ} (hx0 : 0 < x) {c : ℝ} (hc1 : 1 < c) {U : ℕ} (hU : Odd U) {R : ℝ} (hR : 0 < R)
    (hRz : ∀ ρ ∈ riemannZetaNontrivialZeros, |ρ.im| ≠ R) :
    (RectilinearRectangle.ofBounds (-(U : ℝ)) c (-R) R).boundaryIntegral
        (fun s => -(deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ s / s)) =
      2 * (Real.pi : ℂ) * I *
        ((x : ℂ) - ∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0) -
          deriv riemannZeta 0 / riemannZeta 0 +
          ∑ m ∈ Finset.Icc 1 (U / 2), (x : ℂ) ^ (-(2 * (m : ℂ))) / (2 * (m : ℂ))) := by
  classical
  set F : ℂ → ℂ := fun s => -(deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ s / s)
  obtain ⟨j, hj⟩ := hU
  have hUpos : (0 : ℝ) < U := by rw [hj]; positivity
  have hmem_of := mem_riemannZetaNontrivialZeros_of_card_eq_analyticOrderAt hz
  have hNfin := finite_setOf_abs_im_lt_of_card_eq_analyticOrderAt hz R
  set NF := hNfin.toFinset with hNF
  set Z : Finset ℂ := NF.image z with hZ
  set T : Finset ℂ := (Finset.Icc 1 (U / 2)).image (fun m : ℕ => -(2 * (m : ℂ))) with hT
  set S : Finset ℂ := insert 1 (insert 0 (Z ∪ T)) with hS
  have hZmem : ∀ p, p ∈ Z ↔ p ∈ riemannZetaNontrivialZeros ∧ |p.im| < R := by
    intro p; constructor
    · intro hp
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨hmem_of n, by simpa [NF] using hn⟩
    · rintro ⟨hp, hpR⟩
      obtain ⟨n, hn⟩ := exists_eq_of_card_eq_analyticOrderAt hz hp
      exact Finset.mem_image.mpr ⟨n, by simp [NF, hn, hpR], hn⟩
  have hTmem : ∀ p, p ∈ T ↔ ∃ m : ℕ, 0 < m ∧ 2 * m < U ∧ p = -(2 * (m : ℂ)) := by
    intro p
    simp only [T, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨m, ⟨h1, h2⟩, rfl⟩; exact ⟨m, h1, by omega, rfl⟩
    · rintro ⟨m, h1, h2, rfl⟩; exact ⟨m, ⟨h1, by omega⟩, rfl⟩
  have hζ1 : riemannZeta 1 ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
  have hζ0 : riemannZeta 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
  have hZprop : ∀ p ∈ Z, p ≠ 0 ∧ p ≠ 1 ∧ 0 ≤ p.re ∧ p.re ≤ 1 ∧ |p.im| < R := by
    intro p hp
    obtain ⟨hnt, hpR⟩ := (hZmem p).mp hp
    exact ⟨ne_zero_of_mem_riemannZetaNontrivialZeros hnt,
      ne_one_of_mem_riemannZetaNontrivialZeros hnt, hnt.2.1, hnt.2.2, hpR⟩
  have hTprop : ∀ p ∈ T, p.re < 0 ∧ -(U : ℝ) < p.re ∧ p.im = 0 := by
    intro p hp
    obtain ⟨m, h1, h2, rfl⟩ := (hTmem p).mp hp
    have h1' : (0 : ℝ) < m := by exact_mod_cast h1
    have h2' : (2 * m : ℝ) < U := by exact_mod_cast h2
    simp
    constructor <;> linarith
  -- residues
  let mo : ℂ → ℕ := fun p => (analyticOrderAt riemannXi p).toNat
  let kf : ℂ → ℤ := fun p => if p = 1 then -1 else if p ∈ Z then (mo p : ℤ) else 1
  let r : ℂ → ℂ := fun p =>
    if p = 0 then -(deriv riemannZeta 0 / riemannZeta 0) else -(kf p : ℂ) * ((x : ℂ) ^ p / p)
  have h1Z : (1 : ℂ) ∉ Z := fun h => (hZprop 1 h).2.1 rfl
  have h0Z : (0 : ℂ) ∉ Z := fun h => (hZprop 0 h).1 rfl
  have h1T : (1 : ℂ) ∉ T := fun h => by have := (hTprop 1 h).1; simp at this; linarith
  have h0T : (0 : ℂ) ∉ T := fun h => by have := (hTprop 0 h).1; simp at this
  have hZT : ∀ p ∈ T, p ∉ Z := fun p hp hpZ => by
    linarith [(hTprop p hp).1, (hZprop p hpZ).2.2.1]
  have hloc : ∀ p ∈ S, ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ p ∧
      ∀ᶠ s in 𝓝[≠] p, F s = r p / (s - p) + φ s := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · obtain ⟨φ, h1, h2⟩ := exists_local_pole_one hx0
      refine ⟨φ, h1, ?_⟩
      have hr : r 1 = -(((-1 : ℤ) : ℤ) : ℂ) * ((x : ℂ) ^ (1 : ℂ) / 1) := by simp [r, kf]
      rw [hr]; exact h2
    rcases Finset.mem_insert.mp hp with rfl | hp
    · obtain ⟨φ, h1, h2⟩ := exists_local_pole_origin hx0
      refine ⟨φ, h1, ?_⟩
      have hr : r 0 = -(deriv riemannZeta 0 / riemannZeta 0) := by simp [r]
      rw [hr]; exact h2
    rcases Finset.mem_union.mp hp with hpZ | hpT
    · obtain ⟨hp0, hp1, -⟩ := hZprop p hpZ
      have hm : analyticOrderAt riemannXi p = (mo p : ℕ) :=
        (ENat.natCast_toNat (analyticOrderAt_riemannXi_ne_top p)).symm
      obtain ⟨φ, h1, h2⟩ := exists_local_pole_zero hx0 ((hZmem p).mp hpZ).1 hm
      refine ⟨φ, h1, ?_⟩
      have hr : r p = -(((mo p : ℕ) : ℤ) : ℂ) * ((x : ℂ) ^ p / p) := by
        simp [r, kf, hp0, hp1, hpZ]
      rw [hr]; exact h2
    · obtain ⟨m, hm0, -, rfl⟩ := (hTmem p).mp hpT
      obtain ⟨φ, h1, h2⟩ := exists_local_pole_trivial hx0 hm0
      refine ⟨φ, h1, ?_⟩
      have hre := (hTprop _ hpT).1
      have hp0 : -(2 * (m : ℂ)) ≠ 0 := fun h => by rw [h] at hre; simp at hre
      have hp1 : -(2 * (m : ℂ)) ≠ 1 := fun h => by rw [h] at hre; simp at hre; linarith
      have hr : r (-(2 * (m : ℂ))) = -(((1 : ℤ)) : ℂ) *
          ((x : ℂ) ^ (-(2 * (m : ℂ))) / (-(2 * (m : ℂ)))) := by
        simp only [r, kf, hp0, hp1, hZT _ hpT, ite_false]
      rw [hr]; exact h2
  set rect := RectilinearRectangle.ofBounds (-(U : ℝ)) c (-R) R with hrect
  have hKre : ∀ s ∈ rect.carrier, -(U : ℝ) ≤ s.re ∧ s.re ≤ c ∧ -R ≤ s.im ∧ s.im ≤ R := by
    intro s hs
    obtain ⟨h1, h2⟩ := Complex.mem_reProdIm.mp hs
    simp only [hrect, RectilinearRectangle.ofBounds_first_re,
      RectilinearRectangle.ofBounds_second_re, RectilinearRectangle.ofBounds_first_im,
      RectilinearRectangle.ofBounds_second_im] at h1 h2
    rw [Set.uIcc_of_le (by linarith)] at h1 h2
    exact ⟨h1.1, h1.2, h2.1, h2.2⟩
  have hdiff : ∀ s ∈ rect.carrier, s ∉ S → DifferentiableAt ℂ F s := by
    intro s hsK hsS
    obtain ⟨k1, k2, k3, k4⟩ := hKre s hsK
    have hs1 : s ≠ 1 := fun h => hsS (by simp [S, h])
    have hs0 : s ≠ 0 := fun h => hsS (by simp [S, h])
    have hζs : riemannZeta s ≠ 0 := by
      intro h0
      rcases le_or_gt 0 s.re with hre | hre
      · rcases le_or_gt 1 s.re with hre1 | hre1
        · exact riemannZeta_ne_zero_of_one_le_re hre1 h0
        · have hnt : s ∈ riemannZetaNontrivialZeros := ⟨h0, hre, hre1.le⟩
          have hIm : |s.im| < R := lt_of_le_of_ne (abs_le.mpr ⟨k3, k4⟩) (hRz s hnt)
          exact hsS (by simp [S, (hZmem s).mpr ⟨hnt, hIm⟩])
      · obtain ⟨n, hn, rfl⟩ := exists_eq_neg_two_mul_of_riemannZeta_eq_zero_of_re_neg hre h0
        have hle : (2 * n : ℝ) ≤ U := by simp at k1; linarith
        have hle' : 2 * n ≤ U := by exact_mod_cast hle
        have hT' : -(2 * (n : ℂ)) ∈ T := (hTmem _).mpr ⟨n, hn, by omega, rfl⟩
        exact hsS (by simp [S, hT'])
    have hζa : AnalyticAt ℂ riemannZeta s := by
      rw [Complex.analyticAt_iff_eventually_differentiableAt]
      filter_upwards [isOpen_compl_singleton.mem_nhds (show s ∈ ({1}ᶜ : Set ℂ) from hs1)]
        with t ht using differentiableAt_riemannZeta ht
    have hx0' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    exact ((hζa.deriv.differentiableAt.div hζa.differentiableAt hζs).neg).mul
      ((differentiableAt_id.const_cpow (Or.inl hx0')).div differentiableAt_id hs0)
  obtain ⟨g, hg, hfg⟩ := Complex.exists_differentiableOn_eq_add_sum_div_sub _ S r F hloc
    fun s hs hsS => (hdiff s hs hsS).differentiableWithinAt
  have hin : ∀ p ∈ S, rect.first.re < p.re ∧ p.re < rect.second.re ∧ rect.first.im < p.im ∧
      p.im < rect.second.im := by
    intro p hp
    simp only [hrect, RectilinearRectangle.ofBounds_first_re,
      RectilinearRectangle.ofBounds_second_re, RectilinearRectangle.ofBounds_first_im,
      RectilinearRectangle.ofBounds_second_im]
    rcases Finset.mem_insert.mp hp with rfl | hp
    · rw [one_re, one_im]; exact ⟨by linarith, hc1, by linarith, hR⟩
    rcases Finset.mem_insert.mp hp with rfl | hp
    · rw [zero_re, zero_im]; exact ⟨by linarith, by linarith, by linarith, hR⟩
    rcases Finset.mem_union.mp hp with hpZ | hpT
    · obtain ⟨-, -, h1, h2, h3⟩ := hZprop p hpZ
      exact ⟨by linarith, by linarith, (abs_lt.mp h3).1, (abs_lt.mp h3).2⟩
    · obtain ⟨h1, h2, h3⟩ := hTprop p hpT
      exact ⟨h2, by linarith, by rw [h3]; linarith, by rw [h3]; exact hR⟩
  rw [RectilinearRectangle.boundaryIntegral_eq_two_pi_mul_I_mul_sum rect S r F g hin hg hfg]
  congr 1
  -- the residue sum
  have hcard : ∀ p ∈ Z, (NF.filter (fun n => z n = p)).card = mo p := by
    intro p hp
    have hpR := (hZprop p hp).2.2.2.2
    have := finite_of_card_eq_analyticOrderAt hz p
    have h := hz p
    rw [ENat.card_eq_coe_natCard, Nat.subtype_card (NF.filter (fun n => z n = p)) (by
      intro n
      simp only [NF, Finset.mem_filter, Set.Finite.mem_toFinset, mem_ofPred_eq]
      exact ⟨And.right, fun h => ⟨h ▸ hpR, h⟩⟩),
      ← ENat.natCast_toNat (analyticOrderAt_riemannXi_ne_top p)] at h
    exact_mod_cast h
  have htsum : ∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0) =
      ∑ p ∈ Z, (mo p : ℂ) * ((x : ℂ) ^ p / p) := by
    rw [tsum_eq_sum (s := NF) (fun n hn => ite_eq_right (by simpa [NF] using hn)),
      Finset.sum_congr rfl (fun n hn => ite_eq_left (by simpa [NF] using hn)),
      Finset.sum_comp (fun p => (x : ℂ) ^ p / p) z]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hcard p hp, nsmul_eq_mul]
  have hinj : Set.InjOn (fun m : ℕ => -(2 * (m : ℂ))) (Finset.Icc 1 (U / 2) : Set ℕ) := by
    intro a _ b _ h
    simp only [neg_inj, mul_eq_mul_left_iff, two_ne_zero, or_false, Nat.cast_inj] at h
    exact h
  have hdisj : Disjoint Z T := Finset.disjoint_right.mpr hZT
  rw [Finset.sum_insert (by simp [h1Z, h1T]), Finset.sum_insert (by simp [h0Z, h0T]),
    Finset.sum_union hdisj, htsum, Finset.sum_image hinj]
  have hr1 : r 1 = x := by simp [r, kf]
  have hr0 : r 0 = -(deriv riemannZeta 0 / riemannZeta 0) := by simp [r]
  have hrZ : ∑ p ∈ Z, r p = -∑ p ∈ Z, (mo p : ℂ) * ((x : ℂ) ^ p / p) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hp0, hp1, -⟩ := hZprop p hp
    simp [r, kf, hp0, hp1, hp]
  have hrT : ∑ m ∈ Finset.Icc 1 (U / 2), r (-(2 * (m : ℂ))) =
      ∑ m ∈ Finset.Icc 1 (U / 2), (x : ℂ) ^ (-(2 * (m : ℂ))) / (2 * (m : ℂ)) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hpT : -(2 * (m : ℂ)) ∈ T := Finset.mem_image.mpr ⟨m, hm, rfl⟩
    have hre := (hTprop _ hpT).1
    have hp0 : -(2 * (m : ℂ)) ≠ 0 := fun h => by rw [h] at hre; simp at hre
    have hp1 : -(2 * (m : ℂ)) ≠ 1 := fun h => by rw [h] at hre; simp at hre; linarith
    simp only [r, kf, hp0, hp1, hZT _ hpT, ite_false]
    rw [div_neg]
    push_cast
    ring
  rw [hr1, hr0, hrZ, hrT]
  ring

end RiemannXi

/-! ### The contribution of the trivial zeros -/

/-- For `y ≥ 3/2`, `‖½ log (1 - y⁻²)‖ ≤ ½`. -/
theorem norm_half_log_one_sub_zpow_neg_two_le {y : ℝ} (hy : 3 / 2 ≤ y) :
    ‖(1 / 2 : ℂ) * (Real.log (1 - y ^ (-2 : ℤ)) : ℂ)‖ ≤ 1 / 2 := by
  have hw : y ^ (-2 : ℤ) = (y ^ 2)⁻¹ := by rw [zpow_neg]; norm_cast
  rw [hw]
  have hsq : 9 / 4 ≤ y ^ 2 := by nlinarith
  have hw0 : 0 < (y ^ 2)⁻¹ := by positivity
  have hw1 : (y ^ 2)⁻¹ * y ^ 2 = 1 := inv_mul_cancel₀ (by positivity)
  have hw49 : (y ^ 2)⁻¹ ≤ 4 / 9 := by nlinarith
  set u : ℝ := 1 - (y ^ 2)⁻¹ with hu
  have hu0 : 5 / 9 ≤ u := by linarith
  have hu1 : u ≤ 1 := by linarith
  have hupos : 0 < u := by linarith
  have hlog : |Real.log u| ≤ 1 := by
    rw [abs_le]; constructor
    · have h1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hupos)
      rw [Real.log_inv] at h1
      have h2 : u * u⁻¹ = 1 := mul_inv_cancel₀ hupos.ne'
      have h3 := mul_nonneg (by linarith : 0 ≤ u - 5 / 9) (inv_pos.mpr hupos).le
      linarith
    · linarith [Real.log_nonpos hupos.le hu1]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  norm_num
  linarith

/-- **The trivial zeros in the explicit formula**: for `x > 1`,
`∑_{m = 1}^{k} x^{-2m}/(2m) → -½ log (1 - x⁻²)` as `k → ∞`. -/
theorem tendsto_sum_cpow_neg_two_mul_div_two_mul {x : ℝ} (hx : 1 < x) :
    Tendsto (fun k : ℕ => ∑ m ∈ Finset.Icc 1 k, (x : ℂ) ^ (-(2 * (m : ℂ))) / (2 * (m : ℂ)))
      atTop (𝓝 (-((1 / 2 : ℂ) * (Real.log (1 - x ^ (-2 : ℤ)) : ℂ)))) := by
  have hx0 : 0 < x := by linarith
  set y : ℝ := x ^ (-2 : ℤ) with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y < 1 := by
    rw [hy, zpow_neg]
    apply inv_lt_one_of_one_lt₀
    have : (1 : ℝ) < x ^ (2 : ℕ) := by nlinarith
    exact_mod_cast this
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one
    (show |y| < 1 by rw [abs_of_nonneg hy0]; exact hy1)
  have h := (Complex.continuous_ofReal.tendsto _).comp ((hs.mul_left (1 / 2)).tendsto_sum_nat)
  have htarget : (((1 / 2) * -Real.log (1 - y) : ℝ) : ℂ) =
      -((1 / 2 : ℂ) * (Real.log (1 - y) : ℂ)) := by push_cast; ring
  rw [htarget] at h
  have key : ∀ N : ℕ, (x : ℂ) ^ (-(2 * (N : ℂ))) = ((y ^ N : ℝ) : ℂ) := by
    intro N
    have : -(2 * (N : ℂ)) = (((-2 * N : ℤ)) : ℂ) := by push_cast; ring
    rw [this, Complex.cpow_intCast, hy, ← zpow_natCast, ← zpow_mul, Complex.ofReal_zpow]
  refine h.congr fun k => ?_
  simp only [Function.comp_apply]
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Complex.ofReal_sum]
  refine Finset.sum_congr (by simp) fun n _ => ?_
  rw [key]
  have hn : (1 + (n : ℂ)) ≠ 0 := by
    have : ((1 + n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact_mod_cast this
  push_cast
  field_simp
  ring
