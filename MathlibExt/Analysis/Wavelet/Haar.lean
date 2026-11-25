/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral

/-!
# The Haar function and the Haar system

The Haar function `H = 1_{[0,1/2)} - 1_{[1/2,1)}` (R. A. DeVore, *Nonlinear approximation*, Acta
Numerica 7 (1998), Section 3.5, (3.40)) is the wavelet of the simplest multiresolution
approximation, whose scaling function is `1_{[0,1)}` (S. Mallat, *Multiresolution
approximations and wavelet orthonormal bases of `L²(ℝ)`*, Trans. Amer. Math. Soc. 315 (1989),
Section 4, after (70)). Its dyadic dilates and translates `H_{j,k}(x) = 2^{j/2} H(2^j x - k)` form
the Haar system, which is orthonormal in `L²(ℝ)` (`integral_haarSystem_mul_haarSystem`). Its
completeness, that is that the Haar system is an orthonormal basis of `L²(ℝ)` and that
`1_{[0,1)}` with the `H_{j,k}` fitted to `[0,1)` is an orthonormal basis of `L²[0,1)`
(DeVore (3.47)), is recorded in `WantedExt.Analysis.Wavelet.HaarBasisWanted`.

## Main declarations

* `haarFunction` : `H`.
* `haarSystem j k` : `x ↦ 2^{j/2} H(2^j x - k)`.
* `integral_haarFunction` : `∫ H = 0` (one vanishing moment).
* `integral_haarFunction_sq` : `∫ H² = 1`.
* `integral_haarSystem_mul_haarSystem` : `∫ H_{j,k} H_{j',k'} = δ_{(j,k),(j',k')}`.
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace MathlibExt.Analysis.Wavelet.Haar

/-- **Haar function.** `H = 1_{[0,1/2)} - 1_{[1/2,1)}`, equal to `1` on `[0, 1/2)`, to `-1`
on `[1/2, 1)` and to `0` elsewhere (R. A. DeVore, *Nonlinear approximation*, Acta Numerica 7
(1998), (3.40); S. Mallat, Trans. Amer. Math. Soc. 315 (1989), Section 4, after (70)). -/
def haarFunction (x : ℝ) : ℝ :=
  (Ico (0 : ℝ) (1 / 2)).indicator 1 x - (Ico (1 / 2 : ℝ) 1).indicator 1 x

/-- **Haar system.** `haarSystem j k x = 2^{j/2} H(2^j x - k)` for `j, k ∈ ℤ`, the dyadic
dilates and translates of the Haar function, normalized in `L²(ℝ)` (S. Mallat, Trans. Amer.
Math. Soc. 315 (1989), the family `√(2^j) ψ(2^j x - k)` of Section 4 (after (70)) with `ψ = H`;
DeVore, *Nonlinear approximation*, (3.41) for `0 ≤ k < 2^j`). -/
def haarSystem (j k : ℤ) (x : ℝ) : ℝ :=
  (2 : ℝ) ^ ((j : ℝ) / 2) * haarFunction ((2 : ℝ) ^ j * x - k)

theorem haarFunction_eq_one {x : ℝ} (hx : x ∈ Ico (0 : ℝ) (1 / 2)) : haarFunction x = 1 := by
  have : x ∉ Ico (1 / 2 : ℝ) 1 := fun h => by linarith [hx.2, h.1]
  rw [haarFunction, indicator_of_mem hx, indicator_of_notMem this]
  simp

theorem haarFunction_eq_neg_one {x : ℝ} (hx : x ∈ Ico (1 / 2 : ℝ) 1) :
    haarFunction x = -1 := by
  have : x ∉ Ico (0 : ℝ) (1 / 2) := fun h => by linarith [hx.1, h.2]
  rw [haarFunction, indicator_of_mem hx, indicator_of_notMem this]
  simp

theorem haarFunction_eq_zero {x : ℝ} (hx : x ∉ Ico (0 : ℝ) 1) : haarFunction x = 0 := by
  have h1 : x ∉ Ico (0 : ℝ) (1 / 2) := fun h => hx ⟨h.1, by linarith [h.2]⟩
  have h2 : x ∉ Ico (1 / 2 : ℝ) 1 := fun h => hx ⟨by linarith [h.1], h.2⟩
  rw [haarFunction, indicator_of_notMem h1, indicator_of_notMem h2]
  simp

/-- **The Haar function has mean zero**: `∫ H = 0`, its single vanishing moment. -/
theorem integral_haarFunction : ∫ x, haarFunction x = 0 := by
  have hint : ∀ a b : ℝ, Integrable ((Ico a b).indicator (1 : ℝ → ℝ)) := fun a b => by
    rw [integrable_indicator_iff measurableSet_Ico]
    exact integrableOn_const (by simp)
  unfold haarFunction
  rw [integral_sub (hint _ _) (hint _ _), integral_indicator_one measurableSet_Ico,
    integral_indicator_one measurableSet_Ico, Measure.real, Measure.real, Real.volume_Ico,
    Real.volume_Ico]
  norm_num

/-- **The Haar function has unit `L²` norm**: `∫ H² = 1`. -/
theorem integral_haarFunction_sq : ∫ x, haarFunction x ^ 2 = 1 := by
  have hsq : (fun x => haarFunction x ^ 2) = (Ico (0 : ℝ) 1).indicator 1 := by
    funext x
    by_cases h1 : x ∈ Ico (0 : ℝ) (1 / 2)
    · have : x ∈ Ico (0 : ℝ) 1 := ⟨h1.1, by linarith [h1.2]⟩
      simp [haarFunction_eq_one h1, this]
    · by_cases h2 : x ∈ Ico (1 / 2 : ℝ) 1
      · have : x ∈ Ico (0 : ℝ) 1 := ⟨by linarith [h2.1], h2.2⟩
        simp [haarFunction_eq_neg_one h2, this]
      · have : x ∉ Ico (0 : ℝ) 1 := fun h => by
          rcases lt_or_ge x (1 / 2) with hx | hx
          · exact h1 ⟨h.1, hx⟩
          · exact h2 ⟨hx, h.2⟩
        simp [haarFunction_eq_zero this, this]
  rw [hsq, integral_indicator_one measurableSet_Ico, Measure.real, Real.volume_Ico]
  norm_num

/-! ### Orthonormality of the Haar system -/

-- The value of `H` on the half-integer interval `[m/2, (m+1)/2)`.
def haarStep (m : ℤ) : ℝ := if m = 0 then 1 else if m = 1 then -1 else 0

theorem haarFunction_eq_haarStep {m : ℤ} {t : ℝ} (ht : t ∈ Ico ((m : ℝ) / 2) ((m + 1) / 2)) :
    haarFunction t = haarStep m := by
  obtain ⟨h1, h2⟩ := ht
  rcases lt_trichotomy m 0 with hm | rfl | hm
  · have hm' : (m : ℝ) + 1 ≤ 0 := by exact_mod_cast hm
    rw [haarFunction_eq_zero fun h => by linarith [h.1]]
    simp [haarStep, show m ≠ 0 by omega, show m ≠ 1 by omega]
  · simp only [haarStep, ↓reduceIte]
    exact haarFunction_eq_one ⟨by simpa using h1, by simpa using h2⟩
  · rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm2
    · simp only [haarStep, one_ne_zero, ↓reduceIte]
      exact haarFunction_eq_neg_one ⟨by simpa using h1, by norm_num at h2; linarith⟩
    · have hm2' : (2 : ℝ) ≤ m := by exact_mod_cast hm2
      rw [haarFunction_eq_zero fun h => by linarith [h.2]]
      simp [haarStep, show m ≠ 0 by omega, show m ≠ 1 by omega]

-- Dyadic change of variables: `∫ g(2^j x - k) dx = 2^{-j} ∫ g`.
theorem integral_comp_dyadic (g : ℝ → ℝ) (j k : ℤ) :
    ∫ x, g ((2 : ℝ) ^ j * x - k) = (2 : ℝ) ^ (-j) * ∫ y, g y := by
  have := Measure.integral_comp_mul_left (fun z => g (z - k)) ((2 : ℝ) ^ j)
  rw [this, integral_sub_right_eq_self (fun z => g z) (k : ℝ), smul_eq_mul, zpow_neg,
    abs_of_pos (inv_pos.mpr (zpow_pos (by norm_num) j))]

-- Haar functions of the same scale and different translations have disjoint supports.
theorem haarFunction_mul_haarFunction_add_int {n : ℤ} (hn : n ≠ 0) (y : ℝ) :
    haarFunction y * haarFunction (y + n) = 0 := by
  by_cases hy : y ∈ Ico (0 : ℝ) 1
  · have : y + n ∉ Ico (0 : ℝ) 1 := by
      intro h
      rcases lt_or_gt_of_ne hn with hn' | hn'
      · have : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
        linarith [h.1, hy.2]
      · have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
        linarith [h.2, hy.1]
    rw [haarFunction_eq_zero this, mul_zero]
  · rw [haarFunction_eq_zero hy, zero_mul]

-- On `[0, 1)`, a coarser Haar function is constant: for `d ≥ 1`,
-- `y ↦ H(2^{-d} (y + k') - k)` takes one value on `[0, 1)`.
theorem exists_haarFunction_coarse_const (d : ℕ) (k k' : ℤ) :
    ∃ v : ℝ, ∀ y ∈ Ico (0 : ℝ) 1,
      haarFunction (((2 : ℝ) ^ (d + 1))⁻¹ * (y + k') - k) = v := by
  set q : ℤ := 2 ^ d
  have hq : 0 < q := by positivity
  refine ⟨haarStep (k' / q - 2 * k), fun y hy => haarFunction_eq_haarStep ?_⟩
  have hdiv := Int.mul_ediv_add_emod k' q
  have hr0 := Int.emod_nonneg k' hq.ne'
  have hrq := Int.emod_lt_of_pos k' hq
  have hqR : ((q : ℤ) : ℝ) = (2 : ℝ) ^ d := by simp [q]
  have h2q : (2 : ℝ) ^ (d + 1) = 2 * (q : ℝ) := by rw [hqR, pow_succ]; ring
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  set m0 := k' / q
  set r := k' % q
  have hk' : (k' : ℝ) = q * m0 + r := by
    have : k' = q * m0 + r := hdiv.symm
    exact_mod_cast this
  have hr0' : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  have hrq' : (r : ℝ) + 1 ≤ q := by exact_mod_cast (show r + 1 ≤ q by omega)
  rw [h2q, hk']
  push_cast
  constructor
  · rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have : (m0 : ℝ) ≤ (2 * (q : ℝ))⁻¹ * (y + (q * m0 + r)) * 2 := by
      rw [show (2 * (q : ℝ))⁻¹ * (y + (q * m0 + r)) * 2 = (y + q * m0 + r) / q by
        field_simp; ring]
      rw [le_div_iff₀ hqpos]; nlinarith [hy.1]
    linarith
  · rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have : (2 * (q : ℝ))⁻¹ * (y + (q * m0 + r)) * 2 < m0 + 1 := by
      rw [show (2 * (q : ℝ))⁻¹ * (y + (q * m0 + r)) * 2 = (y + q * m0 + r) / q by
        field_simp; ring]
      rw [div_lt_iff₀ hqpos]; nlinarith [hy.2]
    linarith

-- Haar functions at two different scales are orthogonal.
theorem integral_haarSystem_mul_haarSystem_of_lt {j j' : ℤ} (hjj : j < j') (k k' : ℤ) :
    ∫ x, haarSystem j k x * haarSystem j' k' x = 0 := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, j' - j = d + 1 := ⟨(j' - j - 1).toNat, by omega⟩
  obtain ⟨v, hv⟩ := exists_haarFunction_coarse_const d k k'
  set g : ℝ → ℝ := fun z =>
    haarFunction (((2 : ℝ) ^ (d + 1))⁻¹ * (z + k') - k) * haarFunction z
  have hscale : ∀ x : ℝ,
      ((2 : ℝ) ^ (d + 1))⁻¹ * ((2 : ℝ) ^ j' * x - k' + k') = (2 : ℝ) ^ j * x := by
    intro x
    have : (2 : ℝ) ^ j' = (2 : ℝ) ^ (d + 1) * (2 : ℝ) ^ j := by
      rw [show j' = ((d + 1 : ℕ) : ℤ) + j by push_cast; omega, zpow_add₀ (by norm_num),
        zpow_natCast]
    rw [sub_add_cancel, this]; field_simp
  have hint : ∀ x, haarSystem j k x * haarSystem j' k' x =
      ((2 : ℝ) ^ ((j : ℝ) / 2) * (2 : ℝ) ^ ((j' : ℝ) / 2)) * g ((2 : ℝ) ^ j' * x - k') := by
    intro x
    simp only [haarSystem, g, hscale]
    ring
  have hg : ∀ z, g z = v * haarFunction z := by
    intro z
    by_cases hz : z ∈ Ico (0 : ℝ) 1
    · simp only [g, hv z hz]
    · simp only [g, haarFunction_eq_zero hz, mul_zero]
  simp_rw [hint]
  rw [integral_const_mul, integral_comp_dyadic, show (∫ y, g y) = 0 by
    simp_rw [hg]; rw [integral_const_mul, integral_haarFunction, mul_zero]]
  simp

/-- **Orthonormality of the Haar system.** For `j, k, j', k' ∈ ℤ`,
`∫ H_{j,k} H_{j',k'} = 1` if `(j, k) = (j', k')` and `0` otherwise, where
`H_{j,k}(x) = 2^{j/2} H(2^j x - k)` (S. Mallat, *Multiresolution approximations and wavelet
orthonormal bases of `L²(ℝ)`*, Trans. Amer. Math. Soc. 315 (1989), Section 4, after (70); R. A.
DeVore, *Nonlinear approximation*, Acta Numerica 7 (1998), Section 3.5). Functions of the same scale
have disjoint supports, and at two different scales the coarser one is constant on the support
of the finer one, which has mean zero. Completeness is recorded in `WantedExt`. -/
theorem integral_haarSystem_mul_haarSystem (j k j' k' : ℤ) :
    ∫ x, haarSystem j k x * haarSystem j' k' x = if (j, k) = (j', k') then 1 else 0 := by
  rcases lt_trichotomy j j' with hjj | rfl | hjj
  · rw [integral_haarSystem_mul_haarSystem_of_lt hjj]
    simp [hjj.ne]
  · set G : ℝ → ℝ := fun y => haarFunction y * haarFunction (y + (k - k' : ℤ)) with hG
    have hint : ∀ x, haarSystem j k x * haarSystem j k' x =
        (2 : ℝ) ^ j * G ((2 : ℝ) ^ j * x - k) := by
      intro x
      have h2 : (2 : ℝ) ^ ((j : ℝ) / 2) * (2 : ℝ) ^ ((j : ℝ) / 2) = (2 : ℝ) ^ j := by
        rw [← Real.rpow_add (by norm_num), add_halves, Real.rpow_intCast]
      simp only [haarSystem, G]
      push_cast
      rw [show (2 : ℝ) ^ j * x - k + (k - k') = (2 : ℝ) ^ j * x - k' by ring]
      linear_combination (haarFunction ((2 : ℝ) ^ j * x - k) *
        haarFunction ((2 : ℝ) ^ j * x - k')) * h2
    rw [show (fun x => haarSystem j k x * haarSystem j k' x) =
        fun x => (2 : ℝ) ^ j * G ((2 : ℝ) ^ j * x - k) from funext hint]
    rw [integral_const_mul, integral_comp_dyadic, ← mul_assoc, ← zpow_add₀ (by norm_num),
      add_neg_cancel, zpow_zero, one_mul]
    by_cases hkk : k = k'
    · subst hkk
      simp only [G, sub_self, Int.cast_zero, add_zero, ↓reduceIte]
      simpa [sq] using integral_haarFunction_sq
    · simp only [G, haarFunction_mul_haarFunction_add_int (sub_ne_zero.mpr hkk)]
      simp [hkk]
  · rw [show (fun x => haarSystem j k x * haarSystem j' k' x) =
        fun x => haarSystem j' k' x * haarSystem j k x from funext fun x => mul_comm _ _,
      integral_haarSystem_mul_haarSystem_of_lt hjj]
    simp [hjj.ne']

end MathlibExt.Analysis.Wavelet.Haar
