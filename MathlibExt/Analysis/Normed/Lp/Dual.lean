/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Duality of `ℓ^p` spaces

For `1 ≤ p < ∞` and `q` the Hölder conjugate of `p`, the continuous dual of
`ℓ^p(ι, 𝕜)` is isometrically isomorphic to `ℓ^q(ι, 𝕜)`. The isomorphism sends
`a ∈ ℓ^q` to the functional `x ↦ ∑' i, a i * x i`.

This is the sequence-space form of the duality theorem for `L^p` spaces; it is the
companion in the `v1` Functional Analysis book of the Hölder and Minkowski
inequalities and of the definition of the `L^p` norm (April 6, 2021 section).
Mathlib provides the pairing in one direction (`lp.dualPairing`, with the norm bound
`lp.norm_dualPairing`) but not surjectivity or the isometry, which are proved here.
The heart of the proof is the coefficient estimate: given `Φ` in the dual, the
sequence `i ↦ Φ (lp.single p i 1)` lies in `ℓ^q` with norm at most `‖Φ‖`, proved
with the usual test vector `conj (a i) * |a i| ^ (q - 2)` on finite subsets.

## Main declarations

* `lpDualPairing` : the pairing `ℓ^q →L[𝕜] (ℓ^p →L[𝕜] 𝕜)`.
* `lpDualEquiv` : the isometric isomorphism `ℓ^q ≃ₗᵢ[𝕜] (ℓ^p →L[𝕜] 𝕜)`.
* `lpDualPairing_apply` : the pairing is given by `∑' i, a i * x i`.
* `lpDualPairing_norm` : the pairing is norm-preserving.
-/

@[expose] public section

namespace MathlibExt.Analysis.Normed.Lp.Dual

open scoped ENNReal

section Helpers

variable {ι : Type*} {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞} [Fact (1 ≤ p)]
  [p.HolderConjugate q]

-- The Hölder relation in `ℝ≥0∞` form.
omit [Fact (1 ≤ p)] in
private theorem holderConjugate_inv_add_inv : p⁻¹ + q⁻¹ = 1 := by
  have h := ENNReal.HolderTriple.inv_add_inv_eq_inv p q 1
  rwa [inv_one] at h

-- The Hölder conjugate of `p ≥ 1` is at least `1`.
omit [Fact (1 ≤ p)] in
theorem one_le_of_holderConjugate (_hp : 1 ≤ p) : 1 ≤ q := by
  have hq : q⁻¹ ≤ 1 := by
    rw [← holderConjugate_inv_add_inv (p := p) (q := q)]
    exact le_add_of_nonneg_left zero_le
  exact ENNReal.inv_le_one.mp hq

-- If `1 < p` then its Hölder conjugate is finite.
omit [Fact (1 ≤ p)] in
private theorem q_ne_top_of_one_lt (hp1 : 1 < p) : q ≠ ⊤ := by
  intro hq
  have h := holderConjugate_inv_add_inv (p := p) (q := q)
  rw [hq, ENNReal.inv_top, add_zero] at h
  have hp : p = 1 := ENNReal.inv_eq_one.mp h
  exact absurd hp (ne_of_gt hp1)

/-- The real-valued form of the Hölder relation and its consequences. -/
private theorem holderConjugate_real (hp_top : p ≠ ⊤) (hq_top : q ≠ ⊤) (hp1 : 1 < p) :
    (p.toReal)⁻¹ + (q.toReal)⁻¹ = 1 ∧ 1 < p.toReal ∧ 1 < q.toReal ∧
      p.toReal * q.toReal = p.toReal + q.toReal := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hq0 : q ≠ 0 :=
    (zero_lt_one.trans_le (one_le_of_holderConjugate (Fact.out : 1 ≤ p))).ne'
  have hreal : (p.toReal)⁻¹ + (q.toReal)⁻¹ = 1 := by
    have h2 := congrArg ENNReal.toReal (holderConjugate_inv_add_inv (p := p) (q := q))
    rw [ENNReal.toReal_add (ENNReal.inv_ne_top.mpr hp0) (ENNReal.inv_ne_top.mpr hq0),
      ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_one] at h2
    exact h2
  have hp_real : 1 < p.toReal := by
    have h := (ENNReal.toReal_lt_toReal (by simp) hp_top).mpr hp1
    simpa using h
  have hqpos : 0 < q.toReal := ENNReal.toReal_pos hq0 hq_top
  have hq_real : 1 < q.toReal := by
    have hpinv : (p.toReal)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp_real
    have hpinv_pos : 0 < (p.toReal)⁻¹ := inv_pos.mpr (zero_lt_one.trans hp_real)
    have hqinv : (q.toReal)⁻¹ < 1 := by linarith [hreal, hpinv_pos]
    calc (1 : ℝ) = q.toReal * (q.toReal)⁻¹ :=
          (mul_inv_cancel₀ hqpos.ne').symm
      _ < q.toReal * 1 := mul_lt_mul_of_pos_left hqinv hqpos
      _ = q.toReal := mul_one _
  have hp_real_ne : p.toReal ≠ 0 := (zero_lt_one.trans hp_real).ne'
  have hq_real_ne : q.toReal ≠ 0 := (zero_lt_one.trans hq_real).ne'
  have hprod : p.toReal * q.toReal = p.toReal + q.toReal := by
    have hmul : (p.toReal * q.toReal) * ((p.toReal)⁻¹ + (q.toReal)⁻¹)
        = p.toReal * q.toReal := by
      rw [hreal, mul_one]
    have e : (p.toReal * q.toReal) * ((p.toReal)⁻¹ + (q.toReal)⁻¹)
        = q.toReal + p.toReal := by
      rw [mul_add]
      have e1 : p.toReal * q.toReal * (p.toReal)⁻¹ = q.toReal := by
        rw [mul_comm p.toReal q.toReal, mul_assoc, mul_inv_cancel₀ hp_real_ne, mul_one]
      have e2 : p.toReal * q.toReal * (q.toReal)⁻¹ = p.toReal := by
        rw [mul_assoc, mul_inv_cancel₀ hq_real_ne, mul_one]
      rw [e1, e2]
    linarith [hmul, e]
  exact ⟨hreal, hp_real, hq_real, hprod⟩

/-- A coordinate of a dual functional is bounded by the functional's norm. -/
private theorem coeff_bound [DecidableEq ι] (Φ : StrongDual 𝕜 (lp (fun _ : ι => 𝕜) p)) (i : ι) :
    ‖Φ (lp.single p i (1 : 𝕜))‖ ≤ ‖Φ‖ := by
  classical
  have h1 := Φ.le_opNorm (lp.single p i (1 : 𝕜) : lp (fun _ : ι => 𝕜) p)
  rw [lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p)), norm_one, mul_one] at h1
  exact h1

-- Summing `a j * (single i 1) j` over `j` picks out `a i`.
omit [Fact (1 ≤ p)] [p.HolderConjugate q] in
private theorem tsum_mul_single [DecidableEq ι] (a : lp (fun _ : ι => 𝕜) q) (i : ι) :
    ∑' j, a j * ((lp.single p i (1 : 𝕜) : lp (fun _ : ι => 𝕜) p)) j = a i := by
  rw [tsum_eq_single i]
  · simp
  · intro j hj
    show a j * ((lp.single p i (1 : 𝕜) : lp (fun _ : ι => 𝕜) p)) j = 0
    rw [lp.single_apply_ne _ _ _ hj, mul_zero]

/-- The scalar identity behind the test vector: for `w : 𝕜`,
`(conj w * ‖w‖ ^ (q - 2)) * w = ‖w‖ ^ q`. -/
private theorem conj_mul_rpow (w : 𝕜) (hq : 0 < q.toReal) :
    ((starRingEnd 𝕜) w * (↑(‖w‖ ^ (q.toReal - 2)) : 𝕜)) * w
      = (↑(‖w‖ ^ q.toReal) : 𝕜) := by
  by_cases hw : w = 0
  · simp [hw, Real.zero_rpow (ne_of_gt hq)]
  · have hnorm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    calc ((starRingEnd 𝕜) w * (↑(‖w‖ ^ (q.toReal - 2)) : 𝕜)) * w
        = ((starRingEnd 𝕜) w * w) * (↑(‖w‖ ^ (q.toReal - 2)) : 𝕜) := by ring
      _ = (↑‖w‖ : 𝕜) ^ 2 * (↑(‖w‖ ^ (q.toReal - 2)) : 𝕜) := by rw [RCLike.conj_mul]
      _ = (↑(‖w‖ ^ q.toReal) : 𝕜) := by
          rw [← RCLike.ofReal_pow, ← RCLike.ofReal_mul, ← Real.rpow_two,
            ← Real.rpow_add hnorm_pos, show (2 : ℝ) + (q.toReal - 2) = q.toReal by ring]

/-- The finite-subset estimate for the coefficients of a dual functional, for `1 < p`.
This is where the test vector `conj (a i) * ‖a i‖ ^ (q - 2)` is used. -/
private theorem coeff_sum_le [DecidableEq ι] (hp1 : 1 < p) (hp_top : p ≠ ⊤)
    (Φ : StrongDual 𝕜 (lp (fun _ : ι => 𝕜) p)) (s : Finset ι) :
    ∑ i ∈ s, ‖Φ (lp.single p i (1 : 𝕜))‖ ^ q.toReal ≤ ‖Φ‖ ^ q.toReal := by
  classical
  have hq_top : q ≠ ⊤ := q_ne_top_of_one_lt hp1
  obtain ⟨hreal, hp_real, hq_real, hprod⟩ := holderConjugate_real hp_top hq_top hp1
  have hp_real_pos : 0 < p.toReal := zero_lt_one.trans hp_real
  have hq_real_pos : 0 < q.toReal := zero_lt_one.trans hq_real
  have hexp : p.toReal + (q.toReal - 2) * p.toReal = q.toReal := by
    have e1 : (q.toReal - 2) * p.toReal = p.toReal * q.toReal - 2 * p.toReal := by ring
    linarith [hprod, e1]
  set S : ℝ := ∑ i ∈ s, ‖Φ (lp.single p i (1 : 𝕜))‖ ^ q.toReal with hSdef
  have hS_nonneg : 0 ≤ S := Finset.sum_nonneg fun i _ => by positivity
  set c : ι → 𝕜 := fun i =>
    if i ∈ s then (starRingEnd 𝕜) (Φ (lp.single p i (1 : 𝕜))) *
      (↑(‖Φ (lp.single p i (1 : 𝕜))‖ ^ (q.toReal - 2)) : 𝕜) else 0 with hcdef
  set x : lp (fun _ : ι => 𝕜) p := ∑ i ∈ s, lp.single p i (c i) with hxdef
  have hc_apply : ∀ i ∈ s, c i = (starRingEnd 𝕜) (Φ (lp.single p i (1 : 𝕜))) *
      (↑(‖Φ (lp.single p i (1 : 𝕜))‖ ^ (q.toReal - 2)) : 𝕜) :=
    fun i hi => by simp only [hcdef, hi, ite_true]
  have hcoeff : ∀ i ∈ s, ‖c i‖ ^ p.toReal
      = ‖Φ (lp.single p i (1 : 𝕜))‖ ^ q.toReal := by
    intro i hi
    rw [hc_apply i hi]
    by_cases hai : Φ (lp.single p i (1 : 𝕜)) = 0
    · simp [hai, Real.zero_rpow (ne_of_gt hp_real_pos), Real.zero_rpow (ne_of_gt hq_real_pos)]
    · have hnorm_pos : 0 < ‖Φ (lp.single p i (1 : 𝕜))‖ := norm_pos_iff.mpr hai
      have h1 : ‖(starRingEnd 𝕜) (Φ (lp.single p i (1 : 𝕜))) *
            (↑(‖Φ (lp.single p i (1 : 𝕜))‖ ^ (q.toReal - 2)) : 𝕜)‖
          = ‖Φ (lp.single p i (1 : 𝕜))‖ * ‖Φ (lp.single p i (1 : 𝕜))‖ ^ (q.toReal - 2) := by
        rw [norm_mul, RCLike.norm_conj, RCLike.norm_ofReal,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      rw [h1, Real.mul_rpow (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _),
        ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_add hnorm_pos, hexp]
  have hnormx_pow : ‖x‖ ^ p.toReal = S := by
    rw [hxdef, lp.norm_sum_single hp_real_pos, hSdef]
    exact Finset.sum_congr rfl fun i hi => hcoeff i hi
  have hPhi : Φ x = (↑S : 𝕜) := by
    have hstep : ∀ i ∈ s, Φ (lp.single p i (c i))
        = (↑(‖Φ (lp.single p i (1 : 𝕜))‖ ^ q.toReal) : 𝕜) := by
      intro i hi
      have hsplit : lp.single p i (c i)
          = c i • (lp.single p i (1 : 𝕜) : lp (fun _ : ι => 𝕜) p) := by
        rw [← lp.single_smul]
        congr 1
        simp
      rw [hsplit, map_smul, smul_eq_mul, hc_apply i hi]
      exact conj_mul_rpow _ hq_real_pos
    rw [hxdef, map_sum, hSdef]
    rw [show (↑(∑ i ∈ s, ‖Φ (lp.single p i (1 : 𝕜))‖ ^ q.toReal) : 𝕜)
        = ∑ i ∈ s, (↑(‖Φ (lp.single p i (1 : 𝕜))‖ ^ q.toReal) : 𝕜) by simp]
    exact Finset.sum_congr rfl hstep
  have hnormx : ‖x‖ = S ^ (p.toReal)⁻¹ := by
    have h := Real.rpow_rpow_inv (norm_nonneg (a := x)) (ne_of_gt hp_real_pos)
    rw [hnormx_pow] at h
    exact h.symm
  have hle : S ≤ ‖Φ‖ * S ^ (p.toReal)⁻¹ := by
    have h1 : ‖Φ x‖ ≤ ‖Φ‖ * ‖x‖ := Φ.le_opNorm x
    rw [hPhi, RCLike.norm_ofReal, abs_of_nonneg hS_nonneg, hnormx] at h1
    exact h1
  rcases hS_nonneg.eq_or_lt with hS0 | hSpos
  · rw [← hS0]
    positivity
  · have hS1 : S = S ^ (q.toReal)⁻¹ * S ^ (p.toReal)⁻¹ := by
      rw [← Real.rpow_add hSpos, add_comm, hreal, Real.rpow_one]
    have hpos : 0 < S ^ (p.toReal)⁻¹ := Real.rpow_pos_of_pos hSpos _
    have hdiv : S ^ (q.toReal)⁻¹ ≤ ‖Φ‖ := by
      by_contra hcon
      push Not at hcon
      have hlt := mul_lt_mul_of_pos_right hcon hpos
      rw [← hS1] at hlt
      exact (not_lt_of_ge hle) hlt
    have hfinal : (S ^ (q.toReal)⁻¹) ^ q.toReal ≤ ‖Φ‖ ^ q.toReal :=
      Real.rpow_le_rpow (Real.rpow_nonneg hS_nonneg _) hdiv (le_of_lt hq_real_pos)
    have h2 : (S ^ (q.toReal)⁻¹) ^ q.toReal = S := by
      rw [← Real.rpow_mul hS_nonneg, inv_mul_cancel₀ (ne_of_gt hq_real_pos), Real.rpow_one]
    rw [h2] at hfinal
    exact hfinal

/-- The coefficients of a dual functional form an `ℓ^q` sequence of norm at most `‖Φ‖`. -/
private theorem exists_coeff [DecidableEq ι] (hp_top : p ≠ ⊤)
    (Φ : StrongDual 𝕜 (lp (fun _ : ι => 𝕜) p)) :
    ∃ a : lp (fun _ : ι => 𝕜) q, (∀ i, Φ (lp.single p i (1 : 𝕜)) = a i) ∧ ‖a‖ ≤ ‖Φ‖ := by
  classical
  rcases eq_or_lt_of_le (Fact.out : (1 : ℝ≥0∞) ≤ p) with h1 | h1
  · subst h1
    have hq : q = ⊤ :=
      ENNReal.HolderTriple.unique_of_ne_zero (1 : ℝ≥0∞) q (∞ : ℝ≥0∞) one_ne_zero
    subst hq
    have hmem : Memℓp (fun i => Φ (lp.single (1 : ℝ≥0∞) i (1 : 𝕜)) : ι → 𝕜) ⊤ :=
      memℓp_infty ⟨‖Φ‖, fun y hy => by
        obtain ⟨i, rfl⟩ := hy
        exact coeff_bound Φ i⟩
    refine ⟨⟨_, hmem⟩, fun i => rfl, ?_⟩
    exact lp.norm_le_of_forall_le (norm_nonneg _) fun i => coeff_bound Φ i
  · have hmem : Memℓp (fun i => Φ (lp.single p i (1 : 𝕜)) : ι → 𝕜) q :=
      memℓp_gen' fun s => coeff_sum_le h1 hp_top Φ s
    refine ⟨⟨_, hmem⟩, fun i => rfl, ?_⟩
    have hq_real_pos : 0 < q.toReal := by
      have hq_top : q ≠ ⊤ := q_ne_top_of_one_lt h1
      have h := (holderConjugate_real hp_top hq_top h1).2.2.1
      exact zero_lt_one.trans h
    exact lp.norm_le_of_forall_sum_le hq_real_pos (norm_nonneg _) fun s =>
      coeff_sum_le h1 hp_top Φ s

end Helpers

section Pairing

variable {ι : Type*} {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [p.HolderConjugate q]

/-- The canonical pairing `ℓ^q × ℓ^p → 𝕜`, as a continuous linear map
`ℓ^q →L[𝕜] (ℓ^p →L[𝕜] 𝕜)`. -/
noncomputable def lpDualPairing :
    lp (fun _ : ι => 𝕜) q →L[𝕜] StrongDual 𝕜 (lp (fun _ : ι => 𝕜) p) := by
  exact lp.dualPairing (K := 1) q p (fun _ => ContinuousLinearMap.mul 𝕜 𝕜)
    (fun _ => by rw [NNReal.coe_one]; exact ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜)

/-- The pairing is given by the sum of coordinatewise products. -/
theorem lpDualPairing_apply (a : lp (fun _ : ι => 𝕜) q)
    (x : lp (fun _ : ι => 𝕜) p) :
    lpDualPairing (𝕜 := 𝕜) (ι := ι) (p := p) (q := q) a x = ∑' i, a i * x i := by
  classical
  have h : (lp.dualPairing (K := 1) q p (fun _ => ContinuousLinearMap.mul 𝕜 𝕜)
      (fun _ => by rw [NNReal.coe_one]; exact ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜)) a x
      = ∑' i, a i * x i := by
    rw [lp.dualPairing_apply]
    refine tsum_congr fun i => ?_
    simp [ContinuousLinearMap.mul_apply']
  exact h

/-- The pairing has operator norm at most one. -/
theorem norm_lpDualPairing_le :
    ‖lpDualPairing (𝕜 := 𝕜) (ι := ι) (p := p) (q := q)‖ ≤ 1 := by
  classical
  have h := lp.norm_dualPairing (K := 1) (𝕜 := 𝕜) (ι := ι) (E := fun _ : ι => 𝕜)
      (F := fun _ : ι => 𝕜) (H := 𝕜) (p := q) (q := p)
      (fun _ => ContinuousLinearMap.mul 𝕜 𝕜)
      (fun _ => by rw [NNReal.coe_one]; exact ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜)
  exact_mod_cast h

/-- The pairing is surjective: every continuous linear functional on `ℓ^p` is given
by pairing with some `ℓ^q` sequence. -/
theorem lpDualPairing_surjective (hp_top : p ≠ ⊤) :
    Function.Surjective (lpDualPairing (𝕜 := 𝕜) (ι := ι) (p := p) (q := q)) := by
  classical
  intro Φ
  obtain ⟨a, ha, -⟩ := exists_coeff (q := q) hp_top Φ
  refine ⟨a, ?_⟩
  apply lp.ext_continuousLinearMap hp_top
  intro i
  apply ContinuousLinearMap.ext fun y => ?_
  -- It suffices to check on the scalar `1`, since both sides are linear in `y`.
  have h1 : (lpDualPairing (𝕜 := 𝕜) (ι := ι) (p := p) (q := q) a)
      (lp.single p i (1 : 𝕜) : lp (fun _ : ι => 𝕜) p)
      = Φ (lp.single p i (1 : 𝕜)) := by
    rw [lpDualPairing_apply, tsum_mul_single a i]
    exact (ha i).symm
  have hsmul : lp.single p i y
      = y • (lp.single p i (1 : 𝕜) : lp (fun _ : ι => 𝕜) p) := by
    rw [← lp.single_smul]
    congr 1
    rw [smul_eq_mul, mul_one]
  calc ((lpDualPairing (𝕜 := 𝕜) (ι := ι) (p := p) (q := q) a).comp
          (lp.singleContinuousLinearMap 𝕜 (fun _ : ι => 𝕜) p i)) y
      = (lpDualPairing (𝕜 := 𝕜) (ι := ι) (p := p) (q := q) a) (lp.single p i y) := by
        simp [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply]
    _ = y • (lpDualPairing (𝕜 := 𝕜) (ι := ι) (p := p) (q := q) a)
        (lp.single p i (1 : 𝕜) : lp (fun _ : ι => 𝕜) p) := by
        rw [hsmul, map_smul]
    _ = y • Φ (lp.single p i (1 : 𝕜)) := by rw [h1]
    _ = (Φ.comp (lp.singleContinuousLinearMap 𝕜 (fun _ : ι => 𝕜) p i)) y := by
        rw [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply, hsmul,
          map_smul]

/-- The pairing is norm-preserving. -/
theorem lpDualPairing_norm (hp_top : p ≠ ⊤) (a : lp (fun _ : ι => 𝕜) q) :
    ‖lpDualPairing (𝕜 := 𝕜) (ι := ι) (p := p) (q := q) a‖ = ‖a‖ := by
  classical
  apply le_antisymm
  · calc ‖lpDualPairing (𝕜 := 𝕜) (ι := ι) (p := p) (q := q) a‖
        ≤ ‖lpDualPairing (𝕜 := 𝕜) (ι := ι) (p := p) (q := q)‖ * ‖a‖ :=
          (lpDualPairing (𝕜 := 𝕜) (ι := ι) (p := p) (q := q)).le_opNorm a
      _ ≤ 1 * ‖a‖ := by
          gcongr
          exact norm_lpDualPairing_le
      _ = ‖a‖ := one_mul _
  · obtain ⟨b, hb, hbnorm⟩ := exists_coeff (q := q) hp_top
      (lpDualPairing (𝕜 := 𝕜) (ι := ι) (p := p) (q := q) a)
    have hba : b = a := by
      apply Subtype.ext
      funext i
      have h1 : (lpDualPairing (𝕜 := 𝕜) (ι := ι) (p := p) (q := q) a)
          (lp.single p i (1 : 𝕜) : lp (fun _ : ι => 𝕜) p) = a i := by
        rw [lpDualPairing_apply, tsum_mul_single a i]
      rw [← h1]
      exact (hb i).symm
    rw [hba] at hbnorm
    exact hbnorm

/-- The dual of `ℓ^p` is isometrically isomorphic to `ℓ^q`. -/
noncomputable def lpDualEquiv (hp_top : p ≠ ⊤) :
    lp (fun _ : ι => 𝕜) q ≃ₗᵢ[𝕜] StrongDual 𝕜 (lp (fun _ : ι => 𝕜) p) := by
  classical
  exact LinearIsometryEquiv.ofSurjective
    ⟨(lpDualPairing (𝕜 := 𝕜) (ι := ι) (p := p) (q := q)).toLinearMap,
      fun a => lpDualPairing_norm hp_top a⟩
    (lpDualPairing_surjective hp_top)

end Pairing

end MathlibExt.Analysis.Normed.Lp.Dual
