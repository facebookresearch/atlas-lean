/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Code.Percolation.DctItem2
import Code.Percolation.SharpnessUnconditional

open MeasureTheory Set Filter Topology Real
open scoped NNReal ENNReal

namespace StatMech

namespace Sharpness

open StatMech.Percolation StatMech.Lattice

variable {d : ℕ}









noncomputable def pBeta (J β : ℝ) : ℝ := 1 - Real.exp (-β * J)


theorem pBeta_lt_one (J β : ℝ) : pBeta J β < 1 := by
  have := Real.exp_pos (-β * J); unfold pBeta; linarith


theorem pBeta_nonneg {J β : ℝ} (h : 0 ≤ β * J) : 0 ≤ pBeta J β := by
  unfold pBeta
  have : Real.exp (-β * J) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  linarith




theorem pBeta_strictMono {J : ℝ} (hJ : 0 < J) : StrictMono (pBeta J) := by
  intro a b hab
  unfold pBeta
  have : -b * J < -a * J := by nlinarith
  have := Real.exp_lt_exp.mpr this
  linarith


theorem pBeta_toNNReal_le_one (J β : ℝ) : (pBeta J β).toNNReal ≤ 1 :=
  Real.toNNReal_le_one.mpr (le_of_lt (pBeta_lt_one J β))









noncomputable def betaTildeC (d : ℕ) (J : ℝ) : ℝ := -Real.log (1 - (tildePc d : ℝ)) / J




theorem pBeta_betaTildeC {J : ℝ} (hJ : 0 < J) (htc1 : (tildePc d : ℝ) < 1) :
    pBeta J (betaTildeC d J) = (tildePc d : ℝ) := by
  have h1ptc : 0 < 1 - (tildePc d : ℝ) := by linarith
  unfold pBeta betaTildeC
  have hexp : -(-Real.log (1 - (tildePc d : ℝ)) / J) * J = Real.log (1 - (tildePc d : ℝ)) := by
    field_simp
  rw [hexp, Real.exp_log h1ptc]; ring



theorem betaTildeC_pos {J : ℝ} (hJ : 0 < J) (hd : 0 < d) (htc1 : (tildePc d : ℝ) < 1) :
    0 < betaTildeC d J := by
  have hptc0 : 0 < (tildePc d : ℝ) := tildePc_pos hd
  have h1ptc : 0 < 1 - (tildePc d : ℝ) := by linarith
  unfold betaTildeC
  have hlog : Real.log (1 - (tildePc d : ℝ)) < 0 := Real.log_neg h1ptc (by linarith)
  exact div_pos (by linarith) hJ
















theorem one_sub_exp_secant (J a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    a * (1 - Real.exp (-b * J)) ≤ b * (1 - Real.exp (-a * J)) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  set θ := a / b with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθle1 : θ ≤ 1 := by rw [hθ, div_le_one hb]; exact hab
  have hθ1 : 0 ≤ 1 - θ := by linarith
  
  have hconv : ConvexOn ℝ univ (fun t => Real.exp (-t * J)) := by
    have hconv := (convexOn_exp).comp_affineMap
      ((LinearMap.toAffineMap ((-J) • LinearMap.id : ℝ →ₗ[ℝ] ℝ)))
    have hpre :
        (⇑((LinearMap.toAffineMap ((-J) • LinearMap.id : ℝ →ₗ[ℝ] ℝ)) : ℝ →ᵃ[ℝ] ℝ)) ⁻¹' univ
          = univ := by simp
    rw [hpre] at hconv
    convert hconv using 1
    funext t; simp [LinearMap.toAffineMap]; ring
  
  have hcc := hconv.2 (mem_univ b) (mem_univ (0 : ℝ)) hθ0 hθ1 (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, neg_zero, zero_mul, Real.exp_zero, mul_one] at hcc
  have hθb : θ * b = a := by rw [hθ]; field_simp
  rw [hθb] at hcc
  nlinarith [hcc, hθb, mul_pos ha hb, Real.exp_pos (-b * J), Real.exp_pos (-a * J)]














theorem pform_le_betaform (J β βtc ptc thetaVal : ℝ) (hJ : 0 < J)
    (hβtc : 0 < βtc) (hβ : βtc < β) (hptc0 : 0 < ptc) (hptc1 : ptc < 1)
    (hptc_eq : ptc = 1 - Real.exp (-βtc * J))
    (hpform : ((1 - Real.exp (-β * J)) - ptc)
        / ((1 - Real.exp (-β * J)) * (1 - ptc)) ≤ thetaVal) :
    (β - βtc) / β ≤ thetaVal := by
  set p := 1 - Real.exp (-β * J) with hp
  have hβpos : 0 < β := lt_trans hβtc hβ
  have hexpβ : 0 < Real.exp (-β * J) := Real.exp_pos _
  have hp1 : p < 1 := by rw [hp]; linarith
  have hexpcmp : Real.exp (-β * J) < Real.exp (-βtc * J) := by
    apply Real.exp_lt_exp.mpr; nlinarith
  have h1ptc : 0 < 1 - ptc := by linarith
  have h1ptc_eq : 1 - ptc = Real.exp (-βtc * J) := by rw [hptc_eq]; ring
  have hp0 : 0 < p := by rw [hp]; rw [hptc_eq] at hptc1; linarith
  have hpmptc : p - ptc = Real.exp (-βtc * J) - Real.exp (-β * J) := by rw [hp, hptc_eq]; ring
  have hkey : (β - βtc) / β ≤ (p - ptc) / (p * (1 - ptc)) := by
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    rw [h1ptc_eq, hpmptc, hp]
    have hcore := one_sub_exp_secant J (β - βtc) β (by linarith) (by linarith)
    have hfact : Real.exp (-βtc * J) - Real.exp (-β * J)
        = Real.exp (-βtc * J) * (1 - Real.exp (-(β - βtc) * J)) := by
      rw [mul_sub, mul_one, ← Real.exp_add]; ring_nf
    rw [hfact]
    have he2 : 0 < Real.exp (-βtc * J) := Real.exp_pos _
    nlinarith [hcore, he2]
  exact le_trans hkey hpform

























theorem theta_ge_betaForm {J β : ℝ} (hJ : 0 < J) (hd : 0 < d)
    (htc1 : (tildePc d : ℝ) < 1) (hβ : betaTildeC d J < β) :
    theta d (pBeta J β).toNNReal (pBeta_toNNReal_le_one J β)
      ≥ (β - betaTildeC d J) / β := by
  set ptc := (tildePc d : ℝ) with hptc
  have hptc0 : 0 < ptc := tildePc_pos hd
  have h1ptc : 0 < 1 - ptc := by linarith
  set βtc := betaTildeC d J with hβtc_def
  have hβtc_pos : 0 < βtc := betaTildeC_pos hJ hd htc1
  
  have hβtc_val : ptc = 1 - Real.exp (-βtc * J) := by
    have h := pBeta_betaTildeC (d := d) hJ htc1
    rw [pBeta, ← hβtc_def] at h
    rw [hptc, ← h]
  have hβpos : 0 < β := lt_trans hβtc_pos hβ
  have hexpβ : 0 < Real.exp (-β * J) := Real.exp_pos _
  
  have hpval1 : pBeta J β < 1 := pBeta_lt_one J β
  have hexpcmp : Real.exp (-β * J) < Real.exp (-βtc * J) := by
    apply Real.exp_lt_exp.mpr; nlinarith
  have hpval0 : 0 < pBeta J β := by
    rw [pBeta]; rw [hβtc_val] at hptc0; linarith
  set q : ℝ≥0 := (pBeta J β).toNNReal with hq_def
  have hqcoe : (q : ℝ) = pBeta J β := Real.coe_toNNReal _ (le_of_lt hpval0)
  have hq1 : q ≤ 1 := pBeta_toNNReal_le_one J β
  have hq1r : (q : ℝ) < 1 := by rw [hqcoe]; exact hpval1
  
  have hgt : tildePc d < q := by
    rw [← NNReal.coe_lt_coe, hqcoe, ← hptc, hβtc_val, pBeta]; linarith [hexpcmp]
  
  have hpform := theta_ge_meanField_unconditional q hq1 hptc0 hgt hq1r
  rw [hqcoe, ← hptc, pBeta] at hpform
  
  have hgoal := pform_le_betaform J β βtc ptc (theta d q hq1) hJ hβtc_pos hβ hptc0 htc1
    hβtc_val hpform
  exact ge_iff_le.mpr hgoal

end Sharpness

end StatMech
