/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Code.Probability.FullRangeHC

open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]






theorem cvg_convexGap_le {G : ℝ → ℝ} (hG : ConvexOn ℝ (Icc (0:ℝ) 1) G)
    (h0 : G 0 ≤ 0) (h1 : G 1 ≤ 0) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    G u ≤ 0 := by
  have hmem0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hmem1 : (1:ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hkey := hG.le_on_segment' hmem0 hmem1 (a := 1 - u) (b := u) (by linarith) hu0 (by ring)
  have heq : (1 - u) • (0:ℝ) + u • (1:ℝ) = u := by simp
  rw [heq] at hkey
  calc G u ≤ max (G 0) (G 1) := hkey
    _ ≤ 0 := max_le h0 h1




theorem cvg_convexOn_sum {α : Type*} (s : Finset α) (g : α → ℝ → ℝ) {D : Set ℝ}
    (hD : Convex ℝ D) (hg : ∀ a ∈ s, ConvexOn ℝ D (g a)) :
    ConvexOn ℝ D (fun u => ∑ a ∈ s, g a u) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using convexOn_const (0:ℝ) hD
  | cons a t ha ih =>
    have hgt : ∀ b ∈ t, ConvexOn ℝ D (g b) := fun b hb => hg b (Finset.mem_cons.mpr (Or.inr hb))
    have hga : ConvexOn ℝ D (g a) := hg a (Finset.mem_cons_self a t)
    have heq : (fun u => ∑ b ∈ Finset.cons a t ha, g b u)
        = (fun u => g a u + ∑ b ∈ t, g b u) := by
      funext u; rw [Finset.sum_cons]
    rw [heq]
    exact hga.add (ih hgt)



theorem cvg_oneSubPow_convexOn (k : ℕ) :
    ConvexOn ℝ (Icc (0:ℝ) 1) (fun u : ℝ => (1 - u) ^ k) := by
  have hpow : ConvexOn ℝ (Ici (0:ℝ)) (fun x : ℝ => x ^ k) := convexOn_pow k
  have hcomp := hpow.comp_affineMap (AffineMap.const ℝ ℝ (1:ℝ) - AffineMap.id ℝ ℝ)
  apply hcomp.subset
  · intro u hu
    simp only [Set.mem_preimage, AffineMap.coe_sub, AffineMap.coe_const, AffineMap.coe_id,
      Pi.sub_apply, Function.const_apply, id_eq, Set.mem_Ici]
    rcases hu with ⟨_, h1⟩
    linarith
  · exact convex_Icc 0 1




theorem cvg_L_convexOn (p : ℝ) (φ : ConfigSpace ι → Bool) :
    ConvexOn ℝ (Icc (0:ℝ) 1)
      (fun u => ∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) := by
  apply cvg_convexOn_sum univ _ (convex_Icc 0 1)
  intro S _
  
  have hbase : ConvexOn ℝ (Icc (0:ℝ) 1) (fun u : ℝ => (1 - u) ^ (S.card - 1)) :=
    cvg_oneSubPow_convexOn (S.card - 1)
  have hc : (0:ℝ) ≤ 4 * (S.card : ℝ) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
    positivity
  have hscaled := hbase.smul hc
  
  have heq : (fun u : ℝ => (4 * (S.card : ℝ)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) • (1 - u) ^ (S.card - 1))
      = (fun u : ℝ => 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) := by
    funext u; simp only [smul_eq_mul]; ring
  rw [heq] at hscaled
  exact hscaled





theorem cvg_Q_firstDeriv (m u : ℝ) (hu : (2:ℝ) - u ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.exp (m * (y / (2 - y))))
      (Real.exp (m * (u / (2 - u))) * (m * (2 / (2 - u) ^ 2))) u := by
  have hk : HasDerivAt (fun y : ℝ => y / (2 - y)) (2 / (2 - u) ^ 2) u := by
    have hnum : HasDerivAt (fun y : ℝ => y) 1 u := hasDerivAt_id u
    have hden : HasDerivAt (fun y : ℝ => 2 - y) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub 2
    have := hnum.div hden hu
    convert this using 1; field_simp; ring
  have hmk : HasDerivAt (fun y : ℝ => m * (y / (2 - y))) (m * (2 / (2 - u) ^ 2)) u := hk.const_mul m
  exact (Real.hasDerivAt_exp (m * (u / (2 - u)))).comp u hmk



theorem cvg_Q_secondDeriv (m u : ℝ) (hu : (2:ℝ) - u ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.exp (m * (y / (2 - y))) * (m * (2 / (2 - y) ^ 2)))
      ((Real.exp (m * (u / (2 - u))) * (m * (2 / (2 - u) ^ 2))) * (m * (2 / (2 - u) ^ 2))
        + Real.exp (m * (u / (2 - u))) * (m * (4 / (2 - u) ^ 3))) u := by
  have hD : HasDerivAt (fun y : ℝ => Real.exp (m * (y / (2 - y))))
      (Real.exp (m * (u / (2 - u))) * (m * (2 / (2 - u) ^ 2))) u := cvg_Q_firstDeriv m u hu
  have hE : HasDerivAt (fun y : ℝ => m * (2 / (2 - y) ^ 2)) (m * (4 / (2 - u) ^ 3)) u := by
    have hden : HasDerivAt (fun y : ℝ => (2 - y) ^ 2) (2 * (2 - u) * (-1)) u := by
      have h1 : HasDerivAt (fun y : ℝ => 2 - y) (-1) u := by
        simpa using (hasDerivAt_id u).const_sub 2
      have := h1.pow 2
      convert this using 1; ring
    have hne2 : ((2:ℝ) - u) ^ 2 ≠ 0 := pow_ne_zero 2 hu
    have hdiv : HasDerivAt (fun y : ℝ => 2 / (2 - y) ^ 2) (4 / (2 - u) ^ 3) u := by
      have := (hasDerivAt_const u (2:ℝ)).div hden hne2
      convert this using 1; field_simp; ring
    exact hdiv.const_mul m
  exact hD.mul hE




theorem cvg_Q_concaveOn {m : ℝ} (hm0 : m ≤ 0) (hm1 : -1 ≤ m) :
    ConcaveOn ℝ (Icc (0:ℝ) 1) (fun u : ℝ => Real.exp (m * (u / (2 - u)))) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1)
    (f' := fun u => Real.exp (m * (u / (2 - u))) * (m * (2 / (2 - u) ^ 2)))
    (f'' := fun u => (Real.exp (m * (u / (2 - u))) * (m * (2 / (2 - u) ^ 2))) * (m * (2 / (2 - u) ^ 2))
        + Real.exp (m * (u / (2 - u))) * (m * (4 / (2 - u) ^ 3)))
  · 
    apply ContinuousOn.rexp
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div continuousOn_id (by fun_prop)
    intro u hu
    rcases hu with ⟨_, h1⟩
    intro h; linarith
  · 
    intro u hu
    rw [interior_Icc] at hu
    have hwne : (2:ℝ) - u ≠ 0 := by have := hu.2; intro h; linarith
    exact (cvg_Q_firstDeriv m u hwne).hasDerivWithinAt
  · 
    intro u hu
    rw [interior_Icc] at hu
    have hwne : (2:ℝ) - u ≠ 0 := by have := hu.2; intro h; linarith
    exact (cvg_Q_secondDeriv m u hwne).hasDerivWithinAt
  · 
    intro u hu
    rw [interior_Icc] at hu
    have hu0 : 0 < u := hu.1
    have hu1 : u < 1 := hu.2
    have hw : (0:ℝ) < 2 - u := by linarith
    set D := Real.exp (m * (u / (2 - u))) with hD
    have hDpos : 0 < D := Real.exp_pos _
    have hfactor : (D * (m * (2 / (2 - u) ^ 2))) * (m * (2 / (2 - u) ^ 2))
          + D * (m * (4 / (2 - u) ^ 3))
        = D * ((4 * m / (2 - u) ^ 4) * (m + (2 - u))) := by
      have hbig : (m * (2 / (2 - u) ^ 2)) * (m * (2 / (2 - u) ^ 2)) + m * (4 / (2 - u) ^ 3)
          = (4 * m / (2 - u) ^ 4) * (m + (2 - u)) := by
        field_simp; ring
      rw [← hbig]; ring
    rw [hfactor]
    apply mul_nonpos_of_nonneg_of_nonpos hDpos.le
    have h4m : 4 * m / (2 - u) ^ 4 ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg (by linarith); positivity
    have hmw : 0 ≤ m + (2 - u) := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg h4m hmw




theorem cvg_R_concaveOn {δ T : ℝ} (hδlo : Real.exp (-1) ≤ δ) (hδhi : δ ≤ 1) (hT : 0 ≤ T) :
    ConcaveOn ℝ (Icc (0:ℝ) 1) (fun u : ℝ => δ ^ (u / (2 - u)) * T) := by
  have hδ0 : 0 < δ := lt_of_lt_of_le (Real.exp_pos _) hδlo
  have hm0 : Real.log δ ≤ 0 := Real.log_nonpos hδ0.le hδhi
  have hm1 : -1 ≤ Real.log δ := by
    rw [← Real.log_exp (-1)]; exact Real.log_le_log (Real.exp_pos _) hδlo
  have hQ := cvg_Q_concaveOn hm0 hm1
  
  have heq : (fun u : ℝ => δ ^ (u / (2 - u)) * T)
      = (fun u : ℝ => T • Real.exp (Real.log δ * (u / (2 - u)))) := by
    funext u
    rw [Real.rpow_def_of_pos hδ0, smul_eq_mul, mul_comm]
  rw [heq]
  exact hQ.smul hT









theorem cvg_openResidue_of_concaveR [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool)
    (hconc : ConcaveOn ℝ (Icc (0:ℝ) 1)
      (fun u => (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
        ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)))
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδ
  set T := totalInfl (OSSS.bernoulliWeight p) f with hT
  
  set Lf := fun u : ℝ => ∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
    * (ptn_coeff p f S) ^ 2 with hLf
  set Rf := fun u : ℝ => δ ^ (u / (2 - u)) * T with hRf
  set G := fun u : ℝ => Lf u - Rf u with hG
  
  have hLconv : ConvexOn ℝ (Icc (0:ℝ) 1) Lf := cvg_L_convexOn p φ
  have hnegR : ConvexOn ℝ (Icc (0:ℝ) 1) (fun u => - Rf u) := hconc.neg
  have hGconv : ConvexOn ℝ (Icc (0:ℝ) 1) G := by
    have hadd := hLconv.add hnegR
    refine hadd.congr ?_
    intro u _
    simp [hG, sub_eq_add_neg]
  
  have hLf0 : Lf 0 ≤ T := frh_at_zero hp0 hp1 φ
  have hR0 : Rf 0 = T := by
    simp only [hRf]
    rw [show (0:ℝ) / (2 - 0) = 0 by norm_num, Real.rpow_zero, one_mul]
  have hG0 : G 0 ≤ 0 := by
    have : G 0 = Lf 0 - Rf 0 := rfl
    rw [this, hR0]; linarith
  
  have hLf1 : Lf 1 ≤ δ ^ ((1:ℝ) / (2 - 1)) * T := frh_endpoint_one hp0 hp1 φ
  have hR1 : Rf 1 = δ ^ ((1:ℝ) / (2 - 1)) * T := by simp only [hRf]
  have hG1 : G 1 ≤ 0 := by
    have : G 1 = Lf 1 - Rf 1 := rfl
    rw [this, hR1]; linarith
  
  have hfin := cvg_convexGap_le hGconv hG0 hG1 hu0.le hu1.le
  have : Lf u - Rf u ≤ 0 := hfin
  have hgoal : Lf u ≤ Rf u := by linarith
  simpa only [hLf, hRf] using hgoal






theorem cvg_maxInfl_le_one [Nonempty ι] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (φ : ConfigSpace ι → Bool) :
    maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) ≤ 1 := by
  obtain ⟨e, he⟩ := kkl_exists_maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
  rw [← he]
  have hν : OSSS.IsProbWeight (OSSS.bernoulliWeight (E := ι) p) :=
    OSSS.bernoulliWeight_isProbWeight hp0 hp1
  unfold OSSS.infl
  calc OSSS.expect (OSSS.bernoulliWeight p)
        (fun ω => |(fun ω => if φ ω then (1 : ℝ) else 0) (StatMech.setOpen e ω)
          - (fun ω => if φ ω then (1 : ℝ) else 0) (StatMech.setClosed e ω)|)
      ≤ OSSS.expect (OSSS.bernoulliWeight p) (fun _ => (1:ℝ)) := by
        apply OSSS.expect_mono hν
        intro ω; simp only []
        rcases (φ (StatMech.setOpen e ω)) <;> rcases (φ (StatMech.setClosed e ω)) <;> norm_num
    _ = 1 := OSSS.expect_one hν





theorem cvg_openResidue_largeDelta [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool)
    (hδlo : Real.exp (-1) ≤ maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  have hTnn : 0 ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
    kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) _
  have hδhi : maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) ≤ 1 :=
    cvg_maxInfl_le_one hp0.le hp1.le φ
  have hconc := cvg_R_concaveOn hδlo hδhi hTnn
  exact cvg_openResidue_of_concaveR hp0 hp1 φ hconc hu0 hu1















def cvg_smallDeltaResidue (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, p < 1 → ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (φ : ConfigSpace E → Bool),
      maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) < Real.exp (-1) →
      ∀ u : ℝ, 0 < u → u < 1 →
      (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
        ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
          * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)






theorem cvg_openResidue_of_smallDelta {q : ℝ}
    (H : cvg_smallDeltaResidue q) : frh_openResidue q := by
  intro p hp hp1 E _ _ _ φ u hu0 hu1
  have hp0 : 0 < p := by have := hp.1; linarith
  by_cases hδ : Real.exp (-1) ≤ maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
  · exact cvg_openResidue_largeDelta hp0 hp1 φ hδ hu0 hu1
  · rw [not_le] at hδ
    exact H p hp hp1 φ hδ u hu0 hu1




theorem cvg_martingaleHC_of_smallDelta {q : ℝ}
    (H : cvg_smallDeltaResidue q) : mxd_martingaleHC_statement q :=
  frh_martingaleHC_of_openResidue (cvg_openResidue_of_smallDelta H)

end StatMech.Probability
