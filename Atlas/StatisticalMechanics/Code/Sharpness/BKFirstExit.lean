/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Code.Sharpness.BkCriterion
import Code.Sharpness.PercoItems

open MeasureTheory Finset Set
open scoped NNReal

namespace StatMech

namespace Sharpness

open ConfigSpace
































theorem susceptibility_self_consistent {ι κ : Type*} [DecidableEq ι]
    (Lam S : Finset ι) (hSΛ : S ⊆ Lam) (bnd : Finset κ) (outer : κ → ι)
    (p : ℝ) (hp0 : 0 ≤ p) (cw : κ → ℝ) (q : ι → ℝ) (q' : ι → ι → ℝ)
    (hq'_nonneg : ∀ b x, 0 ≤ q' b x) (hcw_nonneg : ∀ e, 0 ≤ cw e)
    (hq_le_one : ∀ x ∈ S, q x ≤ 1)
    (hfe : ∀ x ∈ Lam, x ∉ S → q x ≤ ∑ e ∈ bnd, (p * cw e) * q' (outer e) x)
    (χ : ℝ) (hχ : χ = ∑ x ∈ Lam, q x)
    (hcont : ∀ b, ∑ x ∈ Lam, q' b x ≤ χ)
    (φ : ℝ) (hφ : φ = p * ∑ e ∈ bnd, cw e) :
    χ ≤ (S.card : ℝ) + φ * χ := by
  classical
  
  have hsplit : χ = (∑ x ∈ Lam \ S, q x) + ∑ x ∈ S, q x := by
    rw [hχ, ← Finset.sum_sdiff hSΛ]
  
  have hpartS : (∑ x ∈ S, q x) ≤ (S.card : ℝ) := by
    calc (∑ x ∈ S, q x) ≤ ∑ _x ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun x hx => hq_le_one x hx)
      _ = (S.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  
  have hpartSc : (∑ x ∈ Lam \ S, q x) ≤ φ * χ := by
    
    have hbound : (∑ x ∈ Lam \ S, q x)
        ≤ ∑ x ∈ Lam \ S, ∑ e ∈ bnd, (p * cw e) * q' (outer e) x := by
      apply Finset.sum_le_sum
      intro x hx
      rw [Finset.mem_sdiff] at hx
      exact hfe x hx.1 hx.2
    
    have hswap : (∑ x ∈ Lam \ S, ∑ e ∈ bnd, (p * cw e) * q' (outer e) x)
        = ∑ e ∈ bnd, (p * cw e) * (∑ x ∈ Lam \ S, q' (outer e) x) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun e _ => by rw [Finset.mul_sum])
    
    have heach : ∀ e ∈ bnd,
        (p * cw e) * (∑ x ∈ Lam \ S, q' (outer e) x) ≤ (p * cw e) * χ := by
      intro e _
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hp0 (hcw_nonneg e))
      calc (∑ x ∈ Lam \ S, q' (outer e) x) ≤ ∑ x ∈ Lam, q' (outer e) x :=
            Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
              (fun x _ _ => hq'_nonneg _ x)
        _ ≤ χ := hcont (outer e)
    calc (∑ x ∈ Lam \ S, q x)
        ≤ ∑ x ∈ Lam \ S, ∑ e ∈ bnd, (p * cw e) * q' (outer e) x := hbound
      _ = ∑ e ∈ bnd, (p * cw e) * (∑ x ∈ Lam \ S, q' (outer e) x) := hswap
      _ ≤ ∑ e ∈ bnd, (p * cw e) * χ := Finset.sum_le_sum heach
      _ = φ * χ := by rw [hφ, ← Finset.sum_mul, Finset.mul_sum]
  
  linarith [hpartS, hpartSc, hsplit]









variable {V : Type*}



















theorem firstExit_target_bound {ι : Type*} [Fintype V] [DecidableEq V]
    {p : ℝ≥0} (hp : p ≤ 1) (G : SimpleGraph V) (Lam S : Set V) (u x : V)
    (s : Finset ι) (bp : ι → V × V)
    (hincl : connEvent G Lam u {x} ⊆
      ⋃ i ∈ s, disjointOccurrence (connEvent G S u {(bp i).1})
        (disjointOccurrence (edgeOpenEvent (bp i).1 (bp i).2)
          (connEvent G Lam (bp i).2 {x})))
    (hedge : ∀ i ∈ s, (bernoulliProductMeasure (E := Sym2 V) p hp).real
        (edgeOpenEvent (bp i).1 (bp i).2) ≤ (p : ℝ)) :
    (bernoulliProductMeasure (E := Sym2 V) p hp).real (connEvent G Lam u {x})
      ≤ ∑ i ∈ s,
          ((p : ℝ) * (bernoulliProductMeasure (E := Sym2 V) p hp).real
              (connEvent G S u {(bp i).1}))
          * (bernoulliProductMeasure (E := Sym2 V) p hp).real
              (connEvent G Lam (bp i).2 {x}) := by
  set μ := bernoulliProductMeasure (E := Sym2 V) p hp with hμ
  have hbk := bk_criterion_conn hp G Lam S {x} u s bp hincl
  calc μ.real (connEvent G Lam u {x})
      ≤ ∑ i ∈ s, μ.real (connEvent G S u {(bp i).1})
          * μ.real (edgeOpenEvent (bp i).1 (bp i).2)
          * μ.real (connEvent G Lam (bp i).2 {x}) := hbk
    _ ≤ ∑ i ∈ s, ((p : ℝ) * μ.real (connEvent G S u {(bp i).1}))
          * μ.real (connEvent G Lam (bp i).2 {x}) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have hcwnn : 0 ≤ μ.real (connEvent G S u {(bp i).1}) := measureReal_nonneg
        have hq'nn : 0 ≤ μ.real (connEvent G Lam (bp i).2 {x}) := measureReal_nonneg
        have hedgenn : 0 ≤ μ.real (edgeOpenEvent (bp i).1 (bp i).2) := measureReal_nonneg
        nlinarith [hedge i hi, mul_nonneg hcwnn hq'nn, mul_nonneg hcwnn hedgenn]




























theorem susceptibility_self_consistent_bk
    [Fintype V] [DecidableEq V] {p : ℝ≥0} (hp : p ≤ 1) (G : SimpleGraph V)
    (Lam S : Finset V) (hSΛ : S ⊆ Lam) (u : V) {κ : Type*} (bnd : Finset κ)
    (bp : κ → V × V)
    
    (hincl : ∀ x ∈ Lam, x ∉ S → connEvent G (Lam : Set V) u {x} ⊆
      ⋃ e ∈ bnd, disjointOccurrence (connEvent G (S : Set V) u {(bp e).1})
        (disjointOccurrence (edgeOpenEvent (bp e).1 (bp e).2)
          (connEvent G (Lam : Set V) (bp e).2 {x})))
    
    (hedge : ∀ e ∈ bnd, (bernoulliProductMeasure (E := Sym2 V) p hp).real
        (edgeOpenEvent (bp e).1 (bp e).2) ≤ (p : ℝ))
    
    (hSone : ∀ x ∈ S, (bernoulliProductMeasure (E := Sym2 V) p hp).real
        (connEvent G (Lam : Set V) u {x}) ≤ 1)
    (χ : ℝ)
    (hχ : χ = ∑ x ∈ Lam, (bernoulliProductMeasure (E := Sym2 V) p hp).real
        (connEvent G (Lam : Set V) u {x}))
    
    (hcont : ∀ b : V, ∑ x ∈ Lam, (bernoulliProductMeasure (E := Sym2 V) p hp).real
        (connEvent G (Lam : Set V) b {x}) ≤ χ)
    (φ : ℝ)
    (hφ : φ = (p : ℝ) * ∑ e ∈ bnd, (bernoulliProductMeasure (E := Sym2 V) p hp).real
        (connEvent G (S : Set V) u {(bp e).1})) :
    χ ≤ (S.card : ℝ) + φ * χ := by
  classical
  set μ := bernoulliProductMeasure (E := Sym2 V) p hp with hμ
  
  set q : V → ℝ := fun x => μ.real (connEvent G (Lam : Set V) u {x}) with hq
  set q' : V → V → ℝ := fun b x => μ.real (connEvent G (Lam : Set V) b {x}) with hq'
  set cw : κ → ℝ := fun e => μ.real (connEvent G (S : Set V) u {(bp e).1}) with hcw
  refine susceptibility_self_consistent Lam S hSΛ bnd (fun e => (bp e).2)
    (p : ℝ) p.coe_nonneg cw q q' (fun b x => measureReal_nonneg)
    (fun e => measureReal_nonneg) hSone ?_ χ hχ hcont φ ?_
  · 
    intro x hxL hxS
    have hb := firstExit_target_bound hp G (Lam : Set V) (S : Set V) u x bnd bp
      (hincl x hxL hxS) hedge
    simpa only [hq, hq', hcw] using hb
  · 
    rw [hφ]




















theorem susceptibility_finite_of_self_consistent (chi Sval phival : ℝ)
    (hchi : 0 ≤ chi) (hphi1 : phival < 1) (hself : chi ≤ Sval + phival * chi) :
    0 ≤ chi ∧ chi ≤ Sval / (1 - phival) :=
  StatMech.Sharpness.susceptibility_finite chi Sval phival hchi hphi1 hself

end Sharpness

end StatMech
