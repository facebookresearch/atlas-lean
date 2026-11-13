/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Code.OSSS.GrandCoupling
import Code.OSSS.GrandCouplingAssembly

open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech
namespace Walls

open OSSS.Monotonic OSSS.Coding StatMech.Probability StatMech.OSSS.GrandCoupling

variable {E : Type*} [Fintype E] [DecidableEq E]













lemma oc2_integrable_g_codeMap (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (g : ConfigSpace E → ℝ) :
    Integrable (fun u : Fin n → ℝ => g (codeMap μ (σ : Fin n → E) u)) (Vcube n) := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, |g x| ≤ C := by
    refine ⟨Finset.univ.sup' ⟨Classical.arbitrary _, Finset.mem_univ _⟩ (fun x => |g x|), ?_⟩
    intro x
    exact Finset.le_sup' (fun x => |g x|) (Finset.mem_univ x)
  refine Integrable.of_bound (measurable_g_codeMap μ σ g).aestronglyMeasurable C ?_
  filter_upwards with u
  simpa [Real.norm_eq_abs] using hC _

















theorem oc2_codingLawJoint (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (h : ConfigSpace E → ConfigSpace E → ℝ) :
    ∫ p, h (codeMap μ (σ : Fin n → E) p.1) (codeMap μ (σ : Fin n → E) p.2)
        ∂((Vcube n).prod (Vcube n))
      = ∑ x, ∑ y, h x y * μ x * μ y := by
  
  have hmeas : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      h (codeMap μ (σ : Fin n → E) p.1) (codeMap μ (σ : Fin n → E) p.2)) := by
    have hm1 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        codeMap μ (σ : Fin n → E) p.1) := (measurable_codeMap μ σ).comp measurable_fst
    have hm2 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        codeMap μ (σ : Fin n → E) p.2) := (measurable_codeMap μ σ).comp measurable_snd
    exact (measurable_of_finite (Function.uncurry h)).comp (hm1.prodMk hm2)
  
  obtain ⟨C, hC⟩ : ∃ C, ∀ x y, |h x y| ≤ C := by
    refine ⟨Finset.univ.sup' ⟨(Classical.arbitrary _, Classical.arbitrary _), Finset.mem_univ _⟩
      (fun p : ConfigSpace E × ConfigSpace E => |h p.1 p.2|), ?_⟩
    intro x y
    exact Finset.le_sup' (fun p : ConfigSpace E × ConfigSpace E => |h p.1 p.2|)
      (Finset.mem_univ (x, y))
  have hint : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      h (codeMap μ (σ : Fin n → E) p.1) (codeMap μ (σ : Fin n → E) p.2))
      ((Vcube n).prod (Vcube n)) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable C ?_
    filter_upwards with p
    simpa [Real.norm_eq_abs] using hC _ _
  
  rw [integral_prod _ hint]
  
  have hinner : ∀ U : Fin n → ℝ,
      (∫ V, h (codeMap μ (σ : Fin n → E) U) (codeMap μ (σ : Fin n → E) V) ∂(Vcube n))
        = ∑ y, h (codeMap μ (σ : Fin n → E) U) y * μ y :=
    fun U => integral_g_codeMap μ hpos hμ1 σ (fun y => h (codeMap μ (σ : Fin n → E) U) y)
  simp_rw [hinner]
  
  rw [integral_finsetSum]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [integral_mul_const, integral_g_codeMap μ hpos hμ1 σ (fun x => h x y), Finset.sum_mul]
  · exact fun y _ => (oc2_integrable_g_codeMap μ σ (fun x => h x y)).mul_const (μ y)










lemma oc2_Wt_zero {n : ℕ} (U V : Fin n → ℝ) : Wt U V 0 = U := by
  funext i; unfold Wt; simp



lemma oc2_Wt_full {n : ℕ} (U V : Fin n → ℝ) : Wt U V n = V := by
  funext i; unfold Wt; simp [i.isLt]










theorem oc2_codingLawJoint_interp (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (h : ConfigSpace E → ConfigSpace E → ℝ) :
    ∫ p, h (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 0))
          (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 n))
        ∂((Vcube n).prod (Vcube n))
      = ∑ x, ∑ y, h x y * μ x * μ y := by
  have hrw : (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        h (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 0))
          (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 n)))
      = (fun p => h (codeMap μ (σ : Fin n → E) p.1) (codeMap μ (σ : Fin n → E) p.2)) := by
    funext p; rw [oc2_Wt_zero, oc2_Wt_full]
  rw [hrw]
  exact oc2_codingLawJoint μ hpos hμ1 σ h











theorem oc2_codingLawJoint_factor (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (h : ConfigSpace E → ConfigSpace E → ℝ) :
    ∫ p, h (codeMap μ (σ : Fin n → E) p.1) (codeMap μ (σ : Fin n → E) p.2)
        ∂((Vcube n).prod (Vcube n))
      = ∑ x, (∑ y, h x y * μ y) * μ x := by
  rw [oc2_codingLawJoint μ hpos hμ1 σ h]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  ring








theorem oc2_codingLawJoint_marginal (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (a b : ConfigSpace E → ℝ) :
    ∫ p, a (codeMap μ (σ : Fin n → E) p.1) * b (codeMap μ (σ : Fin n → E) p.2)
        ∂((Vcube n).prod (Vcube n))
      = (∑ x, a x * μ x) * (∑ y, b y * μ y) := by
  rw [oc2_codingLawJoint μ hpos hμ1 σ (fun x y => a x * b y)]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  ring







section FK

open StatMech.OSSS.MonotonicFK






theorem oc2_fk_codingLawJoint {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    (h : ConfigSpace (Sym2 V) → ConfigSpace (Sym2 V) → ℝ) :
    ∫ pr, h (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) pr.1)
          (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) pr.2)
        ∂((Vcube n).prod (Vcube n))
      = ∑ x, ∑ y, h x y * fkMass G p q x * fkMass G p q y := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact oc2_codingLawJoint (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq0 ω)
    (fkMass_sum_eq_one G hp hp1 hq0) σ h

end FK

end Walls
end StatMech
