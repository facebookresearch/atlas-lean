/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































































import Mathlib
import Code.OSSS.RevealmentBoxCrossing
import Code.OSSS.MonotonicOSSS
import Code.Walls.oc3_core

open scoped BigOperators
open MeasureTheory Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace StatMech
namespace Walls

open StatMech.OSSS
open StatMech.OSSS.AdaptMConditional
open StatMech.OSSS.RevealmentBoxCrossing
open StatMech.OSSS.Coding

variable {E : Type*} [Fintype E] [DecidableEq E]
















noncomputable def oc4_notDetProb (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (e : E) : ℝ :=
  ∑ X, (if detAtC (σ : Fin n → E) f X (σ.symm e : ℕ) then (0 : ℝ) else 1) * μ X







theorem oc4_notDet_iff_prefix {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    (X : ConfigSpace E) (e : E) :
    ¬ detAtC (σ : Fin n → E) f X (σ.symm e : ℕ)
      ↔ ∃ w : ConfigSpace E,
          (∀ c ∈ prefixSet (σ : Fin n → E) (σ.symm e : ℕ), w c = X c) ∧ f w ≠ f X := by
  unfold detAtC
  push Not
  rfl





theorem oc4_mem_prefix_iff {n : ℕ} (σ : Fin n ≃ E) (e c : E) :
    c ∈ prefixSet (σ : Fin n → E) (σ.symm e : ℕ)
      ↔ ∃ s : Fin n, (s : ℕ) < (σ.symm e : ℕ) ∧ σ s = c :=
  mem_prefixSet_iff (σ : Fin n → E) (σ.symm e : ℕ) c
















theorem oc4_reachProb_eq_notDetProb (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (e : E) :
    reachProb μ σ f e = oc4_notDetProb μ σ f e := by
  unfold reachProb oc4_notDetProb Lindeberg.mean reachInd
  rfl






















theorem oc4_reveal_eq_reach {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e : E) :
    revealAdapt μ σ f e = reachProb μ σ f e
      ∧ reachProb μ σ f e = oc4_notDetProb μ σ f e :=
  ⟨revealAdapt_eq_reachProb hpos hμ1 σ f e, oc4_reachProb_eq_notDetProb μ σ f e⟩








theorem oc4_reveal_eq_notDetProb {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e : E) :
    revealAdapt μ σ f e = oc4_notDetProb μ σ f e := by
  obtain ⟨h1, h2⟩ := oc4_reveal_eq_reach hpos hμ1 σ f e
  rw [h1, h2]








theorem oc4_notDetProb_nonneg {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e : E) :
    0 ≤ oc4_notDetProb μ σ f e := by
  unfold oc4_notDetProb
  apply Finset.sum_nonneg
  intro X _
  apply mul_nonneg _ (le_of_lt (hpos X))
  split <;> norm_num


theorem oc4_notDetProb_le_one {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e : E) :
    oc4_notDetProb μ σ f e ≤ 1 := by
  unfold oc4_notDetProb
  calc (∑ X, (if detAtC (σ : Fin n → E) f X (σ.symm e : ℕ) then (0 : ℝ) else 1) * μ X)
      ≤ ∑ X, (1 : ℝ) * μ X := by
        apply Finset.sum_le_sum
        intro X _
        apply mul_le_mul_of_nonneg_right _ (le_of_lt (hpos X))
        split <;> norm_num
    _ = 1 := by simp only [one_mul]; exact hμ1





theorem oc4_reveal_le_notDetProb {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e : E) :
    revealAdapt μ σ f e ≤ oc4_notDetProb μ σ f e :=
  le_of_eq (oc4_reveal_eq_notDetProb hpos hμ1 σ f e)









section FK

open StatMech.OSSS.MonotonicFK










theorem oc4_fk_reveal_eq_reach {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    (f : ConfigSpace (Sym2 V) → ℝ) (e : Sym2 V) :
    revealAdapt (fkMass G p q) σ f e = reachProb (fkMass G p q) σ f e
      ∧ reachProb (fkMass G p q) σ f e = oc4_notDetProb (fkMass G p q) σ f e :=
  oc4_reveal_eq_reach (fun ω => fkMass_pos G hp hp1 hq ω)
    (fkMass_sum_eq_one G hp hp1 hq) σ f e






theorem oc4_fk_reveal_eq_notDetProb {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    (f : ConfigSpace (Sym2 V) → ℝ) (e : Sym2 V) :
    revealAdapt (fkMass G p q) σ f e = oc4_notDetProb (fkMass G p q) σ f e :=
  oc4_reveal_eq_notDetProb (fun ω => fkMass_pos G hp hp1 hq ω)
    (fkMass_sum_eq_one G hp hp1 hq) σ f e

end FK


















theorem oc4_reveal_codingFrame {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e : E) :
    revealAdapt μ σ f e = ∑ X, truncIndC σ f X ((σ.symm e : ℕ) + 1) * μ X
      ∧ (∑ X, truncIndC σ f X ((σ.symm e : ℕ) + 1) * μ X) = oc4_notDetProb μ σ f e := by
  refine ⟨revealAdapt_eq_truncSum μ hpos hμ1 σ f e, ?_⟩
  unfold oc4_notDetProb
  apply Finset.sum_congr rfl
  intro X _
  rw [truncIndC_succ_eq_reachInd σ f X (σ.symm e : ℕ)]
  unfold reachInd
  rfl

end Walls
end StatMech
