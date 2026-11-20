/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































































import Mathlib
import Code.Inequalities.OSSS
import Code.OSSS.CovLowerBound
import Code.OSSS.Lindeberg
import Code.OSSS.MonotonicOSSS
import Code.Walls.oc2_whynotperedge

open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace StatMech
namespace Walls

open StatMech.OSSS
open StatMech.OSSS.CovLowerBound
open StatMech.OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]

















theorem oc3_weight_eq_of_match {μ : ConfigSpace E → ℝ} {ν : E → Bool → ℝ}
    (hmatch : ∀ g, expect ν g = Lindeberg.mean μ g) (ω₀ : ConfigSpace E) :
    weight ν ω₀ = μ ω₀ := by
  have h := hmatch (fun ω => if ω = ω₀ then (1 : ℝ) else 0)
  have hL : expect ν (fun ω => if ω = ω₀ then (1 : ℝ) else 0) = weight ν ω₀ := by
    unfold OSSS.expect
    rw [Finset.sum_eq_single ω₀]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hR : Lindeberg.mean μ (fun ω => if ω = ω₀ then (1 : ℝ) else 0) = μ ω₀ := by
    unfold Lindeberg.mean
    rw [Finset.sum_eq_single ω₀]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hL, hR] at h; exact h







theorem oc3_cov_eq_of_match {μ : ConfigSpace E → ℝ} {ν : E → Bool → ℝ}
    (hmatch : ∀ g, expect ν g = Lindeberg.mean μ g) (F G : ConfigSpace E → ℝ) :
    cov ν F G = Lindeberg.cov μ F G := by
  unfold cov Lindeberg.cov
  rw [hmatch (fun ω => F ω * G ω), hmatch F, hmatch G]








theorem oc3_coordI_flipAt_ne (e e' : E) (he : e ≠ e') (ω : ConfigSpace E) :
    coordI e' (flipAt e ω) = coordI e' ω := by
  unfold coordI
  rw [flipAt_eval_ne e e' (Ne.symm he) ω]








theorem oc3_cov_coordI_cross {ν : E → Bool → ℝ} (hν : IsProbWeight ν) (e e' : E) (he : e ≠ e') :
    cov ν (coordI e) (coordI e') = 0 :=
  cov_coordI_indep hν e (coordI e') (fun ω => oc3_coordI_flipAt_ne e e' he ω)










def oc3_GenuinelyCorrelated (μ : ConfigSpace E → ℝ) : Prop :=
  ∃ e e' : E, e ≠ e' ∧ Lindeberg.cov μ (Lindeberg.coord e) (Lindeberg.coord e') ≠ 0














theorem oc3_no_product_weight {μ : ConfigSpace E → ℝ} (hcorr : oc3_GenuinelyCorrelated μ) :
    ¬ ∃ ν : E → Bool → ℝ, IsProbWeight ν ∧ ∀ g, expect ν g = Lindeberg.mean μ g := by
  obtain ⟨e, e', he, hne⟩ := hcorr
  rintro ⟨ν, hν, hmatch⟩
  apply hne
  rw [show Lindeberg.coord e = coordI e from rfl, show Lindeberg.coord e' = coordI e' from rfl,
      ← oc3_cov_eq_of_match hmatch (coordI e) (coordI e')]
  exact oc3_cov_coordI_cross hν e e' he





theorem oc3_match_forces_uncorrelated {μ : ConfigSpace E → ℝ} {ν : E → Bool → ℝ}
    (hν : IsProbWeight ν) (hmatch : ∀ g, expect ν g = Lindeberg.mean μ g) (e e' : E)
    (he : e ≠ e') :
    Lindeberg.cov μ (Lindeberg.coord e) (Lindeberg.coord e') = 0 := by
  rw [show Lindeberg.coord e = coordI e from rfl, show Lindeberg.coord e' = coordI e' from rfl,
      ← oc3_cov_eq_of_match hmatch (coordI e) (coordI e')]
  exact oc3_cov_coordI_cross hν e e' he






theorem oc3_match_iff_weight_eq {μ : ConfigSpace E → ℝ} {ν : E → Bool → ℝ} :
    (∀ g, expect ν g = Lindeberg.mean μ g) ↔ (∀ ω, weight ν ω = μ ω) := by
  constructor
  · intro hmatch ω; exact oc3_weight_eq_of_match hmatch ω
  · intro hw g
    unfold OSSS.expect Lindeberg.mean
    exact Finset.sum_congr rfl (fun ω _ => by rw [hw ω]; ring)




















theorem oc3_match_forces_revealment_one {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e₀ : E)
    (he₀ : (σ.symm e₀ : ℕ) = 0) (hnc : ∀ X, ¬ ∀ w, f w = f X)
    {ν : E → Bool → ℝ} (T : DecisionTree E)
    (hmatch : revealAdapt μ σ f e₀ = reveal ν T e₀) :
    reveal ν T e₀ = 1 :=
  oc2_perEdge_match_forces_one hpos hμ1 σ f e₀ he₀ hnc T hmatch












noncomputable def oc3_corrMu : ConfigSpace (Fin 2) → ℝ :=
  fun ω => if ω 0 = ω 1 then (1 : ℝ) / 2 else 0


theorem oc3_corrMu_sum_eq_one : ∑ ω : ConfigSpace (Fin 2), oc3_corrMu ω = 1 := by
  have huniv : (Finset.univ : Finset (ConfigSpace (Fin 2)))
      = {![false, false], ![false, true], ![true, false], ![true, true]} := by decide
  rw [huniv]
  unfold oc3_corrMu
  norm_num [Finset.sum_insert, Finset.mem_insert, Matrix.cons_val_zero, Matrix.cons_val_one]


theorem oc3_corrMu_nonneg : ∀ ω, 0 ≤ oc3_corrMu ω := by
  intro ω; unfold oc3_corrMu; split <;> norm_num


theorem oc3_corrMu_cov_ne_zero :
    Lindeberg.cov oc3_corrMu (Lindeberg.coord (0 : Fin 2)) (Lindeberg.coord (1 : Fin 2)) ≠ 0 := by
  unfold Lindeberg.cov Lindeberg.mean Lindeberg.coord oc3_corrMu
  have huniv : (Finset.univ : Finset (ConfigSpace (Fin 2)))
      = {![false, false], ![false, true], ![true, false], ![true, true]} := by decide
  rw [huniv]
  norm_num [Finset.sum_insert, Finset.mem_insert, Matrix.cons_val_zero, Matrix.cons_val_one]



theorem oc3_corrMu_genuinelyCorrelated : oc3_GenuinelyCorrelated oc3_corrMu :=
  ⟨0, 1, by decide, oc3_corrMu_cov_ne_zero⟩










theorem oc3_no_product_weight_witness :
    ¬ ∃ ν : Fin 2 → Bool → ℝ, IsProbWeight ν ∧
        ∀ g, expect ν g = Lindeberg.mean oc3_corrMu g :=
  oc3_no_product_weight oc3_corrMu_genuinelyCorrelated









section FK

open StatMech.OSSS.MonotonicFK











theorem oc3_fk_no_product_weight {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p q : ℝ) (e e' : Sym2 V) (he : e ≠ e')
    (hcorr : Lindeberg.cov (fkMass G p q) (Lindeberg.coord e) (Lindeberg.coord e') ≠ 0) :
    ¬ ∃ ν : Sym2 V → Bool → ℝ, IsProbWeight ν ∧
        ∀ g, expect ν g = Lindeberg.mean (fkMass G p q) g :=
  oc3_no_product_weight ⟨e, e', he, hcorr⟩

end FK

end Walls
end StatMech
