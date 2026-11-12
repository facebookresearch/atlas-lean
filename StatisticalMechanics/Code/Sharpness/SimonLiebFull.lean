/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Mathlib
import Code.Sharpness.RandomCurrent
import Code.Sharpness.CurrentRep
import Code.Sharpness.BackboneProps
import Code.Sharpness.SimonLieb
import Code.Sharpness.ClaimIsingFull
import Code.Sharpness.IsingSharpnessFull

open SimpleGraph Finset
open scoped BigOperators Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]












noncomputable def ssl_backboneClassSum (β : ℝ) (J : Sym2 V → ℝ) (x y : V)
    {ι : Type*} (sel : (↥G.edgeFinset → ℕ) → ι) (i : ι) : ℝ :=
  ∑' m : ↥G.edgeFinset → ℕ,
    if sources G (ofEdgeFun G m) = {x, y} ∧ sel m = i
      then weight G β J (ofEdgeFun G m) else 0



theorem ssl_summable_classTerm (β : ℝ) (J : Sym2 V → ℝ) (x y : V)
    {ι : Type*} (sel : (↥G.edgeFinset → ℕ) → ι) (i : ι) :
    Summable (fun m : ↥G.edgeFinset → ℕ =>
      if sources G (ofEdgeFun G m) = {x, y} ∧ sel m = i
        then weight G β J (ofEdgeFun G m) else 0) := by
  refine Summable.of_norm ((summable_norm_weight_ofEdgeFun G β J).of_nonneg_of_le
    (fun m => norm_nonneg _) (fun m => ?_))
  by_cases h : sources G (ofEdgeFun G m) = {x, y} ∧ sel m = i
  · rw [if_pos h]
  · rw [if_neg h]; simp





theorem ssl_sum_backboneClassSum (β : ℝ) (J : Sym2 V → ℝ) (x y : V)
    {ι : Type*} [Fintype ι] (sel : (↥G.edgeFinset → ℕ) → ι) :
    ∑ i : ι, ssl_backboneClassSum G β J x y sel i = currentSum G β J {x, y} := by
  classical
  unfold ssl_backboneClassSum currentSum
  rw [← Summable.tsum_finsetSum (s := (Finset.univ : Finset ι))
        (fun i _ => ssl_summable_classTerm G β J x y sel i)]
  refine tsum_congr (fun m => ?_)
  by_cases hsrc : sources G (ofEdgeFun G m) = {x, y}
  · rw [if_pos hsrc, Finset.sum_eq_single (sel m)]
    · rw [if_pos ⟨hsrc, rfl⟩]
    · intro j _ hj; rw [if_neg]; rintro ⟨_, h2⟩; exact hj h2.symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hsrc]
    exact Finset.sum_eq_zero (fun j _ => by rw [if_neg]; rintro ⟨h1, _⟩; exact hsrc h1)






noncomputable def ssl_backboneWeight (β : ℝ) (J : Sym2 V → ℝ) (x y : V)
    {ι : Type*} (sel : (↥G.edgeFinset → ℕ) → ι) (i : ι) : ℝ :=
  ssl_backboneClassSum G β J x y sel i / currentSum G β J ∅











theorem ssl_P1 (β : ℝ) (J : Sym2 V → ℝ) (x y : V)
    {ι : Type*} [Fintype ι] (sel : (↥G.edgeFinset → ℕ) → ι) :
    expectationJ G β J {x, y} = ∑ i : ι, ssl_backboneWeight G β J x y sel i := by
  rw [current_representation]
  unfold ssl_backboneWeight
  rw [← Finset.sum_div, ssl_sum_backboneClassSum]







theorem ssl_weight_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (n : Current V) : 0 ≤ weight G β J n := by
  unfold weight
  exact Finset.prod_nonneg (fun e _ =>
    div_nonneg (pow_nonneg (mul_nonneg hβ (hJ e)) _) (by positivity))


theorem ssl_currentSum_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (A : Finset V) : 0 ≤ currentSum G β J A := by
  unfold currentSum
  exact tsum_nonneg (fun m => by
    by_cases h : sources G (ofEdgeFun G m) = A
    · rw [if_pos h]; exact ssl_weight_nonneg G β J hβ hJ _
    · rw [if_neg h])



theorem ssl_expectationJ_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (A : Finset V) : 0 ≤ expectationJ G β J A := by
  rw [current_representation]
  exact div_nonneg (ssl_currentSum_nonneg G β J hβ hJ A) (ssl_currentSum_nonneg G β J hβ hJ ∅)


theorem ssl_backboneWeight_nonneg (β : ℝ) (J : Sym2 V → ℝ) (x y : V)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    {ι : Type*} (sel : (↥G.edgeFinset → ℕ) → ι) (i : ι) :
    0 ≤ ssl_backboneWeight G β J x y sel i := by
  unfold ssl_backboneWeight ssl_backboneClassSum
  apply div_nonneg
  · exact tsum_nonneg (fun m => by
      by_cases h : sources G (ofEdgeFun G m) = {x, y} ∧ sel m = i
      · rw [if_pos h]; exact ssl_weight_nonneg G β J hβ hJ _
      · rw [if_neg h])
  · exact ssl_currentSum_nonneg G β J hβ hJ ∅









theorem ssl_sum_prod_restrict (S T : Finset V) (f : V → V → ℝ) :
    ∑ p : V × V, (if p.1 ∈ S ∧ p.2 ∈ T then f p.1 p.2 else 0)
      = ∑ x ∈ S, ∑ y ∈ T, f x y := by
  classical
  rw [Fintype.sum_prod_type]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => x ∈ S)]
  rw [show (∑ x ∈ Finset.univ.filter (fun x => x ∉ S),
        ∑ y : V, (if x ∈ S ∧ y ∈ T then f x y else 0)) = 0 from ?_]
  · rw [add_zero, Finset.filter_univ_mem]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun y => y ∈ T)]
    rw [show (∑ y ∈ Finset.univ.filter (fun y => y ∉ T),
          (if x ∈ S ∧ y ∈ T then f x y else 0)) = 0 from ?_]
    · rw [add_zero, Finset.filter_univ_mem]
      exact Finset.sum_congr rfl (fun y hy => by rw [if_pos ⟨hx, hy⟩])
    · exact Finset.sum_eq_zero (fun y hy => by
        rw [Finset.mem_filter] at hy; rw [if_neg (fun h => hy.2 h.2)])
  · exact Finset.sum_eq_zero (fun x hx => by
      rw [Finset.mem_filter] at hx
      exact Finset.sum_eq_zero (fun y _ => by rw [if_neg (fun h => hx.2 h.1)]))




























theorem ssl_simon_at_target (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (o : V)
    (boundaryTargets : Finset V) (z : V)
    (selFE : (↥G.edgeFinset → ℕ) → V × V)
    (hFE_bound : ∀ x ∈ S, ∀ y ∈ boundaryTargets,
      ssl_backboneWeight G β J o z selFE (x, y)
        ≤ simonWeight G β J S o x y * expectationJ G β J {y, z})
    (hFE_zero : ∀ p : V × V, ¬ (p.1 ∈ S ∧ p.2 ∈ boundaryTargets) →
      ssl_backboneWeight G β J o z selFE p ≤ 0) :
    expectationJ G β J {o, z}
      ≤ ∑ x ∈ S, ∑ y ∈ boundaryTargets,
          simonWeight G β J S o x y * expectationJ G β J {y, z} := by
  classical
  calc expectationJ G β J {o, z}
      = ∑ p : V × V, ssl_backboneWeight G β J o z selFE p := ssl_P1 G β J o z selFE
    _ ≤ ∑ p : V × V, (if p.1 ∈ S ∧ p.2 ∈ boundaryTargets
            then simonWeight G β J S o p.1 p.2 * expectationJ G β J {p.2, z} else 0) := by
          refine Finset.sum_le_sum (fun p _ => ?_)
          by_cases hp : p.1 ∈ S ∧ p.2 ∈ boundaryTargets
          · rw [if_pos hp]; exact hFE_bound p.1 hp.1 p.2 hp.2
          · rw [if_neg hp]; exact hFE_zero p hp
    _ = ∑ x ∈ S, ∑ y ∈ boundaryTargets,
          simonWeight G β J S o x y * expectationJ G β J {y, z} :=
          ssl_sum_prod_restrict S boundaryTargets
            (fun x y => simonWeight G β J S o x y * expectationJ G β J {y, z})







theorem ssl_simonLieb_of_firstExit (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (o : V)
    (boundaryTargets : Finset V)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (hcorr : ∀ x, 0 ≤ expectationJ G β (couplingIn J S) {o, x})
    (selFE : V → (↥G.edgeFinset → ℕ) → V × V)
    (hFE_bound : ∀ z, z ∉ S → ∀ x ∈ S, ∀ y ∈ boundaryTargets,
      ssl_backboneWeight G β J o z (selFE z) (x, y)
        ≤ simonWeight G β J S o x y * expectationJ G β J {y, z})
    (hFE_zero : ∀ z, z ∉ S → ∀ p : V × V, ¬ (p.1 ∈ S ∧ p.2 ∈ boundaryTargets) →
      ssl_backboneWeight G β J o z (selFE z) p ≤ 0) :
    SimonLieb (fun a b => expectationJ G β J {a, b}) o S (simonWeight G β J S o) boundaryTargets :=
  simonLieb_of_firstExit (fun a b => expectationJ G β J {a, b}) o S (simonWeight G β J S o)
    boundaryTargets
    (fun a b => ssl_expectationJ_nonneg G β J hβ hJ {a, b})
    (simonWeight_nonneg G β J S o hβ hJ hcorr)
    (fun z hz => ssl_simon_at_target G β J S o boundaryTargets z (selFE z)
      (hFE_bound z hz) (hFE_zero z hz))











theorem ssl_finite_susceptibility (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (o : V)
    (boundaryTargets : Finset V)
    (hSL : SimonLieb (fun a b => expectationJ G β J {a, b}) o S (simonWeight G β J S o)
      boundaryTargets)
    (hφ1 : simonConst S (simonWeight G β J S o) boundaryTargets < 1)
    (Λ W : Finset V)
    (hχbarW : ∀ y ∈ boundaryTargets,
      ∑ z ∈ W \ S, expectationJ G β J {y, z} ≤ ∑ z ∈ W, expectationJ G β J {o, z})
    (hSboundW : ∑ z ∈ W ∩ S, expectationJ G β J {o, z} ≤ (S.card : ℝ))
    (hΛbar : ∑ z ∈ Λ, expectationJ G β J {o, z} ≤ ∑ z ∈ W, expectationJ G β J {o, z}) :
    ∑ z ∈ Λ, expectationJ G β J {o, z}
      ≤ (S.card : ℝ) / (1 - simonConst S (simonWeight G β J S o) boundaryTargets) :=
  ising_sharpness_finite_susceptibility (fun a b => expectationJ G β J {a, b}) o S
    (simonWeight G β J S o) boundaryTargets hSL hφ1 Λ W hχbarW hSboundW hΛbar

end Sharpness

end StatMech
