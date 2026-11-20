/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Mathlib
import Code.Sharpness.RandomCurrent
import Code.Sharpness.ClaimIsing
import Code.Sharpness.CurrentRep
import Code.Sharpness.TwoReplica
import Code.Sharpness.ClaimIsingFull

open SimpleGraph Finset
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace StatMech

namespace Sharpness









section Claim2Consumption

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]












theorem localized_two_point_of_claim2 (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (g : V)
    (hg : g ∉ S) (zero x : V) (h0 : zero ∈ S) (hx : x ∈ S)
    (hZ : currentSum G β (couplingIn J S) ∅ ≠ 0)
    (hden : (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
          (if sources G (ofEdgeFun G pq.1) = ∅ then weight G β J (ofEdgeFun G pq.1) else 0)
            * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0)
            * (if notConnComp G (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) g = S
                then 1 else 0)) ≠ 0) :
    expectationJ G β (couplingIn J S) {zero, x}
      = (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
          (if sources G (ofEdgeFun G pq.1) = {zero, x} then weight G β J (ofEdgeFun G pq.1) else 0)
            * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0)
            * (if notConnComp G (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) g = S
                then 1 else 0))
        / (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
          (if sources G (ofEdgeFun G pq.1) = ∅ then weight G β J (ofEdgeFun G pq.1) else 0)
            * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0)
            * (if notConnComp G (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) g = S
                then 1 else 0)) := by
  rw [claim2_ising G β J S g hg zero x h0 hx hZ, mul_div_assoc, div_self hden, mul_one]

end Claim2Consumption










section SelfImprovement

variable {V : Type*}













structure SimonLieb (τ : V → V → ℝ) (o : V) (S : Finset V)
    (simWeight : V → V → ℝ) (boundaryTargets : Finset V) : Prop where
  
  τ_nonneg : ∀ a b, 0 ≤ τ a b
  
  weight_nonneg : ∀ x y, 0 ≤ simWeight x y
  
  simon : ∀ z, z ∉ S →
    τ o z ≤ ∑ x ∈ S, ∑ y ∈ boundaryTargets, simWeight x y * τ y z



noncomputable def simonConst (S : Finset V) (simWeight : V → V → ℝ) (boundaryTargets : Finset V) :
    ℝ := ∑ x ∈ S, ∑ y ∈ boundaryTargets, simWeight x y


theorem simonConst_nonneg (S : Finset V) (simWeight : V → V → ℝ) (boundaryTargets : Finset V)
    (hw : ∀ x y, 0 ≤ simWeight x y) :
    0 ≤ simonConst S simWeight boundaryTargets :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hw _ _



















theorem susceptibility_self_consistent_sl [DecidableEq V] (τ : V → V → ℝ) (o : V) (S : Finset V)
    (simWeight : V → V → ℝ) (boundaryTargets : Finset V)
    (hSL : SimonLieb τ o S simWeight boundaryTargets)
    (Λ : Finset V) (χbar : ℝ)
    (hχbar : ∀ y ∈ boundaryTargets, ∑ z ∈ Λ \ S, τ y z ≤ χbar)
    (hχnn : 0 ≤ χbar)
    (hSbound : ∑ z ∈ Λ ∩ S, τ o z ≤ (S.card : ℝ)) :
    ∑ z ∈ Λ, τ o z ≤ (S.card : ℝ) + simonConst S simWeight boundaryTargets * χbar := by
  classical
  
  rw [← Finset.sum_inter_add_sum_diff Λ S (τ o)]
  refine add_le_add hSbound ?_
  
  calc ∑ z ∈ Λ \ S, τ o z
      ≤ ∑ z ∈ Λ \ S, ∑ x ∈ S, ∑ y ∈ boundaryTargets, simWeight x y * τ y z := by
        refine Finset.sum_le_sum (fun z hz => ?_)
        exact hSL.simon z (Finset.mem_sdiff.mp hz).2
    _ = ∑ x ∈ S, ∑ y ∈ boundaryTargets, simWeight x y * (∑ z ∈ Λ \ S, τ y z) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [Finset.mul_sum]
    _ ≤ ∑ x ∈ S, ∑ y ∈ boundaryTargets, simWeight x y * χbar := by
        refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y hy => ?_))
        exact mul_le_mul_of_nonneg_left (hχbar y hy) (hSL.weight_nonneg x y)
    _ = simonConst S simWeight boundaryTargets * χbar := by
        unfold simonConst; rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.sum_mul]








theorem susceptibility_solve (χ Sval φ : ℝ) (hχ : 0 ≤ χ) (hφ1 : φ < 1)
    (hself : χ ≤ Sval + φ * χ) :
    χ ≤ Sval / (1 - φ) := by
  have h1mφ : 0 < 1 - φ := by linarith
  rw [le_div_iff₀ h1mφ]
  nlinarith [hself]






theorem susceptibility_uniform_of_simon (S : Finset V) (simWeight : V → V → ℝ)
    (boundaryTargets : Finset V) (χbar : ℝ) (hχnn : 0 ≤ χbar)
    (hφ1 : simonConst S simWeight boundaryTargets < 1)
    (hself : χbar ≤ (S.card : ℝ) + simonConst S simWeight boundaryTargets * χbar) :
    χbar ≤ (S.card : ℝ) / (1 - simonConst S simWeight boundaryTargets) :=
  susceptibility_solve χbar (S.card : ℝ) (simonConst S simWeight boundaryTargets) hχnn hφ1 hself







theorem decay_iterate (φ : ℝ) (hφ0 : 0 ≤ φ) (f : ℕ → ℝ) (hf0 : f 0 ≤ 1)
    (hstep : ∀ k, f (k + 1) ≤ φ * f k) : ∀ k, f k ≤ φ ^ k := by
  intro k
  induction k with
  | zero => simpa using hf0
  | succ n ih =>
    calc f (n + 1) ≤ φ * f n := hstep n
      _ ≤ φ * φ ^ n := mul_le_mul_of_nonneg_left ih hφ0
      _ = φ ^ (n + 1) := by ring





theorem exponential_decay_of_geom (φ : ℝ) (hφ0 : 0 < φ) (hφ1 : φ < 1) (L : ℕ) (hL : 1 ≤ L) :
    ∃ c > 0, ∃ C > 0, ∀ n : ℕ, φ ^ (n / L) ≤ C * Real.exp (-c * n) := by
  have hlog : Real.log φ < 0 := Real.log_neg hφ0 hφ1
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hφinv : (0 : ℝ) < φ⁻¹ := by positivity
  have hcpos : 0 < -Real.log φ / L := div_pos (by linarith) hLpos
  refine ⟨-Real.log φ / L, hcpos, φ⁻¹, hφinv, fun n => ?_⟩
  
  have hk : (n : ℝ) / L - 1 ≤ (↑(n / L) : ℝ) := by
    have h : n < (n / L + 1) * L := by
      have h1 := Nat.div_add_mod n L
      have h2 := Nat.mod_lt n (by omega : 0 < L)
      nlinarith [h1, h2]
    have hr : (n : ℝ) < ((n / L : ℕ) + 1) * L := by exact_mod_cast h
    rw [div_sub' (by positivity), div_le_iff₀ hLpos]
    push_cast at hr ⊢
    nlinarith
  calc φ ^ (n / L) = Real.exp ((↑(n / L) : ℝ) * Real.log φ) := by
        rw [Real.exp_nat_mul, Real.exp_log hφ0]
    _ ≤ Real.exp (((n : ℝ) / L - 1) * Real.log φ) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hk hlog.le)
    _ = φ⁻¹ * Real.exp (-(-Real.log φ / L) * n) := by
        rw [← Real.exp_log hφinv, ← Real.exp_add, Real.log_inv]
        congr 1; field_simp; ring













theorem exponential_decay_of_simon (φ : ℝ) (hφ0 : 0 < φ) (hφ1 : φ < 1) (L : ℕ) (hL : 1 ≤ L)
    (f : ℕ → ℝ) (hfnn : ∀ n, 0 ≤ f n) (hf0 : f 0 ≤ 1)
    (hstep : ∀ k, f ((k + 1) * L) ≤ φ * f (k * L))
    (hmono : ∀ m n, m ≤ n → f n ≤ f m) :
    ∃ c > 0, ∃ C > 0, ∀ n : ℕ, f n ≤ C * Real.exp (-c * n) := by
  
  have hgeom : ∀ k, f (k * L) ≤ φ ^ k := by
    refine decay_iterate φ hφ0.le (fun k => f (k * L)) ?_ ?_
    · simpa using hf0
    · intro k; exact hstep k
  
  obtain ⟨c, hc, C, hC, hexp⟩ := exponential_decay_of_geom φ hφ0 hφ1 L hL
  refine ⟨c, hc, C, hC, fun n => ?_⟩
  
  have hle : (n / L) * L ≤ n := Nat.div_mul_le_self n L
  calc f n ≤ f ((n / L) * L) := hmono _ _ hle
    _ ≤ φ ^ (n / L) := hgeom (n / L)
    _ ≤ C * Real.exp (-c * n) := hexp n




















theorem ising_sharpness_finite_susceptibility [DecidableEq V] (τ : V → V → ℝ) (o : V)
    (S : Finset V) (simWeight : V → V → ℝ) (boundaryTargets : Finset V)
    (hSL : SimonLieb τ o S simWeight boundaryTargets)
    (hφ1 : simonConst S simWeight boundaryTargets < 1)
    (Λ W : Finset V)
    (hχbarW : ∀ y ∈ boundaryTargets, ∑ z ∈ W \ S, τ y z ≤ ∑ z ∈ W, τ o z)
    (hSboundW : ∑ z ∈ W ∩ S, τ o z ≤ (S.card : ℝ))
    (hΛbar : ∑ z ∈ Λ, τ o z ≤ ∑ z ∈ W, τ o z) :
    ∑ z ∈ Λ, τ o z ≤ (S.card : ℝ) / (1 - simonConst S simWeight boundaryTargets) := by
  
  have hWnn : 0 ≤ ∑ z ∈ W, τ o z := Finset.sum_nonneg fun z _ => hSL.τ_nonneg o z
  
  have hself : ∑ z ∈ W, τ o z
      ≤ (S.card : ℝ) + simonConst S simWeight boundaryTargets * (∑ z ∈ W, τ o z) :=
    susceptibility_self_consistent_sl τ o S simWeight boundaryTargets hSL W
      (∑ z ∈ W, τ o z) hχbarW hWnn hSboundW
  
  exact le_trans hΛbar
    (susceptibility_uniform_of_simon S simWeight boundaryTargets (∑ z ∈ W, τ o z) hWnn hφ1 hself)

end SelfImprovement

end Sharpness

end StatMech
