/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Mathlib
import Code.FK.EdwardsSokal
import Code.FK.RandomCluster
import Code.FK.EsCorrelations

open scoped BigOperators

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]






theorem esWeight_spinsum_factor_q {q : ℕ} (p : ℝ) (ω : ConfigSpace (Sym2 V))
    (g : (V → Fin q) → ℝ) :
    (∑ σ : V → Fin q, esWeight G p σ ω * g σ)
      = edgeProduct G p ω
        * ∑ σ : V → Fin q, (if ConstOnOpen G ω σ then (1 : ℝ) else 0) * g σ := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [esWeight_factor, monoProd_eq_indicator]
  ring




theorem card_constEq_real_conn {q : ℕ} (ω : ConfigSpace (Sym2 V)) {x y : V}
    (hxy : Connected G ω x y) :
    ((Finset.univ.filter (fun σ : V → Fin q => ConstOnOpen G ω σ ∧ σ x = σ y)).card : ℝ)
      = (q : ℝ) ^ numClusters G ω := by
  have hc := card_constEq_connected (q := q) G ω hxy
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
  rw [hc]; push_cast; ring




theorem card_constEq_real_disc {q : ℕ} (ω : ConfigSpace (Sym2 V)) {x y : V}
    (hxy : ¬ Connected G ω x y) :
    ((Finset.univ.filter (fun σ : V → Fin q => ConstOnOpen G ω σ ∧ σ x = σ y)).card : ℝ)
      = (q : ℝ) ^ (numClusters G ω - 1) := by
  have hc := card_constEq_disconnected (q := q) G ω hxy
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
  rw [hc]; push_cast; ring













theorem spinAgree_sum_eq {q : ℕ} [NeZero q] (p : ℝ) (ω : ConfigSpace (Sym2 V)) (x y : V) :
    (∑ σ : V → Fin q, esWeight G p σ ω * (if σ x = σ y then (1 : ℝ) else 0))
      = if Connected G ω x y then fkWeight G p (q : ℝ) ω
        else fkWeight G p (q : ℝ) ω / q := by
  rw [esWeight_spinsum_factor_q]
  have hinner : (∑ σ : V → Fin q,
        (if ConstOnOpen G ω σ then (1 : ℝ) else 0) * (if σ x = σ y then (1 : ℝ) else 0))
      = ((Finset.univ.filter (fun σ : V → Fin q => ConstOnOpen G ω σ ∧ σ x = σ y)).card : ℝ) := by
    rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro σ _
    by_cases hc : ConstOnOpen G ω σ <;> by_cases he : σ x = σ y <;> simp [hc, he]
  rw [hinner]
  by_cases h : Connected G ω x y
  · rw [if_pos h, card_constEq_real_conn G ω h]
    unfold fkWeight; ring
  · rw [if_neg h, card_constEq_real_disc G ω h]
    have hqne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
    have hk : 1 ≤ numClusters G ω := one_le_numClusters G ω x
    unfold fkWeight
    rw [mul_div_assoc]
    congr 1
    rw [eq_div_iff hqne, mul_comm ((q : ℝ) ^ (numClusters G ω - 1)) (q : ℝ), ← pow_succ']
    congr 1
    omega






noncomputable def pottsAgreeProb (q : ℕ) (β J : ℝ) (x y : V) : ℝ :=
  ∑ σ ∈ Finset.univ.filter (fun σ : V → Fin q => σ x = σ y), Potts.pottsProb G q β J σ





theorem pottsAgreeProb_eq_joint (q : ℕ) [NeZero q] (β J : ℝ) (x y : V) :
    pottsAgreeProb G q β J x y
      = (∑ ω : ConfigSpace (Sym2 V), ∑ σ : V → Fin q,
          esWeight G (1 - Real.exp (-(β * J))) σ ω * (if σ x = σ y then (1 : ℝ) else 0))
        / esZ G q (1 - Real.exp (-(β * J))) := by
  unfold pottsAgreeProb
  rw [Finset.sum_congr rfl (fun σ _ => (esFirstMarginal_eq_pottsProb G q β J σ).symm)]
  unfold esFirstMarginal
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases he : σ x = σ y <;> simp [he]













theorem edwards_sokal_correlation (q : ℕ) [NeZero q] (β J : ℝ) (x y : V)
    (hp : 0 < 1 - Real.exp (-(β * J))) (hp1 : 1 - Real.exp (-(β * J)) < 1)
    (hq : 0 < (q : ℝ)) :
    pottsAgreeProb G q β J x y - 1 / q
      = (1 - 1 / q) * connProb G (1 - Real.exp (-(β * J))) q x y := by
  set p := 1 - Real.exp (-(β * J)) with hpdef
  rw [pottsAgreeProb_eq_joint]
  rw [Finset.sum_congr rfl (fun ω _ => spinAgree_sum_eq G p ω x y)]
  rw [esZ_eq_fkZ, Finset.sum_div]
  
  have hterm : ∀ ω : ConfigSpace (Sym2 V),
      (if Connected G ω x y then fkWeight G p (q : ℝ) ω else fkWeight G p (q : ℝ) ω / q)
          / fkZ G p q
        = if Connected G ω x y then fkProb G p q ω else fkProb G p q ω / q := by
    intro ω
    by_cases h : Connected G ω x y
    · rw [if_pos h, if_pos h]; rfl
    · rw [if_neg h, if_neg h]; unfold fkProb; rw [div_div, mul_comm (q : ℝ), ← div_div]
  rw [Finset.sum_congr rfl (fun ω _ => hterm ω)]
  
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun ω : ConfigSpace (Sym2 V) => Connected G ω x y)]
  have hc : (∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => Connected G ω x y),
        (if Connected G ω x y then fkProb G p q ω else fkProb G p q ω / q))
      = connProb G p q x y := by
    unfold connProb
    apply Finset.sum_congr rfl
    intro ω hω; rw [if_pos (Finset.mem_filter.1 hω).2]
  have hd : (∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ¬ Connected G ω x y),
        (if Connected G ω x y then fkProb G p q ω else fkProb G p q ω / q))
      = (1 - connProb G p q x y) / q := by
    rw [Finset.sum_congr rfl (fun ω hω => if_neg (Finset.mem_filter.1 hω).2)]
    rw [← Finset.sum_div]
    congr 1
    
    have htot : (∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => Connected G ω x y),
          fkProb G p q ω)
        + (∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ¬ Connected G ω x y),
          fkProb G p q ω) = 1 := by
      rw [Finset.sum_filter_add_sum_filter_not]
      exact fkProb_sum_eq_one G hp hp1 hq
    have hconn : (∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => Connected G ω x y),
          fkProb G p q ω) = connProb G p q x y := rfl
    rw [hconn] at htot
    linarith
  rw [hc, hd]
  field_simp
  ring







theorem edwards_sokal_correlation' (q : ℕ) [NeZero q] (β J : ℝ) (x y : V)
    (hp : 0 < 1 - Real.exp (-(β * J))) (hp1 : 1 - Real.exp (-(β * J)) < 1)
    (hq : 0 < (q : ℝ)) :
    pottsAgreeProb G q β J x y - 1 / q
      = ((q : ℝ) - 1) / q * connProb G (1 - Real.exp (-(β * J))) q x y := by
  rw [edwards_sokal_correlation G q β J x y hp hp1 hq]
  congr 1
  field_simp





theorem pottsAgreeProb_ge (q : ℕ) [NeZero q] (β J : ℝ) (x y : V)
    (hp : 0 < 1 - Real.exp (-(β * J))) (hp1 : 1 - Real.exp (-(β * J)) < 1)
    (hq : 2 ≤ q) :
    1 / q ≤ pottsAgreeProb G q β J x y := by
  have hqr : (0 : ℝ) < q := by positivity
  have hkey := edwards_sokal_correlation G q β J x y hp hp1 hqr
  have hconn_nonneg : 0 ≤ connProb G (1 - Real.exp (-(β * J))) q x y := by
    unfold connProb
    apply Finset.sum_nonneg
    intro ω _
    exact fkProb_nonneg G hp hp1 hqr ω
  have hcoef : 0 ≤ 1 - 1 / (q : ℝ) := by
    rw [sub_nonneg, div_le_one hqr]
    exact_mod_cast Nat.one_le_of_lt hq
  nlinarith [mul_nonneg hcoef hconn_nonneg]

end FK

end StatMech
