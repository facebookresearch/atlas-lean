/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.StatisticalMechanics.RandomCluster.SuperMultiplicative
import Mathlib.Data.Sym.Card

/-!
# Juxtaposition and raw-partition regressions

The zero-index contradiction is independent of probability parameters. Restricting edge
positivity to positive indices would not fix raw pressure: for `q ≥ 1`, quadratic unused
coordinate growth prevents the required lower bound. A one-edge graph exercises the retained
finite-graph inequality with positive edge count.
-/

open scoped BigOperators
open SimpleGraph _root_.StatMech _root_.StatMech.FK

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.SuperMultiplicative

private lemma empty_of_self_sum {V : Type*} [Fintype V] (e : V ≃ V ⊕ V) : IsEmpty V := by
  have h := Fintype.card_congr e
  rw [Fintype.card_sum] at h
  exact Fintype.card_eq_zero_iff.mp (by omega)

private lemma no_positive_edges {V : Type*} [Fintype V] [DecidableEq V] [IsEmpty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ¬ 0 < G.edgeFinset.card := by
  have h : G.edgeFinset = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro e he
    induction e using Sym2.ind with
    | _ a b => exact isEmptyElim a
  simp [h]

example {V : ℕ → Type*} [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (G : ∀ n, SimpleGraph (V n)) [∀ n, DecidableRel (G n).Adj]
    (hjux : ∀ m n, G (m + n) ≃g G m ⊕g G n) :
    ¬ (∀ n, 0 < (G n).edgeFinset.card) := by
  intro hE
  let : IsEmpty (V 0) := empty_of_self_sum (hjux 0 0).toEquiv
  exact no_positive_edges (G 0) (hE 0)

private lemma half_partition_lower {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℝ} (hq : 1 ≤ q) :
    (2 : ℝ) ^ Fintype.card (Sym2 V) * (1 / 2 : ℝ) ^ G.edgeFinset.card ≤
      fkZ G (1 / 2) q := by
  have hw (ω : ConfigSpace (Sym2 V)) :
      (1 / 2 : ℝ) ^ G.edgeFinset.card ≤ fkWeight G (1 / 2) q ω := by
    have hp : edgeProduct G (1 / 2) ω = (1 / 2 : ℝ) ^ G.edgeFinset.card := by
      norm_num [edgeProduct]
      rw [one_div, inv_pow]
    rw [fkWeight, hp]
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hq)
  have hcard : Fintype.card (ConfigSpace (Sym2 V)) = 2 ^ Fintype.card (Sym2 V) := by
    change Fintype.card (Sym2 V → Bool) = _
    rw [Fintype.card_fun, Fintype.card_bool]
  calc _ = ∑ _ω : ConfigSpace (Sym2 V), (1 / 2 : ℝ) ^ G.edgeFinset.card := by
         simp [hcard]
       _ ≤ fkZ G (1 / 2) q := Finset.sum_le_sum (fun ω _ => hw ω)

private lemma log_half_partition_lower {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℝ} (hq : 1 ≤ q) :
    ((Fintype.card (Sym2 V) : ℝ) - G.edgeFinset.card) * Real.log 2 ≤
      Real.log (fkZ G (1 / 2) q) := by
  have h := Real.log_le_log (by positivity) (half_partition_lower G hq)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h
  have hl : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hl] at h
  nlinarith

private lemma card_sym2_lower (V : Type*) [Fintype V] :
    Fintype.card V ^ 2 ≤ 2 * Fintype.card (Sym2 V) + 1 := by
  simp only [Sym2.card, Nat.choose_two_right, Nat.add_sub_cancel]
  have hmod := Nat.mod_lt ((Fintype.card V + 1) * Fintype.card V) (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div ((Fintype.card V + 1) * Fintype.card V) 2
  nlinarith

private lemma additive_nat_values (f : ℕ → ℕ)
    (hf : ∀ m n, f (m + n) = f m + f n) (n : ℕ) : f n = n * f 1 := by
  induction n with
  | zero =>
      have h := hf 0 0
      simp only [Nat.zero_add] at h
      simp only [Nat.zero_mul]
      omega
  | succ n ih =>
      rw [hf, ih]
      ring

private lemma juxtaposition_cardinals {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (G : ∀ n, SimpleGraph (V n)) [∀ n, DecidableRel (G n).Adj]
    (hjux : ∀ m n, G (m + n) ≃g G m ⊕g G n) (n : ℕ) :
    Fintype.card (V n) = n * Fintype.card (V 1) ∧
      (G n).edgeFinset.card = n * (G 1).edgeFinset.card := by
  constructor
  · apply additive_nat_values (fun k => Fintype.card (V k)) _ n
    intro a b
    simpa only [Fintype.card_sum] using Fintype.card_congr (hjux a b).toEquiv
  · apply additive_nat_values (fun k => (G k).edgeFinset.card) _ n
    intro a b
    rw [(hjux a b).card_edgeFinset_eq, fsm_edgeFinset_sum,
      Finset.card_union_of_disjoint (fsm_images_disjoint (G a) (G b)),
      Finset.card_image_of_injective _ fsm_map_inl_injective,
      Finset.card_image_of_injective _ fsm_map_inr_injective]

private theorem raw_partition_unbounded {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (G : ∀ n, SimpleGraph (V n)) [∀ n, DecidableRel (G n).Adj]
    {q : ℝ} (hq : 1 ≤ q) (hV : 0 < Fintype.card (V 1))
    (hjux : ∀ m n, G (m + n) ≃g G m ⊕g G n) :
    ¬ BddBelow (Set.range fun n => -Real.log (fkZ (G n) (1 / 2) q) / n) := by
  rintro ⟨b, hb⟩
  let B : ℝ := (G 1).edgeFinset.card
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_gt
    (max 1 ((2 * B * Real.log 2 - 2 * b + Real.log 2) / Real.log 2))
  have hn1 : 1 < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hn0 : 0 < (n : ℝ) := lt_trans zero_lt_one hn1
  have hchoose : 2 * B * Real.log 2 - 2 * b + Real.log 2 < (n : ℝ) * Real.log 2 :=
    (div_lt_iff₀ hL).mp (lt_of_le_of_lt (le_max_right _ _) hn)
  obtain ⟨hN, hE⟩ := juxtaposition_cardinals G hjux n
  have hnN : n ≤ Fintype.card (V n) := by
    rw [hN]
    simpa using Nat.mul_le_mul_left n hV
  have hM : (n : ℝ) ^ 2 ≤ 2 * (Fintype.card (Sym2 (V n)) : ℝ) + 1 := by
    exact_mod_cast (Nat.pow_le_pow_left hnN 2).trans (card_sym2_lower (V n))
  have hMlog := mul_le_mul_of_nonneg_right hM hL.le
  have hlog := log_half_partition_lower (G n) hq
  rw [hE, Nat.cast_mul] at hlog
  have hbd : b ≤ -Real.log (fkZ (G n) (1 / 2) q) / n := hb (Set.mem_range_self n)
  have hupper : Real.log (fkZ (G n) (1 / 2) q) ≤ -b * n := by
    have h := (le_div_iff₀ hn0).mp hbd
    linarith
  have hscale := mul_lt_mul_of_pos_left hchoose hn0
  have hnlog : Real.log 2 ≤ (n : ℝ) * Real.log 2 := by
    nlinarith [mul_nonneg (le_of_lt (sub_pos.mpr hn1)) hL.le]
  dsimp [B] at hscale
  nlinarith

-- A real graph with an edge, not an edgeless graph or a scalar placeholder.
private abbrev oneEdge : SimpleGraph (Fin 2) := ⊤

example : 0 < oneEdge.edgeFinset.card := by decide

example : fkZ oneEdge (1 / 2) 2 * fkZ oneEdge (1 / 2) 2 ≤
    fkZ (oneEdge ⊕g oneEdge) (1 / 2) 2 :=
  fsm_fkZ_sum_ge oneEdge oneEdge (by norm_num) (by norm_num) (by norm_num)

run_cmd do
  if (← Lean.getEnv).contains `StatMech.FK.fsm_fekete_limit then
    throwError "Retired juxtaposition limit wrapper is still present"

end PhyslibExtTest.StatisticalMechanics.RandomCluster.SuperMultiplicative
