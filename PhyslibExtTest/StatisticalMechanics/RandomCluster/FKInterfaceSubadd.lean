/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.StatisticalMechanics.RandomCluster.FKInterfaceSubadd
import PhyslibExt.StatisticalMechanics.RandomCluster.EdgePartitionFunction
import Mathlib.Data.Sym.Card

/-!
# Box-split obstructions and finite-interface regression

Box cardinalities rule out the old disjoint-carrier isomorphism. The existing edge-partition
factorization rules out both raw `q = 2` box-Fekete predicates, in every dimension and at every
tilt. A real crossing edge and a nonzero scalar sequence exercise the retained APIs.
-/

open SimpleGraph Filter Topology
open _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.FKInterfaceSubadd

example (d m n : ℕ) (K : SimpleGraph (boxVerts d m ⊕ boxVerts d n)) :
    IsEmpty ((boxGraph d (m + n)) ≃g K) := by
  refine ⟨fun e => ?_⟩
  have h := Fintype.card_congr e.toEquiv
  rw [Fintype.card_sum] at h
  simp only [ecz_boxVerts_card] at h
  have hmod := congrArg (fun k => k % 2) h
  norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod] at hmod

private lemma raw_log_lower {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (Fintype.card (Sym2 V) : ℝ) * Real.log 2 -
        G.edgeFinset.card * (Real.log 2 - Real.log (1 - p)) ≤ Real.log (fkZ G p 2) := by
  have hZ := ecz_fkZEdge_pos G hp hp1 (by norm_num : (0 : ℝ) < 2)
  have hbound := ecz_neglogZEdge_le_edges G hp hp1 (by norm_num : (1 : ℝ) ≤ 2)
  have hcard : G.edgeFinset.card ≤ Fintype.card (Sym2 V) := Finset.card_le_univ _
  have hNE : (ecz_NE G : ℝ) = (Fintype.card (Sym2 V) : ℝ) - G.edgeFinset.card := by
    rw [ecz_NE_eq, Nat.cast_sub hcard]
  rw [ecz_factorization, Real.log_mul (by positivity) hZ.ne', Real.log_pow, hNE]
  nlinarith

private lemma box_card_bounds (d n : ℕ) (hd : 1 ≤ d) :
    n ≤ Fintype.card (boxVerts d n) ∧
      (boxGraph d n).edgeFinset.card ≤ d * Fintype.card (boxVerts d n) := by
  constructor
  · rw [ecz_boxVerts_card]
    have h : (2 * n + 1) ^ 1 ≤ (2 * n + 1) ^ d :=
      Nat.pow_le_pow_right (by omega) hd
    simp only [pow_one] at h
    exact (show n ≤ 2 * n + 1 by omega).trans h
  · rw [ecz_boxVerts_card, EdgeCount.boxGraph_edgeCard d n hd]
    have hpow : (2 * n + 1) ^ d = (2 * n + 1) * (2 * n + 1) ^ (d - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hpow]
    exact Nat.mul_le_mul_left d (Nat.mul_le_mul_right _ (by omega : 2 * n ≤ 2 * n + 1))

private lemma card_sym2_lower (V : Type*) [Fintype V] :
    Fintype.card V ^ 2 ≤ 2 * Fintype.card (Sym2 V) + 1 := by
  simp only [Sym2.card, Nat.choose_two_right, Nat.add_sub_cancel]
  have hmod := Nat.mod_lt ((Fintype.card V + 1) * Fintype.card V) (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div ((Fintype.card V + 1) * Fintype.card V) 2
  nlinarith

private theorem raw_box_no_eventual_lower (d : ℕ) (hd : 1 ≤ d) (t : ℝ) :
    ¬ ∃ (b : ℝ) (N : ℕ), ∀ n, N ≤ n →
      b ≤ -Real.log (fkZ (boxGraph d n) (fsc_logistic t) 2) / n := by
  rintro ⟨b, N, hb⟩
  let C := Real.log 2 - Real.log (1 - fsc_logistic t)
  have hp := fsc_logistic_pos t
  have hp1 := fsc_logistic_lt_one t
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 ≤ C := by
    have hneg : Real.log (1 - fsc_logistic t) < 0 :=
      Real.log_neg (by linarith) (by linarith)
    dsimp [C]
    linarith
  obtain ⟨n, hn⟩ := exists_nat_gt
    (max (N : ℝ) (max 1 ((2 * ((d : ℝ) * C + |b|) + Real.log 2) / Real.log 2)))
  have hnN : N ≤ n := by
    have h : (N : ℝ) < n := lt_of_le_of_lt (le_max_left _ _) hn
    exact_mod_cast h.le
  have hthreshold := lt_of_le_of_lt (le_max_right _ _) hn
  have hn1 : 1 < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hthreshold
  have hn0 : 0 < (n : ℝ) := lt_trans zero_lt_one hn1
  have hlarge : 2 * ((d : ℝ) * C + |b|) + Real.log 2 < (n : ℝ) * Real.log 2 :=
    (div_lt_iff₀ hL).mp (lt_of_le_of_lt (le_max_right _ _) hthreshold)
  obtain ⟨hnV, hE⟩ := box_card_bounds d n hd
  let v : ℝ := Fintype.card (boxVerts d n)
  have hnv : (n : ℝ) ≤ v := by dsimp [v]; exact_mod_cast hnV
  have hv0 : 0 < v := lt_of_lt_of_le hn0 hnv
  have hVlarge : 2 * ((d : ℝ) * C + |b|) + Real.log 2 < v * Real.log 2 :=
    hlarge.trans_le (mul_le_mul_of_nonneg_right hnv hL.le)
  have hscale := mul_lt_mul_of_pos_left hVlarge hv0
  have hVlog : Real.log 2 ≤ v * Real.log 2 := by
    nlinarith [mul_nonneg (show 0 ≤ v - 1 by linarith) hL.le]
  have hM : v ^ 2 ≤ 2 * (Fintype.card (Sym2 (boxVerts d n)) : ℝ) + 1 := by
    dsimp [v]
    exact_mod_cast card_sym2_lower (boxVerts d n)
  have hMlog := mul_le_mul_of_nonneg_right hM hL.le
  have hEreal : ((boxGraph d n).edgeFinset.card : ℝ) ≤ (d : ℝ) * v := by
    dsimp [v]
    exact_mod_cast hE
  have hEC := mul_le_mul_of_nonneg_right hEreal hC
  have hlog := raw_log_lower (boxGraph d n) hp hp1
  have hupper : Real.log (fkZ (boxGraph d n) (fsc_logistic t) 2) ≤ -b * n := by
    have h := (le_div_iff₀ hn0).mp (hb n hnN)
    linarith
  have hupper' : Real.log (fkZ (boxGraph d n) (fsc_logistic t) 2) ≤ |b| * v :=
    hupper.trans ((mul_le_mul_of_nonneg_right (neg_le_abs b) hn0.le).trans
      (mul_le_mul_of_nonneg_left hnv (abs_nonneg b)))
  change _ - _ * C ≤ _ at hlog
  nlinarith

private lemma raw_box_corrected_not_bdd (d : ℕ) (hd : 1 ≤ d) (t : ℝ)
    (c : ℕ → ℝ) (hc : Tendsto (fun n => c n / n) atTop (𝓝 0)) :
    ¬ BddBelow (Set.range fun n =>
      (-Real.log (fkZ (boxGraph d n) (fsc_logistic t) 2) + c n) / n) := by
  rintro ⟨b, hb⟩
  have h := (tendsto_order.1 hc).2 1 (by norm_num)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
  apply raw_box_no_eventual_lower d hd t
  refine ⟨b - 1, N, fun n hn => ?_⟩
  have hupper := hN n hn
  have hlower := hb (Set.mem_range_self n)
  rw [add_div] at hlower
  linarith

private lemma zero_dim_edges (n : ℕ) : (boxGraph 0 n).edgeFinset.card = 0 := by
  let : Subsingleton (boxVerts 0 n) := ⟨Fintype.card_le_one_iff.mp (by
    rw [ecz_boxVerts_card]
    simp)⟩
  have hempty : (boxGraph 0 n).edgeFinset = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : a = b := Subsingleton.elim a b
      subst b
      simp at he
  simp [hempty]

-- The exact former near-subadditive box assumptions, without a replacement public predicate.
private lemma no_box_interface_data (d : ℕ) (t : ℝ) :
    ¬ ∃ (c : ℕ → ℝ) (κ : ℝ),
      Subadditive (fun n => -Real.log (fkZ (boxGraph d n) (fsc_logistic t) 2) + c n) ∧
      BddBelow (Set.range fun n =>
        (-Real.log (fkZ (boxGraph d n) (fsc_logistic t) 2) + c n) / n) ∧
      Tendsto (fun n => c n / n) atTop (𝓝 0) ∧ κ ≠ 0 ∧
      Tendsto (fun n => ((boxGraph d n).edgeFinset.card : ℝ) / n) atTop (𝓝 κ) := by
  rintro ⟨c, κ, hsub, hbdd, hc, hκ, he⟩
  by_cases hd : d = 0
  · subst d
    have he0 : Tendsto
        (fun n => ((boxGraph 0 n).edgeFinset.card : ℝ) / n) atTop (𝓝 0) := by
      simp only [zero_dim_edges, Nat.cast_zero, zero_div]
      exact tendsto_const_nhds
    exact hκ (tendsto_nhds_unique he he0)
  · exact raw_box_corrected_not_bdd d (by omega) t c hc hbdd

-- The exact former uniform box-split assumptions, for every dimension and tilt at q=2.
example (d : ℕ) (t : ℝ) :
    ¬ ∃ (C κ : ℝ), 0 ≤ C ∧ κ ≠ 0 ∧
      (∀ m n, -Real.log (fkZ (boxGraph d (m + n)) (fsc_logistic t) 2) ≤
        -Real.log (fkZ (boxGraph d m) (fsc_logistic t) 2) +
        -Real.log (fkZ (boxGraph d n) (fsc_logistic t) 2) + C) ∧
      BddBelow (Set.range fun n =>
        (-Real.log (fkZ (boxGraph d n) (fsc_logistic t) 2) + C) / n) ∧
      Tendsto (fun n => ((boxGraph d n).edgeFinset.card : ℝ) / n) atTop (𝓝 κ) := by
  rintro ⟨C, κ, hC, hκ, hglue, hbdd, he⟩
  apply no_box_interface_data d t
  refine ⟨fun _ => C, κ, fis_subadditive_of_bounded hC hglue, hbdd, ?_, hκ, he⟩
  simpa using (tendsto_const_nhds (x := C)).div_atTop tendsto_natCast_atTop_atTop

private abbrev leftVertex : SimpleGraph (Fin 1) := ⊥
private abbrev crossingEdge : SimpleGraph (Fin 1 ⊕ Fin 1) := ⊤

private lemma crossing_interface : fis_CrossInterface leftVertex leftVertex crossingEdge := by
  refine ⟨le_top, ?_, ?_⟩
  · intro a b h
    have hab : a = b := Subsingleton.elim a b
    subst b
    simp at h
  · intro a b h
    have hab : a = b := Subsingleton.elim a b
    subst b
    simp at h

example : (fis_interface leftVertex leftVertex crossingEdge).card = 1 := by decide

example : (1 - (1 / 2 : ℝ)) ^ (fis_interface leftVertex leftVertex crossingEdge).card *
    (fkZ leftVertex (1 / 2) 2 * fkZ leftVertex (1 / 2) 2) ≤
      fkZ crossingEdge (1 / 2) 2 :=
  fis_fkZ_interface_ge crossing_interface (by norm_num) (by norm_num) (by norm_num)

-- A nonzero scalar sequence with a nonzero, sublinear correction.
example : ∃ h : Subadditive (fun n : ℕ => (n : ℝ) + 1),
    Tendsto (fun n : ℕ => (n : ℝ) / n) atTop (𝓝 h.lim) := by
  have hs : Subadditive (fun n : ℕ => (n : ℝ) + 1) := by
    intro m n
    push_cast
    linarith
  refine ⟨hs, bfd_tendsto_div_of_nearSubadditive (fun n => (n : ℝ)) (fun _ => 1) hs ?_ ?_⟩
  · refine ⟨0, ?_⟩
    rintro x ⟨n, rfl⟩
    positivity
  · simpa using (tendsto_const_nhds (x := (1 : ℝ))).div_atTop tendsto_natCast_atTop_atTop

run_cmd do
  for name in [`StatMech.FK.fis_gluingBound_of_crossSplit, `StatMech.FK.fis_UniformBoxSplit,
      `StatMech.FK.fis_boxInterfaceData_of_split, `StatMech.FK.fis_interfaceData_of_bounded,
      `StatMech.FK.bfd_FKInterfaceData] do
    if (← Lean.getEnv).contains name then
      throwError "Retired box-Fekete API is still present: {name}"

end PhyslibExtTest.StatisticalMechanics.RandomCluster.FKInterfaceSubadd
