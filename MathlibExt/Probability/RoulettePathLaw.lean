/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.RoulettePathMass
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Basic.ENNReal.BigOperators

@[expose] public section

namespace RussianRoulette

/-- Completed-path weight of a list: `q` at the final state times the product
of survival-kernel entries along the list. The empty list has weight `0`. -/
def listCompletedWeight {S : Type*} (q : S → ℝ) (Q : S → S → ℝ) : List S → ℝ
  | [] => 0
  | [x] => q x
  | x :: y :: t => Q x y * listCompletedWeight q Q (y :: t)

/-- `ENNReal` path weight of a list from start `i`: zero on the empty list and
on lists not starting at `i`. -/
noncomputable def listPathWeight {S : Type*} [DecidableEq S] (q : S → ℝ)
    (Q : S → S → ℝ) (i : S) (l : List S) : ENNReal :=
  match l with
  | [] => 0
  | x :: _ => if x = i then ENNReal.ofReal (listCompletedWeight q Q l) else 0

theorem listCompletedWeight_ofFn {S : Type*} (q : S → ℝ) (Q : S → S → ℝ)
    {n : ℕ} (x : Fin (n + 1) → S) :
    listCompletedWeight q Q (List.ofFn x) = completedWeight q Q x := by
  have key : ∀ (m : ℕ) (y : Fin (m + 1) → S),
      listCompletedWeight q Q (List.ofFn y) = completedWeight q Q y := by
    intro m
    induction m with
    | zero =>
        intro y
        have hofn : List.ofFn y = [y 0] := by
          rw [List.ofFn_succ, List.ofFn_zero]
        rw [hofn]
        change q (y 0) = completedWeight q Q y
        unfold completedWeight survivalWeight
        rw [Fin.prod_univ_zero, Fin.last_zero, mul_one]
    | succ m ih =>
        intro y
        have hcons : List.ofFn y
            = y 0 :: List.ofFn (fun k : Fin (m + 1) => y k.succ) :=
          List.ofFn_succ
        have htail : List.ofFn (fun k : Fin (m + 1) => y k.succ)
            = y (Fin.succ 0) :: List.ofFn (fun k : Fin m => y k.succ.succ) :=
          List.ofFn_succ
        rw [hcons, htail]
        simp only [listCompletedWeight]
        have hfold : (y (Fin.succ 0) :: List.ofFn (fun k : Fin m => y k.succ.succ))
            = List.ofFn (fun k : Fin (m + 1) => y k.succ) :=
          (List.ofFn_succ (f := fun k : Fin (m + 1) => y k.succ)).symm
        rw [hfold, ih]
        have hcast : ∀ k : Fin m, k.succ.castSucc = k.castSucc.succ := by
          intro k
          ext
          simp
        have hlast : (Fin.last m).succ = Fin.last (m + 1) := by
          ext
          simp
        have hprod : ∏ k : Fin (m + 1), Q (y k.castSucc) (y k.succ)
            = Q (y 0) (y (Fin.succ 0))
              * ∏ k : Fin m, Q (y k.castSucc.succ) (y k.succ.succ) := by
          have h := Fin.prod_univ_succ
            (fun k : Fin (m + 1) => Q (y k.castSucc) (y k.succ))
          simpa only [Fin.castSucc_zero, hcast] using h
        change Q (y 0) (y (Fin.succ 0))
            * (q (y (Fin.last m).succ)
              * ∏ k : Fin m, Q (y k.castSucc.succ) (y k.succ.succ))
          = q (y (Fin.last (m + 1)))
            * ∏ k : Fin (m + 1), Q (y k.castSucc) (y k.succ)
        rw [hlast, hprod]
        ring
  exact key n x

theorem listPathWeight_ofFn {S : Type*} [DecidableEq S] (q : S → ℝ)
    (Q : S → S → ℝ) (i : S) {m : ℕ} (x : Fin (m + 1) → S) :
    listPathWeight q Q i (List.ofFn x)
      = if x 0 = i then ENNReal.ofReal (completedWeight q Q x) else 0 := by
  have hcons : List.ofFn x = x 0 :: List.ofFn (fun k : Fin m => x k.succ) :=
    List.ofFn_succ
  rw [hcons]
  have hmatch :
      listPathWeight q Q i (x 0 :: List.ofFn (fun k : Fin m => x k.succ))
      = if x 0 = i then ENNReal.ofReal
        (listCompletedWeight q Q (x 0 :: List.ofFn (fun k : Fin m => x k.succ)))
        else 0 := rfl
  rw [hmatch, ← hcons, listCompletedWeight_ofFn]

theorem tsum_listPathWeight_eq {S : Type*} [Fintype S] [DecidableEq S]
    (q : S → ℝ) (Q : S → S → ℝ) (hq : ∀ a : S, 0 ≤ q a)
    (hQ : ∀ a b : S, 0 ≤ Q a b) (i : S) :
    ∑' l : List S, listPathWeight q Q i l
      = ∑' n : ℕ, ENNReal.ofReal (stoppedMass q Q i n) := by
  have h1 : ∑' l : List S, listPathWeight q Q i l
      = ∑' p : Σ m : ℕ, (Fin m → S),
        listPathWeight q Q i (List.ofFn p.2) := by
    have h := Equiv.tsum_eq List.equivSigmaTuple.symm
      (fun l : List S => listPathWeight q Q i l)
    simp only [List.equivSigmaTuple_symm_apply] at h
    exact h.symm
  have hsig : ∑' p : Σ m : ℕ, (Fin m → S),
        listPathWeight q Q i (List.ofFn p.2)
      = ∑' (m : ℕ) (x : Fin m → S), listPathWeight q Q i (List.ofFn x) :=
    ENNReal.tsum_sigma
      (fun (m : ℕ) (x : Fin m → S) => listPathWeight q Q i (List.ofFn x))
  have hF0 : (∑' x : Fin 0 → S, listPathWeight q Q i (List.ofFn x)) = 0 := by
    have hz : ∀ x : Fin 0 → S, listPathWeight q Q i (List.ofFn x) = 0 := by
      intro x
      rw [List.ofFn_zero]
      rfl
    have hfun : (fun x : Fin 0 → S => listPathWeight q Q i (List.ofFn x))
        = fun _ => 0 := funext hz
    rw [hfun]
    exact tsum_zero
  have hF : ∀ n : ℕ,
      (∑' x : Fin (n + 1) → S, listPathWeight q Q i (List.ofFn x))
        = ENNReal.ofReal (stoppedMass q Q i n) := by
    intro n
    have hnn : ∀ x ∈ (Finset.univ : Finset (Fin (n + 1) → S)),
        0 ≤ (if x 0 = i then completedWeight q Q x else 0) := by
      intro x _
      split_ifs
      · unfold completedWeight survivalWeight
        exact mul_nonneg (hq _) (Finset.prod_nonneg fun k _ => hQ _ _)
      · exact le_rfl
    rw [tsum_fintype]
    unfold stoppedMass
    rw [ENNReal.ofReal_sum_of_nonneg hnn]
    apply Finset.sum_congr rfl
    intro x _
    rw [listPathWeight_ofFn]
    split_ifs
    · rfl
    · exact ENNReal.ofReal_zero.symm
  rw [h1, hsig]
  have hshift : ∑' m : ℕ, (∑' x : Fin m → S, listPathWeight q Q i (List.ofFn x))
      = (∑' x : Fin 0 → S, listPathWeight q Q i (List.ofFn x))
        + ∑' n : ℕ, (∑' x : Fin (n + 1) → S,
          listPathWeight q Q i (List.ofFn x)) :=
    tsum_eq_zero_add' ENNReal.summable
  rw [hshift, hF0, zero_add]
  apply tsum_congr
  intro n
  exact hF n

theorem hasSum_listPathWeight {S : Type*} [Fintype S] [DecidableEq S]
    (q : S → ℝ) (Q : S → S → ℝ) (c : ℝ) (hc1 : c < 1)
    (hQ : ∀ a b : S, 0 ≤ Q a b)
    (hrow : ∀ j : S, q j + ∑ k : S, Q j k = 1)
    (hsurv : ∀ a : S, ∑ b : S, Q a b ≤ c) (i : S) :
    HasSum (listPathWeight q Q i) 1 := by
  have hc0 : 0 ≤ c := le_trans (Finset.sum_nonneg fun b _ => hQ i b) (hsurv i)
  have hq : ∀ a : S, 0 ≤ q a := fun a => by linarith [hrow a, hsurv a]
  have hnonneg : ∀ n : ℕ, 0 ≤ stoppedMass q Q i n :=
    fun n => stoppedMass_nonneg q Q hq hQ i n
  have hpart : ∀ n : ℕ, (∑ k ∈ Finset.range n,
        ENNReal.ofReal (stoppedMass q Q i k))
      = ENNReal.ofReal (∑ k ∈ Finset.range n, stoppedMass q Q i k) := by
    intro n
    exact (ENNReal.ofReal_sum_of_nonneg (fun k _ => hnonneg k)).symm
  have hcons : ∀ n : ℕ, (∑ k ∈ Finset.range n, stoppedMass q Q i k)
      = 1 - survivalMass Q i n := by
    intro n
    linarith [sum_stoppedMass_add_survival q Q hrow i n]
  have hsurv0 : Filter.Tendsto (fun n : ℕ => survivalMass Q i n) Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => survivalMass_nonneg Q hQ i n)
      (fun n => survivalMass_le_pow Q c hQ hsurv i n)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1)
  have hle : (∑' n : ℕ, ENNReal.ofReal (stoppedMass q Q i n)) ≤ 1 := by
    rw [ENNReal.tsum_eq_iSup_nat]
    apply iSup_le
    intro n
    simp only [hpart n, hcons n]
    calc ENNReal.ofReal (1 - survivalMass Q i n)
        ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (by
          linarith [survivalMass_nonneg Q hQ i n])
      _ = 1 := ENNReal.ofReal_one
  have hge : 1 ≤ ∑' n : ℕ, ENNReal.ofReal (stoppedMass q Q i n) := by
    have h1 : Filter.Tendsto (fun n : ℕ => 1 - survivalMass Q i n) Filter.atTop (nhds 1) := by
      have h : Filter.Tendsto (fun n : ℕ => 1 - survivalMass Q i n) Filter.atTop (nhds (1 - 0)) :=
        tendsto_const_nhds.sub hsurv0
      rwa [sub_zero] at h
    have hlim : Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
        ENNReal.ofReal (stoppedMass q Q i k)) Filter.atTop (nhds 1) := by
      have hfun : (fun n : ℕ => ∑ k ∈ Finset.range n,
            ENNReal.ofReal (stoppedMass q Q i k))
          = fun n => ENNReal.ofReal (1 - survivalMass Q i n) := by
        funext n
        simp only [hpart n, hcons n]
      rw [hfun]
      have h2 := (ENNReal.continuous_ofReal.tendsto 1).comp h1
      rw [ENNReal.ofReal_one] at h2
      exact h2
    apply le_of_tendsto hlim
    apply Filter.Eventually.of_forall
    intro n
    rw [ENNReal.tsum_eq_iSup_nat]
    exact le_iSup (fun m => ∑ a ∈ Finset.range m, ENNReal.ofReal (stoppedMass q Q i a)) n
  have htsum : (∑' l : List S, listPathWeight q Q i l) = 1 := by
    rw [tsum_listPathWeight_eq q Q hq hQ i]
    exact le_antisymm hle hge
  exact ENNReal.summable.hasSum_iff.mpr htsum

/-- The normalized completed-path law from start `i`, as a PMF on lists. -/
noncomputable def pathPMF {S : Type*} [Fintype S] [DecidableEq S] (q : S → ℝ)
    (Q : S → S → ℝ) (c : ℝ) (hc1 : c < 1)
    (hQ : ∀ a b : S, 0 ≤ Q a b)
    (hrow : ∀ j : S, q j + ∑ k : S, Q j k = 1)
    (hsurv : ∀ a : S, ∑ b : S, Q a b ≤ c) (i : S) : PMF (List S) :=
  ⟨listPathWeight q Q i, by
    simpa using hasSum_listPathWeight q Q c hc1 hQ hrow hsurv i⟩

theorem pathPMF_apply {S : Type*} [Fintype S] [DecidableEq S] (q : S → ℝ)
    (Q : S → S → ℝ) (c : ℝ) (hc1 : c < 1)
    (hQ : ∀ a b : S, 0 ≤ Q a b)
    (hrow : ∀ j : S, q j + ∑ k : S, Q j k = 1)
    (hsurv : ∀ a : S, ∑ b : S, Q a b ≤ c) (i : S) (l : List S) :
    pathPMF q Q c hc1 hQ hrow hsurv i l = listPathWeight q Q i l := by
  rfl


theorem tsum_listPathWeight_length_gt {S : Type*} [Fintype S] [DecidableEq S]
    (q : S → ℝ) (Q : S → S → ℝ) (c : ℝ) (hc1 : c < 1)
    (hQ : ∀ a b : S, 0 ≤ Q a b)
    (hrow : ∀ j : S, q j + ∑ k : S, Q j k = 1)
    (hsurv : ∀ a : S, ∑ b : S, Q a b ≤ c) (i : S) (n : ℕ) :
    ∑' l : List S, (if n < l.length then listPathWeight q Q i l else 0)
      = ENNReal.ofReal (survivalMass Q i n) := by
  have hq : ∀ a : S, 0 ≤ q a := fun a => by linarith [hrow a, hsurv a]
  have htot : (∑' l : List S, listPathWeight q Q i l) = 1 :=
    (hasSum_listPathWeight q Q c hc1 hQ hrow hsurv i).tsum_eq
  have hsplit : (∑' l : List S,
      (if n < l.length then listPathWeight q Q i l else 0))
      + (∑' l : List S,
        (if n < l.length then (0 : ENNReal)
          else listPathWeight q Q i l))
      = ∑' l : List S, listPathWeight q Q i l := by
    rw [← ENNReal.tsum_add]
    apply tsum_congr
    intro l
    by_cases h : n < l.length <;> simp [h]
  have hF0 : (∑' x : Fin 0 → S,
      listPathWeight q Q i (List.ofFn x)) = 0 := by
    have hz : ∀ x : Fin 0 → S,
        listPathWeight q Q i (List.ofFn x) = 0 := by
      intro x
      rw [List.ofFn_zero]
      rfl
    have hfun : (fun x : Fin 0 → S =>
        listPathWeight q Q i (List.ofFn x)) = fun _ => 0 := funext hz
    rw [hfun]
    exact tsum_zero
  have hF : ∀ n : ℕ,
      (∑' x : Fin (n + 1) → S, listPathWeight q Q i (List.ofFn x))
        = ENNReal.ofReal (stoppedMass q Q i n) := by
    intro n
    have hnn : ∀ x ∈ (Finset.univ : Finset (Fin (n + 1) → S)),
        0 ≤ (if x 0 = i then completedWeight q Q x else 0) := by
      intro x _
      split_ifs
      · unfold completedWeight survivalWeight
        exact mul_nonneg (hq _) (Finset.prod_nonneg fun n _ => hQ _ _)
      · exact le_rfl
    rw [tsum_fintype]
    unfold stoppedMass
    rw [ENNReal.ofReal_sum_of_nonneg hnn]
    apply Finset.sum_congr rfl
    intro x _
    rw [listPathWeight_ofFn]
    split_ifs
    · rfl
    · exact ENNReal.ofReal_zero.symm
  have hhead : (∑' l : List S,
      (if n < l.length then (0 : ENNReal)
        else listPathWeight q Q i l))
      = ENNReal.ofReal (1 - survivalMass Q i n) := by
    have h1 : (∑' l : List S,
        (if n < l.length then (0 : ENNReal)
          else listPathWeight q Q i l))
        = ∑' p : Σ m : ℕ, (Fin m → S),
          (if n < (List.ofFn p.2).length then (0 : ENNReal)
            else listPathWeight q Q i (List.ofFn p.2)) := by
      have h := Equiv.tsum_eq List.equivSigmaTuple.symm
        (fun l : List S =>
          (if n < l.length then (0 : ENNReal)
            else listPathWeight q Q i l))
      simp only [List.equivSigmaTuple_symm_apply] at h
      exact h.symm
    rw [h1]
    simp only [List.length_ofFn]
    have hsig : (∑' p : Σ m : ℕ, (Fin m → S),
          (if n < p.1 then (0 : ENNReal)
            else listPathWeight q Q i (List.ofFn p.2)))
        = ∑' (m : ℕ) (x : Fin m → S),
          (if n < m then (0 : ENNReal)
            else listPathWeight q Q i (List.ofFn x)) :=
      ENNReal.tsum_sigma
        (fun (m : ℕ) (x : Fin m → S) =>
          (if n < m then (0 : ENNReal)
            else listPathWeight q Q i (List.ofFn x)))
    rw [hsig]
    have hinner : ∀ m : ℕ, (∑' x : Fin m → S,
        (if n < m then (0 : ENNReal)
          else listPathWeight q Q i (List.ofFn x)))
        = (if n < m then 0
          else (∑' x : Fin m → S,
            listPathWeight q Q i (List.ofFn x))) := by
      intro m
      by_cases h : n < m <;> simp [h]
    have hhead2 : (∑' (m : ℕ) (x : Fin m → S),
        (if n < m then (0 : ENNReal)
          else listPathWeight q Q i (List.ofFn x)))
        = ∑' m : ℕ, (if n < m then 0
          else (∑' x : Fin m → S,
            listPathWeight q Q i (List.ofFn x))) := by
      apply tsum_congr
      intro m
      exact hinner m
    rw [hhead2]
    have hts : (∑' m : ℕ, (if n < m then (0 : ENNReal)
        else (∑' x : Fin m → S, listPathWeight q Q i (List.ofFn x))))
        = ∑ m ∈ Finset.range (n + 1), (if n < m then (0 : ENNReal)
          else (∑' x : Fin m → S,
            listPathWeight q Q i (List.ofFn x))) := by
      apply tsum_eq_sum
      intro m hm
      simp only [Finset.mem_range, not_lt] at hm
      rw [ite_eq_left (by omega : n < m)]
    rw [hts]
    have hifneg : ∀ m ∈ Finset.range (n + 1),
        (if n < m then (0 : ENNReal)
          else (∑' x : Fin m → S,
            listPathWeight q Q i (List.ofFn x)))
        = (∑' x : Fin m → S,
          listPathWeight q Q i (List.ofFn x)) := by
      intro m hm
      simp only [Finset.mem_range] at hm
      rw [ite_eq_right (by omega : ¬ n < m)]
    rw [Finset.sum_congr rfl hifneg]
    simp only [Finset.sum_range_succ', hF0, add_zero]
    have hFcongr : ∀ j ∈ Finset.range n,
        (∑' x : Fin (j + 1) → S, listPathWeight q Q i (List.ofFn x))
        = ENNReal.ofReal (stoppedMass q Q i j) := fun j _ => hF j
    rw [Finset.sum_congr rfl hFcongr]
    have hnonneg : ∀ j ∈ Finset.range n, 0 ≤ stoppedMass q Q i j :=
      fun j _ => stoppedMass_nonneg q Q hq hQ i j
    rw [← ENNReal.ofReal_sum_of_nonneg hnonneg]
    have hcons : (∑ j ∈ Finset.range n, stoppedMass q Q i j)
        = 1 - survivalMass Q i n := by
      linarith [sum_stoppedMass_add_survival q Q hrow i n]
    rw [hcons]
  have hs0 : 0 ≤ survivalMass Q i n := survivalMass_nonneg Q hQ i n
  have hs1 : survivalMass Q i n ≤ 1 := by
    have hcons := sum_stoppedMass_add_survival q Q hrow i n
    have hstop : 0 ≤ ∑ j ∈ Finset.range n, stoppedMass q Q i j :=
      Finset.sum_nonneg (fun j _ => stoppedMass_nonneg q Q hq hQ i j)
    linarith
  have hunit : ENNReal.ofReal (1 - survivalMass Q i n)
      + ENNReal.ofReal (survivalMass Q i n) = 1 := by
    rw [← ENNReal.ofReal_add (by linarith) hs0, sub_add_cancel,
      ENNReal.ofReal_one]
  rw [hhead, htot, ← hunit,
    add_comm _ (ENNReal.ofReal (1 - survivalMass Q i n))] at hsplit
  exact WithTop.add_left_cancel ENNReal.ofReal_ne_top hsplit

theorem tsum_listPathWeight_toReal_length_sub_le {S : Type*} [Fintype S]
    [DecidableEq S] (q : S → ℝ) (Q : S → S → ℝ) (c : ℝ)
    (hc1 : c < 1) (hQ : ∀ a b : S, 0 ≤ Q a b)
    (hrow : ∀ j : S, q j + ∑ k : S, Q j k = 1)
    (hsurv : ∀ a : S, ∑ b : S, Q a b ≤ c) (i : S) :
    ∑' l : List S, (listPathWeight q Q i l).toReal * ((l.length : ℝ) - 1)
      ≤ c / (1 - c) := by
  have hc0 : 0 ≤ c := le_trans (Finset.sum_nonneg fun b _ => hQ i b) (hsurv i)
  have htail : ∀ k : ℕ, (∑' l : List S,
      (if k < l.length then listPathWeight q Q i l else 0))
      = ENNReal.ofReal (survivalMass Q i k) :=
    fun k => tsum_listPathWeight_length_gt q Q c hc1 hQ hrow hsurv i k
  have hcount : ∀ l : List S,
      listPathWeight q Q i l * ((l.length - 1 : ℕ) : ENNReal)
      = ∑' n : ℕ,
        (if n < l.length - 1 then listPathWeight q Q i l else 0) := by
    intro l
    have hts : (∑' n : ℕ,
        (if n < l.length - 1 then listPathWeight q Q i l else 0))
        = ∑ n ∈ Finset.range (l.length - 1),
          (if n < l.length - 1 then listPathWeight q Q i l else 0) := by
      apply tsum_eq_sum
      intro n hn
      simp only [Finset.mem_range, not_lt] at hn
      rw [ite_eq_right (by omega : ¬ n < l.length - 1)]
    rw [hts]
    have hpos : ∀ n ∈ Finset.range (l.length - 1),
        (if n < l.length - 1 then listPathWeight q Q i l else 0)
        = listPathWeight q Q i l := by
      intro n hn
      simp only [Finset.mem_range] at hn
      rw [ite_eq_left hn]
    rw [Finset.sum_congr rfl hpos, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    exact mul_comm _ _
  have henn : (∑' l : List S,
      listPathWeight q Q i l * ((l.length - 1 : ℕ) : ENNReal))
      = ∑' n : ℕ, ENNReal.ofReal (survivalMass Q i (n + 1)) := by
    have hcond : ∀ (n : ℕ) (l : List S),
        (if n < l.length - 1 then listPathWeight q Q i l else 0)
        = (if n + 1 < l.length then listPathWeight q Q i l else 0) := by
      intro n l
      have heq : (n < l.length - 1) ↔ (n + 1 < l.length) := by omega
      simp only [heq]
    have hswap : (∑' l : List S, ∑' n : ℕ,
        (if n < l.length - 1 then listPathWeight q Q i l else 0))
        = ∑' n : ℕ, ∑' l : List S,
          (if n < l.length - 1 then listPathWeight q Q i l else 0) :=
      ENNReal.tsum_comm
    have hl : (∑' l : List S,
        listPathWeight q Q i l * ((l.length - 1 : ℕ) : ENNReal))
        = ∑' l : List S, ∑' n : ℕ,
          (if n < l.length - 1 then listPathWeight q Q i l else 0) := by
      apply tsum_congr
      intro l
      exact hcount l
    rw [hl, hswap]
    apply tsum_congr
    intro n
    have hcc : (∑' l : List S,
        (if n < l.length - 1 then listPathWeight q Q i l else 0))
        = ∑' l : List S,
          (if n + 1 < l.length then listPathWeight q Q i l else 0) := by
      apply tsum_congr
      intro l
      exact hcond n l
    rw [hcc]
    exact htail (n + 1)
  have hle : (∑' n : ℕ, ENNReal.ofReal (survivalMass Q i (n + 1)))
      ≤ ENNReal.ofReal (c / (1 - c)) := by
    have hterm : ∀ n : ℕ, ENNReal.ofReal (survivalMass Q i (n + 1))
        ≤ ENNReal.ofReal (c ^ (n + 1)) :=
      fun n => ENNReal.ofReal_le_ofReal
        (survivalMass_le_pow Q c hQ hsurv i (n + 1))
    have h1 : (∑' n : ℕ, ENNReal.ofReal (survivalMass Q i (n + 1)))
        ≤ ∑' n : ℕ, ENNReal.ofReal (c ^ (n + 1)) :=
      ENNReal.tsum_le_tsum hterm
    have h2 : (∑' n : ℕ, ENNReal.ofReal (c ^ (n + 1)))
        = ENNReal.ofReal (c / (1 - c)) := by
      have hpow : ∀ n : ℕ, ENNReal.ofReal (c ^ (n + 1))
          = ENNReal.ofReal c * ENNReal.ofReal (c ^ n) := by
        intro n
        rw [pow_succ', ENNReal.ofReal_mul hc0]
      rw [tsum_congr hpow, ENNReal.tsum_mul_left]
      have hgeom : (∑' n : ℕ, ENNReal.ofReal (c ^ n))
          = ENNReal.ofReal ((1 - c)⁻¹) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => pow_nonneg hc0 n)
          (summable_geometric_of_lt_one hc0 hc1),
          tsum_geometric_of_lt_one hc0 hc1]
      rw [hgeom, ← ENNReal.ofReal_mul hc0]
      congr 1
    exact h1.trans h2.le
  have hwfin : ∀ l : List S, listPathWeight q Q i l ≠ ⊤ := by
    intro l
    cases l with
    | nil =>
        have h0 : listPathWeight q Q i [] = 0 := rfl
        rw [h0]
        simp
    | cons x t =>
        simp only [listPathWeight]
        split_ifs with h
        · exact ENNReal.ofReal_ne_top
        · simp
  have hfin : ∀ l : List S,
      (listPathWeight q Q i l * ((l.length - 1 : ℕ) : ENNReal)) ≠ ⊤ := by
    intro l
    exact ENNReal.mul_ne_top (hwfin l) (ENNReal.natCast_ne_top _)
  have htoReal : ((∑' l : List S,
      listPathWeight q Q i l * ((l.length - 1 : ℕ) : ENNReal))).toReal
      = ∑' l : List S,
        (listPathWeight q Q i l).toReal * ((l.length : ℝ) - 1) := by
    rw [ENNReal.tsum_toReal_eq hfin]
    apply tsum_congr
    intro l
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
    by_cases hlen : l.length = 0
    · have hl : l = [] := List.length_eq_zero_iff.mp hlen
      subst hl
      have hw0 : listPathWeight q Q i [] = 0 := rfl
      rw [hw0, ENNReal.toReal_zero, zero_mul, zero_mul]
    · have h1 : 1 ≤ l.length := by omega
      have hcast : (((l.length - 1 : ℕ) : ℝ)) = (l.length : ℝ) - 1 := by
        rw [Nat.cast_sub h1, Nat.cast_one]
      rw [hcast]
  have hle2 : (∑' l : List S,
      listPathWeight q Q i l * ((l.length - 1 : ℕ) : ENNReal))
      ≤ ENNReal.ofReal (c / (1 - c)) := by
    rw [henn]
    exact hle
  have hfin2 : (∑' l : List S,
      listPathWeight q Q i l * ((l.length - 1 : ℕ) : ENNReal)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle2
  have hreal : ((∑' l : List S,
      listPathWeight q Q i l * ((l.length - 1 : ℕ) : ENNReal))).toReal
      ≤ c / (1 - c) := by
    have h := (ENNReal.toReal_le_toReal hfin2 ENNReal.ofReal_ne_top).mpr hle2
    rwa [ENNReal.toReal_ofReal
      (div_nonneg hc0 (by linarith : (0 : ℝ) ≤ 1 - c))] at h
  rwa [htoReal] at hreal

theorem tsum_listPathWeight_toReal_length_le {S : Type*} [Fintype S]
    [DecidableEq S] (q : S → ℝ) (Q : S → S → ℝ) (c : ℝ)
    (hc1 : c < 1) (hQ : ∀ a b : S, 0 ≤ Q a b)
    (hrow : ∀ j : S, q j + ∑ k : S, Q j k = 1)
    (hsurv : ∀ a : S, ∑ b : S, Q a b ≤ c) (i : S) :
    ∑' l : List S, (listPathWeight q Q i l).toReal * (l.length : ℝ)
      ≤ 1 / (1 - c) := by
  have hc0 : 0 ≤ c := le_trans (Finset.sum_nonneg fun b _ => hQ i b) (hsurv i)
  have htail : ∀ k : ℕ, (∑' l : List S,
      (if k < l.length then listPathWeight q Q i l else 0))
      = ENNReal.ofReal (survivalMass Q i k) :=
    fun k => tsum_listPathWeight_length_gt q Q c hc1 hQ hrow hsurv i k
  have hcount : ∀ l : List S, listPathWeight q Q i l * (l.length : ENNReal)
      = ∑' n : ℕ, (if n < l.length then listPathWeight q Q i l else 0) := by
    intro l
    have hts : (∑' n : ℕ,
        (if n < l.length then listPathWeight q Q i l else 0))
        = ∑ n ∈ Finset.range l.length,
          (if n < l.length then listPathWeight q Q i l else 0) := by
      apply tsum_eq_sum
      intro n hn
      simp only [Finset.mem_range, not_lt] at hn
      rw [ite_eq_right (by omega : ¬ n < l.length)]
    rw [hts]
    have hpos : ∀ n ∈ Finset.range l.length,
        (if n < l.length then listPathWeight q Q i l else 0)
        = listPathWeight q Q i l := by
      intro n hn
      simp only [Finset.mem_range] at hn
      rw [ite_eq_left hn]
    rw [Finset.sum_congr rfl hpos, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    exact mul_comm _ _
  have henn : (∑' l : List S, listPathWeight q Q i l * (l.length : ENNReal))
      = ∑' n : ℕ, ENNReal.ofReal (survivalMass Q i n) := by
    have hswap : (∑' l : List S, ∑' n : ℕ,
        (if n < l.length then listPathWeight q Q i l else 0))
        = ∑' n : ℕ, ∑' l : List S,
          (if n < l.length then listPathWeight q Q i l else 0) :=
      ENNReal.tsum_comm
    have hl : (∑' l : List S, listPathWeight q Q i l * (l.length : ENNReal))
        = ∑' l : List S, ∑' n : ℕ,
          (if n < l.length then listPathWeight q Q i l else 0) := by
      apply tsum_congr
      intro l
      exact hcount l
    rw [hl, hswap]
    apply tsum_congr
    intro n
    exact htail n
  have hle : (∑' n : ℕ, ENNReal.ofReal (survivalMass Q i n))
      ≤ ENNReal.ofReal (1 / (1 - c)) := by
    have hterm : ∀ n : ℕ, ENNReal.ofReal (survivalMass Q i n)
        ≤ ENNReal.ofReal (c ^ n) :=
      fun n => ENNReal.ofReal_le_ofReal (survivalMass_le_pow Q c hQ hsurv i n)
    have h1 : (∑' n : ℕ, ENNReal.ofReal (survivalMass Q i n))
        ≤ ∑' n : ℕ, ENNReal.ofReal (c ^ n) :=
      ENNReal.tsum_le_tsum hterm
    have h2 : (∑' n : ℕ, ENNReal.ofReal (c ^ n))
        = ENNReal.ofReal (1 / (1 - c)) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => pow_nonneg hc0 n)
        (summable_geometric_of_lt_one hc0 hc1),
        tsum_geometric_of_lt_one hc0 hc1]
      congr 1
      exact inv_eq_one_div _
    exact h1.trans h2.le
  have hwfin : ∀ l : List S, listPathWeight q Q i l ≠ ⊤ := by
    intro l
    cases l with
    | nil =>
        have h0 : listPathWeight q Q i [] = 0 := rfl
        rw [h0]
        simp
    | cons x t =>
        simp only [listPathWeight]
        split_ifs with h
        · exact ENNReal.ofReal_ne_top
        · simp
  have hfin : ∀ l : List S,
      (listPathWeight q Q i l * (l.length : ENNReal)) ≠ ⊤ := by
    intro l
    exact ENNReal.mul_ne_top (hwfin l) (ENNReal.natCast_ne_top _)
  have htoReal : ((∑' l : List S,
      listPathWeight q Q i l * (l.length : ENNReal))).toReal
      = ∑' l : List S, (listPathWeight q Q i l).toReal * (l.length : ℝ) := by
    rw [ENNReal.tsum_toReal_eq hfin]
    apply tsum_congr
    intro l
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hle2 : (∑' l : List S, listPathWeight q Q i l * (l.length : ENNReal))
      ≤ ENNReal.ofReal (1 / (1 - c)) := by
    rw [henn]
    exact hle
  have hfin2 : (∑' l : List S,
      listPathWeight q Q i l * (l.length : ENNReal)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle2
  have hreal : ((∑' l : List S,
      listPathWeight q Q i l * (l.length : ENNReal))).toReal ≤ 1 / (1 - c) := by
    have h := (ENNReal.toReal_le_toReal hfin2 ENNReal.ofReal_ne_top).mpr hle2
    rwa [ENNReal.toReal_ofReal
      (one_div_nonneg.mpr (by linarith : (0 : ℝ) ≤ 1 - c))] at h
  rwa [htoReal] at hreal

end RussianRoulette

end
public section
