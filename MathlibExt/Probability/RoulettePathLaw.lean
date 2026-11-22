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

private theorem listPathWeight_ofFn {S : Type*} [DecidableEq S] (q : S → ℝ)
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

end RussianRoulette

end
public section
