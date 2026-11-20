/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.GeneralUmlaufsatz
import Code.Onsager.KWPhaseLoops
import Code.Onsager.KWLoopWeight










namespace StatMech.Onsager

open Matrix BigOperators
open StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind
  StatMech.Onsager.GeneralUmlaufsatz


def ons_reduceSite (L : ℕ) (p : ℤ × ℤ) : ZMod L × ZMod L :=
  ((p.1 : ZMod L), (p.2 : ZMod L))



def ons_liftDir {L n : ℕ} [NeZero n] (v : Fin n → ons_Dart L) : Fin n → Fin 4 :=
  fun k => (v (-k)).2


def ons_liftSite {L n : ℕ} [NeZero n]
    (v : Fin n → ons_Dart L) : Fin n → ZMod L × ZMod L :=
  fun k => (v (-k)).1

theorem ons_stepOf_eq_exponents (mu : Fin 4) :
    stepOf mu = (ons_dirExponentX mu, ons_dirExponentY mu) := by
  fin_cases mu <;> rfl

theorem ons_reduceSite_add_step (L : ℕ) (p : ℤ × ℤ) (mu : Fin 4) :
    ons_reduceSite L (p + stepOf mu) =
      ons_dirStep L mu (ons_reduceSite L p) := by
  fin_cases mu <;> ext <;>
    simp [ons_reduceSite, stepOf, ons_dirStep, sub_eq_add_neg]

theorem ons_liftSite_succ {L n : ℕ} [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (k : Fin n) :
    ons_liftSite v (k + 1) =
      ons_dirStep L (ons_liftDir v k) (ons_liftSite v k) := by
  have h := hvalid (-(k + 1))
  simpa [ons_liftSite, ons_liftDir, neg_add_rev] using h

theorem ons_liftDir_sum_step {L n : ℕ} [NeZero n]
    (v : Fin n → ons_Dart L) :
    ∑ k, stepOf (ons_liftDir v k) =
      ((∑ k, ons_dirExponentX (v k).2),
        ∑ k, ons_dirExponentY (v k).2) := by
  calc
    (∑ k, stepOf (ons_liftDir v k)) =
        ∑ k, (ons_dirExponentX (ons_liftDir v k),
          ons_dirExponentY (ons_liftDir v k)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact ons_stepOf_eq_exponents (ons_liftDir v k)
    _ = ((∑ k, ons_dirExponentX (ons_liftDir v k)),
          ∑ k, ons_dirExponentY (ons_liftDir v k)) := by
      apply Prod.ext
      · simp only [Prod.fst_sum]
      · simp only [Prod.snd_sum]
    _ = ((∑ k, ons_dirExponentX (v k).2),
          ∑ k, ons_dirExponentY (v k).2) := by
      congr 1
      · exact Equiv.sum_comp (Equiv.neg (Fin n))
          (fun k => ons_dirExponentX (v k).2)
      · exact Equiv.sum_comp (Equiv.neg (Fin n))
          (fun k => ons_dirExponentY (v k).2)



theorem ons_pos_succ_cast {m : ℕ} (d : Fin (m + 1) → Fin 4) (i : Fin m) :
    pos d i.succ = pos d i.castSucc + stepOf (d i.castSucc) := by
  have hfilter : (Finset.univ.filter (· < i.succ) : Finset (Fin (m + 1))) =
      insert i.castSucc (Finset.univ.filter (· < i.castSucc)) := by
    apply Finset.ext
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hj
      rw [Fin.lt_def] at hj
      simp only [Fin.val_succ] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
      · exact Or.inr (Fin.lt_def.mpr hlt)
      · exact Or.inl (Fin.ext heq)
    · rintro (rfl | hj)
      · exact Fin.castSucc_lt_succ
      · exact hj.trans Fin.castSucc_lt_succ
  have hnotmem : i.castSucc ∉
      (Finset.univ.filter (· < i.castSucc) : Finset (Fin (m + 1))) := by
    simp
  rw [pos, pos, hfilter, Finset.sum_insert hnotmem, add_comm]

theorem ons_liftSite_eq_reduce_pos {L n : ℕ} [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (k : Fin n) :
    ons_liftSite v k =
      ((ons_reduceSite L (pos (ons_liftDir v) k)).1 + (ons_liftSite v 0).1,
        (ons_reduceSite L (pos (ons_liftDir v) k)).2 + (ons_liftSite v 0).2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  refine Fin.induction ?_ (fun i ih => ?_) k
  · simp [ons_liftSite, pos_zero, ons_reduceSite]
  · have hisucc : i.succ = i.castSucc + 1 := by
      apply Fin.ext
      simp
    rw [hisucc]
    rw [ons_liftSite_succ v hvalid i.castSucc, ih]
    rw [← hisucc, ons_pos_succ_cast (ons_liftDir v) i,
      ons_reduceSite_add_step]
    exact ons_dirStep_shift L (ons_liftDir v i.castSucc)
      (ons_liftSite v 0) (ons_reduceSite L (pos (ons_liftDir v) i.castSucc))

theorem ons_liftDir_pos_injective {L n : ℕ} [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k => (v k).1)) :
    Function.Injective (pos (ons_liftDir v)) := by
  intro i j hij
  have hi := ons_liftSite_eq_reduce_pos v hvalid i
  have hj := ons_liftSite_eq_reduce_pos v hvalid j
  rw [hij] at hi
  have hs : ons_liftSite v i = ons_liftSite v j := hi.trans hj.symm
  have hneg : -i = -j := hsite hs
  exact neg_injective hneg




theorem ons_liftDir_reduce_pos_injective {L n : ℕ} [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k => (v k).1))
    {i j : Fin n}
    (hij : ons_reduceSite L (pos (ons_liftDir v) i) =
      ons_reduceSite L (pos (ons_liftDir v) j)) :
    i = j := by
  have hi := ons_liftSite_eq_reduce_pos v hvalid i
  have hj := ons_liftSite_eq_reduce_pos v hvalid j
  rw [hij] at hi
  have hs : ons_liftSite v i = ons_liftSite v j := hi.trans hj.symm
  exact neg_injective (hsite hs)

theorem ons_liftDir_no_period_translate {L n : ℕ} [NeZero L] [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k => (v k).1))
    {i j : Fin n} {a b : ℤ}
    (hij : pos (ons_liftDir v) i =
      pos (ons_liftDir v) j + ((L : ℤ) * a, (L : ℤ) * b)) :
    i = j ∧ a = 0 ∧ b = 0 := by
  have hreduce : ons_reduceSite L (pos (ons_liftDir v) i) =
      ons_reduceSite L (pos (ons_liftDir v) j) := by
    rw [hij]
    ext <;> simp [ons_reduceSite]
  have heq := ons_liftDir_reduce_pos_injective v hvalid hsite hreduce
  subst j
  have hLa : (L : ℤ) * a = 0 := by
    have h := congrArg Prod.fst hij
    simp only [Prod.fst_add] at h
    omega
  have hLb : (L : ℤ) * b = 0 := by
    have h := congrArg Prod.snd hij
    simp only [Prod.snd_add] at h
    omega
  have hL : (L : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne L)
  exact ⟨rfl, (mul_eq_zero.mp hLa).resolve_left hL,
    (mul_eq_zero.mp hLb).resolve_left hL⟩

theorem ons_liftDir_nonUturn {L n : ℕ} [NeZero n]
    (v : Fin n → ons_Dart L)
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2) :
    ∀ k, ons_liftDir v (k + 1) ≠ ons_liftDir v k + 2 := by
  intro k
  simpa [ons_liftDir, neg_add_rev] using hnu (-(k + 1))

theorem ons_liftDir_turnProduct {L n : ℕ} [NeZero n]
    (omega : ℂ) (v : Fin n → ons_Dart L) :
    (∏ k, ons_turnW omega (v (k + 1)).2 (v k).2) =
      ∏ k, ons_turnW omega (ons_liftDir v k) (ons_liftDir v (k + 1)) := by
  let e : Equiv.Perm (Fin n) :=
    (Equiv.neg (Fin n)).trans (Equiv.addRight (-1 : Fin n))
  simpa [e, ons_liftDir, neg_add_rev, add_assoc, add_comm] using
    (Equiv.prod_comp e
      (fun k => ons_turnW omega (v (k + 1)).2 (v k).2)).symm



theorem ons_contractible_turnProduct_eq_neg_one {L n : ℕ} [NeZero n]
    (omega : ℂ) (homega : omega ≠ 0) (hI : omega ^ 2 = Complex.I)
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k => (v k).1))
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
    (hx : ∑ k, ons_dirExponentX (v k).2 = 0)
    (hy : ∑ k, ons_dirExponentY (v k).2 = 0)
    (hn : 3 ≤ n) :
    ∏ k, ons_turnW omega (v (k + 1)).2 (v k).2 = -1 := by
  have hclosed : ∑ k, stepOf (ons_liftDir v k) = 0 := by
    rw [ons_liftDir_sum_step, hx, hy]
    exact Prod.ext (by simp) (by simp)
  rw [ons_liftDir_turnProduct omega v]
  exact turnWeightProduct_eq_neg_one omega homega hI (ons_liftDir v)
    hclosed (ons_liftDir_pos_injective v hvalid hsite) hn
    (ons_liftDir_nonUturn v hnu)



theorem ons_contractible_loopWeight {L n : ℕ} [NeZero L] [NeZero n]
    (x omega : ℂ) (homega : omega ≠ 0) (hI : omega ^ 2 = Complex.I)
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k => (v k).1))
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
    (hx : ∑ k, ons_dirExponentX (v k).2 = 0)
    (hy : ∑ k, ons_dirExponentY (v k).2 = 0)
    (hn : 3 ≤ n) :
    ons_loopWeight (ons_KWmat L x omega) v = -x ^ n := by
  rw [ons_loopWeight_KW_eq x omega v hvalid,
    ons_contractible_turnProduct_eq_neg_one omega homega hI v hvalid
      hsite hnu hx hy hn]
  ring



theorem ons_contractible_loopWeight_phase {L n : ℕ} [NeZero L] [NeZero n]
    (x omega u w : ℂ) (homega : omega ≠ 0) (hI : omega ^ 2 = Complex.I)
    (hu : u ≠ 0) (hw : w ≠ 0) (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k => (v k).1))
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
    (hx : ∑ k, ons_dirExponentX (v k).2 = 0)
    (hy : ∑ k, ons_dirExponentY (v k).2 = 0)
    (hn : 3 ≤ n) :
    ons_loopWeight (ons_KWmatPhase L x omega u w) v = -x ^ n := by
  rw [ons_loopWeight_KWmatPhase_zpow x omega u w hu hw v, hx, hy]
  simp only [zpow_zero, one_mul]
  exact ons_contractible_loopWeight x omega homega hI v hvalid hsite hnu hx hy hn

end StatMech.Onsager
