/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingFreeStateCoordinateSymmetry

open MeasureTheory

namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}



def isingSignNormalize (mask x : Site d) : Site d :=
  fun a => if mask a < 0 then -x a else x a

@[simp] theorem isingSignNormalize_involutive
    (mask x : Site d) :
    isingSignNormalize mask (isingSignNormalize mask x) = x := by
  funext a
  by_cases ha : mask a < 0 <;> simp [isingSignNormalize, ha]

def isingSignNormalizeEquiv (mask : Site d) : Site d ≃ Site d where
  toFun := isingSignNormalize mask
  invFun := isingSignNormalize mask
  left_inv := isingSignNormalize_involutive mask
  right_inv := isingSignNormalize_involutive mask

theorem hypercubicLattice_adj_signNormalize
    (mask x y : Site d) :
    (hypercubicLattice d).Adj x y ↔
      (hypercubicLattice d).Adj
        (isingSignNormalize mask x) (isingSignNormalize mask y) := by
  change (∑ a, (x a - y a).natAbs) = 1 ↔
    (∑ a, (isingSignNormalize mask x a -
      isingSignNormalize mask y a).natAbs) = 1
  have hsum :
      (∑ a, (isingSignNormalize mask x a -
        isingSignNormalize mask y a).natAbs) =
        ∑ a, (x a - y a).natAbs := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : mask a < 0
    · simp only [isingSignNormalize, if_pos ha]
      rw [show -x a - -y a = -(x a - y a) by ring, Int.natAbs_neg]
    · simp [isingSignNormalize, ha]
  rw [hsum]

theorem mem_boxFinset_signNormalize_iff
    (mask : Site d) (n : Nat) (x : Site d) :
    x ∈ boxFinset d n ↔
      isingSignNormalize mask x ∈ boxFinset d n := by
  simp only [mem_boxFinset, mem_box]
  constructor <;> intro hx a
  · by_cases ha : mask a < 0
    · simpa [isingSignNormalize, ha] using hx a
    · simpa [isingSignNormalize, ha] using hx a
  · have h := hx a
    by_cases ha : mask a < 0
    · simpa [isingSignNormalize, ha] using h
    · simpa [isingSignNormalize, ha] using h

def isingAbsSite (x : Site d) : Site d := fun a => |x a|

@[simp] theorem isingAbsSite_nonneg (x : Site d) (a : Fin d) :
    0 <= isingAbsSite x a := abs_nonneg _

theorem isingSignNormalize_self (x : Site d) :
    isingSignNormalize x x = isingAbsSite x := by
  funext a
  by_cases ha : x a < 0
  · simp [isingSignNormalize, isingAbsSite, ha, abs_of_neg ha]
  · simp [isingSignNormalize, isingAbsSite, ha,
      abs_of_nonneg (le_of_not_gt ha)]

theorem currentContinuityFreeTwoPoint_absSite
    (beta : Real) (hbeta : 0 <= beta) (x : Site d) :
    currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (isingAbsSite x) =
      currentContinuityFreeTwoPoint d beta (Percolation.origin d) x := by
  have h := integral_freeState_spinProd_boxAutomorphism
    (isingSignNormalizeEquiv x)
    (hypercubicLattice_adj_signNormalize x)
    (mem_boxFinset_signNormalize_iff x)
    beta hbeta ({Percolation.origin d, x} : Finset (Site d))
  have ho : isingSignNormalize x (Percolation.origin d) =
      Percolation.origin d := by
    funext a
    by_cases ha : x a < 0 <;>
      simp [isingSignNormalize, Percolation.origin, ha]
  simp [isingSignNormalizeEquiv] at h
  rw [ho, isingSignNormalize_self] at h
  simpa [currentContinuityFreeTwoPoint] using h



def isingMergeFinset
    (i : Fin d) (S : Finset (Fin d)) (x : Site d) : Site d :=
  fun a => if a = i then x i + ∑ j ∈ S, x j
    else if a ∈ S then 0 else x a

theorem isingMergeFinset_empty (i : Fin d) (x : Site d) :
    isingMergeFinset i ∅ x = x := by
  funext a
  by_cases hai : a = i
  · subst a
    simp [isingMergeFinset]
  · simp [isingMergeFinset, hai]

theorem isingMergeCoordinates_mergeFinset
    (i j : Fin d) (S : Finset (Fin d))
    (hij : i ≠ j) (hiS : i ∉ S) (hjS : j ∉ S) (x : Site d) :
    isingMergeCoordinates i j (isingMergeFinset i S x) =
      isingMergeFinset i (insert j S) x := by
  funext a
  by_cases hai : a = i
  · subst a
    simp [isingMergeCoordinates, isingMergeFinset, hij, Ne.symm hij,
      hiS, hjS]
    ring
  · by_cases haj : a = j
    · subst a
      simp [isingMergeCoordinates, isingMergeFinset, hai, hiS, hjS]
    · by_cases haS : a ∈ S
      · simp [isingMergeCoordinates, isingMergeFinset, hai, haj, haS]
      · simp [isingMergeCoordinates, isingMergeFinset, hai, haj, haS]

theorem isingMergeFinset_accumulator_pos
    (i : Fin d) (S : Finset (Fin d)) (x : Site d)
    (hi : 0 < x i) (hS : ∀ j ∈ S, 0 <= x j) :
    0 < isingMergeFinset i S x i := by
  rw [isingMergeFinset]
  simp only [if_pos]
  have hsum : 0 <= ∑ j ∈ S, x j :=
    Finset.sum_nonneg fun j hj => hS j hj
  linarith

theorem currentContinuityFreeTwoPoint_mergeFinset_le
    (i : Fin d) (S : Finset (Fin d)) (hiS : i ∉ S)
    (beta : Real) (hbeta : 0 <= beta)
    (x : Site d) (hi : 0 < x i)
    (hS : ∀ j ∈ S, 0 <= x j) :
    currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (isingMergeFinset i S x) <=
      currentContinuityFreeTwoPoint d beta (Percolation.origin d) x := by
  induction S using Finset.induction_on with
  | empty =>
      rw [isingMergeFinset_empty]
  | @insert j S hjS ih =>
      have hij : i ≠ j := by
        intro h
        subst j
        exact hiS (by simp)
      have hiS' : i ∉ S := by
        intro h
        exact hiS (Finset.mem_insert_of_mem h)
      have hj : 0 <= x j := hS j (by simp)
      have hS' : ∀ a ∈ S, 0 <= x a := by
        intro a ha
        exact hS a (Finset.mem_insert_of_mem ha)
      let y := isingMergeFinset i S x
      have hyi : 0 < y i :=
        isingMergeFinset_accumulator_pos i S x hi hS'
      have hyj : 0 <= y j := by
        dsimp [y]
        simp [isingMergeFinset, Ne.symm hij, hjS, hj]
      have hstep := currentContinuityFreeTwoPoint_mergeCoordinates_le
        i j hij beta hbeta y hyi hyj
      rw [isingMergeCoordinates_mergeFinset i j S hij hiS' hjS x] at hstep
      exact hstep.trans (ih hiS' hS')

theorem isingMergeFinset_erase_eq_single
    (i : Fin d) (x : Site d) :
    isingMergeFinset i (Finset.univ.erase i) x =
      Pi.single i (∑ j, x j) := by
  funext a
  by_cases hai : a = i
  · subst a
    rw [isingMergeFinset]
    simp only [if_pos, Pi.single_eq_same]
    have hsum := Finset.sum_erase_add Finset.univ x (Finset.mem_univ i)
    simp only [Finset.sum_filter] at hsum ⊢
    linarith
  · rw [isingMergeFinset]
    simp [hai]



theorem currentContinuityFreeTwoPoint_axisSum_le_of_nonneg
    (i : Fin d) (beta : Real) (hbeta : 0 <= beta)
    (x : Site d) (hi : 0 < x i) (hx : ∀ j, 0 <= x j) :
    currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (Pi.single i (∑ j, x j)) <=
      currentContinuityFreeTwoPoint d beta (Percolation.origin d) x := by
  have hmerge := currentContinuityFreeTwoPoint_mergeFinset_le
    i (Finset.univ.erase i) (by simp)
    beta hbeta x hi (by intro j hj; exact hx j)
  rwa [isingMergeFinset_erase_eq_single] at hmerge



theorem currentContinuityFreeTwoPoint_l1Axis_le
    (i : Fin d) (beta : Real) (hbeta : 0 <= beta)
    (x : Site d) (hi : x i ≠ 0) :
    currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (Pi.single i ((∑ j, (x j).natAbs : Nat) : Int)) <=
      currentContinuityFreeTwoPoint d beta (Percolation.origin d) x := by
  have hiabs : 0 < isingAbsSite x i := by
    rw [isingAbsSite, ← Int.natCast_natAbs]
    exact_mod_cast Int.natAbs_pos.mpr hi
  have hmerge := currentContinuityFreeTwoPoint_axisSum_le_of_nonneg
    i beta hbeta (isingAbsSite x) hiabs (isingAbsSite_nonneg x)
  have hsum : (∑ j, isingAbsSite x j) =
      ((∑ j, (x j).natAbs : Nat) : Int) := by
    simp only [isingAbsSite, ← Int.natCast_natAbs, Nat.cast_sum]
  rw [hsum] at hmerge
  exact hmerge.trans_eq (currentContinuityFreeTwoPoint_absSite beta hbeta x)






theorem currentContinuityFreeTwoPoint_axis_add_two_mul_le
    (hd : 2 <= d) (i : Fin d)
    (beta : Real) (hbeta : 0 <= beta)
    (p : Nat) (hp : 0 < p) (t : Nat) :
    currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (Pi.single i (((p + 2 * t : Nat) : Int))) <=
      currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (Pi.single i (p : Int)) := by
  by_cases ht : t = 0
  · subst t
    simp
  · let i0 : Fin d := ⟨0, by omega⟩
    let i1 : Fin d := ⟨1, by omega⟩
    let j : Fin d := if i = i0 then i1 else i0
    have hij : i ≠ j := by
      dsimp [j]
      split_ifs with hi
      · subst i
        intro h
        have := congrArg Fin.val h
        simp [i0, i1] at this
      · exact hi
    let b : Site d := Pi.single i (p : Int)
    let c : Int := (p + t : Nat)
    let z : Site d := isingDiagonalReflect i j c b
    have hzform : z = Pi.single i ((p + t : Nat) : Int) +
        Pi.single j (-(t : Int)) := by
      funext a
      by_cases hai : a = i
      · subst a
        simp [z, b, c, hij, Ne.symm hij]
      · by_cases haj : a = j
        · subst a
          simp [z, b, c, hij, Ne.symm hij]
        · rw [show z a = b a by
              exact isingDiagonalReflect_apply_of_ne i j a hai haj c b]
          simp [b, hai, haj]
    have hzi : z i ≠ 0 := by
      rw [hzform]
      simp [hij]
      omega
    have hzsum : (∑ a, (z a).natAbs) = p + 2 * t := by
      rw [hzform]
      classical
      have hterm (a : Fin d) :
          (((Pi.single i ((p + t : Nat) : Int) : Site d) +
            (Pi.single j (-(t : Int)) : Site d)) a).natAbs =
            if a = i then p + t else if a = j then t else 0 := by
        by_cases hai : a = i
        · subst a
          simp [hij, Ne.symm hij]
          rw [← Nat.cast_add, Int.natAbs_natCast]
        · by_cases haj : a = j
          · subst a
            simp [Pi.single_apply, hai]
          · simp [Pi.single_apply, hai, haj]
      simp_rw [hterm]
      let f : Fin d → Nat := fun a =>
        if a = i then p + t else if a = j then t else 0
      change (∑ a, f a) = p + 2 * t
      rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)]
      have hjmem : j ∈ Finset.univ.erase i := by
        simp [Ne.symm hij]
      rw [← Finset.sum_erase_add (Finset.univ.erase i) f hjmem]
      have hzero : ∑ a ∈ (Finset.univ.erase i).erase j, f a = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        obtain ⟨haj, ha⟩ := Finset.mem_erase.mp ha
        have hai := (Finset.mem_erase.mp ha).1
        simp [f, hai, haj]
      rw [hzero]
      simp [f, hij, Ne.symm hij]
      omega
    have hl1 := currentContinuityFreeTwoPoint_l1Axis_le
      i beta hbeta z hzi
    rw [hzsum] at hl1
    have hreflect :
        currentContinuityFreeTwoPoint d beta (Percolation.origin d) z <=
          currentContinuityFreeTwoPoint d beta (Percolation.origin d) b := by
      dsimp [z]
      apply currentContinuityFreeTwoPoint_diagonalReflect_le
        i j hij c beta hbeta (Percolation.origin d) b
      · simp [Percolation.origin, c]
        omega
      · simp [b, c, hij]
        omega
      · intro h
        have hcoord := congrFun h i
        simp [Percolation.origin, b] at hcoord
        omega
      · intro h
        have hcoord := congrFun h i
        simp [Percolation.origin, b, c, hij] at hcoord
        omega
    exact hl1.trans (by simpa [b] using hreflect)

end StatMech.FrontierA
