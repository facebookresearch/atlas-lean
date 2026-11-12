/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.OSSS.AdaptiveCausalMoments

open scoped BigOperators

namespace StatMech
namespace OSSS
namespace AdaptiveCausalKernel

open Coding Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]

lemma cExp_coord_eq_condProbBit_true (mu : ConfigSpace E → ℝ)
    (F : Finset E) (seed : ConfigSpace E) (q : E) :
    Lindeberg.cExp mu F (Lindeberg.coord q) seed =
      condProbBit mu F seed q true := by
  rw [GrandCoupling.condProbBit_true_eq_open]
  unfold Lindeberg.cExp Lindeberg.coord condProbOpen OpenAt
  apply Finset.sum_congr rfl
  intro target _
  by_cases hq : target q
  · simp [hq]
  · simp [hq]




theorem baseSum_coord_mul_crossTripleProb_right_rootFlip
    (mu : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < mu ω)
    (F : Finset E) (base left seed : ConfigSpace E) {R : Finset E}
    (q : E) (hq : q ∈ R) (closed opened : TripleOrder (R.erase q))
    (hR : R = Finset.univ \ F) :
    baseSum F seed (fun right =>
        Lindeberg.coord q right *
          crossTripleProb mu F base left right
            (.node q hq .flip closed opened)) =
      condProbBit mu F seed q true *
        targetProb mu F base left
          (TripleOrder.leftOrder (.node q hq .flip closed opened)) := by
  have hqF : q ∉ F := by
    intro hqMem
    have : q ∈ Finset.univ \ F := by rw [← hR]; exact hq
    exact (Finset.mem_sdiff.mp this).2 hqMem
  have hchild : R.erase q = Finset.univ \ insert q F := by
    rw [hR]
    ext x
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Finset.mem_insert]
    tauto
  rw [baseSum_split F seed (fun right =>
    Lindeberg.coord q right *
      crossTripleProb mu F base left right
        (.node q hq .flip closed opened)) q hqF]
  let a := condProbClosed mu F base q
  let p := condProbClosed mu F left q
  let r := condProbClosed mu F seed q
  have hbranch (z : Bool) :
      baseSum (insert q F) (Function.update seed q z) (fun right =>
          Lindeberg.coord q right *
            crossTripleProb mu F base left right
              (.node q hq .flip closed opened)) =
        (if z then 1 else 0) *
          (crossTripleWeight .flip a p r false (left q) z *
              baseSum (insert q F) (Function.update seed q z) (fun right =>
                crossTripleProb mu (insert q F)
                  (Function.update base q false) left right closed) +
            crossTripleWeight .flip a p r true (left q) z *
              baseSum (insert q F) (Function.update seed q z) (fun right =>
                crossTripleProb mu (insert q F)
                  (Function.update base q true) left right opened)) := by
    unfold baseSum
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro right _
    by_cases hA : Agree (insert q F) (Function.update seed q z) right
    · have hbit : right q = z := by
        have h := hA q (Finset.mem_insert_self q F)
        simpa using h
      have hag : Agree F seed right := by
        intro x hx
        have hxq : x ≠ q := fun hxq => hqF (hxq ▸ hx)
        have h := hA x (Finset.mem_insert_of_mem hx)
        rw [Function.update_of_ne hxq] at h
        exact h
      have hr : condProbClosed mu F right q = r := by
        change condProbClosed mu F right q = condProbClosed mu F seed q
        exact condProbClosed_congr mu F right seed q (fun x hx => hag x hx)
      simp only [hA, if_true]
      rw [crossTripleProb, hr, hbit]
      simp [Lindeberg.coord, hbit]
      ring
    · simp [hA]
  rw [hbranch false, hbranch true]
  simp only [Bool.false_eq_true, if_false, zero_mul, zero_add, if_true, one_mul]
  rw [baseSum_crossTripleProb_right_eq_targetProb mu hpos
    (insert q F) (Function.update base q false) left
    (Function.update seed q true) closed hchild]
  rw [baseSum_crossTripleProb_right_eq_targetProb mu hpos
    (insert q F) (Function.update base q true) left
    (Function.update seed q true) opened hchild]
  have hopen : bitWeight r true = condProbBit mu F seed q true := by
    have hsum := condProbBit_true_add_false mu F seed q
      (condNorm_pos hpos F seed).ne'
    unfold r condProbClosed bitWeight
    simp only [if_true]
    linarith
  rw [TripleOrder.leftOrder, targetProb]
  simp only [crossTripleWeight, splitWeight, TripleMode.leftIndependent,
    Bool.false_eq_true, if_false]
  rw [hopen]
  ring



theorem baseSum_coord_mul_crossTripleProb_right_rootFlip_eq_cExp_mul_condMass
    (mu : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < mu ω)
    (F : Finset E) (driver left rightSeed : ConfigSpace E) {R : Finset E}
    (q : E) (hq : q ∈ R) (closed opened : TripleOrder (R.erase q))
    (hR : R = Finset.univ \ F) :
    baseSum F rightSeed (fun right =>
        Lindeberg.coord q right *
          crossTripleProb mu F driver left right
            (.node q hq .flip closed opened)) =
      Lindeberg.cExp mu F (Lindeberg.coord q) rightSeed *
        condMass mu F left left := by
  rw [baseSum_coord_mul_crossTripleProb_right_rootFlip
    mu hpos F driver left rightSeed q hq closed opened hR]
  rw [targetProb_eq_condMass_core mu hpos F driver left]
  · rw [cExp_coord_eq_condProbBit_true]
  · exact hR




theorem baseSum_coord_mul_crossTripleProb_left_rootFlip_eq_cExp_mul_condMass
    (mu : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < mu ω)
    (F : Finset E) (driver right leftSeed : ConfigSpace E) {R : Finset E}
    (q : E) (hq : q ∈ R) (closed opened : TripleOrder (R.erase q))
    (hR : R = Finset.univ \ F) :
    baseSum F leftSeed (fun left =>
        Lindeberg.coord q left *
          crossTripleProb mu F driver left right
            (.node q hq .flip closed opened)) =
      Lindeberg.cExp mu F (Lindeberg.coord q) leftSeed *
        condMass mu F right right := by
  have hqF : q ∉ F := by
    intro hqMem
    have : q ∈ Finset.univ \ F := by rw [← hR]; exact hq
    exact (Finset.mem_sdiff.mp this).2 hqMem
  have hchild : R.erase q = Finset.univ \ insert q F := by
    rw [hR]
    ext x
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Finset.mem_insert]
    tauto
  rw [baseSum_split F leftSeed (fun left =>
    Lindeberg.coord q left *
      crossTripleProb mu F driver left right
        (.node q hq .flip closed opened)) q hqF]
  let a := condProbClosed mu F driver q
  let p := condProbClosed mu F leftSeed q
  let r := condProbClosed mu F right q
  have hbranch (z : Bool) :
      baseSum (insert q F) (Function.update leftSeed q z) (fun left =>
          Lindeberg.coord q left *
            crossTripleProb mu F driver left right
              (.node q hq .flip closed opened)) =
        (if z then 1 else 0) *
          (crossTripleWeight .flip a p r false z (right q) *
              baseSum (insert q F) (Function.update leftSeed q z) (fun left =>
                crossTripleProb mu (insert q F)
                  (Function.update driver q false) left right closed) +
            crossTripleWeight .flip a p r true z (right q) *
              baseSum (insert q F) (Function.update leftSeed q z) (fun left =>
                crossTripleProb mu (insert q F)
                  (Function.update driver q true) left right opened)) := by
    unfold baseSum
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro left _
    by_cases hA : Agree (insert q F) (Function.update leftSeed q z) left
    · have hbit : left q = z := by
        have h := hA q (Finset.mem_insert_self q F)
        simpa using h
      have hag : Agree F leftSeed left := by
        intro x hx
        have hxq : x ≠ q := fun hxq => hqF (hxq ▸ hx)
        have h := hA x (Finset.mem_insert_of_mem hx)
        rw [Function.update_of_ne hxq] at h
        exact h
      have hp : condProbClosed mu F left q = p := by
        change condProbClosed mu F left q = condProbClosed mu F leftSeed q
        exact condProbClosed_congr mu F left leftSeed q (fun x hx => hag x hx)
      simp only [hA, if_true]
      rw [crossTripleProb, hp, hbit]
      simp [Lindeberg.coord, hbit]
      ring
    · simp [hA]
  rw [hbranch false, hbranch true]
  simp only [Bool.false_eq_true, if_false, zero_mul, zero_add, if_true, one_mul]
  rw [baseSum_crossTripleProb_left_eq_targetProb mu hpos
    (insert q F) (Function.update driver q false) right
    (Function.update leftSeed q true) closed hchild]
  rw [baseSum_crossTripleProb_left_eq_targetProb mu hpos
    (insert q F) (Function.update driver q true) right
    (Function.update leftSeed q true) opened hchild]
  rw [targetProb_eq_condMass_core mu hpos (insert q F)
    (Function.update driver q false) right closed.rightOrder hchild]
  rw [targetProb_eq_condMass_core mu hpos (insert q F)
    (Function.update driver q true) right opened.rightOrder hchild]
  have hopen : bitWeight p true = condProbBit mu F leftSeed q true := by
    have hsum := condProbBit_true_add_false mu F leftSeed q
      (condNorm_pos hpos F leftSeed).ne'
    unfold p condProbClosed bitWeight
    simp only [if_true]
    linarith
  have hchain := condMass_chain_step mu hpos F right q hqF
  rw [condProbBit_eq_closed_or_one_sub mu hpos F right q] at hchain
  rw [cExp_coord_eq_condProbBit_true, ← hopen]
  simp only [crossTripleWeight]
  rw [show
      overlapWeight a p false true * bitWeight r (right q) *
            condMass mu (insert q F) right right +
          overlapWeight a p true true * bitWeight r (right q) *
            condMass mu (insert q F) right right =
        (overlapWeight a p false true + overlapWeight a p true true) *
          bitWeight r (right q) * condMass mu (insert q F) right right by ring]
  rw [overlapWeight_sum_base]
  simp only [if_true]
  rw [show 1 - p = bitWeight p true by simp [bitWeight]]
  rw [hchain]
  unfold r
  cases right q <;> simp [bitWeight] <;> ring

end AdaptiveCausalKernel
end OSSS
end StatMech
