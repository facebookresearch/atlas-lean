/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.OSSS.AdaptiveCausalRootFlip

open scoped BigOperators

namespace StatMech.OSSS.AdaptiveCausalKernel

open Coding Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]



theorem flipCrossTripleProb_right_coord_marginal_extendDecisionTreeTriple
    (mu : ConfigSpace E → ℝ) (hpos : ∀ omega, 0 < mu omega)
    (F : Finset E) (driver left rightSeed : ConfigSpace E) (z : E)
    (t : ℕ) (T : DecisionTree E) (known : ConfigSpace E) (R : Finset E)
    (hR : R = Finset.univ \ F) :
    baseSum F rightSeed (fun right => Lindeberg.coord z right *
      flipCrossTripleProb mu F driver left right z
        (extendDecisionTreeTriple (some t) T known R)) =
      Lindeberg.cExp mu F (Lindeberg.coord z) rightSeed *
        condMass mu F left left *
          flipBaseProb mu F driver z
            (extendDecisionTreeTriple (some t) T known R) := by
  induction T generalizing t F driver rightSeed known R with
  | leaf b => simp [extendDecisionTreeTriple, baseSum]
  | node q opened closed iho ihc =>
      rw [extendDecisionTreeTriple]
      by_cases hqR : q ∈ R
      · rw [dif_pos hqR]
        have hqF : q ∉ F := by
          intro hqF
          have : q ∈ Finset.univ \ F := by rw [← hR]; exact hqR
          exact (Finset.mem_sdiff.mp this).2 hqF
        have hchild : R.erase q = Finset.univ \ insert q F := by
          rw [hR]
          ext x
          simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
            true_and, Finset.mem_insert]
          tauto
        cases t with
        | zero =>
            by_cases hzq : z = q
            · subst z
              simp only [flipCrossTripleProb, if_true, flipBaseProb]
              simpa using
                baseSum_coord_mul_crossTripleProb_right_rootFlip_eq_cExp_mul_condMass
                  mu hpos F driver left rightSeed q hqR
                (extendDecisionTreeTriple none closed
                  (Function.update known q false) (R.erase q))
                (extendDecisionTreeTriple none opened
                  (Function.update known q true) (R.erase q)) hR
            · simp [flipCrossTripleProb, flipBaseProb, hzq, baseSum]
        | succ t =>
            by_cases hzq : z = q
            · simp [flipCrossTripleProb, flipBaseProb, hzq, baseSum]
            · rw [baseSum_split F rightSeed (fun right =>
                Lindeberg.coord z right *
                  flipCrossTripleProb mu F driver left right z
                    (.node q hqR .before
                      (extendDecisionTreeTriple (some t) closed
                        (Function.update known q false) (R.erase q))
                      (extendDecisionTreeTriple (some t) opened
                        (Function.update known q true) (R.erase q)))) q hqF]
              have hbranch (b : Bool) :
                  baseSum (insert q F) (Function.update rightSeed q b)
                    (fun right => Lindeberg.coord z right *
                      flipCrossTripleProb mu F driver left right z
                        (.node q hqR .before
                          (extendDecisionTreeTriple (some t) closed
                            (Function.update known q false) (R.erase q))
                          (extendDecisionTreeTriple (some t) opened
                            (Function.update known q true) (R.erase q)))) =
                    bitWeight (condProbClosed mu F rightSeed q) b *
                      (bitWeight (condProbClosed mu F driver q) false *
                        bitWeight (condProbClosed mu F left q) (left q) *
                        baseSum (insert q F) (Function.update rightSeed q b)
                          (fun right => Lindeberg.coord z right *
                            flipCrossTripleProb mu (insert q F)
                              (Function.update driver q false) left right z
                              (extendDecisionTreeTriple (some t) closed
                                (Function.update known q false) (R.erase q))) +
                       bitWeight (condProbClosed mu F driver q) true *
                        bitWeight (condProbClosed mu F left q) (left q) *
                        baseSum (insert q F) (Function.update rightSeed q b)
                          (fun right => Lindeberg.coord z right *
                            flipCrossTripleProb mu (insert q F)
                              (Function.update driver q true) left right z
                              (extendDecisionTreeTriple (some t) opened
                                (Function.update known q true) (R.erase q)))) := by
                unfold baseSum
                rw [mul_add]
                simp_rw [Finset.mul_sum]
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro right _
                by_cases hA : Agree (insert q F) (Function.update rightSeed q b) right
                · have hbit : right q = b := by
                    have h := hA q (Finset.mem_insert_self q F)
                    simpa using h
                  have hag : Agree F rightSeed right := by
                    intro x hx
                    have hxq : x ≠ q := fun hxq => hqF (hxq ▸ hx)
                    have h := hA x (Finset.mem_insert_of_mem hx)
                    rw [Function.update_of_ne hxq] at h
                    exact h
                  have hr : condProbClosed mu F right q =
                      condProbClosed mu F rightSeed q :=
                    condProbClosed_congr mu F right rightSeed q
                      (fun x hx => hag x hx)
                  simp only [hA, if_true]
                  rw [flipCrossTripleProb, hr, hbit]
                  simp [crossTripleWeight, hzq, mul_add, mul_assoc]
                  ring
                · simp [hA]
              rw [hbranch false, hbranch true]
              rw [ihc (insert q F) (Function.update driver q false)
                (Function.update rightSeed q false) t (Function.update known q false)
                (R.erase q) hchild]
              rw [iho (insert q F) (Function.update driver q true)
                (Function.update rightSeed q false) t (Function.update known q true)
                (R.erase q) hchild]
              rw [ihc (insert q F) (Function.update driver q false)
                (Function.update rightSeed q true) t (Function.update known q false)
                (R.erase q) hchild]
              rw [iho (insert q F) (Function.update driver q true)
                (Function.update rightSeed q true) t (Function.update known q true)
                (R.erase q) hchild]
              have hchain := condMass_chain_step mu hpos F left q hqF
              rw [condProbBit_eq_closed_or_one_sub mu hpos F left q] at hchain
              have hcoordMean : Lindeberg.cExp mu F (Lindeberg.coord q) rightSeed =
                  1 - condProbClosed mu F rightSeed q := by
                have hopen : Lindeberg.cExp mu F (Lindeberg.coord q) rightSeed =
                    condProbOpen mu F rightSeed q := by
                  unfold Lindeberg.cExp condProbOpen Lindeberg.coord OpenAt
                  apply Finset.sum_congr rfl
                  intro ω _
                  by_cases hω : ω q <;> simp [hω]
                rw [hopen]
                have hc := GrandCoupling.condProbClosed_eq_one_sub_open mu F rightSeed q
                  (condNorm_pos hpos F rightSeed)
                linarith
              have hcExp := Lindeberg.cExp_decomp hpos F q hqF
                (Lindeberg.coord z) rightSeed
              rw [hcoordMean] at hcExp
              simp only [setOpen, setClosed] at hcExp
              simp only [flipBaseProb, hzq, if_false, bitWeight]
              by_cases hlq : left q <;>
                simp only [hlq, Bool.false_eq_true, ↓reduceIte] at hchain ⊢ <;>
                rw [hchain, hcExp] <;> ring
      · rw [dif_neg hqR]
        by_cases hkq : known q
        · simp only [hkq, if_true]
          exact iho F driver rightSeed t known R hR
        · simp only [hkq, Bool.false_eq_true, if_false]
          exact ihc F driver rightSeed t known R hR



theorem flipCrossTripleProb_left_coord_marginal_extendDecisionTreeTriple
    (mu : ConfigSpace E → ℝ) (hpos : ∀ omega, 0 < mu omega)
    (F : Finset E) (driver leftSeed right : ConfigSpace E) (z : E)
    (t : ℕ) (T : DecisionTree E) (known : ConfigSpace E) (R : Finset E)
    (hR : R = Finset.univ \ F) :
    baseSum F leftSeed (fun left => Lindeberg.coord z left *
      flipCrossTripleProb mu F driver left right z
        (extendDecisionTreeTriple (some t) T known R)) =
      Lindeberg.cExp mu F (Lindeberg.coord z) leftSeed *
        condMass mu F right right *
          flipBaseProb mu F driver z
            (extendDecisionTreeTriple (some t) T known R) := by
  induction T generalizing t F driver leftSeed known R with
  | leaf b => simp [extendDecisionTreeTriple, baseSum]
  | node q opened closed iho ihc =>
      rw [extendDecisionTreeTriple]
      by_cases hqR : q ∈ R
      · rw [dif_pos hqR]
        have hqF : q ∉ F := by
          intro hqF
          have : q ∈ Finset.univ \ F := by rw [← hR]; exact hqR
          exact (Finset.mem_sdiff.mp this).2 hqF
        have hchild : R.erase q = Finset.univ \ insert q F := by
          rw [hR]
          ext x
          simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
            true_and, Finset.mem_insert]
          tauto
        cases t with
        | zero =>
            by_cases hzq : z = q
            · subst z
              simp only [flipCrossTripleProb, if_true, flipBaseProb]
              simpa using
                baseSum_coord_mul_crossTripleProb_left_rootFlip_eq_cExp_mul_condMass
                  mu hpos F driver right leftSeed q hqR
                (extendDecisionTreeTriple none closed
                  (Function.update known q false) (R.erase q))
                (extendDecisionTreeTriple none opened
                  (Function.update known q true) (R.erase q)) hR
            · simp [flipCrossTripleProb, flipBaseProb, hzq, baseSum]
        | succ t =>
            by_cases hzq : z = q
            · simp [flipCrossTripleProb, flipBaseProb, hzq, baseSum]
            · rw [baseSum_split F leftSeed (fun left =>
                Lindeberg.coord z left *
                  flipCrossTripleProb mu F driver left right z
                    (.node q hqR .before
                      (extendDecisionTreeTriple (some t) closed
                        (Function.update known q false) (R.erase q))
                      (extendDecisionTreeTriple (some t) opened
                        (Function.update known q true) (R.erase q)))) q hqF]
              have hbranch (b : Bool) :
                  baseSum (insert q F) (Function.update leftSeed q b)
                    (fun left => Lindeberg.coord z left *
                      flipCrossTripleProb mu F driver left right z
                        (.node q hqR .before
                          (extendDecisionTreeTriple (some t) closed
                            (Function.update known q false) (R.erase q))
                          (extendDecisionTreeTriple (some t) opened
                            (Function.update known q true) (R.erase q)))) =
                    bitWeight (condProbClosed mu F leftSeed q) b *
                      (bitWeight (condProbClosed mu F driver q) false *
                        bitWeight (condProbClosed mu F right q) (right q) *
                        baseSum (insert q F) (Function.update leftSeed q b)
                          (fun left => Lindeberg.coord z left *
                            flipCrossTripleProb mu (insert q F)
                              (Function.update driver q false) left right z
                              (extendDecisionTreeTriple (some t) closed
                                (Function.update known q false) (R.erase q))) +
                       bitWeight (condProbClosed mu F driver q) true *
                        bitWeight (condProbClosed mu F right q) (right q) *
                        baseSum (insert q F) (Function.update leftSeed q b)
                          (fun left => Lindeberg.coord z left *
                            flipCrossTripleProb mu (insert q F)
                              (Function.update driver q true) left right z
                              (extendDecisionTreeTriple (some t) opened
                                (Function.update known q true) (R.erase q)))) := by
                unfold baseSum
                rw [mul_add]
                simp_rw [Finset.mul_sum]
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro left _
                by_cases hA : Agree (insert q F) (Function.update leftSeed q b) left
                · have hbit : left q = b := by
                    have h := hA q (Finset.mem_insert_self q F)
                    simpa using h
                  have hag : Agree F leftSeed left := by
                    intro x hx
                    have hxq : x ≠ q := fun hxq => hqF (hxq ▸ hx)
                    have h := hA x (Finset.mem_insert_of_mem hx)
                    rw [Function.update_of_ne hxq] at h
                    exact h
                  have hl : condProbClosed mu F left q =
                      condProbClosed mu F leftSeed q :=
                    condProbClosed_congr mu F left leftSeed q
                      (fun x hx => hag x hx)
                  simp only [hA, if_true]
                  rw [flipCrossTripleProb, hl, hbit]
                  simp [crossTripleWeight, hzq, mul_add, mul_assoc]
                  ring
                · simp [hA]
              rw [hbranch false, hbranch true]
              rw [ihc (insert q F) (Function.update driver q false)
                (Function.update leftSeed q false) t (Function.update known q false)
                (R.erase q) hchild]
              rw [iho (insert q F) (Function.update driver q true)
                (Function.update leftSeed q false) t (Function.update known q true)
                (R.erase q) hchild]
              rw [ihc (insert q F) (Function.update driver q false)
                (Function.update leftSeed q true) t (Function.update known q false)
                (R.erase q) hchild]
              rw [iho (insert q F) (Function.update driver q true)
                (Function.update leftSeed q true) t (Function.update known q true)
                (R.erase q) hchild]
              have hchain := condMass_chain_step mu hpos F right q hqF
              rw [condProbBit_eq_closed_or_one_sub mu hpos F right q] at hchain
              have hcoordMean : Lindeberg.cExp mu F (Lindeberg.coord q) leftSeed =
                  1 - condProbClosed mu F leftSeed q := by
                rw [cExp_coord_eq_condProbBit_true]
                have hc := GrandCoupling.condProbClosed_eq_one_sub_open mu F leftSeed q
                  (condNorm_pos hpos F leftSeed)
                rw [GrandCoupling.condProbBit_true_eq_open]
                linarith
              have hcExp := Lindeberg.cExp_decomp hpos F q hqF
                (Lindeberg.coord z) leftSeed
              rw [hcoordMean] at hcExp
              simp only [setOpen, setClosed] at hcExp
              simp only [flipBaseProb, hzq, if_false, bitWeight]
              by_cases hrq : right q <;>
                simp only [hrq, Bool.false_eq_true, ↓reduceIte] at hchain ⊢ <;>
                rw [hchain, hcExp] <;> ring
      · rw [dif_neg hqR]
        by_cases hkq : known q
        · simp only [hkq, if_true]
          exact iho F driver leftSeed t known R hR
        · simp only [hkq, Bool.false_eq_true, if_false]
          exact ihc F driver leftSeed t known R hR

theorem sum_coord_mul_flipCrossTripleProb_right_extendDecisionTreeTriple
    (mu : ConfigSpace E → ℝ) (hpos : ∀ omega, 0 < mu omega)
    (hmu : ∑ omega, mu omega = 1) (driver left rightSeed : ConfigSpace E)
    (z : E) (t : ℕ) (T : DecisionTree E) (known : ConfigSpace E) :
    (∑ right, Lindeberg.coord z right *
      flipCrossTripleProb mu ∅ driver left right z
        (extendDecisionTreeTriple (some t) T known Finset.univ)) =
      Lindeberg.mean mu (Lindeberg.coord z) * mu left *
        flipBaseProb mu ∅ driver z
          (extendDecisionTreeTriple (some t) T known Finset.univ) := by
  have h := flipCrossTripleProb_right_coord_marginal_extendDecisionTreeTriple
    mu hpos ∅ driver left rightSeed z t T known Finset.univ (by simp)
  rw [Lindeberg.cExp_empty hmu (Lindeberg.coord z) rightSeed] at h
  simpa [baseSum, Agree, condMass, condNorm_empty, hmu] using h

theorem sum_coord_mul_flipCrossTripleProb_left_extendDecisionTreeTriple
    (mu : ConfigSpace E → ℝ) (hpos : ∀ omega, 0 < mu omega)
    (hmu : ∑ omega, mu omega = 1) (driver leftSeed right : ConfigSpace E)
    (z : E) (t : ℕ) (T : DecisionTree E) (known : ConfigSpace E) :
    (∑ left, Lindeberg.coord z left *
      flipCrossTripleProb mu ∅ driver left right z
        (extendDecisionTreeTriple (some t) T known Finset.univ)) =
      Lindeberg.mean mu (Lindeberg.coord z) * mu right *
        flipBaseProb mu ∅ driver z
          (extendDecisionTreeTriple (some t) T known Finset.univ) := by
  have h := flipCrossTripleProb_left_coord_marginal_extendDecisionTreeTriple
    mu hpos ∅ driver leftSeed right z t T known Finset.univ (by simp)
  rw [Lindeberg.cExp_empty hmu (Lindeberg.coord z) leftSeed] at h
  simpa [baseSum, Agree, condMass, condNorm_empty, hmu] using h



theorem flipCrossTripleProb_structured_orientations
    (mu : ConfigSpace E → ℝ) (hpos : ∀ omega, 0 < mu omega)
    (hmu : ∑ omega, mu omega = 1) (T : DecisionTree E)
    (seed : ConfigSpace E) (t : ℕ) (z : E) :
    let S := extendDecisionTreeTriple (some t) T seed
      (Finset.univ : Finset E)
    (∑ left, ∑ right,
      T.evalR left * Lindeberg.coord z right *
        flipCrossTripleProb mu ∅ seed left right z S) =
        Lindeberg.mean mu T.evalR *
          Lindeberg.mean mu (Lindeberg.coord z) *
            flipBaseProb mu ∅ seed z S
    ∧
    (∑ left, ∑ right,
      T.evalR right * Lindeberg.coord z left *
        flipCrossTripleProb mu ∅ seed left right z S) =
        Lindeberg.mean mu T.evalR *
          Lindeberg.mean mu (Lindeberg.coord z) *
            flipBaseProb mu ∅ seed z S := by
  dsimp only
  let S := extendDecisionTreeTriple (some t) T seed (Finset.univ : Finset E)
  constructor
  · calc
      _ = ∑ left, T.evalR left *
          (∑ right, Lindeberg.coord z right *
            flipCrossTripleProb mu ∅ seed left right z S) := by
        apply Finset.sum_congr rfl
        intro left _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro right _
        ring
      _ = ∑ left, T.evalR left *
          (Lindeberg.mean mu (Lindeberg.coord z) * mu left *
            flipBaseProb mu ∅ seed z S) := by
        apply Finset.sum_congr rfl
        intro left _
        rw [sum_coord_mul_flipCrossTripleProb_right_extendDecisionTreeTriple
          mu hpos hmu seed left seed z t T seed]
      _ = _ := by
        unfold Lindeberg.mean
        dsimp only [S]
        conv_rhs => rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro left _
        ring
  · rw [Finset.sum_comm]
    calc
      _ = ∑ right, T.evalR right *
          (∑ left, Lindeberg.coord z left *
            flipCrossTripleProb mu ∅ seed left right z S) := by
        apply Finset.sum_congr rfl
        intro right _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro left _
        ring
      _ = ∑ right, T.evalR right *
          (Lindeberg.mean mu (Lindeberg.coord z) * mu right *
            flipBaseProb mu ∅ seed z S) := by
        apply Finset.sum_congr rfl
        intro right _
        rw [sum_coord_mul_flipCrossTripleProb_left_extendDecisionTreeTriple
          mu hpos hmu seed seed right z t T seed]
      _ = _ := by
        unfold Lindeberg.mean
        dsimp only [S]
        conv_rhs => rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro right _
        ring

end StatMech.OSSS.AdaptiveCausalKernel
