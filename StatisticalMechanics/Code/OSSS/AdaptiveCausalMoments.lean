/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.OSSS.AdaptiveCausalKernel

open scoped BigOperators

namespace StatMech
namespace OSSS
namespace AdaptiveCausalKernel

open Coding Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]




theorem flipTripleProb_left_marginal_extendDecisionTreeTriple
    (mu : ConfigSpace E → Real) (hpos : ∀ omega, 0 < mu omega)
    (F : Finset E) (driver leftSeed right : ConfigSpace E) (z : E)
    (t : Nat) (T : DecisionTree E) (known : ConfigSpace E) (R : Finset E)
    (hR : R = Finset.univ \ F) :
    baseSum F leftSeed (fun left =>
      flipTripleProb mu F driver left right z
        (extendDecisionTreeTriple (some t) T known R)) =
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
              simp only [flipTripleProb, if_pos rfl, if_true, flipBaseProb, one_mul]
              rw [baseSum_tripleProb_left_eq_targetProb mu hpos F driver right leftSeed
                (.node q hqR .flip
                  (extendDecisionTreeTriple none closed
                    (Function.update known q false) (R.erase q))
                  (extendDecisionTreeTriple none opened
                    (Function.update known q true) (R.erase q))) hR]
              rw [targetProb_eq_condMass_core mu hpos F driver right]
              · ring
              · exact hR
            · simp [flipTripleProb, flipBaseProb, hzq, baseSum]
        | succ t =>
            by_cases hzq : z = q
            · simp [flipTripleProb, flipBaseProb, hzq, baseSum]
            · rw [baseSum_split F leftSeed (fun left =>
                flipTripleProb mu F driver left right z
                  (.node q hqR .before
                    (extendDecisionTreeTriple (some t) closed
                      (Function.update known q false) (R.erase q))
                    (extendDecisionTreeTriple (some t) opened
                      (Function.update known q true) (R.erase q)))) q hqF]
              have hbranch (b : Bool) :
                  baseSum (insert q F) (Function.update leftSeed q b)
                    (fun left => flipTripleProb mu F driver left right z
                      (.node q hqR .before
                        (extendDecisionTreeTriple (some t) closed
                          (Function.update known q false) (R.erase q))
                        (extendDecisionTreeTriple (some t) opened
                          (Function.update known q true) (R.erase q)))) =
                    overlapWeight (condProbClosed mu F leftSeed q)
                        (condProbClosed mu F right q) b (right q) *
                      (bitWeight (condProbClosed mu F driver q) false *
                        baseSum (insert q F) (Function.update leftSeed q b)
                          (fun left => flipTripleProb mu (insert q F)
                            (Function.update driver q false) left right z
                            (extendDecisionTreeTriple (some t) closed
                              (Function.update known q false) (R.erase q))) +
                       bitWeight (condProbClosed mu F driver q) true *
                        baseSum (insert q F) (Function.update leftSeed q b)
                          (fun left => flipTripleProb mu (insert q F)
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
                    condProbClosed_congr mu F left leftSeed q (fun x hx => hag x hx)
                  simp only [hA, if_true]
                  rw [flipTripleProb, hl, hbit]
                  simp [tripleWeight, hzq, mul_add, mul_assoc]
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
              simp only [flipBaseProb, hzq, if_false, bitWeight]
              rw [← add_mul]
              rw [overlapWeight_sum_base]
              by_cases hrq : right q <;> simp [hrq, bitWeight] at hchain ⊢ <;>
                rw [hchain] <;> ring
      · rw [dif_neg hqR]
        by_cases hkq : known q
        · simp only [hkq, if_true]
          exact iho F driver leftSeed t known R hR
        · simp only [hkq, Bool.false_eq_true, if_false]
          exact ihc F driver leftSeed t known R hR



theorem sum_flipTripleProb_right_extendDecisionTreeTriple
    (mu : ConfigSpace E → ℝ) (hpos : ∀ omega, 0 < mu omega)
    (hmu : ∑ omega, mu omega = 1) (driver left rightSeed : ConfigSpace E)
    (z : E) (t : ℕ) (T : DecisionTree E) (known : ConfigSpace E) :
    (∑ right, flipTripleProb mu ∅ driver left right z
      (extendDecisionTreeTriple (some t) T known Finset.univ)) =
      mu left * flipBaseProb mu ∅ driver z
        (extendDecisionTreeTriple (some t) T known Finset.univ) := by
  have h := flipTripleProb_right_marginal_extendDecisionTreeTriple
    mu hpos ∅ driver left rightSeed z t T known Finset.univ (by simp)
  simpa [baseSum, Agree, condMass, condNorm_empty, hmu] using h



theorem sum_flipTripleProb_left_extendDecisionTreeTriple
    (mu : ConfigSpace E → ℝ) (hpos : ∀ omega, 0 < mu omega)
    (hmu : ∑ omega, mu omega = 1) (driver leftSeed right : ConfigSpace E)
    (z : E) (t : ℕ) (T : DecisionTree E) (known : ConfigSpace E) :
    (∑ left, flipTripleProb mu ∅ driver left right z
      (extendDecisionTreeTriple (some t) T known Finset.univ)) =
      mu right * flipBaseProb mu ∅ driver z
        (extendDecisionTreeTriple (some t) T known Finset.univ) := by
  have h := flipTripleProb_left_marginal_extendDecisionTreeTriple
    mu hpos ∅ driver leftSeed right z t T known Finset.univ (by simp)
  simpa [baseSum, Agree, condMass, condNorm_empty, hmu] using h



theorem flipCrossTripleProb_right_marginal_extendDecisionTreeTriple
    (mu : ConfigSpace E → ℝ) (hpos : ∀ omega, 0 < mu omega)
    (F : Finset E) (driver left rightSeed : ConfigSpace E) (z : E)
    (t : ℕ) (T : DecisionTree E) (known : ConfigSpace E) (R : Finset E)
    (hR : R = Finset.univ \ F) :
    baseSum F rightSeed (fun right =>
      flipCrossTripleProb mu F driver left right z
        (extendDecisionTreeTriple (some t) T known R)) =
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
              simp only [flipCrossTripleProb, if_pos rfl, if_true, flipBaseProb,
                one_mul]
              rw [baseSum_crossTripleProb_right_eq_targetProb mu hpos F driver left
                rightSeed
                (.node q hqR .flip
                  (extendDecisionTreeTriple none closed
                    (Function.update known q false) (R.erase q))
                  (extendDecisionTreeTriple none opened
                    (Function.update known q true) (R.erase q))) hR]
              rw [targetProb_eq_condMass_core mu hpos F driver left]
              · ring
              · exact hR
            · simp [flipCrossTripleProb, flipBaseProb, hzq, baseSum]
        | succ t =>
            by_cases hzq : z = q
            · simp [flipCrossTripleProb, flipBaseProb, hzq, baseSum]
            · rw [baseSum_split F rightSeed (fun right =>
                flipCrossTripleProb mu F driver left right z
                  (.node q hqR .before
                    (extendDecisionTreeTriple (some t) closed
                      (Function.update known q false) (R.erase q))
                    (extendDecisionTreeTriple (some t) opened
                      (Function.update known q true) (R.erase q)))) q hqF]
              have hbranch (b : Bool) :
                  baseSum (insert q F) (Function.update rightSeed q b)
                    (fun right => flipCrossTripleProb mu F driver left right z
                      (.node q hqR .before
                        (extendDecisionTreeTriple (some t) closed
                          (Function.update known q false) (R.erase q))
                        (extendDecisionTreeTriple (some t) opened
                          (Function.update known q true) (R.erase q)))) =
                    bitWeight (condProbClosed mu F rightSeed q) b *
                      (bitWeight (condProbClosed mu F driver q) false *
                        bitWeight (condProbClosed mu F left q) (left q) *
                        baseSum (insert q F) (Function.update rightSeed q b)
                          (fun right => flipCrossTripleProb mu (insert q F)
                            (Function.update driver q false) left right z
                            (extendDecisionTreeTriple (some t) closed
                              (Function.update known q false) (R.erase q))) +
                       bitWeight (condProbClosed mu F driver q) true *
                        bitWeight (condProbClosed mu F left q) (left q) *
                        baseSum (insert q F) (Function.update rightSeed q b)
                          (fun right => flipCrossTripleProb mu (insert q F)
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
              simp only [flipBaseProb, hzq, if_false, bitWeight]
              rw [← add_mul]
              by_cases hlq : left q <;> simp [hlq, bitWeight] at hchain ⊢ <;>
                rw [hchain] <;> ring
      · rw [dif_neg hqR]
        by_cases hkq : known q
        · simp only [hkq, if_true]
          exact iho F driver rightSeed t known R hR
        · simp only [hkq, Bool.false_eq_true, if_false]
          exact ihc F driver rightSeed t known R hR

theorem flipCrossTripleProb_left_marginal_extendDecisionTreeTriple
    (mu : ConfigSpace E → ℝ) (hpos : ∀ omega, 0 < mu omega)
    (F : Finset E) (driver leftSeed right : ConfigSpace E) (z : E)
    (t : ℕ) (T : DecisionTree E) (known : ConfigSpace E) (R : Finset E)
    (hR : R = Finset.univ \ F) :
    baseSum F leftSeed (fun left =>
      flipCrossTripleProb mu F driver left right z
        (extendDecisionTreeTriple (some t) T known R)) =
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
              simp only [flipCrossTripleProb, if_pos rfl, if_true, flipBaseProb,
                one_mul]
              rw [baseSum_crossTripleProb_left_eq_targetProb mu hpos F driver right
                leftSeed
                (.node q hqR .flip
                  (extendDecisionTreeTriple none closed
                    (Function.update known q false) (R.erase q))
                  (extendDecisionTreeTriple none opened
                    (Function.update known q true) (R.erase q))) hR]
              rw [targetProb_eq_condMass_core mu hpos F driver right]
              · ring
              · exact hR
            · simp [flipCrossTripleProb, flipBaseProb, hzq, baseSum]
        | succ t =>
            by_cases hzq : z = q
            · simp [flipCrossTripleProb, flipBaseProb, hzq, baseSum]
            · rw [baseSum_split F leftSeed (fun left =>
                flipCrossTripleProb mu F driver left right z
                  (.node q hqR .before
                    (extendDecisionTreeTriple (some t) closed
                      (Function.update known q false) (R.erase q))
                    (extendDecisionTreeTriple (some t) opened
                      (Function.update known q true) (R.erase q)))) q hqF]
              have hbranch (b : Bool) :
                  baseSum (insert q F) (Function.update leftSeed q b)
                    (fun left => flipCrossTripleProb mu F driver left right z
                      (.node q hqR .before
                        (extendDecisionTreeTriple (some t) closed
                          (Function.update known q false) (R.erase q))
                        (extendDecisionTreeTriple (some t) opened
                          (Function.update known q true) (R.erase q)))) =
                    bitWeight (condProbClosed mu F leftSeed q) b *
                      (bitWeight (condProbClosed mu F driver q) false *
                        bitWeight (condProbClosed mu F right q) (right q) *
                        baseSum (insert q F) (Function.update leftSeed q b)
                          (fun left => flipCrossTripleProb mu (insert q F)
                            (Function.update driver q false) left right z
                            (extendDecisionTreeTriple (some t) closed
                              (Function.update known q false) (R.erase q))) +
                       bitWeight (condProbClosed mu F driver q) true *
                        bitWeight (condProbClosed mu F right q) (right q) *
                        baseSum (insert q F) (Function.update leftSeed q b)
                          (fun left => flipCrossTripleProb mu (insert q F)
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
              simp only [flipBaseProb, hzq, if_false, bitWeight]
              rw [← add_mul]
              by_cases hrq : right q <;> simp [hrq, bitWeight] at hchain ⊢ <;>
                rw [hchain] <;> ring
      · rw [dif_neg hqR]
        by_cases hkq : known q
        · simp only [hkq, if_true]
          exact iho F driver leftSeed t known R hR
        · simp only [hkq, Bool.false_eq_true, if_false]
          exact ihc F driver leftSeed t known R hR

theorem sum_flipCrossTripleProb_right_extendDecisionTreeTriple
    (mu : ConfigSpace E → ℝ) (hpos : ∀ omega, 0 < mu omega)
    (hmu : ∑ omega, mu omega = 1) (driver left rightSeed : ConfigSpace E)
    (z : E) (t : ℕ) (T : DecisionTree E) (known : ConfigSpace E) :
    (∑ right, flipCrossTripleProb mu ∅ driver left right z
      (extendDecisionTreeTriple (some t) T known Finset.univ)) =
      mu left * flipBaseProb mu ∅ driver z
        (extendDecisionTreeTriple (some t) T known Finset.univ) := by
  have h := flipCrossTripleProb_right_marginal_extendDecisionTreeTriple
    mu hpos ∅ driver left rightSeed z t T known Finset.univ (by simp)
  simpa [baseSum, Agree, condMass, condNorm_empty, hmu] using h

theorem sum_flipCrossTripleProb_left_extendDecisionTreeTriple
    (mu : ConfigSpace E → ℝ) (hpos : ∀ omega, 0 < mu omega)
    (hmu : ∑ omega, mu omega = 1) (driver leftSeed right : ConfigSpace E)
    (z : E) (t : ℕ) (T : DecisionTree E) (known : ConfigSpace E) :
    (∑ left, flipCrossTripleProb mu ∅ driver left right z
      (extendDecisionTreeTriple (some t) T known Finset.univ)) =
      mu right * flipBaseProb mu ∅ driver z
        (extendDecisionTreeTriple (some t) T known Finset.univ) := by
  have h := flipCrossTripleProb_left_marginal_extendDecisionTreeTriple
    mu hpos ∅ driver leftSeed right z t T known Finset.univ (by simp)
  simpa [baseSum, Agree, condMass, condNorm_empty, hmu] using h

end AdaptiveCausalKernel
end OSSS
end StatMech
