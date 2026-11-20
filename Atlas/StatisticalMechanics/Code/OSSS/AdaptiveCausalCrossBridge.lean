/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.OSSS.AdaptivePredictableOrder
import Code.OSSS.CrossMonotone
import Code.OSSS.CrossVFKG

namespace StatMech
namespace OSSS
namespace AdaptiveCausalKernel

variable {E : Type*} [Fintype E] [DecidableEq E]



lemma realizedList_extendDecisionTreeAt
    (t : ℕ) (T : DecisionTree E) (known base : ConfigSpace E)
    (R : Finset E) :
    realizedList (extendDecisionTreeAt t T known R) base =
      realizedList (extendDecisionTree T known R) base := by
  induction T generalizing t known R with
  | leaf b =>
      simp [extendDecisionTreeAt, extendDecisionTree]
  | node q opened closed iho ihc =>
      simp only [extendDecisionTreeAt, extendDecisionTree]
      by_cases hqR : q ∈ R
      · rw [dif_pos hqR, dif_pos hqR]
        simp only [realizedList]
        split <;> simp_all
      · rw [dif_neg hqR, dif_neg hqR]
        by_cases hk : known q
        · simp only [hk, if_true]
          exact iho t known R
        · simp only [hk, Bool.false_eq_true, if_false]
          exact ihc t known R



lemma realizedList_extendDecisionTreeTriple
    (phase : Option ℕ) (T : DecisionTree E) (known base : ConfigSpace E)
    (R : Finset E) :
    realizedList (extendDecisionTreeTriple phase T known R).leftOrder base =
      realizedList (extendDecisionTree T known R) base := by
  cases phase with
  | none =>
      rw [extendDecisionTreeTriple_none_leftOrder]
      exact realizedList_extendDecisionTreeAt 0 T known base R
  | some t =>
      rw [extendDecisionTreeTriple_leftOrder]
      exact realizedList_extendDecisionTreeAt t T known base R

lemma realizedEquiv_apply_eq_getElem
    (S : CausalOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (i : Fin (Fintype.card E)) :
    realizedEquiv S base i =
      (realizedList S base)[(i : ℕ)]'(by
        rw [realizedList_length]
        simpa using i.isLt) := by
  unfold realizedEquiv
  simp [List.Nodup.getEquivOfForallMemList_apply]



lemma realizedEquiv_extendDecisionTreeTriple
    (phase : Option ℕ) (T : DecisionTree E) (known base : ConfigSpace E) :
    realizedEquiv
        (extendDecisionTreeTriple phase T known (Finset.univ : Finset E)).leftOrder base =
      realizedEquiv (extendDecisionTree T known Finset.univ) base := by
  apply Equiv.ext
  intro i
  rw [realizedEquiv_apply_eq_getElem, realizedEquiv_apply_eq_getElem]
  have hl := realizedList_extendDecisionTreeTriple phase T known base Finset.univ
  have hopt := congrArg (fun l : List E => l[(i : ℕ)]?) hl
  have hleft : (i : ℕ) <
      (realizedList
        (extendDecisionTreeTriple phase T known Finset.univ).leftOrder base).length := by
    rw [realizedList_length]
    simpa using i.isLt
  have hright : (i : ℕ) <
      (realizedList (extendDecisionTree T known Finset.univ) base).length := by
    rw [realizedList_length]
    simpa using i.isLt
  change
    (realizedList
      (extendDecisionTreeTriple phase T known Finset.univ).leftOrder base)[(i : ℕ)]? =
    (realizedList (extendDecisionTree T known Finset.univ) base)[(i : ℕ)]? at hopt
  rw [List.getElem?_eq_getElem hleft, List.getElem?_eq_getElem hright] at hopt
  exact Option.some.inj hopt



lemma idxOf_flip_extendDecisionTreeTriple
    (t : ℕ) (T : DecisionTree E) (known base : ConfigSpace E)
    (R : Finset E) (e : E)
    (he : tripleModeAt (extendDecisionTreeTriple (some t) T known R) base e = .flip) :
    (realizedList
      (extendDecisionTreeTriple (some t) T known R).leftOrder base).idxOf e = t := by
  induction T generalizing t known R with
  | leaf b =>
      exact False.elim
        (tripleModeAt_beforeOfCausal_ne_flip (fixedOrder R) base e he)
  | node q opened closed iho ihc =>
      by_cases hqR : q ∈ R
      · rw [extendDecisionTreeTriple, dif_pos hqR] at he ⊢
        cases t with
        | zero =>
            change tripleModeAt
              (TripleOrder.node q hqR .flip
                (extendDecisionTreeTriple none closed
                  (Function.update known q false) (R.erase q))
                (extendDecisionTreeTriple none opened
                  (Function.update known q true) (R.erase q))) base e = .flip at he
            have hqflip : tripleModeAt
                (TripleOrder.node q hqR .flip
                  (extendDecisionTreeTriple none closed
                    (Function.update known q false) (R.erase q))
                  (extendDecisionTreeTriple none opened
                    (Function.update known q true) (R.erase q))) base q = .flip := by
              simp [tripleModeAt]
            have heq : e = q := tripleModeAt_extendDecisionTreeTriple_flip_unique
              0 (.node q opened closed) known base R e q (by
                simpa [extendDecisionTreeTriple, hqR] using he) (by
                simpa [extendDecisionTreeTriple, hqR] using hqflip)
            subst e
            simp only [TripleOrder.leftOrder, TripleMode.leftIndependent, realizedList]
            split <;> exact List.idxOf_cons_self
        | succ t =>
            have hne : e ≠ q := by
              intro heq
              subst e
              simp [tripleModeAt] at he
            simp only [TripleOrder.leftOrder, TripleMode.leftIndependent, realizedList,
              tripleModeAt, hne, if_false]
            by_cases hb : base q
            · simp only [tripleModeAt, hne, if_false, hb, if_true] at he
              simp only [hb, if_true]
              rw [List.idxOf_cons_ne _ (Ne.symm hne)]
              rw [iho t (Function.update known q true) (R.erase q) he]
            · simp only [tripleModeAt, hne, if_false, hb,
                Bool.false_eq_true] at he
              simp only [hb, Bool.false_eq_true, if_false]
              rw [List.idxOf_cons_ne _ (Ne.symm hne)]
              rw [ihc t (Function.update known q false) (R.erase q) he]
      · rw [extendDecisionTreeTriple, dif_neg hqR] at he ⊢
        by_cases hk : known q
        · simp only [hk, if_true] at he ⊢
          exact iho t known R he
        · simp only [hk, Bool.false_eq_true, if_false] at he ⊢
          exact ihc t known R he

theorem realizedEquiv_symm_flip
    (t : ℕ) (T : DecisionTree E) (known base : ConfigSpace E) (e : E)
    (he : tripleModeAt
      (extendDecisionTreeTriple (some t) T known (Finset.univ : Finset E))
      base e = .flip) :
    ((realizedEquiv
      (extendDecisionTreeTriple (some t) T known Finset.univ).leftOrder base).symm e : ℕ) = t := by
  rw [realizedEquiv_symm_val]
  exact idxOf_flip_extendDecisionTreeTriple t T known base Finset.univ e he



theorem cross_flip_atom_sum_eq_flipCrossTripleProb_sum
    (mu : ConfigSpace E → ℝ) (seed : ConfigSpace E) (e : E)
    (S : TripleOrder (Finset.univ : Finset E))
    (g : ConfigSpace E → ConfigSpace E → ℝ) :
    (∑ base,
      (if tripleModeAt S base e = .flip then 1 else 0) *
        (∑ left, ∑ right,
          g left right * crossTripleJointProb mu ∅ base left right S)) =
      ∑ left, ∑ right,
        g left right * flipCrossTripleProb mu ∅ seed left right e S := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro right _
  calc
    _ = g left right *
        (∑ base,
          (if tripleModeAt S base e = .flip then 1 else 0) *
            crossTripleJointProb mu ∅ base left right S) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro base _
      ring
    _ = _ := by
      rw [← baseSum_flip_crossTripleJointProb_eq_flipCrossTripleProb
        mu ∅ seed left right e S (by simp)]
      congr 1
      unfold baseSum
      apply Finset.sum_congr rfl
      intro base _
      have hA : Monotonic.Agree (∅ : Finset E) seed base := by
        simp [Monotonic.Agree]
      rw [if_pos hA]

end AdaptiveCausalKernel
end OSSS
end StatMech
