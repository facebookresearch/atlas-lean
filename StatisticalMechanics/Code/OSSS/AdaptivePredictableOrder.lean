/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.OSSS.AdaptiveCausalKernel

namespace StatMech
namespace OSSS
namespace AdaptiveCausalKernel

open Coding Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]



lemma realizedList_take_succ_eq_of_agree {R : Finset E} (S : CausalOrder R)
    (x y : ConfigSpace E) (t : ℕ) (ht : t < R.card)
    (hxy : Agree ((realizedList S x).take t).toFinset x y) :
    (realizedList S y).take (t + 1) = (realizedList S x).take (t + 1) := by
  induction S generalizing t x y with
  | done => simp at ht
  | @node R e he independent closed opened ihc iho =>
      cases t with
      | zero => simp only [realizedList]
                split <;> split <;> simp
      | succ t =>
          have hemem : e ∈ ((realizedList (.node e he independent closed opened) x).take
              (t + 1)).toFinset := by
            simp only [realizedList]
            split <;> simp
          have heq : y e = x e := hxy e hemem
          have htchild : t < (R.erase e).card := by
            rw [Finset.card_erase_of_mem he]
            omega
          by_cases hx : x e
          · have hy : y e := by simpa [heq] using hx
            simp only [realizedList, hx, hy, if_true, List.take_succ_cons]
            congr 1
            apply iho (x := x) (y := y) t htchild
            intro z hz
            apply hxy z
            simpa [realizedList, hx] using Finset.mem_insert_of_mem hz
          · have hy : ¬ y e := by simpa [heq] using hx
            simp only [realizedList, hx, hy, Bool.false_eq_true, if_false,
              List.take_succ_cons]
            congr 1
            apply ihc (x := x) (y := y) t htchild
            intro z hz
            apply hxy z
            simpa [realizedList, hx] using Finset.mem_insert_of_mem hz



theorem realizedEquiv_predictable
    (S : CausalOrder (Finset.univ : Finset E)) :
    AdaptiveCodingLaw.PredictableOrder (fun x => realizedEquiv S x) := by
  intro x y t hxy
  have hagree : Agree ((realizedList S x).take (t : ℕ)).toFinset x y := by
    intro e he
    apply hxy e
    rw [mem_prefixSet_iff]
    have hetake : e ∈ (realizedList S x).take (t : ℕ) := by
      simpa only [List.mem_toFinset] using he
    have hefull : e ∈ realizedList S x := List.mem_of_mem_take hetake
    have hidx : (realizedList S x).idxOf e < (t : ℕ) :=
      (List.mem_take_iff_idxOf_lt hefull).mp hetake
    refine ⟨(realizedEquiv S x).symm e, ?_, by simp⟩
    simpa only [realizedEquiv_symm_val] using hidx
  have ht : (t : ℕ) < (Finset.univ : Finset E).card := by
    simpa using t.isLt
  have htake := realizedList_take_succ_eq_of_agree S x y (t : ℕ) ht hagree
  have htx : (t : ℕ) < (realizedList S x).length := by
    rw [realizedList_length]
    exact ht
  have hty : (t : ℕ) < (realizedList S y).length := by
    rw [realizedList_length]
    exact ht
  have hxget : realizedEquiv S x t = (realizedList S x)[(t : ℕ)]'htx := by
    unfold realizedEquiv
    simp [List.Nodup.getEquivOfForallMemList_apply]
  have hyget : realizedEquiv S y t = (realizedList S y)[(t : ℕ)]'hty := by
    unfold realizedEquiv
    simp [List.Nodup.getEquivOfForallMemList_apply]
  rw [hxget, hyget]
  have hopt := congrArg (fun l : List E => l[(t : ℕ)]?) htake
  simp only [List.getElem?_take, Nat.lt_add_one, if_true,
    List.getElem?_eq_getElem hty, List.getElem?_eq_getElem htx,
    Option.some.injEq] at hopt
  exact hopt



theorem extendDecisionTree_univ_known_congr (T : DecisionTree E)
    (known known' : ConfigSpace E) :
    extendDecisionTree T known (Finset.univ : Finset E) =
      extendDecisionTree T known' Finset.univ := by
  rw [← extendDecisionTreeAt_zero T known Finset.univ,
    ← extendDecisionTreeAt_zero T known' Finset.univ,
    ← extendDecisionTreeTriple_none_leftOrder T known Finset.univ,
    ← extendDecisionTreeTriple_none_leftOrder T known' Finset.univ]
  exact congrArg TripleOrder.leftOrder
    (extendDecisionTreeTriple_univ_seed_congr none T known known')



theorem decisionTree_realizedEquiv_predictable (T : DecisionTree E) :
    AdaptiveCodingLaw.PredictableOrder (fun x =>
      realizedEquiv (extendDecisionTree T x (Finset.univ : Finset E)) x) := by
  let S := extendDecisionTree T (fun _ => false) (Finset.univ : Finset E)
  have heq : (fun x =>
      realizedEquiv (extendDecisionTree T x (Finset.univ : Finset E)) x) =
      (fun x => realizedEquiv S x) := by
    funext x
    congr 1
    exact extendDecisionTree_univ_known_congr T x (fun _ => false)
  rw [heq]
  exact realizedEquiv_predictable S





theorem sharedEdges_extendDecisionTreeAt_eq_sdiff_take
    (t : ℕ) (T : DecisionTree E) (known base : ConfigSpace E) (R : Finset E)
    (hknown : ∀ z, z ∉ R → known z = base z) :
    sharedEdges (extendDecisionTreeAt t T known R) base =
      (T.queried base ∩ R) \
        ((realizedList (extendDecisionTree T known R) base).take t).toFinset := by
  induction T generalizing t known R with
  | leaf b => simp [extendDecisionTreeAt, extendDecisionTree, DecisionTree.queried]
  | node e opened closed iho ihc =>
      simp only [extendDecisionTreeAt, extendDecisionTree]
      by_cases heR : e ∈ R
      · simp only [heR, dif_pos]
        by_cases hb : base e
        · have hk : ∀ z, z ∉ R.erase e →
              Function.update known e true z = base z := by
            intro z hz
            by_cases hze : z = e
            · subst z
              simp [hb]
            · rw [Function.update_of_ne hze]
              apply hknown z
              intro hzR
              exact hz (Finset.mem_erase.mpr ⟨hze, hzR⟩)
          cases t with
          | zero =>
              simp only [sharedEdges, hb, if_true, decide_false, Bool.false_eq_true,
                if_false, DecisionTree.queried, List.take_zero, List.toFinset_nil,
                Finset.sdiff_empty]
              rw [iho 0 (Function.update known e true) (R.erase e) hk]
              ext z
              by_cases hze : z = e <;> simp [hze, heR]
          | succ t =>
              simp only [sharedEdges, hb, if_true, Nat.zero_lt_succ, decide_true,
                DecisionTree.queried, realizedList, List.take_succ_cons, List.toFinset_cons]
              simp only [Nat.add_sub_cancel]
              rw [iho t (Function.update known e true) (R.erase e) hk]
              ext z
              simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_insert,
                Finset.mem_erase]
              by_cases hze : z = e <;> simp [hze]
        · have hb' : base e = false := Bool.eq_false_of_not_eq_true hb
          have hk : ∀ z, z ∉ R.erase e →
              Function.update known e false z = base z := by
            intro z hz
            by_cases hze : z = e
            · subst z
              simp [hb']
            · rw [Function.update_of_ne hze]
              apply hknown z
              intro hzR
              exact hz (Finset.mem_erase.mpr ⟨hze, hzR⟩)
          cases t with
          | zero =>
              simp only [sharedEdges, hb, Bool.false_eq_true, if_false, decide_false,
                DecisionTree.queried, List.take_zero, List.toFinset_nil, Finset.sdiff_empty]
              rw [ihc 0 (Function.update known e false) (R.erase e) hk]
              ext z
              by_cases hze : z = e <;> simp [hze, heR]
          | succ t =>
              simp only [sharedEdges, hb, Bool.false_eq_true, if_false, Nat.zero_lt_succ,
                decide_true, DecisionTree.queried, realizedList, List.take_succ_cons,
                List.toFinset_cons]
              simp only [if_pos, Nat.add_sub_cancel]
              rw [ihc t (Function.update known e false) (R.erase e) hk]
              ext z
              simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_insert,
                Finset.mem_erase]
              by_cases hze : z = e <;> simp [hze]
      · rw [dif_neg heR]
        have hkb : known e = base e := hknown e heR
        by_cases hb : base e
        · simp only [hkb, hb, if_true, DecisionTree.queried]
          rw [iho t known R hknown]
          ext z
          simp [heR]
        · simp only [hkb, hb, Bool.false_eq_true, if_false, DecisionTree.queried]
          rw [ihc t known R hknown]
          ext z
          simp [heR]



lemma prefixSet_realizedEquiv_eq_take
    (S : CausalOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (m : ℕ) (hm : m ≤ Fintype.card E) :
    prefixSet (realizedEquiv S base : Fin (Fintype.card E) → E) m =
      ((realizedList S base).take m).toFinset := by
  ext e
  have hefull : e ∈ realizedList S base := by
    rw [← List.mem_toFinset, realizedList_toFinset]
    exact Finset.mem_univ e
  rw [List.mem_toFinset]
  constructor
  · intro he
    obtain ⟨j, hj, hje⟩ := (mem_prefixSet_iff _ _ _).mp he
    have hidx : (realizedList S base).idxOf e < m := by
      have hj' : j = (realizedEquiv S base).symm e :=
        (realizedEquiv S base).injective (by simpa using hje)
      subst j
      simpa only [realizedEquiv_symm_val] using hj
    exact (List.mem_take_iff_idxOf_lt hefull).mpr hidx
  · intro he
    have hidx := (List.mem_take_iff_idxOf_lt hefull).mp he
    rw [mem_prefixSet_iff]
    refine ⟨(realizedEquiv S base).symm e, ?_, by simp⟩
    simpa only [realizedEquiv_symm_val] using hidx



lemma realizedList_take_queried_extendDecisionTree
    (T : DecisionTree E) (known base : ConfigSpace E) (R : Finset E)
    (hknown : ∀ z, z ∉ R → known z = base z) :
    ((realizedList (extendDecisionTree T known R) base).take
      ((T.queried base ∩ R).card)).toFinset = T.queried base ∩ R := by
  induction T generalizing known R with
  | leaf b => simp [extendDecisionTree, DecisionTree.queried]
  | node e opened closed iho ihc =>
      rw [extendDecisionTree]
      by_cases he : e ∈ R
      · rw [dif_pos he]
        by_cases hb : base e
        · have hk : ∀ z, z ∉ R.erase e →
              Function.update known e true z = base z := by
            intro z hz
            by_cases hze : z = e
            · subst z
              simp [hb]
            · rw [Function.update_of_ne hze]
              apply hknown z
              intro hzR
              exact hz (Finset.mem_erase.mpr ⟨hze, hzR⟩)
          have hi := iho (Function.update known e true) (R.erase e) hk
          let A := opened.queried base ∩ R.erase e
          have heA : e ∉ A := by simp [A]
          have hset : (insert e (opened.queried base) ∩ R) = insert e A := by
            ext z
            simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase, A]
            constructor
            · rintro ⟨rfl | hz, hzR⟩
              · exact Or.inl rfl
              · by_cases hze : z = e
                · exact Or.inl hze
                · exact Or.inr ⟨hz, hze, hzR⟩
            · rintro (rfl | ⟨hz, hze, hzR⟩)
              · exact ⟨Or.inl rfl, he⟩
              · exact ⟨Or.inr hz, hzR⟩
          simp only [DecisionTree.queried, hb, if_true, hset,
            Finset.card_insert_of_notMem heA, realizedList, List.take_succ_cons,
            List.toFinset_cons]
          rw [hi]
        · have hb' : base e = false := Bool.eq_false_of_not_eq_true hb
          have hk : ∀ z, z ∉ R.erase e →
              Function.update known e false z = base z := by
            intro z hz
            by_cases hze : z = e
            · subst z
              simp [hb']
            · rw [Function.update_of_ne hze]
              apply hknown z
              intro hzR
              exact hz (Finset.mem_erase.mpr ⟨hze, hzR⟩)
          have hi := ihc (Function.update known e false) (R.erase e) hk
          let A := closed.queried base ∩ R.erase e
          have heA : e ∉ A := by simp [A]
          have hset : (insert e (closed.queried base) ∩ R) = insert e A := by
            ext z
            simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase, A]
            constructor
            · rintro ⟨rfl | hz, hzR⟩
              · exact Or.inl rfl
              · by_cases hze : z = e
                · exact Or.inl hze
                · exact Or.inr ⟨hz, hze, hzR⟩
            · rintro (rfl | ⟨hz, hze, hzR⟩)
              · exact ⟨Or.inl rfl, he⟩
              · exact ⟨Or.inr hz, hzR⟩
          simp only [DecisionTree.queried, hb, Bool.false_eq_true, if_false, hset,
            Finset.card_insert_of_notMem heA, realizedList, List.take_succ_cons,
            List.toFinset_cons]
          rw [hi]
      · rw [dif_neg he]
        have hkb : known e = base e := hknown e he
        by_cases hb : base e
        · have hset : insert e (opened.queried base) ∩ R =
              opened.queried base ∩ R := by
            ext z
            simp [he]
          simp only [hkb, hb, if_true, DecisionTree.queried, hset]
          exact iho known R hknown
        · have hset : insert e (closed.queried base) ∩ R =
              closed.queried base ∩ R := by
            ext z
            simp [he]
          simp only [hkb, hb, Bool.false_eq_true, if_false, DecisionTree.queried, hset]
          exact ihc known R hknown



theorem prefixSet_decisionTree_realizedEquiv_queried (T : DecisionTree E)
    (base : ConfigSpace E) :
    prefixSet
      (realizedEquiv (extendDecisionTree T base (Finset.univ : Finset E)) base :
        Fin (Fintype.card E) → E)
      (T.queried base).card = T.queried base := by
  rw [prefixSet_realizedEquiv_eq_take]
  · simpa using realizedList_take_queried_extendDecisionTree
      T base base Finset.univ (by simp)
  · simpa using Finset.card_le_card (Finset.subset_univ (T.queried base))



theorem stopVal_decisionTree_realizedEquiv_le_queried_card
    (mu : ConfigSpace E → ℝ) (T : DecisionTree E) (base : ConfigSpace E)
    (U : Fin (Fintype.card E) → ℝ)
    (hU : codeMap mu
      (realizedEquiv (extendDecisionTree T base (Finset.univ : Finset E)) base :
        Fin (Fintype.card E) → E) U = base) :
    AdaptMConditional.stopVal mu
      (realizedEquiv (extendDecisionTree T base (Finset.univ : Finset E)) base)
      T.evalR U ≤ (T.queried base).card := by
  apply Nat.find_le
  intro w hw
  unfold DecisionTree.evalR
  rw [Coding.eval_eq_of_agree_on_queried T base w]
  · rw [hU]
  · intro e he
    have hwe := hw e (by
      rw [prefixSet_decisionTree_realizedEquiv_queried T base]
      exact he)
    rw [hU] at hwe
    exact hwe

end AdaptiveCausalKernel
end OSSS
end StatMech
