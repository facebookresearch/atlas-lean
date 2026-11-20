/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib



namespace StatMech.FrontierD

theorem fkRectList_flatMap_replicate_length {alpha : Type}
    (l : List alpha) (scale : alpha → ℕ) :
    (l.flatMap (fun a => List.replicate (scale a) a)).length =
      ∑ i : Fin l.length, scale (l.get i) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp [Fin.sum_univ_succ, ih]

theorem fkRectList_get_flatMap_replicate_finSigma {alpha : Type}
    (l : List alpha) (scale : alpha → ℕ)
    (i : Fin l.length) (r : Fin (scale (l.get i)))
    (k : Fin (l.flatMap (fun a => List.replicate (scale a) a)).length)
    (hk : k.val = (finSigmaFinEquiv
      (⟨i, r⟩ : Σ i : Fin l.length, Fin (scale (l.get i)))).val) :
    (l.flatMap (fun a => List.replicate (scale a) a)).get k = l.get i := by
  induction l with
  | nil => exact Fin.elim0 i
  | cons a l ih =>
      revert r k
      refine Fin.cases ?_ (fun j => ?_) i
      · intro r k hk
        have hk0 : k.val = r.val := by
          simpa [finSigmaFinEquiv_apply, Fin.sum_univ_eq_sum_range] using hk
        change (List.replicate (scale a) a ++
          l.flatMap (fun b => List.replicate (scale b) b))[k.val]'k.isLt = a
        rw [List.getElem_append_left (by
          simpa [List.length_replicate, hk0] using r.isLt)]
        simp
      · intro r k hk
        rw [finSigmaFinEquiv_apply] at hk
        simp only [Fin.val_succ] at hk
        have hprefix :
            (∑ x : Fin (j.val + 1),
              scale ((a :: l).get (Fin.castLE j.succ.isLt.le x))) =
              scale a +
                ∑ x : Fin j.val,
                  scale (l.get (Fin.castLE j.isLt.le x)) := by
          rw [Fin.sum_univ_succ]
          congr 1
        change k.val =
          (∑ x : Fin (j.val + 1),
            scale ((a :: l).get (Fin.castLE j.succ.isLt.le x))) + r.val at hk
        rw [hprefix] at hk
        have hkSucc : k.val = scale a +
            (finSigmaFinEquiv
              (⟨j, r⟩ : Σ j : Fin l.length,
                Fin (scale (l.get j)))).val := by
          simpa [finSigmaFinEquiv_apply, Fin.sum_univ_succ,
            Nat.add_assoc] using hk
        have hkge : scale a ≤ k.val := by omega
        let kt : Fin (l.flatMap
            (fun b => List.replicate (scale b) b)).length :=
          ⟨k.val - scale a, by
            have hki := k.isLt
            simp only [List.flatMap_cons, List.length_append,
              List.length_replicate] at hki
            omega⟩
        change (List.replicate (scale a) a ++
          l.flatMap (fun b => List.replicate (scale b) b))[k.val]'k.isLt =
            l.get j
        rw [List.getElem_append_right (by
          simp only [List.length_replicate]
          exact hkge)]
        have hkt : kt.val = (finSigmaFinEquiv
            (⟨j, r⟩ : Σ j : Fin l.length,
              Fin (scale (l.get j)))).val := by
          dsimp [kt]
          omega
        simpa only [kt, List.length_replicate] using ih j r kt hkt

end StatMech.FrontierD
