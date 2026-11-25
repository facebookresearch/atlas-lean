/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBoundaryRight.Injective

@[expose] public section

namespace AlgebraicTopology.EilenbergZilber.Shuffle

variable {p q : ℕ}

def rightBoundaryFinEquiv : Fin (p + q + 1) ≃ Fin (p + (q + 1)) :=
  finCongr (by omega)

@[simp]
theorem rightBoundaryFinEquiv_apply_val (x : Fin (p + q + 1)) :
    (rightBoundaryFinEquiv x).val = x.val := by
  rfl

@[simp]
theorem rightBoundaryFinEquiv_symm_apply_val (x : Fin (p + (q + 1))) :
    (rightBoundaryFinEquiv.symm x).val = x.val := by
  rfl

noncomputable def rightBoundarySourcePositions (s : Shuffle p (q + 1)) :
    Set.powersetCard (Fin (p + q + 1)) (q + 1) :=
  Set.powersetCard.map (q + 1) rightBoundaryFinEquiv.symm.toEmbedding s.rightPositions

@[simp]
theorem map_rightBoundarySourcePositions (s : Shuffle p (q + 1)) :
    Set.powersetCard.map (q + 1) rightBoundaryFinEquiv.toEmbedding
        (rightBoundarySourcePositions s) = s.rightPositions := by
  simpa only [rightBoundarySourcePositions] using
    Set.powersetCard.map_equiv_right_inv rightBoundaryFinEquiv s.rightPositions

@[simp]
theorem mem_rightBoundarySourcePositions_iff (s : Shuffle p (q + 1))
    (x : Fin (p + q + 1)) :
    x ∈ rightBoundarySourcePositions s ↔
      rightBoundaryFinEquiv x ∈ s.rightPositions := by
  rw [rightBoundarySourcePositions, Set.powersetCard.mem_map_iff]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = rightBoundaryFinEquiv x := by
      rw [← hyx]
      simp
    rwa [← this]
  · intro hx
    exact ⟨rightBoundaryFinEquiv x, hx, by simp⟩

noncomputable def rightBoundaryPredecessorPositions (s : Shuffle p (q + 1))
    (r : Fin (p + q + 1)) (hr : r ∈ rightBoundarySourcePositions s) :
    Set.powersetCard (Fin (p + q)) q :=
  Set.powersetCard.eraseSuccAbove (rightBoundarySourcePositions s) r hr

@[simp]
theorem insertSuccAbove_rightBoundaryPredecessorPositions
    (s : Shuffle p (q + 1)) (r : Fin (p + q + 1))
    (hr : r ∈ rightBoundarySourcePositions s) :
    Set.powersetCard.insertSuccAbove r
        (rightBoundaryPredecessorPositions s r hr) =
      rightBoundarySourcePositions s := by
  exact Set.powersetCard.insertSuccAbove_eraseSuccAbove _ _ _

theorem map_insertSuccAbove_rightBoundaryPredecessorPositions
    (s : Shuffle p (q + 1)) (r : Fin (p + q + 1))
    (hr : r ∈ rightBoundarySourcePositions s) :
    Set.powersetCard.map (q + 1) rightBoundaryFinEquiv.toEmbedding
        (Set.powersetCard.insertSuccAbove r
          (rightBoundaryPredecessorPositions s r hr)) = s.rightPositions := by
  rw [insertSuccAbove_rightBoundaryPredecessorPositions,
    map_rightBoundarySourcePositions]

private theorem right_succAbove_eq_of_adj {n : ℕ} {r : Fin (n + 1)} {y : Fin n}
    {lower upper : Fin (n + 1)} (hyEq : r.succAbove y = lower)
    (hrEq : r = upper) (hAdj : lower.val + 1 = upper.val) :
    r = y.succ := by
  subst lower
  subst upper
  apply Fin.ext
  by_cases hlt : y.castSucc < r
  · rw [Fin.succAbove_of_castSucc_lt _ _ hlt] at hAdj
    simpa only [Fin.val_castSucc, Fin.val_succ] using hAdj.symm
  · have hle : r ≤ y.castSucc := Fin.not_lt.mp hlt
    rw [Fin.succAbove_of_le_castSucc _ _ hle] at hAdj
    have hleVal : r.val ≤ y.val := hle
    simp only [Fin.val_succ] at hAdj
    omega

noncomputable def rightBoundaryPredecessorShuffle (s : Shuffle p (q + 1))
    (r : Fin (p + q + 1)) (hr : r ∈ rightBoundarySourcePositions s) :
    Shuffle p q :=
  ofRightPositions (rightBoundaryPredecessorPositions s r hr)

@[simp]
theorem rightPositions_rightBoundaryPredecessorShuffle
    (s : Shuffle p (q + 1)) (r : Fin (p + q + 1))
    (hr : r ∈ rightBoundarySourcePositions s) :
    (rightBoundaryPredecessorShuffle s r hr).rightPositions =
      rightBoundaryPredecessorPositions s r hr := by
  exact rightPositions_ofRightPositions _

theorem rightBoundaryShuffle_predecessor
    (s : Shuffle p (q + 1)) (r : Fin (p + q + 1))
    (hr : r ∈ rightBoundarySourcePositions s) (a : Fin (q + 2))
    (ha : rightInsertedPosition (rightBoundaryPredecessorShuffle s r hr) a = r) :
    rightBoundaryShuffle (rightBoundaryPredecessorShuffle s r hr) a = s := by
  apply (equivRightPositions (p := p) (q := q + 1)).injective
  change rightPositions (rightBoundaryShuffle (rightBoundaryPredecessorShuffle s r hr) a) =
    rightPositions s
  rw [rightBoundaryShuffle, rightPositions_ofRightPositions, rightInsertedPositions, ha,
    rightPositions_rightBoundaryPredecessorShuffle]
  simpa only [rightBoundaryFinEquiv] using
    map_insertSuccAbove_rightBoundaryPredecessorPositions s r hr

abbrev RightBoundaryFace (p q : ℕ) :=
  {si : Shuffle p (q + 1) × Fin (p + (q + 1) + 1) //
    IsRightBoundary si.1 si.2}

theorem rightBoundaryPair_surjective :
    Function.Surjective fun x : Fin (q + 2) × Shuffle p q =>
      (⟨rightBoundaryPair x, rightBoundaryPair_isRightBoundary x⟩ :
        RightBoundaryFace p q) := by
  rintro ⟨⟨s, i⟩, h⟩
  rcases h with hzero | hlast | hinterior
  · let r : Fin (p + q + 1) := 0
    have hr : r ∈ rightBoundarySourcePositions s := by
      rw [mem_rightBoundarySourcePositions_iff]
      simpa [r, rightBoundaryFinEquiv] using hzero.2
    let t : Shuffle p q := rightBoundaryPredecessorShuffle s r hr
    refine ⟨((0 : Fin (q + 2)), t), ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · change rightBoundaryShuffle t 0 = s
      exact rightBoundaryShuffle_predecessor s r hr 0 (by simp [r])
    · change rightBoundaryIndex t 0 = i
      exact (rightBoundaryIndex_zero t).trans hzero.1.symm
  · let r : Fin (p + q + 1) := Fin.last (p + q)
    have hr : r ∈ rightBoundarySourcePositions s := by
      rw [mem_rightBoundarySourcePositions_iff]
      simpa [r, rightBoundaryFinEquiv] using hlast.2
    let t : Shuffle p q := rightBoundaryPredecessorShuffle s r hr
    refine ⟨(Fin.last (q + 1), t), ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · change rightBoundaryShuffle t (Fin.last (q + 1)) = s
      exact rightBoundaryShuffle_predecessor s r hr (Fin.last (q + 1)) (by simp [r])
    · change rightBoundaryIndex t (Fin.last (q + 1)) = i
      exact (rightBoundaryIndex_last t).trans hlast.1.symm
  · obtain ⟨lower, upper, hadj, hi, hlower, hupper⟩ := hinterior
    change i = upper.castSucc at hi
    change lower ∈ s.rightPositions at hlower
    change upper ∈ s.rightPositions at hupper
    let r : Fin (p + q + 1) := rightBoundaryFinEquiv.symm upper
    have hr : r ∈ rightBoundarySourcePositions s := by
      rw [mem_rightBoundarySourcePositions_iff]
      simpa [r] using hupper
    let t : Shuffle p q := rightBoundaryPredecessorShuffle s r hr
    have hlowerSource : rightBoundaryFinEquiv.symm lower ∈
        rightBoundarySourcePositions s := by
      rw [mem_rightBoundarySourcePositions_iff]
      simpa using hlower
    have hlowerInsert : rightBoundaryFinEquiv.symm lower ∈
        Set.powersetCard.insertSuccAbove r
          (rightBoundaryPredecessorPositions s r hr) := by
      rw [insertSuccAbove_rightBoundaryPredecessorPositions]
      exact hlowerSource
    rw [Set.powersetCard.mem_insertSuccAbove_iff] at hlowerInsert
    rcases hlowerInsert with hbad | ⟨y, hy, hyEq⟩
    · have hbadVal := congrArg Fin.val hbad
      simp only [rightBoundaryFinEquiv_symm_apply_val] at hbadVal
      have hrVal : r.val = upper.val := by simp [r]
      omega
    · have hyRight : y ∈ t.rightPositions := by
        simpa [t] using hy
      obtain ⟨k, hk⟩ := (mem_rightPositions_iff t y).mp hyRight
      have hAdjSource :
          (rightBoundaryFinEquiv.symm lower).val + 1 =
            (rightBoundaryFinEquiv.symm upper).val := by
        simpa using hadj
      have hrSucc : r = y.succ :=
        right_succAbove_eq_of_adj hyEq rfl hAdjSource
      let a : Fin (q + 2) := Fin.succ (Fin.castSucc k)
      have ha : rightInsertedPosition t a = r := by
        simpa [a, hk] using hrSucc.symm
      have hIndex : rightBoundaryIndex t a = i := by
        rw [hi]
        apply Fin.ext
        simp only [a, rightBoundaryIndex_interior, Fin.val_cast, Fin.val_castSucc, hk, Fin.val_succ]
        have hval := congrArg Fin.val hrSucc
        simpa [r] using hval.symm
      refine ⟨(a, t), ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · change rightBoundaryShuffle t a = s
        exact rightBoundaryShuffle_predecessor s r hr a ha
      · change rightBoundaryIndex t a = i
        exact hIndex

theorem exists_rightBoundaryPair_eq_of_isRightBoundary
    {s : Shuffle p (q + 1)} {i : Fin (p + (q + 1) + 1)}
    (h : IsRightBoundary s i) :
    ∃ x : Fin (q + 2) × Shuffle p q, rightBoundaryPair x = (s, i) := by
  obtain ⟨x, hx⟩ := rightBoundaryPair_surjective
    (⟨(s, i), h⟩ : RightBoundaryFace p q)
  exact ⟨x, congrArg Subtype.val hx⟩

noncomputable def rightBoundaryEquiv :
    Fin (q + 2) × Shuffle p q ≃ RightBoundaryFace p q :=
  Equiv.ofBijective
    (fun x => ⟨rightBoundaryPair x, rightBoundaryPair_isRightBoundary x⟩)
    ⟨fun _ _ h => rightBoundaryPair_injective (congrArg Subtype.val h),
      rightBoundaryPair_surjective⟩

@[simp]
theorem rightBoundaryEquiv_apply_val (x : Fin (q + 2) × Shuffle p q) :
    (rightBoundaryEquiv x).1 = rightBoundaryPair x := by
  rfl

end AlgebraicTopology.EilenbergZilber.Shuffle
