/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBoundaryLeft.Injective

@[expose] public section

namespace AlgebraicTopology.EilenbergZilber.Shuffle

variable {p q : ℕ}

def leftBoundaryFinEquiv : Fin (p + q + 1) ≃ Fin ((p + 1) + q) :=
  finCongr (by omega)

@[simp]
theorem leftBoundaryFinEquiv_apply_val (x : Fin (p + q + 1)) :
    (leftBoundaryFinEquiv x).val = x.val := by
  rfl

@[simp]
theorem leftBoundaryFinEquiv_symm_apply_val (x : Fin ((p + 1) + q)) :
    (leftBoundaryFinEquiv.symm x).val = x.val := by
  rfl

noncomputable def leftBoundarySourcePositions (s : Shuffle (p + 1) q) :
    Set.powersetCard (Fin (p + q + 1)) (p + 1) :=
  Set.powersetCard.map (p + 1) leftBoundaryFinEquiv.symm.toEmbedding s.leftPositions

@[simp]
theorem map_leftBoundarySourcePositions (s : Shuffle (p + 1) q) :
    Set.powersetCard.map (p + 1) leftBoundaryFinEquiv.toEmbedding
        (leftBoundarySourcePositions s) = s.leftPositions := by
  simpa only [leftBoundarySourcePositions] using
    Set.powersetCard.map_equiv_right_inv leftBoundaryFinEquiv s.leftPositions

@[simp]
theorem mem_leftBoundarySourcePositions_iff (s : Shuffle (p + 1) q)
    (x : Fin (p + q + 1)) :
    x ∈ leftBoundarySourcePositions s ↔
      leftBoundaryFinEquiv x ∈ s.leftPositions := by
  rw [leftBoundarySourcePositions, Set.powersetCard.mem_map_iff]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = leftBoundaryFinEquiv x := by
      rw [← hyx]
      simp
    rwa [← this]
  · intro hx
    exact ⟨leftBoundaryFinEquiv x, hx, by simp⟩

noncomputable def leftBoundaryPredecessorPositions (s : Shuffle (p + 1) q)
    (r : Fin (p + q + 1)) (hr : r ∈ leftBoundarySourcePositions s) :
    Set.powersetCard (Fin (p + q)) p :=
  Set.powersetCard.eraseSuccAbove (leftBoundarySourcePositions s) r hr

@[simp]
theorem insertSuccAbove_leftBoundaryPredecessorPositions
    (s : Shuffle (p + 1) q) (r : Fin (p + q + 1))
    (hr : r ∈ leftBoundarySourcePositions s) :
    Set.powersetCard.insertSuccAbove r
        (leftBoundaryPredecessorPositions s r hr) =
      leftBoundarySourcePositions s := by
  exact Set.powersetCard.insertSuccAbove_eraseSuccAbove _ _ _

theorem map_insertSuccAbove_leftBoundaryPredecessorPositions
    (s : Shuffle (p + 1) q) (r : Fin (p + q + 1))
    (hr : r ∈ leftBoundarySourcePositions s) :
    Set.powersetCard.map (p + 1) leftBoundaryFinEquiv.toEmbedding
        (Set.powersetCard.insertSuccAbove r
          (leftBoundaryPredecessorPositions s r hr)) = s.leftPositions := by
  rw [insertSuccAbove_leftBoundaryPredecessorPositions,
    map_leftBoundarySourcePositions]

theorem succAbove_eq_of_adj {n : ℕ} {r : Fin (n + 1)} {y : Fin n}
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

noncomputable def leftBoundaryPredecessorShuffle (s : Shuffle (p + 1) q)
    (r : Fin (p + q + 1)) (hr : r ∈ leftBoundarySourcePositions s) :
    Shuffle p q :=
  ofLeftPositions (leftBoundaryPredecessorPositions s r hr)

@[simp]
theorem leftPositions_leftBoundaryPredecessorShuffle
    (s : Shuffle (p + 1) q) (r : Fin (p + q + 1))
    (hr : r ∈ leftBoundarySourcePositions s) :
    (leftBoundaryPredecessorShuffle s r hr).leftPositions =
      leftBoundaryPredecessorPositions s r hr := by
  exact leftPositions_ofLeftPositions _

theorem leftBoundaryShuffle_predecessor
    (s : Shuffle (p + 1) q) (r : Fin (p + q + 1))
    (hr : r ∈ leftBoundarySourcePositions s) (a : Fin (p + 2))
    (ha : leftInsertedPosition (leftBoundaryPredecessorShuffle s r hr) a = r) :
    leftBoundaryShuffle (leftBoundaryPredecessorShuffle s r hr) a = s := by
  apply (equivLeftPositions (p := p + 1) (q := q)).injective
  change leftPositions (leftBoundaryShuffle (leftBoundaryPredecessorShuffle s r hr) a) =
    leftPositions s
  rw [leftBoundaryShuffle, leftPositions_ofLeftPositions, leftInsertedPositions, ha,
    leftPositions_leftBoundaryPredecessorShuffle]
  simpa only [leftBoundaryFinEquiv] using
    map_insertSuccAbove_leftBoundaryPredecessorPositions s r hr

abbrev LeftBoundaryFace (p q : ℕ) :=
  {si : Shuffle (p + 1) q × Fin ((p + 1) + q + 1) //
    IsLeftBoundary si.1 si.2}

theorem leftBoundaryPair_surjective :
    Function.Surjective fun x : Fin (p + 2) × Shuffle p q =>
      (⟨leftBoundaryPair x, leftBoundaryPair_isLeftBoundary x⟩ :
        LeftBoundaryFace p q) := by
  rintro ⟨⟨s, i⟩, h⟩
  rcases h with hzero | hlast | hinterior
  · let r : Fin (p + q + 1) := 0
    have hr : r ∈ leftBoundarySourcePositions s := by
      rw [mem_leftBoundarySourcePositions_iff]
      simpa [r, leftBoundaryFinEquiv] using hzero.2
    let t : Shuffle p q := leftBoundaryPredecessorShuffle s r hr
    refine ⟨((0 : Fin (p + 2)), t), ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · change leftBoundaryShuffle t 0 = s
      exact leftBoundaryShuffle_predecessor s r hr 0 (by simp [r])
    · change leftBoundaryIndex t 0 = i
      exact (leftBoundaryIndex_zero t).trans hzero.1.symm
  · let r : Fin (p + q + 1) := Fin.last (p + q)
    have hr : r ∈ leftBoundarySourcePositions s := by
      rw [mem_leftBoundarySourcePositions_iff]
      simpa [r, leftBoundaryFinEquiv] using hlast.2
    let t : Shuffle p q := leftBoundaryPredecessorShuffle s r hr
    refine ⟨(Fin.last (p + 1), t), ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · change leftBoundaryShuffle t (Fin.last (p + 1)) = s
      exact leftBoundaryShuffle_predecessor s r hr (Fin.last (p + 1)) (by simp [r])
    · change leftBoundaryIndex t (Fin.last (p + 1)) = i
      exact (leftBoundaryIndex_last t).trans hlast.1.symm
  · obtain ⟨lower, upper, hadj, hi, hlower, hupper⟩ := hinterior
    change i = upper.castSucc at hi
    change lower ∈ s.leftPositions at hlower
    change upper ∈ s.leftPositions at hupper
    let r : Fin (p + q + 1) := leftBoundaryFinEquiv.symm upper
    have hr : r ∈ leftBoundarySourcePositions s := by
      rw [mem_leftBoundarySourcePositions_iff]
      simpa [r] using hupper
    let t : Shuffle p q := leftBoundaryPredecessorShuffle s r hr
    have hlowerSource : leftBoundaryFinEquiv.symm lower ∈
        leftBoundarySourcePositions s := by
      rw [mem_leftBoundarySourcePositions_iff]
      simpa using hlower
    have hlowerInsert : leftBoundaryFinEquiv.symm lower ∈
        Set.powersetCard.insertSuccAbove r
          (leftBoundaryPredecessorPositions s r hr) := by
      rw [insertSuccAbove_leftBoundaryPredecessorPositions]
      exact hlowerSource
    rw [Set.powersetCard.mem_insertSuccAbove_iff] at hlowerInsert
    rcases hlowerInsert with hbad | ⟨y, hy, hyEq⟩
    · have hbadVal := congrArg Fin.val hbad
      simp only [leftBoundaryFinEquiv_symm_apply_val] at hbadVal
      have hrVal : r.val = upper.val := by simp [r]
      omega
    · have hyLeft : y ∈ t.leftPositions := by
        simpa [t] using hy
      obtain ⟨k, hk⟩ := (mem_leftPositions_iff t y).mp hyLeft
      have hAdjSource :
          (leftBoundaryFinEquiv.symm lower).val + 1 =
            (leftBoundaryFinEquiv.symm upper).val := by
        simpa using hadj
      have hrSucc : r = y.succ :=
        succAbove_eq_of_adj hyEq rfl hAdjSource
      let a : Fin (p + 2) := Fin.succ (Fin.castSucc k)
      have ha : leftInsertedPosition t a = r := by
        simpa [a, hk] using hrSucc.symm
      have hIndex : leftBoundaryIndex t a = i := by
        rw [hi]
        apply Fin.ext
        simp only [a, leftBoundaryIndex_interior, Fin.val_cast,
          Fin.val_castSucc, hk, Fin.val_succ]
        have hval := congrArg Fin.val hrSucc
        simpa [r] using hval.symm
      refine ⟨(a, t), ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · change leftBoundaryShuffle t a = s
        exact leftBoundaryShuffle_predecessor s r hr a ha
      · change leftBoundaryIndex t a = i
        exact hIndex

theorem exists_leftBoundaryPair_eq_of_isLeftBoundary
    {s : Shuffle (p + 1) q} {i : Fin ((p + 1) + q + 1)}
    (h : IsLeftBoundary s i) :
    ∃ x : Fin (p + 2) × Shuffle p q, leftBoundaryPair x = (s, i) := by
  obtain ⟨x, hx⟩ := leftBoundaryPair_surjective
    (⟨(s, i), h⟩ : LeftBoundaryFace p q)
  exact ⟨x, congrArg Subtype.val hx⟩

noncomputable def leftBoundaryEquiv :
    Fin (p + 2) × Shuffle p q ≃ LeftBoundaryFace p q :=
  Equiv.ofBijective
    (fun x => ⟨leftBoundaryPair x, leftBoundaryPair_isLeftBoundary x⟩)
    ⟨fun _ _ h => leftBoundaryPair_injective (congrArg Subtype.val h),
      leftBoundaryPair_surjective⟩

@[simp]
theorem leftBoundaryEquiv_apply_val (x : Fin (p + 2) × Shuffle p q) :
    (leftBoundaryEquiv x).1 = leftBoundaryPair x := by
  rfl

end AlgebraicTopology.EilenbergZilber.Shuffle
