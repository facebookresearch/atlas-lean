/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBoundary
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBoundaryLeft.Positions
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBoundaryRight.Positions

@[expose] public section

namespace AlgebraicTopology.EilenbergZilber.Shuffle

variable {p q : ℕ}
abbrev NonmixedBoundaryFace (p q : ℕ) :=
  {si : Shuffle p q × Fin (p + q + 1) // ¬ IsMixedBoundary si.1 si.2}

noncomputable instance : Fintype (NonmixedBoundaryFace p q) :=
  Fintype.ofFinite _

theorem not_isMixedBoundary_iff_isLeftBoundary_or_isRightBoundary
    (s : Shuffle (p + 1) (q + 1)) (i : Fin ((p + 1) + (q + 1) + 1)) :
    ¬ IsMixedBoundary s i ↔ IsLeftBoundary s i ∨ IsRightBoundary s i := by
  constructor
  · intro h
    cases i using Fin.cases with
    | zero =>
        by_cases hm : (0 : Fin ((p + 1) + (q + 1))) ∈ s.leftPositions
        · exact Or.inl (Or.inl ⟨rfl, hm⟩)
        · exact Or.inr (Or.inl
            ⟨rfl, (mem_rightPositions_iff_not_mem_leftPositions s 0).mpr hm⟩)
    | succ a =>
        cases a using Fin.lastCases with
        | last =>
            let lastPos : Fin ((p + 1) + (q + 1)) :=
              Fin.last ((p + 1) + q)
            by_cases hm : lastPos ∈ s.leftPositions
            · left
              right
              left
              refine ⟨?_, ?_⟩
              · apply Fin.ext
                change ((p + 1) + q) + 1 = (p + 1) + (q + 1)
                omega
              · simpa [lastPos] using hm
            · right
              right
              left
              refine ⟨?_, ?_⟩
              · apply Fin.ext
                change ((p + 1) + q) + 1 = (p + 1) + (q + 1)
                omega
              · have hr :=
                  (mem_rightPositions_iff_not_mem_leftPositions s lastPos).mpr hm
                simpa [lastPos] using hr
        | cast k =>
            let lower : Fin ((p + 1) + (q + 1)) :=
              k.castSucc
            let upper : Fin ((p + 1) + (q + 1)) :=
              k.succ
            have hadj : lower.val + 1 = upper.val := by
              simp [lower, upper]
            have hiEq : Fin.succ (Fin.castSucc k) = upper.castSucc := by
              apply Fin.ext
              simp [upper]
            by_cases hl : lower ∈ s.leftPositions
            · by_cases hu : upper ∈ s.leftPositions
              · exact Or.inl (Or.inr (Or.inr
                  ⟨lower, upper, hadj, hiEq, hl, hu⟩))
              · exfalso
                exact h ⟨lower, upper, hadj, hiEq, Or.inl ⟨hl, hu⟩⟩
            · by_cases hu : upper ∈ s.leftPositions
              · exfalso
                exact h ⟨lower, upper, hadj, hiEq, Or.inr ⟨hu, hl⟩⟩
              · exact Or.inr (Or.inr (Or.inr
                  ⟨lower, upper, hadj, hiEq,
                    (mem_rightPositions_iff_not_mem_leftPositions s lower).mpr hl,
                    (mem_rightPositions_iff_not_mem_leftPositions s upper).mpr hu⟩))
  · intro h
    rcases h with hL | hR
    · exact isLeftBoundary_not_isMixedBoundary hL
    · exact isRightBoundary_not_isMixedBoundary hR

theorem isLeftBoundary_not_isRightBoundary
    {s : Shuffle (p + 1) (q + 1)}
    {i : Fin ((p + 1) + (q + 1) + 1)}
    (hl : IsLeftBoundary s i) (hr : IsRightBoundary s i) : False := by
  rcases hl with hzeroL | hlastL | hinteriorL
  · rcases hr with hzeroR | hlastR | hinteriorR
    · exact (mem_rightPositions_iff_not_mem_leftPositions s 0).mp hzeroR.2 hzeroL.2
    · have hval := congrArg Fin.val (hzeroL.1.symm.trans hlastR.1)
      simp at hval
    · obtain ⟨lower, upper, hadj, hi, _, _⟩ := hinteriorR
      have hval := congrArg Fin.val (hzeroL.1.symm.trans hi)
      simp at hval
      omega
  · rcases hr with hzeroR | hlastR | hinteriorR
    · have hval := congrArg Fin.val (hlastL.1.symm.trans hzeroR.1)
      simp at hval
    · let leftLast : Fin ((p + 1) + (q + 1)) :=
        Fin.cast (by omega) (Fin.last (p + (q + 1)))
      let rightLast : Fin ((p + 1) + (q + 1)) :=
        Fin.cast (by omega) (Fin.last ((p + 1) + q))
      have hLast : leftLast = rightLast := by
        apply Fin.ext
        simp [leftLast, rightLast]
      have hleft : rightLast ∈ s.leftPositions := by
        rw [← hLast]
        exact hlastL.2
      exact (mem_rightPositions_iff_not_mem_leftPositions s rightLast).mp
        hlastR.2 hleft
    · obtain ⟨lower, upper, hadj, hi, _, _⟩ := hinteriorR
      have hval := congrArg Fin.val (hlastL.1.symm.trans hi)
      have hu := upper.isLt
      simp at hval
      omega
  · obtain ⟨lowerL, upperL, hadjL, hiL, _, hupperL⟩ := hinteriorL
    rcases hr with hzeroR | hlastR | hinteriorR
    · have hval := congrArg Fin.val (hiL.symm.trans hzeroR.1)
      simp only [Fin.val_castSucc, Fin.val_zero] at hval
      omega
    · have hval := congrArg Fin.val (hiL.symm.trans hlastR.1)
      have hu := upperL.isLt
      simp at hval
      omega
    · obtain ⟨lowerR, upperR, hadjR, hiR, _, hupperR⟩ := hinteriorR
      have hupper : upperL = upperR := by
        apply Fin.ext
        have hval := congrArg Fin.val (hiL.symm.trans hiR)
        simpa using hval
      subst upperR
      exact (mem_rightPositions_iff_not_mem_leftPositions s upperL).mp hupperR hupperL

noncomputable def boundarySumToNonmixed :
    LeftBoundaryFace p (q + 1) ⊕ RightBoundaryFace (p + 1) q →
      NonmixedBoundaryFace (p + 1) (q + 1)
  | Sum.inl x => ⟨x.1, isLeftBoundary_not_isMixedBoundary x.2⟩
  | Sum.inr x => ⟨x.1, isRightBoundary_not_isMixedBoundary x.2⟩

noncomputable def nonmixedBoundaryEquiv :
    LeftBoundaryFace p (q + 1) ⊕ RightBoundaryFace (p + 1) q ≃
      NonmixedBoundaryFace (p + 1) (q + 1) :=
  Equiv.ofBijective boundarySumToNonmixed ⟨by
    intro x y h
    rcases x with x | x <;> rcases y with y | y
    · apply congrArg Sum.inl
      apply Subtype.ext
      simpa [boundarySumToNonmixed] using congrArg Subtype.val h
    · exfalso
      have hval : x.1 = y.1 := by
        simpa [boundarySumToNonmixed] using congrArg Subtype.val h
      have hr := y.2
      rw [← hval] at hr
      exact isLeftBoundary_not_isRightBoundary x.2 hr
    · exfalso
      have hval : x.1 = y.1 := by
        simpa [boundarySumToNonmixed] using congrArg Subtype.val h
      have hl := y.2
      rw [← hval] at hl
      exact isLeftBoundary_not_isRightBoundary hl x.2
    · apply congrArg Sum.inr
      apply Subtype.ext
      simpa [boundarySumToNonmixed] using congrArg Subtype.val h,
    by
      rintro ⟨⟨s, i⟩, h⟩
      rcases (not_isMixedBoundary_iff_isLeftBoundary_or_isRightBoundary s i).mp h with hl | hr
      · refine ⟨Sum.inl ⟨(s, i), hl⟩, rfl⟩
      · refine ⟨Sum.inr ⟨(s, i), hr⟩, rfl⟩⟩

@[simp]
theorem nonmixedBoundaryEquiv_inl_val
    (x : LeftBoundaryFace p (q + 1)) :
    (nonmixedBoundaryEquiv (p := p) (q := q) (Sum.inl x)).1 = x.1 := by
  rfl

@[simp]
theorem nonmixedBoundaryEquiv_inr_val
    (x : RightBoundaryFace (p + 1) q) :
    (nonmixedBoundaryEquiv (p := p) (q := q) (Sum.inr x)).1 = x.1 := by
  rfl

theorem mem_leftPositions_of_right_zero (s : Shuffle p 0)
    (k : Fin (p + 0)) : k ∈ s.leftPositions := by
  by_contra hk
  have hr := (mem_rightPositions_iff_not_mem_leftPositions s k).mpr hk
  rw [mem_rightPositions_iff] at hr
  obtain ⟨j, _⟩ := hr
  exact Fin.elim0 j

theorem mem_rightPositions_of_left_zero (s : Shuffle 0 q)
    (k : Fin (0 + q)) : k ∈ s.rightPositions := by
  apply (mem_rightPositions_iff_not_mem_leftPositions s k).mpr
  intro hl
  rw [mem_leftPositions_iff] at hl
  obtain ⟨i, _⟩ := hl
  exact Fin.elim0 i

theorem isLeftBoundary_of_right_zero
    (s : Shuffle (p + 1) 0) (i : Fin ((p + 1) + 0 + 1)) :
    IsLeftBoundary s i := by
  cases i using Fin.cases with
  | zero =>
      exact Or.inl ⟨rfl, mem_leftPositions_of_right_zero s 0⟩
  | succ a =>
      cases a using Fin.lastCases with
      | last =>
          right
          left
          refine ⟨?_, mem_leftPositions_of_right_zero s _⟩
          rfl
      | cast k =>
          right
          right
          exact ⟨k.castSucc, k.succ, by simp, rfl,
            mem_leftPositions_of_right_zero s _,
            mem_leftPositions_of_right_zero s _⟩

theorem isRightBoundary_of_left_zero
    (s : Shuffle 0 (q + 1)) (i : Fin (0 + (q + 1) + 1)) :
    IsRightBoundary s i := by
  cases i using Fin.cases with
  | zero =>
      exact Or.inl ⟨rfl, mem_rightPositions_of_left_zero s 0⟩
  | succ a =>
      cases a using Fin.lastCases with
      | last =>
          right
          left
          refine ⟨?_, mem_rightPositions_of_left_zero s _⟩
          rfl
      | cast k =>
          right
          right
          exact ⟨k.castSucc, k.succ, by simp, rfl,
            mem_rightPositions_of_left_zero s _,
            mem_rightPositions_of_left_zero s _⟩

noncomputable def leftBoundaryEquivNonmixedRightZero :
    LeftBoundaryFace p 0 ≃ NonmixedBoundaryFace (p + 1) 0 where
  toFun x := ⟨x.1, isLeftBoundary_not_isMixedBoundary x.2⟩
  invFun x := ⟨x.1, isLeftBoundary_of_right_zero x.1.1 x.1.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

noncomputable def rightBoundaryEquivNonmixedLeftZero :
    RightBoundaryFace 0 q ≃ NonmixedBoundaryFace 0 (q + 1) where
  toFun x := ⟨x.1, isRightBoundary_not_isMixedBoundary x.2⟩
  invFun x := ⟨x.1, isRightBoundary_of_left_zero x.1.1 x.1.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

@[simp]
theorem leftBoundaryEquivNonmixedRightZero_apply_val
    (x : LeftBoundaryFace p 0) :
    (leftBoundaryEquivNonmixedRightZero (p := p) x).1 = x.1 := by
  rfl

@[simp]
theorem rightBoundaryEquivNonmixedLeftZero_apply_val
    (x : RightBoundaryFace 0 q) :
    (rightBoundaryEquivNonmixedLeftZero (q := q) x).1 = x.1 := by
  rfl

theorem sum_nonmixedBoundaryFaces_positive
    {A : Type*} [AddCommGroup A]
    (f : Shuffle (p + 1) (q + 1) →
      Fin ((p + 1) + (q + 1) + 1) → A) :
    ∑ z ∈ nonmixedBoundaryFaces (p + 1) (q + 1), f z.1 z.2 =
      (∑ x : Fin (p + 2) × Shuffle p (q + 1),
        f (leftBoundaryPair x).1 (leftBoundaryPair x).2) +
      ∑ x : Fin (q + 2) × Shuffle (p + 1) q,
        f (rightBoundaryPair x).1 (rightBoundaryPair x).2 := by
  classical
  rw [nonmixedBoundaryFaces, ← Finset.sum_subtype_eq_sum_filter]
  rw [Finset.subtype_univ]
  rw [← Fintype.sum_equiv nonmixedBoundaryEquiv
    (fun x : LeftBoundaryFace p (q + 1) ⊕ RightBoundaryFace (p + 1) q =>
      match x with
      | Sum.inl z => f z.1.1 z.1.2
      | Sum.inr z => f z.1.1 z.1.2)
    (fun z : NonmixedBoundaryFace (p + 1) (q + 1) => f z.1.1 z.1.2)
    (fun x => by rcases x with x | x <;> rfl)]
  rw [Fintype.sum_sum_type]
  congr 1
  · rw [← Fintype.sum_equiv leftBoundaryEquiv
      (fun x : Fin (p + 2) × Shuffle p (q + 1) =>
        f (leftBoundaryPair x).1 (leftBoundaryPair x).2)
      (fun z : LeftBoundaryFace p (q + 1) => f z.1.1 z.1.2)
      (fun x => by rw [leftBoundaryEquiv_apply_val])]
  · rw [← Fintype.sum_equiv rightBoundaryEquiv
      (fun x : Fin (q + 2) × Shuffle (p + 1) q =>
        f (rightBoundaryPair x).1 (rightBoundaryPair x).2)
      (fun z : RightBoundaryFace (p + 1) q => f z.1.1 z.1.2)
      (fun x => by rw [rightBoundaryEquiv_apply_val])]

theorem sum_nonmixedBoundaryFaces_right_zero
    {A : Type*} [AddCommGroup A]
    (f : Shuffle (p + 1) 0 → Fin ((p + 1) + 0 + 1) → A) :
    ∑ z ∈ nonmixedBoundaryFaces (p + 1) 0, f z.1 z.2 =
      ∑ x : Fin (p + 2) × Shuffle p 0,
        f (leftBoundaryPair x).1 (leftBoundaryPair x).2 := by
  classical
  rw [nonmixedBoundaryFaces, ← Finset.sum_subtype_eq_sum_filter]
  rw [Finset.subtype_univ]
  rw [← Fintype.sum_equiv leftBoundaryEquivNonmixedRightZero
    (fun z : LeftBoundaryFace p 0 => f z.1.1 z.1.2)
    (fun z : NonmixedBoundaryFace (p + 1) 0 => f z.1.1 z.1.2)
    (fun _ => rfl)]
  rw [← Fintype.sum_equiv leftBoundaryEquiv
    (fun x : Fin (p + 2) × Shuffle p 0 =>
      f (leftBoundaryPair x).1 (leftBoundaryPair x).2)
    (fun z : LeftBoundaryFace p 0 => f z.1.1 z.1.2)
    (fun x => by rw [leftBoundaryEquiv_apply_val])]

theorem sum_nonmixedBoundaryFaces_left_zero
    {A : Type*} [AddCommGroup A]
    (f : Shuffle 0 (q + 1) → Fin (0 + (q + 1) + 1) → A) :
    ∑ z ∈ nonmixedBoundaryFaces 0 (q + 1), f z.1 z.2 =
      ∑ x : Fin (q + 2) × Shuffle 0 q,
        f (rightBoundaryPair x).1 (rightBoundaryPair x).2 := by
  classical
  rw [nonmixedBoundaryFaces, ← Finset.sum_subtype_eq_sum_filter]
  rw [Finset.subtype_univ]
  rw [← Fintype.sum_equiv rightBoundaryEquivNonmixedLeftZero
    (fun z : RightBoundaryFace 0 q => f z.1.1 z.1.2)
    (fun z : NonmixedBoundaryFace 0 (q + 1) => f z.1.1 z.1.2)
    (fun _ => rfl)]
  rw [← Fintype.sum_equiv rightBoundaryEquiv
    (fun x : Fin (q + 2) × Shuffle 0 q =>
      f (rightBoundaryPair x).1 (rightBoundaryPair x).2)
    (fun z : RightBoundaryFace 0 q => f z.1.1 z.1.2)
    (fun x => by rw [rightBoundaryEquiv_apply_val])]

end AlgebraicTopology.EilenbergZilber.Shuffle
