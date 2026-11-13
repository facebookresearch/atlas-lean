/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexHorizontalFineRowProfile










open Finset

namespace StatMech.FrontierD

noncomputable section



abbrev SixVertexHorizontalBoundedSingleRowProfile (T : EvenTorus) :=
  Fin T.height -> Fin (T.width + 1) × Fin (T.width + 1)

def sixVertexHorizontalBoundedSingleRowProfile
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    SixVertexHorizontalBoundedSingleRowProfile T :=
  fun j =>
    (⟨sixVertexHorizontalRowNontransitionCount horizontal j,
      Nat.lt_succ_of_le
        (sixVertexHorizontalRowNontransitionCount_le_width horizontal j)⟩,
     ⟨sixVertexHorizontalRowZeroCount horizontal j,
      Nat.lt_succ_of_le
        (sixVertexHorizontalRowZeroCount_le_width horizontal j)⟩)


def sixVertexHorizontalAddSingleRowProfiles
    {T : EvenTorus}
    (first second : SixVertexHorizontalBoundedSingleRowProfile T) :
    SixVertexHorizontalBoundedFineRowProfile T :=
  fun j =>
    (⟨(first j).1.val + (second j).1.val, by
        have hfirst := (first j).1.isLt
        have hsecond := (second j).1.isLt
        omega⟩,
     ⟨(first j).2.val + (second j).2.val, by
        have hfirst := (first j).2.isLt
        have hsecond := (second j).2.isLt
        omega⟩)

theorem sixVertexHorizontalPairBoundedFineRowProfile_eq_add
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    sixVertexHorizontalPairBoundedFineRowProfile horizontal =
      sixVertexHorizontalAddSingleRowProfiles
        (sixVertexHorizontalBoundedSingleRowProfile horizontal.1)
        (sixVertexHorizontalBoundedSingleRowProfile horizontal.2) := by
  funext j
  apply Prod.ext <;> apply Fin.ext <;> rfl


def sixVertexHorizontalFineRowProfileGrade
    {T : EvenTorus} (profile : SixVertexHorizontalBoundedFineRowProfile T) :
    Nat × Nat :=
  (∑ j : Fin T.height, (profile j).1.val,
    2 * ∑ j : Fin T.height, (profile j).2.val)


def sixVertexHorizontalFineRowProfileRowZero
    {T : EvenTorus} (profile : SixVertexHorizontalBoundedFineRowProfile T) :
    SixVertexHorizontalRowZeroProfile T :=
  fun j => (profile j).2.val

theorem sixVertexHorizontalPairBigrade_eq_fineRowProfileGrade
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    sixVertexHorizontalPairBigrade horizontal =
      sixVertexHorizontalFineRowProfileGrade
        (sixVertexHorizontalPairBoundedFineRowProfile horizontal) := by
  apply Prod.ext
  · rw [sixVertexHorizontalFineRowProfileGrade]
    change sixVertexHorizontalNontransitionCount horizontal.1 +
        sixVertexHorizontalNontransitionCount horizontal.2 =
      ∑ j : Fin T.height,
        sixVertexHorizontalPairRowNontransitionProfile horizontal j
    exact (sum_sixVertexHorizontalPairRowNontransitionProfile horizontal).symm
  · rw [sixVertexHorizontalFineRowProfileGrade]
    change 2 * (sixVertexHorizontalZeroCount horizontal.1 +
        sixVertexHorizontalZeroCount horizontal.2) =
      2 * ∑ j : Fin T.height,
        sixVertexHorizontalPairRowZeroProfile horizontal j
    rw [sum_sixVertexHorizontalPairRowZeroProfile]

theorem sixVertexHorizontalPairRowZeroProfile_eq_fineRowProfileRowZero
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    sixVertexHorizontalPairRowZeroProfile horizontal =
      sixVertexHorizontalFineRowProfileRowZero
        (sixVertexHorizontalPairBoundedFineRowProfile horizontal) := by
  rfl


def sixVertexHorizontalSingleRowProfileSectorSum
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (profile : SixVertexHorizontalBoundedSingleRowProfile T) : Nat :=
  ∑ horizontal : SixVertexHorizontalField T,
    if sixVertexHorizontalBoundedSingleRowProfile horizontal = profile then
      sixVertexHorizontalSectorCompletionChooseCount T sector horizontal
    else 0


def sixVertexHorizontalFineRowProfileSectorPairSum
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (profile : SixVertexHorizontalBoundedFineRowProfile T) : Nat :=
  ∑ horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T,
    if sixVertexHorizontalPairBoundedFineRowProfile horizontal = profile then
      sixVertexHorizontalSectorCompletionChooseCount T left horizontal.1 *
        sixVertexHorizontalSectorCompletionChooseCount T right horizontal.2
    else 0

private theorem finite_pair_fiber_factorization
    {A B P Q R S : Type*}
    [Fintype A] [Fintype B] [Fintype P] [Fintype Q]
    [DecidableEq P] [DecidableEq Q] [DecidableEq R]
    [CommSemiring S]
    (leftProfile : A -> P) (rightProfile : B -> Q)
    (combine : P -> Q -> R) (target : R)
    (leftWeight : A -> S) (rightWeight : B -> S) :
    (∑ pair : A × B,
        if combine (leftProfile pair.1) (rightProfile pair.2) = target
        then leftWeight pair.1 * rightWeight pair.2 else 0) =
      ∑ left : P, ∑ right : Q,
        if combine left right = target then
          (∑ a : A, if leftProfile a = left then leftWeight a else 0) *
            (∑ b : B, if rightProfile b = right then rightWeight b else 0)
        else 0 := by
  classical
  let kernel := fun (profile : P × Q) (pair : A × B) =>
    if profile.1 = leftProfile pair.1 then
      if profile.2 = rightProfile pair.2 then
        if combine profile.1 profile.2 = target then
          leftWeight pair.1 * rightWeight pair.2
        else 0
      else 0
    else 0
  have hpoint (pair : A × B) :
      (∑ profile : P × Q, kernel profile pair) =
        if combine (leftProfile pair.1) (rightProfile pair.2) = target
        then leftWeight pair.1 * rightWeight pair.2 else 0 := by
    rw [Fintype.sum_prod_type]
    simp [kernel]
  calc
    _ = ∑ pair : A × B, ∑ profile : P × Q, kernel profile pair := by
      apply Finset.sum_congr rfl
      intro pair hpair
      exact (hpoint pair).symm
    _ = ∑ profile : P × Q, ∑ pair : A × B, kernel profile pair :=
      Finset.sum_comm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro left hleft
      apply Finset.sum_congr rfl
      intro right hright
      by_cases hcombine : combine left right = target
      · simp_rw [kernel, hcombine, if_pos]
        rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
        simp only [eq_comm, ite_mul, mul_ite, zero_mul, mul_zero]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        by_cases hleftProfile : leftProfile a = left <;>
          by_cases hrightProfile : rightProfile b = right <;>
          simp_all only [eq_comm, if_true, if_false]
      · simp [kernel, hcombine]


theorem sixVertexHorizontalFineRowProfileSectorPairSum_eq_convolution
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (profile : SixVertexHorizontalBoundedFineRowProfile T) :
    sixVertexHorizontalFineRowProfileSectorPairSum T left right profile =
      ∑ first : SixVertexHorizontalBoundedSingleRowProfile T,
        ∑ second : SixVertexHorizontalBoundedSingleRowProfile T,
          if sixVertexHorizontalAddSingleRowProfiles first second = profile then
            sixVertexHorizontalSingleRowProfileSectorSum T left first *
              sixVertexHorizontalSingleRowProfileSectorSum T right second
          else 0 := by
  classical
  unfold sixVertexHorizontalFineRowProfileSectorPairSum
    sixVertexHorizontalSingleRowProfileSectorSum
  simp_rw [sixVertexHorizontalPairBoundedFineRowProfile_eq_add]
  exact finite_pair_fiber_factorization
    sixVertexHorizontalBoundedSingleRowProfile
    sixVertexHorizontalBoundedSingleRowProfile
    sixVertexHorizontalAddSingleRowProfiles profile
    (sixVertexHorizontalSectorCompletionChooseCount T left)
    (sixVertexHorizontalSectorCompletionChooseCount T right)



def sixVertexHorizontalFineRowProfileSignedSum
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (profile : SixVertexHorizontalBoundedFineRowProfile T) : Int :=
  (sixVertexHorizontalFineRowProfileSectorPairSum
      T targetLeft targetRight profile : Int) -
    sixVertexHorizontalFineRowProfileSectorPairSum
      T sourceLeft sourceRight profile



theorem sixVertexHorizontalFineRowProfileSignedSum_eq_minorConvolution
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (profile : SixVertexHorizontalBoundedFineRowProfile T) :
    sixVertexHorizontalFineRowProfileSignedSum T
        sourceLeft sourceRight targetLeft targetRight profile =
      ∑ first : SixVertexHorizontalBoundedSingleRowProfile T,
        ∑ second : SixVertexHorizontalBoundedSingleRowProfile T,
          if sixVertexHorizontalAddSingleRowProfiles first second = profile then
            (sixVertexHorizontalSingleRowProfileSectorSum
                T targetLeft first : Int) *
                sixVertexHorizontalSingleRowProfileSectorSum
                  T targetRight second -
              (sixVertexHorizontalSingleRowProfileSectorSum
                  T sourceLeft first : Int) *
                sixVertexHorizontalSingleRowProfileSectorSum
                  T sourceRight second
          else 0 := by
  unfold sixVertexHorizontalFineRowProfileSignedSum
  rw [sixVertexHorizontalFineRowProfileSectorPairSum_eq_convolution,
    sixVertexHorizontalFineRowProfileSectorPairSum_eq_convolution,
    Nat.cast_sum, Nat.cast_sum]
  simp_rw [Nat.cast_sum, Nat.cast_ite, Nat.cast_mul, Nat.cast_zero]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro first hfirst
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro second hsecond
  by_cases hprofile :
      sixVertexHorizontalAddSingleRowProfiles first second = profile <;>
    simp [hprofile]



theorem sixVertexHorizontalFineRowProfileSignedSum_eq_kernelSum
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (profile : SixVertexHorizontalBoundedFineRowProfile T) :
    sixVertexHorizontalFineRowProfileSignedSum T
        sourceLeft sourceRight targetLeft targetRight profile =
      ∑ horizontal : SixVertexHorizontalField T ×
          SixVertexHorizontalField T,
        if sixVertexHorizontalPairBoundedFineRowProfile horizontal = profile
        then sixVertexHorizontalProfileSignedKernel
          sourceLeft sourceRight targetLeft targetRight
          (sixVertexHorizontalPairCompletionProfile T horizontal)
        else 0 := by
  unfold sixVertexHorizontalFineRowProfileSignedSum
    sixVertexHorizontalFineRowProfileSectorPairSum
    sixVertexHorizontalProfileSignedKernel
  simp_rw [Nat.cast_sum, Nat.cast_ite, Nat.cast_mul, Nat.cast_zero]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro horizontal hhorizontal
  by_cases hprofile :
      sixVertexHorizontalPairBoundedFineRowProfile horizontal = profile
  · simp only [hprofile, if_true]
    rw [← sixVertexHorizontalPairChooseWeight_eq_profile
        T targetLeft targetRight horizontal,
      ← sixVertexHorizontalPairChooseWeight_eq_profile
        T sourceLeft sourceRight horizontal]
    simp
  · simp [hprofile]

private theorem sum_subtype_indicator_eq_sum_indicator_of_imp
    {A : Type*} [Fintype A] (p q : A -> Prop)
    [DecidablePred p] [DecidablePred q]
    (hqp : forall x, q x -> p x) (f : A -> Int) :
    (∑ x : {x : A // p x}, if q x.1 then f x.1 else 0) =
      ∑ x : A, if q x then f x else 0 := by
  classical
  rw [← Finset.sum_subtype
    ((Finset.univ : Finset A).filter p) (by simp) (fun x =>
      if q x then f x else 0), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hq : q x
  · simp [hq, hqp x hq]
  · simp [hq]



theorem fineRowProfileSignedNonnegative_of_raw
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (hraw : forall profile : SixVertexHorizontalBoundedFineRowProfile T,
      0 <= sixVertexHorizontalFineRowProfileSignedSum T
        sourceLeft sourceRight targetLeft targetRight profile) :
    SixVertexHorizontalFineRowProfileAggregateSignedNonnegative T
      sourceLeft sourceRight targetLeft targetRight := by
  intro grade rowProfile profile
  by_cases hgrade :
      grade = sixVertexHorizontalFineRowProfileGrade profile
  · subst grade
    by_cases hrow :
        rowProfile = sixVertexHorizontalFineRowProfileRowZero profile
    · subst rowProfile
      have hrawProfile := hraw profile
      rw [sixVertexHorizontalFineRowProfileSignedSum_eq_kernelSum]
        at hrawProfile
      rw [Finset.sum_filter]
      let p := fun horizontal : SixVertexHorizontalField T ×
          SixVertexHorizontalField T =>
        sixVertexHorizontalPairBigrade horizontal =
            sixVertexHorizontalFineRowProfileGrade profile /\
          sixVertexHorizontalPairRowZeroProfile horizontal =
            sixVertexHorizontalFineRowProfileRowZero profile
      let q := fun horizontal : SixVertexHorizontalField T ×
          SixVertexHorizontalField T =>
        sixVertexHorizontalPairBoundedFineRowProfile horizontal = profile
      let f := fun horizontal : SixVertexHorizontalField T ×
          SixVertexHorizontalField T =>
        sixVertexHorizontalProfileSignedKernel
          sourceLeft sourceRight targetLeft targetRight
          (sixVertexHorizontalPairCompletionProfile T horizontal)
      have hqp : forall horizontal, q horizontal -> p horizontal := by
        intro horizontal hfine
        constructor
        · rw [sixVertexHorizontalPairBigrade_eq_fineRowProfileGrade,
            hfine]
        · rw [sixVertexHorizontalPairRowZeroProfile_eq_fineRowProfileRowZero,
            hfine]
      change 0 <= ∑ horizontal : {horizontal // p horizontal},
        if q horizontal.1 then f horizontal.1 else 0
      rw [sum_subtype_indicator_eq_sum_indicator_of_imp p q hqp f]
      exact hrawProfile
    · have hsum :
          (∑ horizontal ∈
            (Finset.univ : Finset
              (SixVertexHorizontalPairRowBigradeFiber T
                (sixVertexHorizontalFineRowProfileGrade profile)
                rowProfile)).filter
              (fun horizontal =>
                sixVertexHorizontalPairBoundedFineRowProfile horizontal.1 =
                  profile),
            sixVertexHorizontalProfileSignedKernel
              sourceLeft sourceRight targetLeft targetRight
              (sixVertexHorizontalPairCompletionProfile T horizontal.1)) = 0 := by
        apply Finset.sum_eq_zero
        intro horizontal hhorizontal
        have hfine := (Finset.mem_filter.mp hhorizontal).2
        have hforced :=
          sixVertexHorizontalPairRowZeroProfile_eq_fineRowProfileRowZero
            horizontal.1
        rw [hfine] at hforced
        exact False.elim (hrow (horizontal.2.2.symm.trans hforced))
      rw [hsum]
  · have hsum :
        (∑ horizontal ∈
          (Finset.univ : Finset
            (SixVertexHorizontalPairRowBigradeFiber T grade
              rowProfile)).filter
            (fun horizontal =>
              sixVertexHorizontalPairBoundedFineRowProfile horizontal.1 =
                profile),
          sixVertexHorizontalProfileSignedKernel
            sourceLeft sourceRight targetLeft targetRight
            (sixVertexHorizontalPairCompletionProfile T horizontal.1)) = 0 := by
      apply Finset.sum_eq_zero
      intro horizontal hhorizontal
      have hfine := (Finset.mem_filter.mp hhorizontal).2
      have hforced :=
        sixVertexHorizontalPairBigrade_eq_fineRowProfileGrade horizontal.1
      rw [hfine] at hforced
      exact False.elim (hgrade (horizontal.2.1.symm.trans hforced))
    rw [hsum]



theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_rawFineProfile
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hraw : forall profile : SixVertexHorizontalBoundedFineRowProfile T,
      0 <= sixVertexHorizontalFineRowProfileSignedSum T
        ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩
        middle middle profile) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_fineRowProfileSigned
    T middle hmiddle_pos hmiddle_lt
      (fineRowProfileSignedNonnegative_of_raw T
        ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩
        middle middle hraw)

end

end StatMech.FrontierD
