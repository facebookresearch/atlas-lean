/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexHorizontalProfileSign










open Finset

namespace StatMech.FrontierD

noncomputable section

local instance sixVertexHorizontalProfileReflectionPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p

def sixVertexCyclicNeg {N : Nat} (hN : 0 < N) (i : Fin N) : Fin N :=
  if hi : i.val = 0 then ⟨0, hN⟩ else
    ⟨N - i.val, Nat.sub_lt hN (Nat.pos_of_ne_zero hi)⟩

@[simp] theorem sixVertexCyclicNeg_zero {N : Nat} (hN : 0 < N) :
    sixVertexCyclicNeg hN (⟨0, hN⟩ : Fin N) = ⟨0, hN⟩ := by
  simp [sixVertexCyclicNeg]

theorem sixVertexCyclicNeg_val_of_ne_zero
    {N : Nat} (hN : 0 < N) (i : Fin N) (hi : i.val ≠ 0) :
    (sixVertexCyclicNeg hN i).val = N - i.val := by
  simp [sixVertexCyclicNeg, hi]

theorem sixVertexCyclicNeg_involutive {N : Nat} (hN : 0 < N) :
    Function.Involutive (sixVertexCyclicNeg hN) := by
  intro i
  by_cases hi : i.val = 0
  · have hieq : i = ⟨0, hN⟩ := Fin.ext hi
    subst i
    simp
  · have hval := sixVertexCyclicNeg_val_of_ne_zero hN i hi
    have hneg0 : (sixVertexCyclicNeg hN i).val ≠ 0 := by
      rw [hval]
      omega
    apply Fin.ext
    rw [sixVertexCyclicNeg_val_of_ne_zero hN _ hneg0, hval]
    omega

def sixVertexCyclicNegEquiv {N : Nat} (hN : 0 < N) : Fin N ≃ Fin N :=
  { toFun := sixVertexCyclicNeg hN
    invFun := sixVertexCyclicNeg hN
    left_inv := sixVertexCyclicNeg_involutive hN
    right_inv := sixVertexCyclicNeg_involutive hN }

theorem sixVertexCyclicNeg_even_iff
    {N : Nat} (hN : 0 < N) (hEven : Even N) (i : Fin N) :
    Even (sixVertexCyclicNeg hN i).val ↔ Even i.val := by
  by_cases hi : i.val = 0
  · have hieq : i = ⟨0, hN⟩ := Fin.ext hi
    subst i
    simp
  · rw [sixVertexCyclicNeg_val_of_ne_zero hN i hi,
      Nat.even_sub (Nat.le_of_lt i.isLt)]
    simp [hEven]

theorem sixVertexCyclicNeg_cyclicPred
    {N : Nat} (hN : 0 < N) (i : Fin N) :
    sixVertexCyclicNeg hN (SixVertexArrows.cyclicPred hN i) =
      finitePeriodicSucc hN (sixVertexCyclicNeg hN i) := by
  apply Fin.ext
  by_cases hN1 : N = 1
  · subst N
    simp [sixVertexCyclicNeg, SixVertexArrows.cyclicPred,
      finitePeriodicSucc]
  · have hNtwo : 2 ≤ N := by omega
    by_cases hi0 : i.val = 0
    · have hpredVal :
          (SixVertexArrows.cyclicPred hN i).val = N - 1 := by
        change (i.val + N - 1) % N = N - 1
        rw [hi0]
        simp
      have hpredNe :
          (SixVertexArrows.cyclicPred hN i).val ≠ 0 := by
        rw [hpredVal]
        omega
      rw [sixVertexCyclicNeg_val_of_ne_zero hN _ hpredNe,
        hpredVal]
      unfold finitePeriodicSucc
      simp only
      have hnegZero : (sixVertexCyclicNeg hN i).val = 0 := by
        have hieq : i = ⟨0, hN⟩ := Fin.ext hi0
        subst i
        simp
      rw [hnegZero, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
      omega
    · have hiPos : 0 < i.val := Nat.pos_of_ne_zero hi0
      have hpredVal :
          (SixVertexArrows.cyclicPred hN i).val = i.val - 1 := by
        unfold SixVertexArrows.cyclicPred
        simp only
        rw [show i.val + N - 1 = N + (i.val - 1) by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      by_cases hi1 : i.val = 1
      · have hpredZero :
            SixVertexArrows.cyclicPred hN i = ⟨0, hN⟩ := by
          apply Fin.ext
          rw [hpredVal, hi1]
        rw [hpredZero, sixVertexCyclicNeg_zero]
        unfold finitePeriodicSucc
        change 0 = ((sixVertexCyclicNeg hN i).val + 1) % N
        rw [sixVertexCyclicNeg_val_of_ne_zero hN i hi0, hi1]
        rw [show N - 1 + 1 = N by omega, Nat.mod_self]
      · have hpredNe :
            (SixVertexArrows.cyclicPred hN i).val ≠ 0 := by
          rw [hpredVal]
          omega
        rw [sixVertexCyclicNeg_val_of_ne_zero hN _ hpredNe,
          hpredVal]
        unfold finitePeriodicSucc
        change N - (i.val - 1) =
          ((sixVertexCyclicNeg hN i).val + 1) % N
        rw [sixVertexCyclicNeg_val_of_ne_zero hN i hi0]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega

def sixVertexReflectHorizontalField
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    SixVertexHorizontalField T :=
  fun v => horizontal (sixVertexCyclicNeg T.width_pos v.1, v.2)

theorem fkMedialVertexParity_cyclicNeg
    {T : EvenTorus} (v : T.Vertex) :
    fkMedialVertexParity (sixVertexCyclicNeg T.width_pos v.1, v.2) =
      fkMedialVertexParity v := by
  unfold fkMedialVertexParity
  have hEven := sixVertexCyclicNeg_even_iff
    T.width_pos T.width_even v.1
  have hdecide : decide (Even (sixVertexCyclicNeg T.width_pos v.1).val) =
      decide (Even v.1.val) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using hEven
  rw [hdecide]

theorem sixVertexHorizontalGaugeBit_reflect
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T)
    (v : T.Vertex) :
    sixVertexHorizontalGaugeBit
        (sixVertexReflectHorizontalField horizontal) v =
      sixVertexHorizontalGaugeBit horizontal
        (sixVertexCyclicNeg T.width_pos v.1, v.2) := by
  unfold sixVertexHorizontalGaugeBit sixVertexReflectHorizontalField
  rw [fkMedialVertexParity_cyclicNeg]

theorem sixVertexHorizontalZeroCount_reflect
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    sixVertexHorizontalZeroCount
        (sixVertexReflectHorizontalField horizontal) =
      sixVertexHorizontalZeroCount horizontal := by
  let vertexEquiv : T.Vertex ≃ T.Vertex :=
    { toFun := fun v => (sixVertexCyclicNeg T.width_pos v.1, v.2)
      invFun := fun v => (sixVertexCyclicNeg T.width_pos v.1, v.2)
      left_inv := fun v => by
        apply Prod.ext
        · exact sixVertexCyclicNeg_involutive T.width_pos v.1
        · rfl
      right_inv := fun v => by
        apply Prod.ext
        · exact sixVertexCyclicNeg_involutive T.width_pos v.1
        · rfl }
  unfold sixVertexHorizontalZeroCount
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv vertexEquiv
  intro v
  change sixVertexHorizontalGaugeBit
      (sixVertexReflectHorizontalField horizontal) v = false ↔
    sixVertexHorizontalGaugeBit horizontal (vertexEquiv v) = false
  rw [sixVertexHorizontalGaugeBit_reflect]
  rfl

theorem sixVertexHorizontalNontransitionCount_reflect
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    sixVertexHorizontalNontransitionCount
        (sixVertexReflectHorizontalField horizontal) =
      sixVertexHorizontalNontransitionCount horizontal := by
  let xEquiv : Fin T.width ≃ Fin T.width :=
    (sixVertexCyclicNegEquiv T.width_pos).trans
      (svFinitePeriodicSuccEquiv T.width_pos)
  let vertexEquiv : T.Vertex ≃ T.Vertex :=
    xEquiv.prodCongr (Equiv.refl _)
  unfold sixVertexHorizontalNontransitionCount
  calc
    (∑ v : T.Vertex,
      if sixVertexHorizontalGaugeBit
            (sixVertexReflectHorizontalField horizontal)
            (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) =
          sixVertexHorizontalGaugeBit
            (sixVertexReflectHorizontalField horizontal) v
      then 1 else 0) =
        ∑ v : T.Vertex,
          if sixVertexHorizontalGaugeBit horizontal
                (SixVertexArrows.cyclicPred T.width_pos
                  (vertexEquiv v).1, (vertexEquiv v).2) =
              sixVertexHorizontalGaugeBit horizontal (vertexEquiv v)
          then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [sixVertexHorizontalGaugeBit_reflect,
        sixVertexHorizontalGaugeBit_reflect]
      have hnegPred := sixVertexCyclicNeg_cyclicPred
        T.width_pos v.1
      have hpredSucc := svCyclicPred_finitePeriodicSucc
        T.width_pos (sixVertexCyclicNeg T.width_pos v.1)
      change (if sixVertexHorizontalGaugeBit horizontal
            (sixVertexCyclicNeg T.width_pos
              (SixVertexArrows.cyclicPred T.width_pos v.1), v.2) =
          sixVertexHorizontalGaugeBit horizontal
            (sixVertexCyclicNeg T.width_pos v.1, v.2)
        then 1 else 0) = _
      rw [hnegPred]
      have hvertex : vertexEquiv v =
          (finitePeriodicSucc T.width_pos
            (sixVertexCyclicNeg T.width_pos v.1), v.2) := by
        rfl
      rw [hvertex, hpredSucc]
      simp only [eq_comm]
    _ = _ := by
      exact vertexEquiv.sum_comp fun v =>
        if sixVertexHorizontalGaugeBit horizontal
              (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) =
            sixVertexHorizontalGaugeBit horizontal v
        then 1 else 0

def sixVertexReflectHorizontalPair
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    SixVertexHorizontalField T × SixVertexHorizontalField T :=
  (sixVertexReflectHorizontalField horizontal.1,
    sixVertexReflectHorizontalField horizontal.2)

theorem sixVertexReflectHorizontalPair_involutive
    {T : EvenTorus} :
    Function.Involutive (sixVertexReflectHorizontalPair (T := T)) := by
  intro horizontal
  apply Prod.ext <;> funext v
  · apply congrArg horizontal.1
    apply Prod.ext
    · exact sixVertexCyclicNeg_involutive T.width_pos v.1
    · rfl
  · apply congrArg horizontal.2
    apply Prod.ext
    · exact sixVertexCyclicNeg_involutive T.width_pos v.1
    · rfl

theorem sixVertexHorizontalPairBigrade_reflect
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    sixVertexHorizontalPairBigrade
        (sixVertexReflectHorizontalPair horizontal) =
      sixVertexHorizontalPairBigrade horizontal := by
  unfold sixVertexHorizontalPairBigrade sixVertexReflectHorizontalPair
  rw [sixVertexHorizontalNontransitionCount_reflect,
    sixVertexHorizontalNontransitionCount_reflect,
    sixVertexHorizontalZeroCount_reflect,
    sixVertexHorizontalZeroCount_reflect]

theorem sixVertexHorizontalColumnSeamAllowed_reflect_false_iff
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T)
    (i : Fin T.width) :
    sixVertexHorizontalColumnSeamAllowed
        (sixVertexReflectHorizontalField horizontal) i false ↔
      sixVertexHorizontalColumnSeamAllowed horizontal
        (finitePeriodicSucc T.width_pos
          (sixVertexCyclicNeg T.width_pos i)) true := by
  rw [sixVertexHorizontalColumnSeamAllowed_false_iff_forward,
    sixVertexHorizontalColumnSeamAllowed_true_iff_backward]
  unfold sixVertexReflectHorizontalField
  change SixVertexForwardInterlaced
      (fun j => horizontal
        (sixVertexCyclicNeg T.width_pos
          (SixVertexArrows.cyclicPred T.width_pos i), j))
      (fun j => horizontal (sixVertexCyclicNeg T.width_pos i, j)) ↔
    SixVertexForwardInterlaced
      (fun j => horizontal
        (finitePeriodicSucc T.width_pos
          (sixVertexCyclicNeg T.width_pos i), j))
      (fun j => horizontal
        (SixVertexArrows.cyclicPred T.width_pos
          (finitePeriodicSucc T.width_pos
            (sixVertexCyclicNeg T.width_pos i)), j))
  rw [sixVertexCyclicNeg_cyclicPred,
    svCyclicPred_finitePeriodicSucc]

theorem sixVertexHorizontalColumnSeamAllowed_reflect_true_iff
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T)
    (i : Fin T.width) :
    sixVertexHorizontalColumnSeamAllowed
        (sixVertexReflectHorizontalField horizontal) i true ↔
      sixVertexHorizontalColumnSeamAllowed horizontal
        (finitePeriodicSucc T.width_pos
          (sixVertexCyclicNeg T.width_pos i)) false := by
  rw [sixVertexHorizontalColumnSeamAllowed_true_iff_backward,
    sixVertexHorizontalColumnSeamAllowed_false_iff_forward]
  unfold sixVertexReflectHorizontalField
  change SixVertexForwardInterlaced
      (fun j => horizontal (sixVertexCyclicNeg T.width_pos i, j))
      (fun j => horizontal
        (sixVertexCyclicNeg T.width_pos
          (SixVertexArrows.cyclicPred T.width_pos i), j)) ↔
    SixVertexForwardInterlaced
      (fun j => horizontal
        (SixVertexArrows.cyclicPred T.width_pos
          (finitePeriodicSucc T.width_pos
            (sixVertexCyclicNeg T.width_pos i)), j))
      (fun j => horizontal
        (finitePeriodicSucc T.width_pos
          (sixVertexCyclicNeg T.width_pos i), j))
  rw [sixVertexCyclicNeg_cyclicPred,
    svCyclicPred_finitePeriodicSucc]

def sixVertexHorizontalFalseForcedColumns
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    Finset (Fin T.width) :=
  Finset.univ.filter fun i =>
    sixVertexHorizontalColumnSeamAllowed horizontal i false ∧
      Not (sixVertexHorizontalColumnSeamAllowed horizontal i true)

theorem sixVertexHorizontalFalseForcedColumns_eq_compl_trueAllowed
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (completion : SixVertexVerticalCompletion T horizontal) :
    sixVertexHorizontalFalseForcedColumns horizontal =
      Finset.univ \ sixVertexHorizontalTrueAllowedColumns horizontal := by
  ext i
  simp only [sixVertexHorizontalFalseForcedColumns, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_sdiff,
    sixVertexHorizontalTrueAllowedColumns]
  constructor
  · rintro ⟨hfalse, hnotTrue⟩
    exact hnotTrue
  · intro hnotAllowed
    rcases sixVertexHorizontalColumnSeamAllowed_false_or_true completion i with
      hfalse | htrue
    · exact ⟨hfalse, hnotAllowed⟩
    · exact (hnotAllowed htrue).elim

theorem sixVertexVerticalCompletion_reflect
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (completion : SixVertexVerticalCompletion T horizontal) :
    Nonempty (SixVertexVerticalCompletion T
      (sixVertexReflectHorizontalField horizontal)) := by
  refine ⟨sixVertexVerticalCompletionOfColumns (fun i => ?_)⟩
  let k := finitePeriodicSucc T.width_pos
    (sixVertexCyclicNeg T.width_pos i)
  apply Classical.choice
  change Nonempty
    (SixVertexVerticalColumnCompletion T
      (sixVertexReflectHorizontalField horizontal) i)
  rcases sixVertexHorizontalColumnSeamAllowed_false_or_true
      completion k with hfalse | htrue
  · have hreflected :
        sixVertexHorizontalColumnSeamAllowed
          (sixVertexReflectHorizontalField horizontal) i true :=
      (sixVertexHorizontalColumnSeamAllowed_reflect_true_iff
        horizontal i).2 hfalse
    exact ⟨(Classical.choice hreflected).1⟩
  · have hreflected :
        sixVertexHorizontalColumnSeamAllowed
          (sixVertexReflectHorizontalField horizontal) i false :=
      (sixVertexHorizontalColumnSeamAllowed_reflect_false_iff
        horizontal i).2 htrue
    exact ⟨(Classical.choice hreflected).1⟩

theorem sixVertexVerticalCompletion_reflect_iff
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    Nonempty (SixVertexVerticalCompletion T
        (sixVertexReflectHorizontalField horizontal)) ↔
      Nonempty (SixVertexVerticalCompletion T horizontal) := by
  constructor
  · rintro ⟨completion⟩
    have hreflected := sixVertexVerticalCompletion_reflect completion
    have hfield :
        sixVertexReflectHorizontalField
            (sixVertexReflectHorizontalField horizontal) = horizontal := by
      funext v
      apply congrArg horizontal
      apply Prod.ext
      · exact sixVertexCyclicNeg_involutive T.width_pos v.1
      · rfl
    rw [hfield] at hreflected
    exact hreflected
  · rintro ⟨completion⟩
    exact sixVertexVerticalCompletion_reflect completion

theorem card_sixVertexHorizontalFreeColumns_reflect
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    (sixVertexHorizontalFreeColumns
        (sixVertexReflectHorizontalField horizontal)).card =
      (sixVertexHorizontalFreeColumns horizontal).card := by
  let xEquiv : Fin T.width ≃ Fin T.width :=
    (sixVertexCyclicNegEquiv T.width_pos).trans
      (svFinitePeriodicSuccEquiv T.width_pos)
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv xEquiv
  intro i
  change i ∈ sixVertexHorizontalFreeColumns
      (sixVertexReflectHorizontalField horizontal) ↔
    xEquiv i ∈ sixVertexHorizontalFreeColumns horizontal
  simp only [sixVertexHorizontalFreeColumns, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [← sixVertexHorizontalColumnSeamAllowed_both_iff_free,
    ← sixVertexHorizontalColumnSeamAllowed_both_iff_free]
  rw [sixVertexHorizontalColumnSeamAllowed_reflect_false_iff,
    sixVertexHorizontalColumnSeamAllowed_reflect_true_iff]
  change (_ ∧ _) ↔
    (sixVertexHorizontalColumnSeamAllowed horizontal
        (finitePeriodicSucc T.width_pos
          (sixVertexCyclicNeg T.width_pos i)) false ∧
      sixVertexHorizontalColumnSeamAllowed horizontal
        (finitePeriodicSucc T.width_pos
          (sixVertexCyclicNeg T.width_pos i)) true)
  tauto

theorem card_sixVertexHorizontalForcedTrueColumns_reflect
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    (sixVertexHorizontalForcedTrueColumns
        (sixVertexReflectHorizontalField horizontal)).card =
      (sixVertexHorizontalFalseForcedColumns horizontal).card := by
  let xEquiv : Fin T.width ≃ Fin T.width :=
    (sixVertexCyclicNegEquiv T.width_pos).trans
      (svFinitePeriodicSuccEquiv T.width_pos)
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv xEquiv
  intro i
  simp only [sixVertexHorizontalForcedTrueColumns, Finset.mem_filter,
    sixVertexHorizontalTrueAllowedColumns, Finset.mem_univ, true_and,
    sixVertexHorizontalFalseForcedColumns]
  rw [sixVertexHorizontalColumnSeamAllowed_reflect_true_iff,
    sixVertexHorizontalColumnSeamAllowed_reflect_false_iff]
  rfl

theorem card_sixVertexHorizontalFalseForcedColumns
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (completion : SixVertexVerticalCompletion T horizontal) :
    (sixVertexHorizontalFalseForcedColumns horizontal).card =
      T.width - (sixVertexHorizontalFreeColumns horizontal).card -
        (sixVertexHorizontalForcedTrueColumns horizontal).card := by
  rw [sixVertexHorizontalFalseForcedColumns_eq_compl_trueAllowed completion,
    Finset.card_sdiff]
  have hInter :
      sixVertexHorizontalTrueAllowedColumns horizontal ∩ Finset.univ =
        sixVertexHorizontalTrueAllowedColumns horizontal :=
    Finset.inter_univ _
  rw [hInter, Finset.card_univ, Fintype.card_fin]
  have hsplit := Finset.card_sdiff_add_card_eq_card
    (sixVertexHorizontalForcedTrueColumns_subset_trueAllowed horizontal)
  rw [sixVertexHorizontalTrueAllowed_sdiff_forced_eq_freeColumns] at hsplit
  omega

def sixVertexReflectHorizontalCompletionProfile
    {T : EvenTorus} (profile : SixVertexHorizontalCompletionProfile T) :
    SixVertexHorizontalCompletionProfile T where
  forcedTrue :=
    if hvalid : profile.forcedTrue.val + profile.free.val <= T.width then
      ⟨T.width - profile.free.val - profile.forcedTrue.val,
        Nat.lt_succ_of_le (by omega)⟩
    else profile.forcedTrue
  free := profile.free

theorem sixVertexHorizontalCompletionProfile_ext
    {T : EvenTorus} {first second : SixVertexHorizontalCompletionProfile T}
    (hforced : first.forcedTrue = second.forcedTrue)
    (hfree : first.free = second.free) : first = second := by
  cases first
  cases second
  simp_all

theorem sixVertexReflectHorizontalCompletionProfile_involutive
    {T : EvenTorus} :
    Function.Involutive
      (sixVertexReflectHorizontalCompletionProfile (T := T)) := by
  intro profile
  apply sixVertexHorizontalCompletionProfile_ext
  · apply Fin.ext
    by_cases hvalid :
        profile.forcedTrue.val + profile.free.val <= T.width
    · have hreflectedValid :
          (T.width - profile.free.val - profile.forcedTrue.val) +
              profile.free.val <= T.width := by omega
      simp [sixVertexReflectHorizontalCompletionProfile, hvalid,
        hreflectedValid]
      omega
    · simp [sixVertexReflectHorizontalCompletionProfile, hvalid]
  · rfl

def sixVertexReflectOptionalHorizontalCompletionProfile
    {T : EvenTorus} :
    Option (SixVertexHorizontalCompletionProfile T) ->
      Option (SixVertexHorizontalCompletionProfile T)
  | none => none
  | some profile => some (sixVertexReflectHorizontalCompletionProfile profile)


def sixVertexHorizontalComplementSector
    (T : EvenTorus) (sector : Fin (T.width + 1)) : Fin (T.width + 1) :=
  ⟨T.width - sector.val, by omega⟩

@[simp] theorem sixVertexHorizontalComplementSector_involutive
    (T : EvenTorus) (sector : Fin (T.width + 1)) :
    sixVertexHorizontalComplementSector T
        (sixVertexHorizontalComplementSector T sector) = sector := by
  apply Fin.ext
  simp only [sixVertexHorizontalComplementSector]
  omega




theorem sixVertexHorizontalProfileChooseCount_reflect
    {T : EvenTorus} (sector : Fin (T.width + 1))
    (profile : SixVertexHorizontalCompletionProfile T)
    (hvalid : profile.forcedTrue.val + profile.free.val <= T.width) :
    sixVertexHorizontalProfileChooseCount sector
        (some (sixVertexReflectHorizontalCompletionProfile profile)) =
      sixVertexHorizontalProfileChooseCount
        (sixVertexHorizontalComplementSector T sector) (some profile) := by
  unfold sixVertexHorizontalProfileChooseCount
    sixVertexReflectHorizontalCompletionProfile
    sixVertexHorizontalComplementSector
  simp only [hvalid, dif_pos]
  by_cases hleft : T.width - profile.free.val -
      profile.forcedTrue.val <= sector.val
  · by_cases hright : profile.forcedTrue.val <=
        T.width - sector.val
    · rw [if_pos hleft, if_pos hright]
      apply Nat.choose_symm_of_eq_add
      omega
    · rw [if_pos hleft, if_neg hright]
      apply Nat.choose_eq_zero_of_lt
      omega
  · by_cases hright : profile.forcedTrue.val <=
        T.width - sector.val
    · rw [if_neg hleft, if_pos hright]
      symm
      apply Nat.choose_eq_zero_of_lt
      omega
    · rw [if_neg hleft, if_neg hright]



theorem sixVertexHorizontalCompletionProfile_valid_of_eq
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T)
    (profile : SixVertexHorizontalCompletionProfile T)
    (hprofile : sixVertexHorizontalCompletionProfile T horizontal =
      some profile) :
    profile.forcedTrue.val + profile.free.val <= T.width := by
  by_cases hcompletion :
      Nonempty (SixVertexVerticalCompletion T horizontal)
  · have hsubset :=
      sixVertexHorizontalForcedTrueColumns_subset_trueAllowed horizontal
    have hsplit := Finset.card_sdiff_add_card_eq_card hsubset
    rw [sixVertexHorizontalTrueAllowed_sdiff_forced_eq_freeColumns] at hsplit
    have hallowed := Finset.card_le_univ
      (sixVertexHorizontalTrueAllowedColumns horizontal)
    rw [sixVertexHorizontalCompletionProfile, dif_pos hcompletion] at hprofile
    have hprofile' := Option.some.inj hprofile
    subst profile
    change (sixVertexHorizontalForcedTrueColumns horizontal).card +
        (sixVertexHorizontalFreeColumns horizontal).card <= T.width
    simpa [Fintype.card_fin, add_comm] using hsplit.trans_le hallowed
  · rw [sixVertexHorizontalCompletionProfile, dif_neg hcompletion]
      at hprofile
    simp at hprofile

theorem sixVertexReflectOptionalHorizontalCompletionProfile_involutive
    {T : EvenTorus} :
    Function.Involutive
      (sixVertexReflectOptionalHorizontalCompletionProfile (T := T)) := by
  intro profile
  cases profile with
  | none => rfl
  | some profile =>
      change some (sixVertexReflectHorizontalCompletionProfile
        (sixVertexReflectHorizontalCompletionProfile profile)) = some profile
      rw [sixVertexReflectHorizontalCompletionProfile_involutive]

theorem sixVertexHorizontalCompletionProfile_reflect
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    sixVertexHorizontalCompletionProfile T
        (sixVertexReflectHorizontalField horizontal) =
      sixVertexReflectOptionalHorizontalCompletionProfile
        (sixVertexHorizontalCompletionProfile T horizontal) := by
  by_cases hcompletion :
      Nonempty (SixVertexVerticalCompletion T horizontal)
  · have hreflected :=
      (sixVertexVerticalCompletion_reflect_iff horizontal).2 hcompletion
    rw [sixVertexHorizontalCompletionProfile, dif_pos hreflected,
      sixVertexHorizontalCompletionProfile, dif_pos hcompletion]
    simp only [sixVertexReflectOptionalHorizontalCompletionProfile,
      Option.some.injEq]
    apply sixVertexHorizontalCompletionProfile_ext
    · apply Fin.ext
      have hvalid :
          (sixVertexHorizontalForcedTrueColumns horizontal).card +
              (sixVertexHorizontalFreeColumns horizontal).card <= T.width := by
        have hsubset :=
          sixVertexHorizontalForcedTrueColumns_subset_trueAllowed horizontal
        have hsplit := Finset.card_sdiff_add_card_eq_card hsubset
        rw [sixVertexHorizontalTrueAllowed_sdiff_forced_eq_freeColumns] at hsplit
        have hallowed := Finset.card_le_univ
          (sixVertexHorizontalTrueAllowedColumns horizontal)
        simpa [Fintype.card_fin, add_comm] using hsplit.trans_le hallowed
      simp only [sixVertexReflectHorizontalCompletionProfile, hvalid,
        dif_pos]
      rw [card_sixVertexHorizontalForcedTrueColumns_reflect,
        card_sixVertexHorizontalFalseForcedColumns
          (Classical.choice hcompletion)]
    · apply Fin.ext
      exact card_sixVertexHorizontalFreeColumns_reflect horizontal
  · have hreflected :
        ¬Nonempty (SixVertexVerticalCompletion T
          (sixVertexReflectHorizontalField horizontal)) := by
      exact fun h => hcompletion
        ((sixVertexVerticalCompletion_reflect_iff horizontal).1 h)
    rw [sixVertexHorizontalCompletionProfile, dif_neg hreflected,
      sixVertexHorizontalCompletionProfile, dif_neg hcompletion]
    rfl



theorem sixVertexHorizontalSectorCompletionChooseCount_reflect
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T) :
    sixVertexHorizontalSectorCompletionChooseCount T sector
        (sixVertexReflectHorizontalField horizontal) =
      sixVertexHorizontalSectorCompletionChooseCount T
        (sixVertexHorizontalComplementSector T sector) horizontal := by
  rw [sixVertexHorizontalSectorCompletionChooseCount_eq_profile,
    sixVertexHorizontalSectorCompletionChooseCount_eq_profile,
    sixVertexHorizontalCompletionProfile_reflect]
  cases hprofile : sixVertexHorizontalCompletionProfile T horizontal with
  | none => rfl
  | some profile =>
      exact sixVertexHorizontalProfileChooseCount_reflect sector profile
        (sixVertexHorizontalCompletionProfile_valid_of_eq
          horizontal profile hprofile)



theorem sixVertexHorizontalChooseSum_reflect
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (grade : Nat × Nat) :
    (∑ horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade},
      sixVertexHorizontalSectorCompletionChooseCount
          T left horizontal.1.1 *
        sixVertexHorizontalSectorCompletionChooseCount
          T right horizontal.1.2) =
      ∑ horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade},
        sixVertexHorizontalSectorCompletionChooseCount T
            (sixVertexHorizontalComplementSector T left) horizontal.1.1 *
          sixVertexHorizontalSectorCompletionChooseCount T
            (sixVertexHorizontalComplementSector T right) horizontal.1.2 := by
  let reflect :
      {horizontal : SixVertexHorizontalField T ×
          SixVertexHorizontalField T //
        sixVertexHorizontalPairBigrade horizontal = grade} ≃
      {horizontal : SixVertexHorizontalField T ×
          SixVertexHorizontalField T //
        sixVertexHorizontalPairBigrade horizontal = grade} :=
    { toFun := fun horizontal =>
        ⟨sixVertexReflectHorizontalPair horizontal.1, by
          rw [sixVertexHorizontalPairBigrade_reflect]
          exact horizontal.2⟩
      invFun := fun horizontal =>
        ⟨sixVertexReflectHorizontalPair horizontal.1, by
          rw [sixVertexHorizontalPairBigrade_reflect]
          exact horizontal.2⟩
      left_inv := fun horizontal => by
        apply Subtype.ext
        exact sixVertexReflectHorizontalPair_involutive horizontal.1
      right_inv := fun horizontal => by
        apply Subtype.ext
        exact sixVertexReflectHorizontalPair_involutive horizontal.1 }
  apply Fintype.sum_equiv reflect
  intro horizontal
  change _ =
    sixVertexHorizontalSectorCompletionChooseCount T
        (sixVertexHorizontalComplementSector T left)
        (sixVertexReflectHorizontalField horizontal.1.1) *
      sixVertexHorizontalSectorCompletionChooseCount T
        (sixVertexHorizontalComplementSector T right)
        (sixVertexReflectHorizontalField horizontal.1.2)
  rw [sixVertexHorizontalSectorCompletionChooseCount_reflect,
    sixVertexHorizontalSectorCompletionChooseCount_reflect]
  rw [sixVertexHorizontalComplementSector_involutive,
    sixVertexHorizontalComplementSector_involutive]

def sixVertexReflectHorizontalPairCompletionProfile
    {T : EvenTorus} (profile : SixVertexHorizontalPairCompletionProfile T) :
    SixVertexHorizontalPairCompletionProfile T :=
  (sixVertexReflectOptionalHorizontalCompletionProfile profile.1,
    sixVertexReflectOptionalHorizontalCompletionProfile profile.2)

theorem sixVertexReflectHorizontalPairCompletionProfile_involutive
    {T : EvenTorus} :
    Function.Involutive
      (sixVertexReflectHorizontalPairCompletionProfile (T := T)) := by
  intro profile
  apply Prod.ext
  · exact sixVertexReflectOptionalHorizontalCompletionProfile_involutive
      profile.1
  · exact sixVertexReflectOptionalHorizontalCompletionProfile_involutive
      profile.2

theorem sixVertexHorizontalPairCompletionProfile_reflect
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    sixVertexHorizontalPairCompletionProfile T
        (sixVertexReflectHorizontalPair horizontal) =
      sixVertexReflectHorizontalPairCompletionProfile
        (sixVertexHorizontalPairCompletionProfile T horizontal) := by
  apply Prod.ext
  · exact sixVertexHorizontalCompletionProfile_reflect horizontal.1
  · exact sixVertexHorizontalCompletionProfile_reflect horizontal.2

def sixVertexHorizontalPairProfileFiberReflectEquiv
    (T : EvenTorus) (grade : Nat × Nat)
    (profile : SixVertexHorizontalPairCompletionProfile T) :
    {horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade} //
      sixVertexHorizontalPairCompletionProfile T horizontal.1 = profile} ≃
      {horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade} //
      sixVertexHorizontalPairCompletionProfile T horizontal.1 =
        sixVertexReflectHorizontalPairCompletionProfile profile} where
  toFun horizontal :=
    ⟨⟨sixVertexReflectHorizontalPair horizontal.1.1, by
        rw [sixVertexHorizontalPairBigrade_reflect]
        exact horizontal.1.2⟩, by
      rw [sixVertexHorizontalPairCompletionProfile_reflect, horizontal.2]⟩
  invFun horizontal :=
    ⟨⟨sixVertexReflectHorizontalPair horizontal.1.1, by
        rw [sixVertexHorizontalPairBigrade_reflect]
        exact horizontal.1.2⟩, by
      rw [sixVertexHorizontalPairCompletionProfile_reflect, horizontal.2,
        sixVertexReflectHorizontalPairCompletionProfile_involutive]⟩
  left_inv horizontal := by
    apply Subtype.ext
    apply Subtype.ext
    exact sixVertexReflectHorizontalPair_involutive horizontal.1.1
  right_inv horizontal := by
    apply Subtype.ext
    apply Subtype.ext
    exact sixVertexReflectHorizontalPair_involutive horizontal.1.1

theorem sixVertexHorizontalPairProfileMultiplicity_reflect
    (T : EvenTorus) (grade : Nat × Nat)
    (profile : SixVertexHorizontalPairCompletionProfile T) :
    sixVertexHorizontalPairProfileMultiplicity T grade
        (sixVertexReflectHorizontalPairCompletionProfile profile) =
      sixVertexHorizontalPairProfileMultiplicity T grade profile := by
  unfold sixVertexHorizontalPairProfileMultiplicity
  exact Fintype.card_congr
    (sixVertexHorizontalPairProfileFiberReflectEquiv T grade profile).symm

end

end StatMech.FrontierD
