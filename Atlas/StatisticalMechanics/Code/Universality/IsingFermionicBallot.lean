/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicKernelCoupling








namespace StatMech.Universality

open Finset
open IsingDiagonalWalkHitSplit

noncomputable section

private def horizontalChoiceStep (b : Bool) : Int × Int :=
  (if b then 1 else -1, 1)

private def horizontalChoiceSteps (bs : List Bool) : List (Int × Int) :=
  bs.map horizontalChoiceStep

private def horizontalStepCode (d : Int × Int) : Bool :=
  decide (d.1 = 1)

private theorem horizontalChoiceSteps_length (bs : List Bool) :
    (horizontalChoiceSteps bs).length = bs.length := by
  simp [horizontalChoiceSteps]

private theorem horizontalChoiceSteps_valid (bs : List Bool) :
    IsingDiagonalWalkStepsValid (horizontalChoiceSteps bs) := by
  intro d hd
  simp only [horizontalChoiceSteps, List.mem_map] at hd
  rcases hd with ⟨b, hb, rfl⟩
  cases b <;> simp [horizontalChoiceStep]

private theorem horizontalChoiceSteps_vertical (bs : List Bool) :
    ∀ d ∈ horizontalChoiceSteps bs, d.2 = 1 := by
  intro d hd
  simp only [horizontalChoiceSteps, List.mem_map] at hd
  rcases hd with ⟨b, hb, rfl⟩
  simp [horizontalChoiceStep]

private theorem horizontalStepCode_choiceStep (b : Bool) :
    horizontalStepCode (horizontalChoiceStep b) = b := by
  cases b <;> simp [horizontalStepCode, horizontalChoiceStep]

private theorem horizontalStepCodes_choiceSteps (bs : List Bool) :
    (horizontalChoiceSteps bs).map horizontalStepCode = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      change horizontalStepCode (horizontalChoiceStep b) ::
        (horizontalChoiceSteps bs).map horizontalStepCode = b :: bs
      rw [horizontalStepCode_choiceStep, ih]

private theorem horizontalChoiceSteps_stepCodes_of_valid
    (path : List (Int × Int))
    (hvalid : IsingDiagonalWalkStepsValid path)
    (hvertical : ∀ d ∈ path, d.2 = 1) :
    horizontalChoiceSteps (path.map horizontalStepCode) = path := by
  induction path with
  | nil => rfl
  | cons d path ih =>
      have hd := hvalid d (by simp)
      have hdvertical := hvertical d (by simp)
      have htailValid : IsingDiagonalWalkStepsValid path := by
        intro e he
        exact hvalid e (by simp [he])
      have htailVertical : ∀ e ∈ path, e.2 = 1 := by
        intro e he
        exact hvertical e (by simp [he])
      have hstep : horizontalChoiceStep (horizontalStepCode d) = d := by
        rcases hd.1 with hdx | hdx <;>
          apply Prod.ext <;>
          simp [horizontalChoiceStep, horizontalStepCode, hdx, hdvertical]
      change horizontalChoiceStep (horizontalStepCode d) ::
        horizontalChoiceSteps (path.map horizontalStepCode) = d :: path
      rw [hstep, ih htailValid htailVertical]

private theorem lineFreeEndpoint_horizontalChoiceSteps
    (bs : List Bool) (start : Int) :
    lineFreeEndpoint start bs =
      (isingDiagonalWalkEndpoint (start, 0)
        (horizontalChoiceSteps bs)).1 := by
  induction bs generalizing start with
  | nil =>
      simp [lineFreeEndpoint, horizontalChoiceSteps,
        isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement]
  | cons b bs ih =>
      cases b with
      | false =>
          convert ih (start - 1) using 1 <;>
            simp [lineFreeEndpoint, horizontalChoiceSteps,
            horizontalChoiceStep, isingDiagonalWalkEndpoint,
            isingDiagonalWalkNext, isingDiagonalWalkDisplacement, add_assoc] <;>
            ring
      | true =>
          convert ih (start + 1) using 1 <;>
            simp [lineFreeEndpoint, horizontalChoiceSteps,
            horizontalChoiceStep, isingDiagonalWalkEndpoint,
            isingDiagonalWalkNext, isingDiagonalWalkDisplacement, add_assoc] <;>
            ring

private theorem lineFreeEndpoint_add (bs : List Bool) (start shift : Int) :
    lineFreeEndpoint (start + shift) bs =
      lineFreeEndpoint start bs + shift := by
  induction bs generalizing start with
  | nil => simp [lineFreeEndpoint]
  | cons b bs ih =>
      rw [lineFreeEndpoint, lineFreeEndpoint]
      calc
        lineFreeEndpoint (start + shift + (if b then 1 else -1)) bs =
            lineFreeEndpoint ((start + (if b then 1 else -1)) + shift) bs := by
              congr 1
              ring
        _ = lineFreeEndpoint (start + (if b then 1 else -1)) bs + shift :=
          ih (start + (if b then 1 else -1))


private def HorizontalFreeBelow (t : Nat) (start level : Int) :=
  {bs : List Bool // bs.length = t ∧ lineFreeEndpoint start bs < level}

private noncomputable instance horizontalFreeBelow_finite
    (t : Nat) (start level : Int) :
    Finite (HorizontalFreeBelow t start level) := by
  letI : Fintype {bs : List Bool // bs.length = t} :=
    (List.finite_length_eq Bool t).fintype
  exact Finite.of_injective
    (fun w : HorizontalFreeBelow t start level =>
      (⟨w.1, w.2.1⟩ : {bs : List Bool // bs.length = t}))
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg
        (fun z : {bs : List Bool // bs.length = t} => z.1) h)


private def HorizontalHitBelow (t : Nat) (start level : Int) :=
  {w : HorizontalFreeBelow t start level //
    isingDiagonalWalkFirstHitSplit? (start, 0) level
      (horizontalChoiceSteps w.val) ≠ none}

private noncomputable instance horizontalHitBelow_finite
    (t : Nat) (start level : Int) :
    Finite (HorizontalHitBelow t start level) := by
  exact Finite.of_injective
    (fun z : HorizontalHitBelow t start level => z.1)
    (by
      intro a b h
      exact Subtype.ext h)


private def HorizontalNoHitBelow (t : Nat) (start level : Int) :=
  {w : HorizontalFreeBelow t start level //
    ¬ isingDiagonalWalkFirstHitSplit? (start, 0) level
      (horizontalChoiceSteps w.val) ≠ none}

private noncomputable instance horizontalNoHitBelow_finite
    (t : Nat) (start level : Int) :
    Finite (HorizontalNoHitBelow t start level) := by
  exact Finite.of_injective
    (fun w : HorizontalNoHitBelow t start level => w.1)
    (by
      intro a b h
      exact Subtype.ext h)

private def horizontalFreeBelowHitNoHitEquiv
    (t : Nat) (start level : Int) :
    HorizontalFreeBelow t start level ≃
      HorizontalHitBelow t start level ⊕
        HorizontalNoHitBelow t start level :=
  (Equiv.sumCompl (fun w : HorizontalFreeBelow t start level =>
    isingDiagonalWalkFirstHitSplit? (start, 0) level
      (horizontalChoiceSteps w.1) ≠ none)).symm


private def HorizontalFirstHitBelow (t : Nat) (start level : Int) :=
  {w : IsingDiagonalWalkHitSplit (start, 0) level //
    w.FirstHit ∧ w.Valid ∧ w.steps.length = t ∧
      w.endpoint.1 < level ∧ ∀ d ∈ w.steps, d.2 = 1}

private noncomputable def horizontalHitBelowSplit
    {t : Nat} {start level : Int}
    (z : HorizontalHitBelow t start level) :
    IsingDiagonalWalkHitSplit (start, 0) level :=
  (isingDiagonalWalkFirstHitSplit? (start, 0) level
    (horizontalChoiceSteps z.1.1)).get
      (Option.ne_none_iff_isSome.mp z.2)

private theorem horizontalHitBelowSplit_spec
    {t : Nat} {start level : Int}
    (z : HorizontalHitBelow t start level) :
    isingDiagonalWalkFirstHitSplit? (start, 0) level
      (horizontalChoiceSteps z.1.1) = some (horizontalHitBelowSplit z) :=
  (Option.some_get (Option.ne_none_iff_isSome.mp z.2)).symm

private noncomputable def horizontalHitBelowToFirstHitBelow
    (t : Nat) (start level : Int) :
    HorizontalHitBelow t start level →
      HorizontalFirstHitBelow t start level := fun z => by
    let split := horizontalHitBelowSplit z
    have hsplit := horizontalHitBelowSplit_spec z
    let q := split.endpoint
    have hsteps := firstHitSplit_steps hsplit
    have hfirst := firstHitSplit_firstHit hsplit
    have hvalid : split.Valid := by
      unfold IsingDiagonalWalkHitSplit.Valid
      rw [hsteps]
      exact horizontalChoiceSteps_valid z.1.1
    have hlength : split.steps.length = t := by
      rw [hsteps, horizontalChoiceSteps_length]
      exact z.1.2.1
    have hbelow : q.1 < level := by
      change split.endpoint.1 < level
      rw [show split.endpoint.1 = lineFreeEndpoint start z.1.1 by
        unfold IsingDiagonalWalkHitSplit.endpoint
        rw [hsteps]
        exact (lineFreeEndpoint_horizontalChoiceSteps z.1.1 start).symm]
      exact z.1.2.2
    exact ⟨split, hfirst, hvalid, hlength, hbelow, by
        intro d hd
        rw [hsteps] at hd
        exact horizontalChoiceSteps_vertical z.1.1 d hd⟩

private noncomputable def horizontalFirstHitBelowToHitBelow
    (t : Nat) (start level : Int) :
    HorizontalFirstHitBelow t start level →
      HorizontalHitBelow t start level := fun z => by
    let split := z.1
    let bs := split.steps.map horizontalStepCode
    have hdecode : horizontalChoiceSteps bs = split.steps :=
      horizontalChoiceSteps_stepCodes_of_valid split.steps
        z.2.2.1 z.2.2.2.2.2
    have hlength : bs.length = t := by
      simpa [bs] using z.2.2.2.1
    have hbelow : lineFreeEndpoint start bs < level := by
      rw [lineFreeEndpoint_horizontalChoiceSteps, hdecode]
      exact z.2.2.2.2.1
    refine ⟨⟨bs, hlength, hbelow⟩, ?_⟩
    rw [hdecode, firstHitSplit_eq_some split z.2.1]
    exact Option.some_ne_none split

private theorem horizontalHitBelowToFirstHitBelow_injective
    (t : Nat) (start level : Int) :
    Function.Injective
      (horizontalHitBelowToFirstHitBelow t start level) := by
  intro a b h
  have hsplits : horizontalHitBelowSplit a = horizontalHitBelowSplit b :=
    congrArg (fun z : HorizontalFirstHitBelow t start level => z.1) h
  have ha := firstHitSplit_steps (horizontalHitBelowSplit_spec a)
  have hb := firstHitSplit_steps (horizontalHitBelowSplit_spec b)
  have hpaths : horizontalChoiceSteps a.1.1 =
      horizontalChoiceSteps b.1.1 := by
    rw [← ha, ← hb, hsplits]
  have hbits := congrArg (List.map horizontalStepCode) hpaths
  rw [horizontalStepCodes_choiceSteps,
    horizontalStepCodes_choiceSteps] at hbits
  exact Subtype.ext (Subtype.ext hbits)

private theorem horizontalFirstHitBelowToHitBelow_injective
    (t : Nat) (start level : Int) :
    Function.Injective
      (horizontalFirstHitBelowToHitBelow t start level) := by
  intro a b h
  apply Subtype.ext
  have hbits : a.1.steps.map horizontalStepCode =
      b.1.steps.map horizontalStepCode := congrArg
    (fun z : HorizontalHitBelow t start level => z.1.1) h
  have ha := horizontalChoiceSteps_stepCodes_of_valid a.1.steps
    a.2.2.1 a.2.2.2.2.2
  have hb := horizontalChoiceSteps_stepCodes_of_valid b.1.steps
    b.2.2.1 b.2.2.2.2.2
  apply Option.some.inj
  rw [← firstHitSplit_eq_some a.1 a.2.1,
    ← firstHitSplit_eq_some b.1 b.2.1, ← ha, ← hb, hbits]

private noncomputable instance horizontalFirstHitBelow_finite
    (t : Nat) (start level : Int) :
    Finite (HorizontalFirstHitBelow t start level) :=
  Finite.of_injective (horizontalFirstHitBelowToHitBelow t start level)
    (horizontalFirstHitBelowToHitBelow_injective t start level)

private theorem natCard_horizontalHitBelow_eq_firstHitBelow
    (t : Nat) (start level : Int) :
    Nat.card (HorizontalHitBelow t start level) =
      Nat.card (HorizontalFirstHitBelow t start level) := by
  apply le_antisymm
  · exact Nat.card_le_card_of_injective
      (horizontalHitBelowToFirstHitBelow t start level)
      (horizontalHitBelowToFirstHitBelow_injective t start level)
  · exact Nat.card_le_card_of_injective
      (horizontalFirstHitBelowToHitBelow t start level)
      (horizontalFirstHitBelowToHitBelow_injective t start level)

private def horizontalFirstHitBelowReflect
    (t : Nat) (start level : Int) :
    HorizontalFirstHitBelow t start level →
      HorizontalFirstHitBelow t (2 * level - start) level := fun z =>
  ⟨z.1.reflectPrefix,
    reflectPrefix_firstHit z.1 z.2.1,
    reflectPrefix_valid z.1 z.2.2.1,
    (reflectPrefix_length z.1).trans z.2.2.2.1,
    (reflectPrefix_endpoint_fst z.1).symm ▸ z.2.2.2.2.1,
    by
      intro d hd
      change d ∈ z.1.before.map reflectIncrement ++
        z.1.after at hd
      rcases List.mem_append.mp hd with hd | hd
      · rcases List.mem_map.mp hd with ⟨e, he, rfl⟩
        simpa [reflectIncrement] using z.2.2.2.2.2 e
          (List.mem_append.mpr (Or.inl he))
      · exact z.2.2.2.2.2 d (List.mem_append.mpr (Or.inr hd))⟩

private theorem horizontalFirstHitBelowReflect_injective
    (t : Nat) (start level : Int) :
    Function.Injective (horizontalFirstHitBelowReflect t start level) := by
  intro a b h
  apply Subtype.ext
  have hsplit := congrArg
    (fun z : HorizontalFirstHitBelow t (2 * level - start) level => z.1) h
  cases a with
  | mk a ha =>
      cases b with
      | mk b hb =>
          cases a with
          | mk ab aa ahit =>
              cases b with
              | mk bb ba bhit =>
                  simp only [horizontalFirstHitBelowReflect, reflectPrefix] at hsplit
                  have hbefore : ab = bb := by
                    have hreflect : Function.Injective reflectIncrement := by
                      intro x y hxy
                      apply Prod.ext
                      · have hx := congrArg Prod.fst hxy
                        simp [reflectIncrement] at hx
                        linarith
                      · simpa [reflectIncrement] using congrArg Prod.snd hxy
                    have hmap := congrArg
                      (fun w : IsingDiagonalWalkHitSplit
                        (reflectedEndpoint level (start, 0)) level => w.before) hsplit
                    exact (Function.Injective.list_map hreflect) hmap
                  have hafter : aa = ba := congrArg
                    (fun w : IsingDiagonalWalkHitSplit
                      (reflectedEndpoint level (start, 0)) level => w.after) hsplit
                  subst bb
                  subst ba
                  rfl

private def horizontalFirstHitBelowLowerToUpper
    (t : Nat) (level : Int) :
    HorizontalFirstHitBelow t (level - 1) level →
      HorizontalFirstHitBelow t (level + 1) level := fun w => by
  simpa only [show 2 * level - (level - 1) = level + 1 by ring] using
    horizontalFirstHitBelowReflect t (level - 1) level w

private def horizontalFirstHitBelowUpperToLower
    (t : Nat) (level : Int) :
    HorizontalFirstHitBelow t (level + 1) level →
      HorizontalFirstHitBelow t (level - 1) level := fun w => by
  simpa only [show 2 * level - (level + 1) = level - 1 by ring] using
    horizontalFirstHitBelowReflect t (level + 1) level w

private theorem natCard_horizontalFirstHitBelow_lower_eq_upper
    (t : Nat) (level : Int) :
    Nat.card (HorizontalFirstHitBelow t (level - 1) level) =
      Nat.card (HorizontalFirstHitBelow t (level + 1) level) := by
  apply le_antisymm
  · have hle := Nat.card_le_card_of_injective
        (horizontalFirstHitBelowReflect t (level - 1) level)
        (horizontalFirstHitBelowReflect_injective t (level - 1) level)
    simpa only [show 2 * level - (level - 1) = level + 1 by ring] using hle
  · have hle := Nat.card_le_card_of_injective
        (horizontalFirstHitBelowReflect t (level + 1) level)
        (horizontalFirstHitBelowReflect_injective t (level + 1) level)
    simpa only [show 2 * level - (level + 1) = level - 1 by ring] using hle

private theorem natCard_horizontalHitBelow_lower_eq_upper
    (t : Nat) (level : Int) :
    Nat.card (HorizontalHitBelow t (level - 1) level) =
      Nat.card (HorizontalHitBelow t (level + 1) level) := by
  rw [natCard_horizontalHitBelow_eq_firstHitBelow,
    natCard_horizontalHitBelow_eq_firstHitBelow,
    natCard_horizontalFirstHitBelow_lower_eq_upper]

private def horizontalFreeBelowUpperEquivHitBelowUpper
    (t : Nat) (level : Int) :
    HorizontalFreeBelow t (level + 1) level ≃
      HorizontalHitBelow t (level + 1) level where
  toFun w := ⟨w, by
    intro hnone
    have hvalid := horizontalChoiceSteps_valid w.1
    have hend :
        (isingDiagonalWalkEndpoint (level + 1, 0)
          (horizontalChoiceSteps w.1)).1 ≤ level := by
      exact (show (isingDiagonalWalkEndpoint (level + 1, 0)
          (horizontalChoiceSteps w.1)).1 < level from by
        rw [← lineFreeEndpoint_horizontalChoiceSteps]
        exact w.2.2).le
    rcases exists_prefix_fst_eq_of_ge_of_gt
        (horizontalChoiceSteps w.1) (level + 1, 0) level
        hvalid (by omega) hend with ⟨k, hk, heq⟩
    exact (firstHitSplit_none_endpoint_fst_ne hnone k hk) heq⟩
  invFun w := w.1
  left_inv _ := rfl
  right_inv w := Subtype.ext rfl

private theorem natCard_horizontalFreeBelow_upper_eq_hitBelow_upper
    (t : Nat) (level : Int) :
    Nat.card (HorizontalFreeBelow t (level + 1) level) =
      Nat.card (HorizontalHitBelow t (level + 1) level) :=
  Nat.card_congr (horizontalFreeBelowUpperEquivHitBelowUpper t level)

private def horizontalFreeBelowUpperEquivDeepLower
    (t : Nat) (level : Int) :
    HorizontalFreeBelow t (level + 1) level ≃
      HorizontalFreeBelow t (level - 1) (level - 2) where
  toFun w := ⟨w.1, w.2.1, by
    have hshift := lineFreeEndpoint_add w.1 (level - 1) 2
    have hstart : level - 1 + 2 = level + 1 := by ring
    rw [hstart] at hshift
    have hu := w.2.2
    rw [hshift] at hu
    omega⟩
  invFun w := ⟨w.1, w.2.1, by
    have hshift := lineFreeEndpoint_add w.1 (level - 1) 2
    have hstart : level - 1 + 2 = level + 1 := by ring
    rw [hstart] at hshift
    have hd := w.2.2
    rw [hshift]
    omega⟩
  left_inv w := Subtype.ext rfl
  right_inv w := Subtype.ext rfl

private theorem natCard_horizontalFreeBelow_upper_eq_deepLower
    (t : Nat) (level : Int) :
    Nat.card (HorizontalFreeBelow t (level + 1) level) =
      Nat.card (HorizontalFreeBelow t (level - 1) (level - 2)) :=
  Nat.card_congr (horizontalFreeBelowUpperEquivDeepLower t level)


private def HorizontalCentralBand (t : Nat) (level : Int) :=
  {w : HorizontalFreeBelow t (level - 1) level //
    ¬ lineFreeEndpoint (level - 1) w.1 < level - 2}

private noncomputable instance horizontalCentralBand_finite
    (t : Nat) (level : Int) : Finite (HorizontalCentralBand t level) := by
  exact Finite.of_injective
    (fun w : HorizontalCentralBand t level => w.1)
    (by intro a b h; exact Subtype.ext h)

private def deepLowerEquivSubtype
    (t : Nat) (level : Int) :
    HorizontalFreeBelow t (level - 1) (level - 2) ≃
      {w : HorizontalFreeBelow t (level - 1) level //
        lineFreeEndpoint (level - 1) w.1 < level - 2} where
  toFun w := ⟨⟨w.1, w.2.1, by
    have h := w.2.2
    omega⟩, w.2.2⟩
  invFun w := ⟨w.1.1, w.1.2.1, w.2⟩
  left_inv w := Subtype.ext rfl
  right_inv w := Subtype.ext rfl

private def centralBandEquivSubtype
    (t : Nat) (level : Int) :
    HorizontalCentralBand t level ≃
      {w : HorizontalFreeBelow t (level - 1) level //
        ¬ lineFreeEndpoint (level - 1) w.1 < level - 2} :=
  Equiv.refl _

private theorem natCard_horizontalFreeBelow_lower_eq_deep_add_band
    (t : Nat) (level : Int) :
    Nat.card (HorizontalFreeBelow t (level - 1) level) =
      Nat.card (HorizontalFreeBelow t (level - 1) (level - 2)) +
        Nat.card (HorizontalCentralBand t level) := by
  rw [← Nat.card_sum, ← Nat.card_congr
    ((Equiv.sumCongr (deepLowerEquivSubtype t level)
      (centralBandEquivSubtype t level)).trans
      (Equiv.sumCompl (fun w : HorizontalFreeBelow t (level - 1) level =>
        lineFreeEndpoint (level - 1) w.1 < level - 2)))]

private theorem natCard_horizontalFreeBelow_lower_eq_hit_add_noHit
    (t : Nat) (level : Int) :
    Nat.card (HorizontalFreeBelow t (level - 1) level) =
      Nat.card (HorizontalHitBelow t (level - 1) level) +
        Nat.card (HorizontalNoHitBelow t (level - 1) level) := by
  rw [← Nat.card_sum, ← Nat.card_congr
    (horizontalFreeBelowHitNoHitEquiv t (level - 1) level)]

private theorem natCard_horizontalNoHitBelow_eq_centralBand
    (t : Nat) (level : Int) :
    Nat.card (HorizontalNoHitBelow t (level - 1) level) =
      Nat.card (HorizontalCentralBand t level) := by
  have hpartition := natCard_horizontalFreeBelow_lower_eq_hit_add_noHit t level
  have hband := natCard_horizontalFreeBelow_lower_eq_deep_add_band t level
  have hreflect := natCard_horizontalHitBelow_lower_eq_upper t level
  have hupper := natCard_horizontalFreeBelow_upper_eq_hitBelow_upper t level
  have htranslate := natCard_horizontalFreeBelow_upper_eq_deepLower t level
  omega

private def horizontalCentralBandEquivEndpointSum
    (t : Nat) (level : Int) :
    HorizontalCentralBand t level ≃
      VerticalChoicePathFamily t (level - 1) (level - 2) ⊕
        VerticalChoicePathFamily t (level - 1) (level - 1) where
  toFun w := by
    by_cases hend : lineFreeEndpoint (level - 1) w.1.1 = level - 2
    · exact Sum.inl ⟨w.1.1, w.1.2.1, hend⟩
    · exact Sum.inr ⟨w.1.1, w.1.2.1, by
        have hlower := w.2
        have hupper := w.1.2.2
        omega⟩
  invFun w := w.elim
    (fun bs => ⟨⟨bs.1, bs.2.1, by rw [bs.2.2]; omega⟩, by
      rw [bs.2.2]
      omega⟩)
    (fun bs => ⟨⟨bs.1, bs.2.1, by rw [bs.2.2]; omega⟩, by
      rw [bs.2.2]
      omega⟩)
  left_inv w := by
    by_cases hend : lineFreeEndpoint (level - 1) w.1.1 = level - 2
    · simp [hend]
    · simp [hend]
  right_inv w := by
    rcases w with bs | bs
    · simp [bs.2.2]
    · have hne : lineFreeEndpoint (level - 1) bs.1 ≠ level - 2 := by
        rw [bs.2.2]
        omega
      simp [hne]

private theorem horizontalFirstHitSplit_eq_none_of_avoids
    (t : Nat) (start level : Int) (bs : List Bool)
    (hlen : bs.length = t)
    (havoid : ∀ k, k ≤ t →
      lineFreeEndpoint start (bs.take k) ≠ level) :
    isingDiagonalWalkFirstHitSplit? (start, 0) level
      (horizontalChoiceSteps bs) = none := by
  cases hsplit : isingDiagonalWalkFirstHitSplit? (start, 0) level
      (horizontalChoiceSteps bs) with
  | none => rfl
  | some split =>
      exfalso
      have hsteps := firstHitSplit_steps hsplit
      have hk : split.before.length ≤ t := by
        calc
          split.before.length ≤ split.steps.length := by
            simp [IsingDiagonalWalkHitSplit.steps]
          _ = (horizontalChoiceSteps bs).length := congrArg List.length hsteps
          _ = t := by rw [horizontalChoiceSteps_length, hlen]
      exact (havoid split.before.length hk) (by
        calc
          lineFreeEndpoint start (bs.take split.before.length) =
              (isingDiagonalWalkEndpoint (start, 0)
                (horizontalChoiceSteps (bs.take split.before.length))).1 :=
            lineFreeEndpoint_horizontalChoiceSteps _ _
          _ = (isingDiagonalWalkEndpoint (start, 0)
                ((horizontalChoiceSteps bs).take split.before.length)).1 := by
            simp [horizontalChoiceSteps, List.map_take]
          _ = (isingDiagonalWalkEndpoint (start, 0) split.before).1 := by
            rw [← hsteps]
            simp [IsingDiagonalWalkHitSplit.steps]
          _ = level := split.hit)

private def horizontalNoHitToNoHitBelow
    (t : Nat) (level : Int) :
    IsingHorizontalNoHitFamily t (level - 1) level →
      HorizontalNoHitBelow t (level - 1) level := fun w => by
  have hnone := horizontalFirstHitSplit_eq_none_of_avoids t (level - 1)
    level w.1 w.2.1 w.2.2
  have hbelow : lineFreeEndpoint (level - 1) w.1 < level := by
    by_contra hnot
    have hend : level ≤
        (isingDiagonalWalkEndpoint (level - 1, 0)
          (horizontalChoiceSteps w.1)).1 := by
      rw [← lineFreeEndpoint_horizontalChoiceSteps]
      omega
    rcases exists_prefix_fst_eq_of_lt_of_le
        (horizontalChoiceSteps w.1) (level - 1, 0) level
        (horizontalChoiceSteps_valid w.1) (by omega) hend with
      ⟨k, hk, heq⟩
    exact (firstHitSplit_none_endpoint_fst_ne hnone k hk) heq
  exact ⟨⟨w.1, w.2.1, hbelow⟩, fun hne => hne hnone⟩

private theorem horizontalNoHitToNoHitBelow_injective
    (t : Nat) (level : Int) :
    Function.Injective (horizontalNoHitToNoHitBelow t level) := by
  intro a b h
  apply Subtype.ext
  exact congrArg
    (fun w : HorizontalNoHitBelow t (level - 1) level => w.1.1) h


theorem natCard_horizontalNoHit_le_endpointFibers
    (t : Nat) (level : Int) :
    Nat.card (IsingHorizontalNoHitFamily t (level - 1) level) ≤
      Nat.card (VerticalChoicePathFamily t (level - 1) (level - 2)) +
        Nat.card (VerticalChoicePathFamily t (level - 1) (level - 1)) := by
  calc
    _ ≤ Nat.card (HorizontalNoHitBelow t (level - 1) level) :=
      Nat.card_le_card_of_injective (horizontalNoHitToNoHitBelow t level)
        (horizontalNoHitToNoHitBelow_injective t level)
    _ = Nat.card (HorizontalCentralBand t level) :=
      natCard_horizontalNoHitBelow_eq_centralBand t level
    _ = _ := by
      rw [Nat.card_congr (horizontalCentralBandEquivEndpointSum t level),
        Nat.card_sum]


theorem horizontalNoHit_weight_le_sqrt
    (t : Nat) (level : Int) :
    Nat.card (IsingHorizontalNoHitFamily t (level - 1) level) /
        (2 : Real) ^ t ≤ 2 * Real.sqrt (2 / (t + 1 : Real)) := by
  have hcard := natCard_horizontalNoHit_le_endpointFibers t level
  have hden : 0 < (2 : Real) ^ t := by positivity
  have hmass :
      Nat.card (IsingHorizontalNoHitFamily t (level - 1) level) /
          (2 : Real) ^ t ≤
        Nat.card (VerticalChoicePathFamily t (level - 1) (level - 2)) /
            (2 : Real) ^ t +
          Nat.card (VerticalChoicePathFamily t (level - 1) (level - 1)) /
            (2 : Real) ^ t := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hden.le
    exact_mod_cast hcard
  let K₀ := isingLineBinomialKernel t (level - 1) (level - 2)
  let K₁ := isingLineBinomialKernel t (level - 1) (level - 1)
  have hroot0 : 0 ≤ Real.sqrt (2 / (t + 1 : Real)) := Real.sqrt_nonneg _
  have hradicand : 0 ≤ 2 / (t + 1 : Real) := by positivity
  have hK₀0 : 0 ≤ K₀ := isingLineBinomialKernel_nonneg _ _ _
  have hK₁0 : 0 ≤ K₁ := isingLineBinomialKernel_nonneg _ _ _
  have hK₀ : K₀ ≤ Real.sqrt (2 / (t + 1 : Real)) := by
    rw [Real.le_sqrt hK₀0 hradicand]
    exact isingLineBinomialKernel_sq_le t (level - 1) (level - 2)
  have hK₁ : K₁ ≤ Real.sqrt (2 / (t + 1 : Real)) := by
    rw [Real.le_sqrt hK₁0 hradicand]
    exact isingLineBinomialKernel_sq_le t (level - 1) (level - 1)
  calc
    _ ≤ _ := hmass
    _ = K₀ + K₁ := by
      rw [← isingLineBinomialKernel_eq_natCard_verticalChoicePath_div,
        ← isingLineBinomialKernel_eq_natCard_verticalChoicePath_div]
    _ ≤ Real.sqrt (2 / (t + 1 : Real)) +
        Real.sqrt (2 / (t + 1 : Real)) := add_le_add hK₀ hK₁
    _ = 2 * Real.sqrt (2 / (t + 1 : Real)) := by ring


theorem horizontalNoHit_diffusive_weight_le
    (ρ : Nat) (level : Int) (hρ : 0 < ρ) :
    Nat.card (IsingHorizontalNoHitFamily (ρ * ρ) (level - 1) level) /
        (2 : Real) ^ (ρ * ρ) ≤ 4 / (ρ : Real) := by
  have hcard := natCard_horizontalNoHit_le_endpointFibers (ρ * ρ) level
  have hden : 0 < (2 : Real) ^ (ρ * ρ) := by positivity
  have hmass :
      Nat.card (IsingHorizontalNoHitFamily (ρ * ρ) (level - 1) level) /
          (2 : Real) ^ (ρ * ρ) ≤
        (Nat.card (VerticalChoicePathFamily (ρ * ρ) (level - 1)
            (level - 2)) +
          Nat.card (VerticalChoicePathFamily (ρ * ρ) (level - 1)
            (level - 1))) / (2 : Real) ^ (ρ * ρ) := by
    apply div_le_div_of_nonneg_right _ hden.le
    exact_mod_cast hcard
  let K₀ := isingLineBinomialKernel (ρ * ρ) (level - 1) (level - 2)
  let K₁ := isingLineBinomialKernel (ρ * ρ) (level - 1) (level - 1)
  have hK₀0 : 0 ≤ K₀ := isingLineBinomialKernel_nonneg _ _ _
  have hK₁0 : 0 ≤ K₁ := isingLineBinomialKernel_nonneg _ _ _
  have hK₀sq := isingLineBinomialKernel_sq_le
    (ρ * ρ) (level - 1) (level - 2)
  have hK₁sq := isingLineBinomialKernel_sq_le
    (ρ * ρ) (level - 1) (level - 1)
  norm_num [Nat.cast_add, Nat.cast_mul] at hK₀sq hK₁sq
  have hdenρ : 0 < (ρ : Real) ^ 2 + 1 := by positivity
  have hK₀sq' : K₀ ^ 2 * ((ρ : Real) ^ 2 + 1) ≤ 2 := by
    apply (le_div_iff₀ hdenρ).mp
    dsimp [K₀]
    convert hK₀sq using 1 <;> ring
  have hK₁sq' : K₁ ^ 2 * ((ρ : Real) ^ 2 + 1) ≤ 2 := by
    apply (le_div_iff₀ hdenρ).mp
    dsimp [K₁]
    convert hK₁sq using 1 <;> ring
  have hρReal : 0 < (ρ : Real) := by positivity
  have boundKernel (K : Real) (hK0 : 0 ≤ K)
      (hKsq : K ^ 2 * ((ρ : Real) ^ 2 + 1) ≤ 2) :
      K ≤ 2 / (ρ : Real) := by
    apply (le_div_iff₀ hρReal).2
    have hprod0 : 0 ≤ (ρ : Real) * K := mul_nonneg hρReal.le hK0
    have hprodSq : ((ρ : Real) * K) ^ 2 ≤ 2 := by
      nlinarith [sq_nonneg K]
    nlinarith
  have hK₀ := boundKernel K₀ hK₀0 hK₀sq'
  have hK₁ := boundKernel K₁ hK₁0 hK₁sq'
  calc
    _ ≤ _ := hmass
    _ = K₀ + K₁ := by
      rw [add_div]
      rw [← isingLineBinomialKernel_eq_natCard_verticalChoicePath_div,
        ← isingLineBinomialKernel_eq_natCard_verticalChoicePath_div]
    _ ≤ 2 / (ρ : Real) + 2 / (ρ : Real) := add_le_add hK₀ hK₁
    _ = 4 / (ρ : Real) := by ring

private theorem lineFreeEndpoint_map_not
    (bs : List Bool) (start level : Int) :
    lineFreeEndpoint (2 * level - start) (bs.map (!·)) =
      2 * level - lineFreeEndpoint start bs := by
  induction bs generalizing start with
  | nil => simp [lineFreeEndpoint]
  | cons b bs ih =>
      cases b with
      | false =>
          simp only [List.map_cons, Bool.not_false, lineFreeEndpoint]
          convert ih (start - 1) using 1 <;> simp <;> ring
      | true =>
          simp only [List.map_cons, Bool.not_true, lineFreeEndpoint]
          convert ih (start + 1) using 1 <;> simp <;> ring

private def horizontalNoHitLowerUpperEquiv
    (t : Nat) (level : Int) :
    IsingHorizontalNoHitFamily t (level - 1) level ≃
      IsingHorizontalNoHitFamily t (level + 1) level where
  toFun w := ⟨w.1.map (!·), by simpa using w.2.1, by
    intro k hk heq
    have hreflect := lineFreeEndpoint_map_not (w.1.take k) (level - 1) level
    have htake : (w.1.map (!·)).take k = (w.1.take k).map (!·) := by
      simp [List.map_take]
    rw [htake] at heq
    have horig : lineFreeEndpoint (level - 1) (w.1.take k) = level := by
      rw [show 2 * level - (level - 1) = level + 1 by ring] at hreflect
      omega
    exact w.2.2 k hk horig⟩
  invFun w := ⟨w.1.map (!·), by simpa using w.2.1, by
    intro k hk heq
    have hreflect := lineFreeEndpoint_map_not (w.1.take k) (level + 1) level
    have htake : (w.1.map (!·)).take k = (w.1.take k).map (!·) := by
      simp [List.map_take]
    rw [htake] at heq
    have horig : lineFreeEndpoint (level + 1) (w.1.take k) = level := by
      rw [show 2 * level - (level + 1) = level - 1 by ring] at hreflect
      omega
    exact w.2.2 k hk horig⟩
  left_inv w := by
    apply Subtype.ext
    simpa [Function.comp_def] using List.map_map (!·) (!·) w.1
  right_inv w := by
    apply Subtype.ext
    simpa [Function.comp_def] using List.map_map (!·) (!·) w.1



theorem horizontalNoHit_diffusive_weight_le_upper
    (ρ : Nat) (level : Int) (hρ : 0 < ρ) :
    Nat.card (IsingHorizontalNoHitFamily (ρ * ρ) (level + 1) level) /
        (2 : Real) ^ (ρ * ρ) ≤ 4 / (ρ : Real) := by
  rw [← Nat.card_congr (horizontalNoHitLowerUpperEquiv (ρ * ρ) level)]
  exact horizontalNoHit_diffusive_weight_le ρ level hρ



theorem killedChoiceNoHitAll_diffusive_weight_le
    (R ρ : Nat) (p : IsingLeapfrogBox R) (level : Int)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level) (hρ : 0 < ρ) :
    Nat.card (IsingLeapfrogKilledChoiceNoHitAll R (ρ * ρ) p level) /
        (4 : Real) ^ (ρ * ρ) ≤ 4 / (ρ : Real) := by
  have hcard := natCard_killedChoiceNoHitAll_le_horizontal_mul_pow
    R (ρ * ρ) p level
  have hcardReal :
      (Nat.card (IsingLeapfrogKilledChoiceNoHitAll R (ρ * ρ) p level) :
          Real) ≤
        Nat.card (IsingHorizontalNoHitFamily (ρ * ρ)
            (isingLeapfrogBoxInt p).1 level) *
          (2 : Real) ^ (ρ * ρ) := by
    exact_mod_cast hcard
  have htwo : 0 < (2 : Real) ^ (ρ * ρ) := by positivity
  have hfour : 0 < (4 : Real) ^ (ρ * ρ) := by positivity
  have hpow : (4 : Real) ^ (ρ * ρ) =
      (2 : Real) ^ (ρ * ρ) * (2 : Real) ^ (ρ * ρ) := by
    rw [show (4 : Real) = 2 * 2 by norm_num, mul_pow]
  have hreduce :
      Nat.card (IsingLeapfrogKilledChoiceNoHitAll R (ρ * ρ) p level) /
          (4 : Real) ^ (ρ * ρ) ≤
        Nat.card (IsingHorizontalNoHitFamily (ρ * ρ)
            (isingLeapfrogBoxInt p).1 level) /
          (2 : Real) ^ (ρ * ρ) := by
    calc
      _ ≤ (Nat.card (IsingHorizontalNoHitFamily (ρ * ρ)
              (isingLeapfrogBoxInt p).1 level) *
            (2 : Real) ^ (ρ * ρ)) /
          (4 : Real) ^ (ρ * ρ) :=
        div_le_div_of_nonneg_right hcardReal hfour.le
      _ = _ := by
        rw [hpow]
        field_simp
  have hx : (isingLeapfrogBoxInt p).1 = level - 1 := by omega
  calc
    _ ≤ _ := hreduce
    _ ≤ 4 / (ρ : Real) := by
      rw [hx]
      exact horizontalNoHit_diffusive_weight_le ρ level hρ

theorem killedChoiceNoHitAll_diffusive_weight_le_upper
    (R ρ : Nat) (p : IsingLeapfrogBox R) (level : Int)
    (hstart : (isingLeapfrogBoxInt p).1 = level + 1) (hρ : 0 < ρ) :
    Nat.card (IsingLeapfrogKilledChoiceNoHitAll R (ρ * ρ) p level) /
        (4 : Real) ^ (ρ * ρ) ≤ 4 / (ρ : Real) := by
  have hcard := natCard_killedChoiceNoHitAll_le_horizontal_mul_pow
    R (ρ * ρ) p level
  have hcardReal :
      (Nat.card (IsingLeapfrogKilledChoiceNoHitAll R (ρ * ρ) p level) :
          Real) ≤
        Nat.card (IsingHorizontalNoHitFamily (ρ * ρ)
            (isingLeapfrogBoxInt p).1 level) *
          (2 : Real) ^ (ρ * ρ) := by
    exact_mod_cast hcard
  have htwo : 0 < (2 : Real) ^ (ρ * ρ) := by positivity
  have hfour : 0 < (4 : Real) ^ (ρ * ρ) := by positivity
  have hpow : (4 : Real) ^ (ρ * ρ) =
      (2 : Real) ^ (ρ * ρ) * (2 : Real) ^ (ρ * ρ) := by
    rw [show (4 : Real) = 2 * 2 by norm_num, mul_pow]
  calc
    _ ≤ (Nat.card (IsingHorizontalNoHitFamily (ρ * ρ)
              (isingLeapfrogBoxInt p).1 level) *
            (2 : Real) ^ (ρ * ρ)) /
          (4 : Real) ^ (ρ * ρ) :=
      div_le_div_of_nonneg_right hcardReal hfour.le
    _ = Nat.card (IsingHorizontalNoHitFamily (ρ * ρ)
              (isingLeapfrogBoxInt p).1 level) /
          (2 : Real) ^ (ρ * ρ) := by
      rw [hpow]
      field_simp
    _ ≤ 4 / (ρ : Real) := by
      rw [hstart]
      exact horizontalNoHit_diffusive_weight_le_upper ρ level hρ

private def SurvivalExceptionalFirstHitBoxSigma
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :=
  Σ q : IsingLeapfrogBox R,
    SurvivalExceptionalFirstHitFamily R (isingLeapfrogBoxInt p) level t
      (isingLeapfrogBoxInt q)

private def SurvivalExceptionalMirrorBoxSigma
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :=
  Σ q : IsingLeapfrogBox R,
    SurvivalExceptionalMirrorFamily R (isingLeapfrogBoxInt p) level t
      (isingLeapfrogBoxInt q)

private def survivalExceptionalFirstHitBoxSigmaToAll
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :
    SurvivalExceptionalFirstHitBoxSigma R t p level →
      SurvivalExceptionalFirstHitFamilyAll R (isingLeapfrogBoxInt p) level t :=
  fun w => ⟨isingLeapfrogBoxInt w.1, w.2⟩

private theorem survivalExceptionalFirstHitBoxSigmaToAll_injective
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :
    Function.Injective
      (survivalExceptionalFirstHitBoxSigmaToAll R t p level) := by
  intro a b h
  rcases Sigma.ext_iff.mp h with ⟨htarget, hw⟩
  exact Sigma.ext (isingLeapfrogBoxInt_injective htarget) hw

private def survivalExceptionalMirrorBoxSigmaToAll
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :
    SurvivalExceptionalMirrorBoxSigma R t p level →
      SurvivalExceptionalMirrorFamilyAll R (isingLeapfrogBoxInt p) level t :=
  fun w => ⟨isingLeapfrogBoxInt w.1, w.2⟩

private theorem survivalExceptionalMirrorBoxSigmaToAll_injective
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :
    Function.Injective
      (survivalExceptionalMirrorBoxSigmaToAll R t p level) := by
  intro a b h
  rcases Sigma.ext_iff.mp h with ⟨htarget, hw⟩
  exact Sigma.ext (isingLeapfrogBoxInt_injective htarget) hw



theorem isingLeapfrogKilledKernel_reflectedStart_l1_le
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p)) :
    (∑ q, |isingLeapfrogKilledKernel R t p q -
        isingLeapfrogKilledKernel R t p' q|) ≤
      Nat.card (SurvivalExceptionalFirstHitFamilyAll R
          (isingLeapfrogBoxInt p) level t) / (4 : Real) ^ t +
        Nat.card (SurvivalExceptionalMirrorFamilyAll R
          (isingLeapfrogBoxInt p) level t) / (4 : Real) ^ t +
        Nat.card (IsingLeapfrogKilledChoiceNoHitAll R t p level) /
          (4 : Real) ^ t +
        Nat.card (IsingLeapfrogKilledChoiceNoHitAll R t p' level) /
          (4 : Real) ^ t := by
  let D := (4 : Real) ^ t
  have hD : 0 < D := by positivity
  have hpoint (q : IsingLeapfrogBox R) :
      |isingLeapfrogKilledKernel R t p q -
          isingLeapfrogKilledKernel R t p' q| ≤
        Nat.card (SurvivalExceptionalFirstHitFamily R
            (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q)) / D +
          Nat.card (SurvivalExceptionalMirrorFamily R
            (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q)) / D +
          Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) / D +
          Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p' q level) / D := by
    have hbase := isingLeapfrogKilledKernel_reflectedStart_abs_le
      R t p p' q level hmirror
    have hdist := natDist_survivingFirstHitFamily_le_exceptions R
      (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q)
    have hdistReal :
        (Nat.dist
          (Nat.card (SurvivingFirstHitFamily R (isingLeapfrogBoxInt p)
            level t (isingLeapfrogBoxInt q)))
          (Nat.card (SurvivingFirstHitFamily R
            (reflectedEndpoint level (isingLeapfrogBoxInt p)) level t
            (isingLeapfrogBoxInt q))) : Real) ≤
          Nat.card (SurvivalExceptionalFirstHitFamily R
            (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q)) +
          Nat.card (SurvivalExceptionalMirrorFamily R
            (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q)) := by
      exact_mod_cast hdist
    have hdiv := div_le_div_of_nonneg_right hdistReal hD.le
    dsimp [D] at hbase ⊢
    calc
      _ ≤ _ := hbase
      _ ≤ (Nat.card (SurvivalExceptionalFirstHitFamily R
              (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q)) +
            Nat.card (SurvivalExceptionalMirrorFamily R
              (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q))) /
            (4 : Real) ^ t +
          Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) /
            (4 : Real) ^ t +
          Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p' q level) /
            (4 : Real) ^ t := by
        dsimp [D] at hdiv
        exact add_le_add_left (add_le_add_left hdiv _) _
      _ = _ := by ring
  have hsum :
      (∑ q, |isingLeapfrogKilledKernel R t p q -
        isingLeapfrogKilledKernel R t p' q|) ≤
      ∑ q, (Nat.card (SurvivalExceptionalFirstHitFamily R
            (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q)) / D +
          Nat.card (SurvivalExceptionalMirrorFamily R
            (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q)) / D +
          Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) / D +
          Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p' q level) / D) :=
    Finset.sum_le_sum (fun q _ => hpoint q)
  simp only [Finset.sum_add_distrib] at hsum
  have hsourceNat :
      ∑ q : IsingLeapfrogBox R, Nat.card (SurvivalExceptionalFirstHitFamily R
          (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q)) ≤
        Nat.card (SurvivalExceptionalFirstHitFamilyAll R
          (isingLeapfrogBoxInt p) level t) := by
    rw [← Nat.card_sigma]
    exact Nat.card_le_card_of_injective
      (survivalExceptionalFirstHitBoxSigmaToAll R t p level)
      (survivalExceptionalFirstHitBoxSigmaToAll_injective R t p level)
  have hmirrorNat :
      ∑ q : IsingLeapfrogBox R, Nat.card (SurvivalExceptionalMirrorFamily R
          (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q)) ≤
        Nat.card (SurvivalExceptionalMirrorFamilyAll R
          (isingLeapfrogBoxInt p) level t) := by
    rw [← Nat.card_sigma]
    exact Nat.card_le_card_of_injective
      (survivalExceptionalMirrorBoxSigmaToAll R t p level)
      (survivalExceptionalMirrorBoxSigmaToAll_injective R t p level)
  have hsourceReal :
      (∑ q : IsingLeapfrogBox R, (Nat.card (SurvivalExceptionalFirstHitFamily R
          (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q)) : Real)) / D ≤
        Nat.card (SurvivalExceptionalFirstHitFamilyAll R
          (isingLeapfrogBoxInt p) level t) / D := by
    apply div_le_div_of_nonneg_right _ hD.le
    exact_mod_cast hsourceNat
  have hmirrorReal :
      (∑ q : IsingLeapfrogBox R, (Nat.card (SurvivalExceptionalMirrorFamily R
          (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q)) : Real)) / D ≤
        Nat.card (SurvivalExceptionalMirrorFamilyAll R
          (isingLeapfrogBoxInt p) level t) / D := by
    apply div_le_div_of_nonneg_right _ hD.le
    exact_mod_cast hmirrorNat
  have hnohit := natCard_killedChoiceNoHitAll_eq_sum R t p level
  have hnohit' := natCard_killedChoiceNoHitAll_eq_sum R t p' level
  have hnohitReal :
      ∑ q, (Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) :
        Real) = Nat.card (IsingLeapfrogKilledChoiceNoHitAll R t p level) := by
    exact_mod_cast hnohit.symm
  have hnohitReal' :
      ∑ q, (Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p' q level) :
        Real) = Nat.card (IsingLeapfrogKilledChoiceNoHitAll R t p' level) := by
    exact_mod_cast hnohit'.symm
  dsimp [D] at hsum hsourceReal hmirrorReal ⊢
  simp_rw [← Finset.sum_div] at hsum
  rw [hnohitReal, hnohitReal'] at hsum
  exact le_trans hsum (by linarith)



theorem isingLeapfrogKilledKernel_reflectedStart_diffusive_l1_le
    (R level ρ : Nat) (p p' : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < ρ) (hleft : ρ + 1 ≤ level)
    (hright : level + 1 + ρ ≤ R) :
    (∑ q, |isingLeapfrogKilledKernel R (ρ * ρ) p q -
        isingLeapfrogKilledKernel R (ρ * ρ) p' q|) ≤
      10 / (ρ : Real) := by
  have hbase := isingLeapfrogKilledKernel_reflectedStart_l1_le R
    (ρ * ρ) p p' (level : Int) hmirror
  have hlevel : 0 < level := by omega
  have hgap : level + 1 < R := by omega
  have hsource :=
    survivalExceptionalFirstHitFamilyAll_weight_le_inv_rightGap R level
      (ρ * ρ) (isingLeapfrogBoxInt p) hstart hlevel hgap
  have hmirrorExc :=
    survivalExceptionalMirrorFamilyAll_weight_le_inv_leftGap R level
      (ρ * ρ) (isingLeapfrogBoxInt p) hstart hlevel
  have hnohit := killedChoiceNoHitAll_diffusive_weight_le R ρ p
    (level : Int) hstart hρ
  have hp' : (isingLeapfrogBoxInt p').1 = (level : Int) + 1 := by
    rw [hmirror]
    unfold reflectedEndpoint
    dsimp
    omega
  have hnohit' := killedChoiceNoHitAll_diffusive_weight_le_upper R ρ p'
    (level : Int) hp' hρ
  have hρReal : 0 < (ρ : Real) := by positivity
  have hrightGap : (ρ : Real) ≤ (R - level : Nat) := by
    exact_mod_cast (show ρ ≤ R - level by omega)
  have hleftGap : (ρ : Real) ≤ level := by
    exact_mod_cast (show ρ ≤ level by omega)
  have hinvRight : 1 / ((R - level : Nat) : Real) ≤
      1 / (ρ : Real) := one_div_le_one_div_of_le hρReal hrightGap
  have hinvLeft : 1 / (level : Real) ≤
      1 / (ρ : Real) := one_div_le_one_div_of_le hρReal hleftGap
  calc
    _ ≤ _ := hbase
    _ ≤ 1 / ((R - level : Nat) : Real) + 1 / (level : Real) +
        4 / (ρ : Real) + 4 / (ρ : Real) := by
      exact add_le_add (add_le_add (add_le_add hsource hmirrorExc) hnohit) hnohit'
    _ ≤ 1 / (ρ : Real) + 1 / (ρ : Real) +
        4 / (ρ : Real) + 4 / (ρ : Real) := by
      exact add_le_add (add_le_add (add_le_add hinvRight hinvLeft) (le_refl _))
        (le_refl _)
    _ = 10 / (ρ : Real) := by ring

end

end StatMech.Universality
