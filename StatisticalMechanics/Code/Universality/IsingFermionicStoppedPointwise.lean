/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicStoppedCoupling











namespace StatMech.Universality

open IsingDiagonalWalkHitSplit

private theorem natCard_subtype_eq_sum_ite_pointwise
    {Omega : Type*} [Fintype Omega]
    (p : Omega -> Prop) [DecidablePred p] :
    Nat.card {x : Omega // p x} =
      ∑ x : Omega, if p x then 1 else 0 := by
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card {x : Omega // p x} =
        Fintype.card (↑(Finset.univ.filter p)) :=
      Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by simp))
    _ = (Finset.univ.filter p).card := Fintype.card_coe _
    _ = ∑ x : Omega, if p x then 1 else 0 := by
      rw [Finset.card_filter]



theorem finiteUniformCoupling_fiber_abs_le_badAt
    {Omega A : Type*} [Fintype Omega] [Fintype A] [DecidableEq A]
    (e : Omega ≃ Omega) (f g : Omega -> A) (a : A) :
    |((Nat.card {w : Omega // f w = a} : Nat) : Real) -
        ((Nat.card {w : Omega // g w = a} : Nat) : Real)| <=
      (Nat.card {w : Omega //
        f w ≠ g (e w) /\ (f w = a \/ g (e w) = a)} : Nat) := by
  classical
  have hfiber :
      (((Nat.card {w : Omega // f w = a} : Nat) : Real) -
          ((Nat.card {w : Omega // g w = a} : Nat) : Real)) =
        ∑ w : Omega, ((if f w = a then 1 else 0) -
          (if g (e w) = a then 1 else 0) : Real) := by
    rw [natCard_subtype_eq_sum_ite_pointwise,
      natCard_subtype_eq_sum_ite_pointwise]
    push_cast
    rw [Finset.sum_sub_distrib]
    congr 1
    exact (Equiv.sum_comp e
      (fun w : Omega => if g w = a then (1 : Real) else 0)).symm
  rw [hfiber]
  calc
    |∑ w : Omega, ((if f w = a then 1 else 0) -
        (if g (e w) = a then 1 else 0) : Real)| <=
        ∑ w : Omega, |((if f w = a then 1 else 0) -
          (if g (e w) = a then 1 else 0) : Real)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ w : Omega,
        if f w ≠ g (e w) /\ (f w = a \/ g (e w) = a)
        then (1 : Real) else 0 := by
      apply Finset.sum_congr rfl
      intro w hw
      by_cases hf : f w = a
      · by_cases hg : g (e w) = a
        · simp [hf, hg]
        · have hane : a ≠ g (e w) := fun h => hg h.symm
          simp [hf, hg, hane]
      · by_cases hg : g (e w) = a
        · simp [hf, hg]
        · simp [hf, hg]
    _ = (Nat.card {w : Omega //
        f w ≠ g (e w) /\ (f w = a \/ g (e w) = a)} : Nat) := by
      rw [natCard_subtype_eq_sum_ite_pointwise]
      push_cast
      rfl


def IsingLeapfrogStoppedCouplingBadAtFamily
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :=
  {w : IsingLeapfrogChoiceStringFamily t //
    isingLeapfrogChoiceRun R p w.1 ≠
      isingLeapfrogChoiceRun R p'
        (isingLeapfrogCouplingChoiceTransform t
          (isingLeapfrogBoxInt p) level w).1 /\
      (isingLeapfrogChoiceRun R p w.1 = q \/
        isingLeapfrogChoiceRun R p'
          (isingLeapfrogCouplingChoiceTransform t
            (isingLeapfrogBoxInt p) level w).1 = q)}

noncomputable instance isingLeapfrogStoppedCouplingBadAtFamily_finite
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Finite (IsingLeapfrogStoppedCouplingBadAtFamily R t p p' q level) := by
  exact Finite.of_injective
    (fun w : IsingLeapfrogStoppedCouplingBadAtFamily R t p p' q level => w.1)
    Subtype.val_injective



theorem isingLeapfrogStoppedKernel_reflectionCoupling_abs_le_badAt
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    |isingLeapfrogStoppedKernel R t p q -
        isingLeapfrogStoppedKernel R t p' q| <=
      (Nat.card
        (IsingLeapfrogStoppedCouplingBadAtFamily R t p p' q level) : Real) /
          (4 : Real) ^ t := by
  classical
  letI := Fintype.ofFinite (IsingLeapfrogChoiceStringFamily t)
  let e := isingLeapfrogCouplingChoiceEquiv t
    (isingLeapfrogBoxInt p) level
  let f : IsingLeapfrogChoiceStringFamily t -> IsingLeapfrogBox R :=
    fun w => isingLeapfrogChoiceRun R p w.1
  let g : IsingLeapfrogChoiceStringFamily t -> IsingLeapfrogBox R :=
    fun w => isingLeapfrogChoiceRun R p' w.1
  have hcount := finiteUniformCoupling_fiber_abs_le_badAt e f g q
  have hden : 0 < (4 : Real) ^ t := by positivity
  have hfiber :
      Nat.card (IsingLeapfrogStoppedChoicePathFamily R t p q) =
        Nat.card {w : IsingLeapfrogChoiceStringFamily t // f w = q} :=
    Nat.card_congr (isingLeapfrogStoppedChoicePathFiberEquiv R t p q)
  have hfiber' :
      Nat.card (IsingLeapfrogStoppedChoicePathFamily R t p' q) =
        Nat.card {w : IsingLeapfrogChoiceStringFamily t // g w = q} :=
    Nat.card_congr (isingLeapfrogStoppedChoicePathFiberEquiv R t p' q)
  simp_rw [isingLeapfrogStoppedKernel_eq_natCard_choicePath_div]
  rw [hfiber, hfiber', div_sub_div_same, abs_div, abs_of_pos hden]
  apply div_le_div_of_nonneg_right _ hden.le
  simpa only [e, f, g, IsingLeapfrogStoppedCouplingBadAtFamily] using hcount



theorem isingLeapfrogExitKernel_reflectionCoupling_abs_le_badAt
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    |isingLeapfrogExitKernel R t p q -
        isingLeapfrogExitKernel R t p' q| <=
      (Nat.card
        (IsingLeapfrogStoppedCouplingBadAtFamily R t p p' q level) : Real) /
          (4 : Real) ^ t := by
  by_cases hq : isingLeapfrogBoxBoundary R q
  · simpa [isingLeapfrogExitKernel, hq] using
      isingLeapfrogStoppedKernel_reflectionCoupling_abs_le_badAt
        R t p p' q level
  · simp only [isingLeapfrogExitKernel, hq, if_false, sub_self, abs_zero]
    positivity





def IsingLeapfrogChoiceNoHitAtFamily
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :=
  {w : IsingLeapfrogChoiceStringFamily t //
    (forall k, k <= t ->
      lineFreeEndpoint (isingLeapfrogBoxInt p).1
        ((w.1.map Prod.fst).take k) ≠ level) /\
    (isingLeapfrogChoiceRun R p w.1 = q \/
      isingLeapfrogChoiceRun R p'
        (isingLeapfrogCouplingChoiceTransform t
          (isingLeapfrogBoxInt p) level w).1 = q)}


def IsingStoppedCouplingSourceFailureAtFamily
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :=
  {w : IsingLeapfrogChoiceStringFamily t //
    IsingStoppedCouplingSourceFailure R p level w /\
    (isingLeapfrogChoiceRun R p w.1 = q \/
      isingLeapfrogChoiceRun R p'
        (isingLeapfrogCouplingChoiceTransform t
          (isingLeapfrogBoxInt p) level w).1 = q)}


def IsingStoppedCouplingMirrorFailureAtFamily
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :=
  {w : IsingLeapfrogChoiceStringFamily t //
    IsingStoppedCouplingMirrorFailure R p p' level w /\
    (isingLeapfrogChoiceRun R p w.1 = q \/
      isingLeapfrogChoiceRun R p'
        (isingLeapfrogCouplingChoiceTransform t
          (isingLeapfrogBoxInt p) level w).1 = q)}

noncomputable instance isingLeapfrogChoiceNoHitAtFamily_finite
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Finite (IsingLeapfrogChoiceNoHitAtFamily R t p p' q level) := by
  exact Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance isingStoppedCouplingSourceFailureAtFamily_finite
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Finite
      (IsingStoppedCouplingSourceFailureAtFamily R t p p' q level) := by
  exact Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance isingStoppedCouplingMirrorFailureAtFamily_finite
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Finite
      (IsingStoppedCouplingMirrorFailureAtFamily R t p p' q level) := by
  exact Finite.of_injective Subtype.val Subtype.val_injective

private noncomputable def stoppedCouplingBadAtCover
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p)) :
    IsingLeapfrogStoppedCouplingBadAtFamily R t p p' q level ->
      Sum (IsingLeapfrogChoiceNoHitAtFamily R t p p' q level)
        (Sum
          (IsingStoppedCouplingSourceFailureAtFamily R t p p' q level)
          (IsingStoppedCouplingMirrorFailureAtFamily R t p p' q level)) :=
  fun w => by
    classical
    let wb : IsingLeapfrogStoppedCouplingBadFamily R t p p' level :=
      ⟨w.1, w.2.1⟩
    by_cases hn : forall k, k <= t ->
        lineFreeEndpoint (isingLeapfrogBoxInt p).1
          ((w.1.1.map Prod.fst).take k) ≠ level
    · exact Sum.inl ⟨w.1, hn, w.2.2⟩
    · by_cases hs : IsingStoppedCouplingSourceFailure R p level w.1
      · exact Sum.inr (Sum.inl ⟨w.1, hs, w.2.2⟩)
      · exact Sum.inr (Sum.inr ⟨w.1, by
          exact (stoppedCouplingBad_cases R t p p' level hmirror wb)
            |>.resolve_left hn |>.resolve_left hs, w.2.2⟩)

private def stoppedCouplingBadAtCoverValue
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Sum (IsingLeapfrogChoiceNoHitAtFamily R t p p' q level)
        (Sum
          (IsingStoppedCouplingSourceFailureAtFamily R t p p' q level)
          (IsingStoppedCouplingMirrorFailureAtFamily R t p p' q level)) ->
      IsingLeapfrogChoiceStringFamily t :=
  Sum.elim (fun w => w.1)
    (Sum.elim (fun w => w.1) (fun w => w.1))

private theorem stoppedCouplingBadAtCoverValue_apply
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p))
    (w : IsingLeapfrogStoppedCouplingBadAtFamily R t p p' q level) :
    stoppedCouplingBadAtCoverValue R t p p' q level
      (stoppedCouplingBadAtCover R t p p' q level hmirror w) = w.1 := by
  classical
  by_cases hn : forall k, k <= t ->
      lineFreeEndpoint (isingLeapfrogBoxInt p).1
        ((w.1.1.map Prod.fst).take k) ≠ level
  · unfold stoppedCouplingBadAtCover
    dsimp only
    rw [dif_pos (by
      intro k hk
      exact hn k hk)]
    rfl
  · by_cases hs : IsingStoppedCouplingSourceFailure R p level w.1
    · unfold stoppedCouplingBadAtCover
      dsimp only
      rw [dif_neg (by
        intro h
        apply hn
        intro k hk
        exact h k hk), dif_pos hs]
      rfl
    · unfold stoppedCouplingBadAtCover
      dsimp only
      rw [dif_neg (by
        intro h
        apply hn
        intro k hk
        exact h k hk), dif_neg hs]
      rfl

private theorem stoppedCouplingBadAtCover_injective
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p)) :
    Function.Injective
      (stoppedCouplingBadAtCover R t p p' q level hmirror) := by
  intro a b hab
  apply Subtype.ext
  rw [<- stoppedCouplingBadAtCoverValue_apply R t p p' q level hmirror a,
    <- stoppedCouplingBadAtCoverValue_apply R t p p' q level hmirror b,
    hab]



theorem natCard_stoppedCouplingBadAt_le_endpointFailures
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p)) :
    Nat.card
        (IsingLeapfrogStoppedCouplingBadAtFamily R t p p' q level) <=
      Nat.card (IsingLeapfrogChoiceNoHitAtFamily R t p p' q level) +
      Nat.card
          (IsingStoppedCouplingSourceFailureAtFamily R t p p' q level) +
        Nat.card
          (IsingStoppedCouplingMirrorFailureAtFamily R t p p' q level) := by
  calc
    _ <= Nat.card
        (Sum (IsingLeapfrogChoiceNoHitAtFamily R t p p' q level)
          (Sum
            (IsingStoppedCouplingSourceFailureAtFamily R t p p' q level)
            (IsingStoppedCouplingMirrorFailureAtFamily R t p p' q level))) :=
      Nat.card_le_card_of_injective
        (stoppedCouplingBadAtCover R t p p' q level hmirror)
        (stoppedCouplingBadAtCover_injective R t p p' q level hmirror)
    _ = _ := by rw [Nat.card_sum, Nat.card_sum]; omega



theorem isingLeapfrogStoppedKernel_reflectedStart_abs_le_of_endpointFailures
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p))
    (C : Real)
    (hfail :
      ((Nat.card (IsingLeapfrogChoiceNoHitAtFamily
            R t p p' q level) +
          Nat.card (IsingStoppedCouplingSourceFailureAtFamily
            R t p p' q level) +
          Nat.card (IsingStoppedCouplingMirrorFailureAtFamily
            R t p p' q level) : Nat) : Real) / (4 : Real) ^ t <= C) :
    |isingLeapfrogStoppedKernel R t p q -
        isingLeapfrogStoppedKernel R t p' q| <= C := by
  have hcard := natCard_stoppedCouplingBadAt_le_endpointFailures
    R t p p' q level hmirror
  have hcardReal :
      (Nat.card
          (IsingLeapfrogStoppedCouplingBadAtFamily R t p p' q level) :
        Real) <=
      ((Nat.card (IsingLeapfrogChoiceNoHitAtFamily
            R t p p' q level) +
          Nat.card (IsingStoppedCouplingSourceFailureAtFamily
            R t p p' q level) +
          Nat.card (IsingStoppedCouplingMirrorFailureAtFamily
            R t p p' q level) : Nat) : Real) := by
    exact_mod_cast hcard
  calc
    _ <= (Nat.card
        (IsingLeapfrogStoppedCouplingBadAtFamily R t p p' q level) :
          Real) / (4 : Real) ^ t :=
      isingLeapfrogStoppedKernel_reflectionCoupling_abs_le_badAt
        R t p p' q level
    _ <= ((Nat.card (IsingLeapfrogChoiceNoHitAtFamily
            R t p p' q level) +
          Nat.card (IsingStoppedCouplingSourceFailureAtFamily
            R t p p' q level) +
          Nat.card (IsingStoppedCouplingMirrorFailureAtFamily
            R t p p' q level) : Nat) : Real) / (4 : Real) ^ t :=
      div_le_div_of_nonneg_right hcardReal (by positivity)
    _ <= C := hfail



theorem isingLeapfrogExitKernel_reflectedStart_abs_le_of_endpointFailures
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p))
    (C : Real)
    (hfail :
      ((Nat.card (IsingLeapfrogChoiceNoHitAtFamily
            R t p p' q level) +
          Nat.card (IsingStoppedCouplingSourceFailureAtFamily
            R t p p' q level) +
          Nat.card (IsingStoppedCouplingMirrorFailureAtFamily
            R t p p' q level) : Nat) : Real) / (4 : Real) ^ t <= C) :
    |isingLeapfrogExitKernel R t p q -
        isingLeapfrogExitKernel R t p' q| <= C := by
  by_cases hq : isingLeapfrogBoxBoundary R q
  · simpa [isingLeapfrogExitKernel, hq] using
      isingLeapfrogStoppedKernel_reflectedStart_abs_le_of_endpointFailures
        R t p p' q level hmirror C hfail
  · have hC : 0 <= C := by
      exact le_trans (by positivity) hfail
    simp [isingLeapfrogExitKernel, hq, hC]

end StatMech.Universality
