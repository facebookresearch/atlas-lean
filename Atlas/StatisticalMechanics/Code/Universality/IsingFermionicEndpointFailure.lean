/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicEndpointEscape
import Code.Universality.IsingFermionicOrderedEndpointConvolution
import Code.Universality.IsingFermionicTailEndpointRace





namespace StatMech.Universality

open Finset
open IsingDiagonalWalkHitSplit

noncomputable section


def IsingSourceFailureOutputAtFamily
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int) :=
  {w : IsingStoppedCouplingSourceFailureFamily R t p level //
    isingLeapfrogChoiceRun R p w.1.1 = q}

noncomputable instance isingSourceFailureOutputAtFamily_finite
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int) :
    Finite (IsingSourceFailureOutputAtFamily R t p q level) := by
  exact Finite.of_injective Subtype.val Subtype.val_injective

private theorem isingLeapfrogChoiceRun_of_boundary_endpointFailure
    (R : Nat) (p : IsingLeapfrogBox R)
    (hp : isingLeapfrogBoxBoundary R p) (bs : List (Bool × Bool)) :
    isingLeapfrogChoiceRun R p bs = p := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [isingLeapfrogChoiceRun]
      rw [show isingLeapfrogChoiceNext R p b = p by
        simp [isingLeapfrogChoiceNext, hp]]
      exact ih

private theorem prodBits_zip_self_endpointFailure
    (bs : List (Bool × Bool)) :
    (bs.map Prod.fst).zip (bs.map Prod.snd) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [ih]

private theorem map_fst_zip_of_length_eq_endpointFailure
    (xs ys : List Bool) (h : xs.length = ys.length) :
    (xs.zip ys).map Prod.fst = xs := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at h
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at h
          simp [ih ys h]

private theorem map_snd_zip_of_length_eq_endpointFailure
    (xs ys : List Bool) (h : xs.length = ys.length) :
    (xs.zip ys).map Prod.snd = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at h
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at h
          simp [ih ys h]

private theorem lineFreeEndpoint_append_endpointFailure
    (start : Int) (a b : List Bool) :
    lineFreeEndpoint start (a ++ b) =
      lineFreeEndpoint (lineFreeEndpoint start a) b := by
  induction a generalizing start with
  | nil => rfl
  | cons x a ih =>
      cases x <;> simp only [List.cons_append, lineFreeEndpoint] <;>
        exact ih _

private def verticalBoundaryAtEndpointFailure
    (R : Nat) (start : Int) (ys : List Bool) (j : Nat) : Prop :=
  j <= ys.length /\
    (lineFreeEndpoint start (ys.take j) = 0 \/
      lineFreeEndpoint start (ys.take j) = R)

private noncomputable def firstVerticalBoundaryTimeEndpointFailure
    (R : Nat) (start : Int) (ys : List Bool) : Nat := by
  classical
  exact if h : exists j, verticalBoundaryAtEndpointFailure R start ys j then
      Nat.find h
    else ys.length

private theorem firstVerticalBoundaryTimeEndpointFailure_eq
    (R : Nat) (start : Int) (ys : List Bool) (j : Nat)
    (hj : j <= ys.length)
    (hboundary : lineFreeEndpoint start (ys.take j) = 0 \/
      lineFreeEndpoint start (ys.take j) = R)
    (hminimal : forall l, l < j ->
      lineFreeEndpoint start (ys.take l) ≠ 0 /\
        lineFreeEndpoint start (ys.take l) ≠ R) :
    firstVerticalBoundaryTimeEndpointFailure R start ys = j := by
  classical
  let hex : exists k, verticalBoundaryAtEndpointFailure R start ys k :=
    ⟨j, hj, hboundary⟩
  unfold firstVerticalBoundaryTimeEndpointFailure
  rw [dif_pos hex]
  apply Nat.le_antisymm
  · exact Nat.find_min' hex ⟨hj, hboundary⟩
  · by_contra hnot
    have hlt : Nat.find hex < j := by omega
    have hspec := Nat.find_spec hex
    rcases hspec.2 with hzero | hR
    · exact (hminimal (Nat.find hex) hlt).1 hzero
    · exact (hminimal (Nat.find hex) hlt).2 hR



private noncomputable def sourceEndpointRaceTarget
    (R t rho : Nat) (p q : IsingLeapfrogBox R)
    (j : Fin (t + 1)) (pref : IsingLineFirstBoundaryFamily rho j)
    (tail : IsingEndpointRaceTail t j) : Int :=
  let ys := pref.1 ++ tail.1.map Prod.snd
  let stop := firstVerticalBoundaryTimeEndpointFailure
    R (isingLeapfrogBoxInt p).2 ys
  (isingLeapfrogBoxInt q).1 -
    lineFreeEndpoint 0 ((tail.1.map Prod.fst).take (stop - (j : Nat)))

private theorem firstVerticalBoundaryTime_of_sourceBoundary
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int)
    (w : IsingSourceFailureOutputAtFamily R t p q level)
    (j : Nat) (hjT : j <= t)
    (hminimal : forall l, l < j -> ¬ isingLeapfrogBoxBoundary R
      (isingLeapfrogChoiceRun R p (w.1.1.1.take l)))
    (hrun : isingLeapfrogBoxInt
        (isingLeapfrogChoiceRun R p (w.1.1.1.take j)) =
      isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceSteps (w.1.1.1.take j)))
    (hprefixQ : isingLeapfrogChoiceRun R p (w.1.1.1.take j) = q)
    (hqVertical : q.2.1 = 0 \/ q.2.1 = R) :
    firstVerticalBoundaryTimeEndpointFailure R
      (isingLeapfrogBoxInt p).2 (w.1.1.1.map Prod.snd) = j := by
  apply firstVerticalBoundaryTimeEndpointFailure_eq
  · simpa [w.1.1.2] using hjT
  · rw [← List.map_take, lineFreeEndpoint_choiceVertical_full]
    have hry := congrArg Prod.snd hrun
    rw [hprefixQ] at hry
    rcases hqVertical with hq0 | hqR
    · left
      rw [← hry]
      unfold isingLeapfrogBoxInt
      dsimp
      exact_mod_cast hq0
    · right
      rw [← hry]
      unfold isingLeapfrogBoxInt
      dsimp
      exact_mod_cast hqR
  · intro l hl
    have hexec : IsingLeapfrogChoiceExecValid R p (w.1.1.1.take l) := by
      intro r hr
      rw [List.length_take] at hr
      have hrl : r < l := by omega
      simpa [List.take_take, Nat.min_eq_left hrl.le] using
        hminimal r (hrl.trans hl)
    have hrunl := choiceExecValid_run_boxInt_eq_endpoint R p
      (w.1.1.1.take l) hexec
    have hry := congrArg Prod.snd hrunl
    change ((isingLeapfrogChoiceRun R p (w.1.1.1.take l)).2.1 : Int) =
      (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceSteps (w.1.1.1.take l))).2 at hry
    have hline : lineFreeEndpoint (isingLeapfrogBoxInt p).2
        ((w.1.1.1.map Prod.snd).take l) =
        ((isingLeapfrogChoiceRun R p (w.1.1.1.take l)).2.1 : Int) := by
      rw [← List.map_take, lineFreeEndpoint_choiceVertical_full, ← hry]
    constructor
    · intro hzero
      apply hminimal l hl
      unfold isingLeapfrogBoxBoundary
      right; right; left
      rw [hline] at hzero
      exact_mod_cast hzero
    · intro hR
      apply hminimal l hl
      unfold isingLeapfrogBoxBoundary
      right; right; right
      rw [hline] at hR
      have : (isingLeapfrogChoiceRun R p
          (w.1.1.1.take l)).2.1 = R := by exact_mod_cast hR
      omega

private theorem exists_sourceFailureOutput_transverseWitness
    (R level rho t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hbottom : rho <= p.2.1)
    (htop : p.2.1 + rho <= R)
    (hqVertical : q.2.1 = 0 \/ q.2.1 = R)
    (w : IsingSourceFailureOutputAtFamily R t p q (level : Int)) :
    exists z : IsingTransverseRaceWitnessFamily rho t (level : Int),
      transverseRaceWitnessValue rho t (level : Int) z = w.1.1 /\
        (z.1 : Nat) <= firstVerticalBoundaryTimeEndpointFailure R
          (isingLeapfrogBoxInt p).2 (w.1.1.1.map Prod.snd) := by
  have hstartLt : (isingLeapfrogBoxInt p).1 < (level : Int) := by omega
  rcases sourceFailure_boundary_data R t p (level : Int) hstartLt w.1 with
    ⟨split, j, hsplit, hj, hb, hminimal, hxlt, hrun⟩
  have hjT : j <= t := by
    have hlen := congrArg List.length (firstHitSplit_steps hsplit)
    simp [IsingDiagonalWalkHitSplit.steps, isingLeapfrogChoiceSteps,
      w.1.1.2] at hlen
    omega
  have hprefixQ : isingLeapfrogChoiceRun R p (w.1.1.1.take j) = q := by
    have hdecomp : w.1.1.1 = w.1.1.1.take j ++ w.1.1.1.drop j :=
      (List.take_append_drop j w.1.1.1).symm
    have hfull : isingLeapfrogChoiceRun R p w.1.1.1 =
        isingLeapfrogChoiceRun R p (w.1.1.1.take j) := by
      calc
        _ = isingLeapfrogChoiceRun R p
            (w.1.1.1.take j ++ w.1.1.1.drop j) := by rw [← hdecomp]
        _ = isingLeapfrogChoiceRun R
            (isingLeapfrogChoiceRun R p (w.1.1.1.take j))
              (w.1.1.1.drop j) := isingLeapfrogChoiceRun_append_full ..
        _ = _ :=
          isingLeapfrogChoiceRun_of_boundary_endpointFailure R _ hb _
    exact hfull.symm.trans w.2
  rcases hqVertical with hqBottom | hqTop
  · have hyEnd : (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceSteps (w.1.1.1.take j))).2 <=
          (isingLeapfrogBoxInt p).2 - rho := by
      have hyrun := congrArg Prod.snd hrun
      rw [hprefixQ] at hyrun
      change ((q.2.1 : Nat) : Int) =
        (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
          (isingLeapfrogChoiceSteps (w.1.1.1.take j))).2 at hyrun
      have hbottomInt : (rho : Int) <= (isingLeapfrogBoxInt p).2 := by
        unfold isingLeapfrogBoxInt
        dsimp
        exact_mod_cast hbottom
      rw [show ((q.2.1 : Nat) : Int) = 0 by exact_mod_cast hqBottom] at hyrun
      omega
    rcases exists_vertical_barrier_prefix_lower rho hρ
      (isingLeapfrogBoxInt p) (w.1.1.1.take j) (by
        unfold isingLeapfrogBoxInt
        dsimp
        exact_mod_cast hbottom) hyEnd with ⟨s, hs, heq⟩
    have hsJ : s <= j := le_trans hs (List.length_take_le ..)
    rcases transverseWitness_of_barrier_exists rho t (level : Int) hρ
      (isingLeapfrogBoxInt p) (by omega) w.1.1 split hsplit j hj
      ⟨s, hsJ, Or.inl (by
        simpa [List.take_take, Nat.min_eq_left hsJ] using heq)⟩ with
      ⟨z, hz, hzj⟩
    refine ⟨z, hz, ?_⟩
    rw [firstVerticalBoundaryTime_of_sourceBoundary R t p q
      (level : Int) w j hjT hminimal hrun hprefixQ (Or.inl hqBottom)]
    exact hzj
  · have hyEnd : (isingLeapfrogBoxInt p).2 + rho <=
        (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
          (isingLeapfrogChoiceSteps (w.1.1.1.take j))).2 := by
      have hyrun := congrArg Prod.snd hrun
      rw [hprefixQ] at hyrun
      change ((q.2.1 : Nat) : Int) =
        (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
          (isingLeapfrogChoiceSteps (w.1.1.1.take j))).2 at hyrun
      have htopInt : (isingLeapfrogBoxInt p).2 + (rho : Int) <= R := by
        unfold isingLeapfrogBoxInt
        dsimp
        exact_mod_cast htop
      rw [show ((q.2.1 : Nat) : Int) = R by exact_mod_cast hqTop] at hyrun
      omega
    rcases exists_vertical_barrier_prefix rho hρ
      (isingLeapfrogBoxInt p) (w.1.1.1.take j) j (by simp [hjT]) (by
        unfold isingLeapfrogBoxInt
        dsimp
        exact_mod_cast hbottom) hyEnd with ⟨s, hs, heq⟩
    have hsJ : s <= j := le_trans hs (List.length_take_le ..)
    rcases transverseWitness_of_barrier_exists rho t (level : Int) hρ
      (isingLeapfrogBoxInt p) (by omega) w.1.1 split hsplit j hj
      ⟨s, hsJ, Or.inr (by
        simpa [List.take_take, Nat.min_eq_left hsJ] using heq)⟩ with
      ⟨z, hz, hzj⟩
    refine ⟨z, hz, ?_⟩
    rw [firstVerticalBoundaryTime_of_sourceBoundary R t p q
      (level : Int) w j hjT hminimal hrun hprefixQ (Or.inr hqTop)]
    exact hzj

private theorem sourceEndpointRaceTarget_eq
    (R level rho t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hqVertical : q.2.1 = 0 \/ q.2.1 = R)
    (w : IsingSourceFailureOutputAtFamily R t p q (level : Int))
    (z : IsingTransverseRaceWitnessFamily rho t (level : Int))
    (hz : transverseRaceWitnessValue rho t (level : Int) z = w.1.1)
    (hmark : (z.1 : Nat) <= firstVerticalBoundaryTimeEndpointFailure R
      (isingLeapfrogBoxInt p).2 (w.1.1.1.map Prod.snd)) :
    lineFreeEndpoint ((level : Int) - 1) z.2.1.1 =
      sourceEndpointRaceTarget R t rho p q z.1 z.2.2.1 z.2.2.2 := by
  have hstartLt : (isingLeapfrogBoxInt p).1 < (level : Int) := by omega
  rcases sourceFailure_boundary_data R t p (level : Int) hstartLt w.1 with
    ⟨split, j, hsplit, hj, hb, hminimal, hxlt, hrun⟩
  have hjT : j <= t := by
    have hlen := congrArg List.length (firstHitSplit_steps hsplit)
    simp [IsingDiagonalWalkHitSplit.steps, isingLeapfrogChoiceSteps,
      w.1.1.2] at hlen
    omega
  have hprefixQ : isingLeapfrogChoiceRun R p (w.1.1.1.take j) = q := by
    have hdecomp : w.1.1.1 = w.1.1.1.take j ++ w.1.1.1.drop j :=
      (List.take_append_drop j w.1.1.1).symm
    have hfull : isingLeapfrogChoiceRun R p w.1.1.1 =
        isingLeapfrogChoiceRun R p (w.1.1.1.take j) := by
      calc
        _ = isingLeapfrogChoiceRun R p
            (w.1.1.1.take j ++ w.1.1.1.drop j) := by rw [← hdecomp]
        _ = isingLeapfrogChoiceRun R
            (isingLeapfrogChoiceRun R p (w.1.1.1.take j))
              (w.1.1.1.drop j) := isingLeapfrogChoiceRun_append_full ..
        _ = _ :=
          isingLeapfrogChoiceRun_of_boundary_endpointFailure R _ hb _
    exact hfull.symm.trans w.2
  have hstop := firstVerticalBoundaryTime_of_sourceBoundary R t p q
    (level : Int) w j hjT hminimal hrun hprefixQ hqVertical
  have hmarkJ : (z.1 : Nat) <= j := by simpa [hstop] using hmark
  have hvalue : (z.2.1.1.zip z.2.2.1.1) ++ z.2.2.2.1 = w.1.1.1 := by
    exact congrArg (fun u : IsingLeapfrogChoiceStringFamily t => u.1) hz
  have hxyLength : z.2.1.1.length = z.2.2.1.1.length := by
    rw [z.2.1.2.1, z.2.2.1.2.1]
  have hxFull : z.2.1.1 ++ z.2.2.2.1.map Prod.fst =
      w.1.1.1.map Prod.fst := by
    have hx := congrArg (List.map Prod.fst) hvalue
    simpa [List.map_append,
      map_fst_zip_of_length_eq_endpointFailure _ _ hxyLength] using hx
  have hyFull : z.2.2.1.1 ++ z.2.2.2.1.map Prod.snd =
      w.1.1.1.map Prod.snd := by
    have hy := congrArg (List.map Prod.snd) hvalue
    simpa [List.map_append,
      map_snd_zip_of_length_eq_endpointFailure _ _ hxyLength] using hy
  have hstopY : firstVerticalBoundaryTimeEndpointFailure R
      (isingLeapfrogBoxInt p).2
        (z.2.2.1.1 ++ z.2.2.2.1.map Prod.snd) = j := by
    rw [hyFull]
    exact hstop
  have hxPrefix : (w.1.1.1.map Prod.fst).take j =
      z.2.1.1 ++ (z.2.2.2.1.map Prod.fst).take (j - (z.1 : Nat)) := by
    rw [← hxFull, List.take_append]
    simp [z.2.1.2.1, hmarkJ]
  have hrawX : lineFreeEndpoint (isingLeapfrogBoxInt p).1
      ((w.1.1.1.map Prod.fst).take j) = (isingLeapfrogBoxInt q).1 := by
    rw [← List.map_take, lineFreeEndpoint_choiceHorizontal_full]
    have hx := congrArg Prod.fst hrun
    rw [hprefixQ] at hx
    exact hx.symm
  have hstartX : (isingLeapfrogBoxInt p).1 = (level : Int) - 1 := by omega
  rw [hstartX, hxPrefix, lineFreeEndpoint_append_endpointFailure] at hrawX
  have htranslate := lineFreeEndpoint_translate
    ((z.2.2.2.1.map Prod.fst).take (j - (z.1 : Nat))) 0
      (lineFreeEndpoint ((level : Int) - 1) z.2.1.1)
  unfold sourceEndpointRaceTarget
  dsimp only
  rw [hstopY]
  rw [htranslate] at hrawX
  linarith

private def tailDependentEndpointRaceValue
    (R t rho : Nat) (p q : IsingLeapfrogBox R) (level : Int) :
    IsingTailDependentEndpointRaceFamily rho t level
        (sourceEndpointRaceTarget R t rho p q) ->
      IsingLeapfrogChoiceStringFamily t := fun z =>
  ⟨(z.2.2.2.1.1.zip z.2.1.1) ++ z.2.2.1.1, by
    rw [List.length_append, List.length_zip, z.2.2.2.1.2.1,
      z.2.1.2.1, z.2.2.1.2]
    simp
    omega⟩

private theorem exists_sourceFailureOutputTransverseCover
    (R level rho t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hbottom : rho <= p.2.1)
    (htop : p.2.1 + rho <= R)
    (hqVertical : q.2.1 = 0 \/ q.2.1 = R)
    (w : IsingSourceFailureOutputAtFamily R t p q (level : Int)) :
    exists u : IsingTailDependentEndpointRaceFamily rho t (level : Int)
        (sourceEndpointRaceTarget R t rho p q),
      tailDependentEndpointRaceValue R t rho p q (level : Int) u = w.1.1 := by
  rcases exists_sourceFailureOutput_transverseWitness R level rho t p q hstart
    hρ hbottom htop hqVertical w with ⟨z, hz, hmark⟩
  let endpointWord : IsingHorizontalNoHitEndpointFamily z.1 (level : Int)
      (sourceEndpointRaceTarget R t rho p q z.1 z.2.2.1 z.2.2.2) :=
    ⟨z.2.1, sourceEndpointRaceTarget_eq R level rho t p q hstart
      hqVertical w z hz hmark⟩
  let u : IsingTailDependentEndpointRaceFamily rho t (level : Int)
      (sourceEndpointRaceTarget R t rho p q) :=
    ⟨z.1, z.2.2.1, z.2.2.2, endpointWord⟩
  refine ⟨u, ?_⟩
  apply Subtype.ext
  have hvalue := congrArg
    (fun v : IsingLeapfrogChoiceStringFamily t => v.1) hz
  simpa [tailDependentEndpointRaceValue, transverseRaceWitnessValue,
    u, endpointWord] using hvalue

private noncomputable def sourceFailureOutputTransverseCover
    (R level rho t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hbottom : rho <= p.2.1)
    (htop : p.2.1 + rho <= R)
    (hqVertical : q.2.1 = 0 \/ q.2.1 = R) :
    IsingSourceFailureOutputAtFamily R t p q (level : Int) ->
      IsingTailDependentEndpointRaceFamily rho t (level : Int)
        (sourceEndpointRaceTarget R t rho p q) := fun w =>
  Classical.choose (exists_sourceFailureOutputTransverseCover R level rho t
    p q hstart hρ hbottom htop hqVertical w)

private theorem sourceFailureOutputTransverseCover_value
    (R level rho t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hbottom : rho <= p.2.1)
    (htop : p.2.1 + rho <= R)
    (hqVertical : q.2.1 = 0 \/ q.2.1 = R)
    (w : IsingSourceFailureOutputAtFamily R t p q (level : Int)) :
    tailDependentEndpointRaceValue R t rho p q (level : Int)
      (sourceFailureOutputTransverseCover R level rho t p q hstart hρ
        hbottom htop hqVertical w) = w.1.1 := by
  exact Classical.choose_spec (exists_sourceFailureOutputTransverseCover
    R level rho t p q hstart hρ hbottom htop hqVertical w)

private theorem sourceFailureOutputTransverseCover_injective
    (R level rho t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hbottom : rho <= p.2.1)
    (htop : p.2.1 + rho <= R)
    (hqVertical : q.2.1 = 0 \/ q.2.1 = R) :
    Function.Injective (sourceFailureOutputTransverseCover R level rho t
      p q hstart hρ hbottom htop hqVertical) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  rw [← sourceFailureOutputTransverseCover_value R level rho t p q hstart
      hρ hbottom htop hqVertical a,
    ← sourceFailureOutputTransverseCover_value R level rho t p q hstart
      hρ hbottom htop hqVertical b, hab]



theorem sourceFailureOutputAt_vertical_diffusive_weight_le
    (R level rho : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hbottom : rho <= p.2.1)
    (htop : p.2.1 + rho <= R)
    (hqVertical : q.2.1 = 0 \/ q.2.1 = R) :
    Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q
        (level : Int)) / (4 : Real) ^ (rho * rho) <=
      24 / (rho : Real) ^ 2 := by
  have hcard := Nat.card_le_card_of_injective
    (sourceFailureOutputTransverseCover R level rho (rho * rho) p q hstart
      hρ hbottom htop hqVertical)
    (sourceFailureOutputTransverseCover_injective R level rho (rho * rho)
      p q hstart hρ hbottom htop hqVertical)
  have hcardReal :
      (Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q
        (level : Int)) : Real) <=
      Nat.card (IsingTailDependentEndpointRaceFamily rho (rho * rho)
        (level : Int) (sourceEndpointRaceTarget R (rho * rho) rho p q)) := by
    exact_mod_cast hcard
  exact (div_le_div_of_nonneg_right hcardReal (by positivity)).trans
    (tailDependentEndpointRace_diffusive_weight_le rho rho (level : Int)
      (sourceEndpointRaceTarget R (rho * rho) rho p q) hρ (le_refl _))

private def endpointFarEscapeWitnessValue
    (m t : Nat) (start target : Int) :
    IsingEndpointFarEscapeWitnessFamily m t start target →
      IsingLeapfrogChoiceStringFamily t := fun z =>
  ⟨(z.2.1.1.zip z.2.2.1.1) ++ z.2.2.2.1, by
    rw [List.length_append, List.length_zip, z.2.1.2.1,
      z.2.2.1.2.1, z.2.2.2.2]
    simp
    omega⟩

private theorem exists_sourceFailureOutputFarCover
    (R level t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hqLeft : q.1.1 = 0)
    (w : IsingSourceFailureOutputAtFamily R t p q (level : Int)) :
    ∃ z : IsingEndpointFarEscapeWitnessFamily level t
        (isingLeapfrogBoxInt p).2 (isingLeapfrogBoxInt q).2,
      endpointFarEscapeWitnessValue level t
        (isingLeapfrogBoxInt p).2 (isingLeapfrogBoxInt q).2 z = w.1.1 := by
  have hstartLt : (isingLeapfrogBoxInt p).1 < (level : Int) := by omega
  rcases sourceFailure_boundary_data R t p (level : Int) hstartLt w.1 with
    ⟨split, j, hsplit, hj, hb, hminimal, hxlt, hrun⟩
  have hjT : j ≤ t := by
    have hlen := congrArg List.length (firstHitSplit_steps hsplit)
    simp [IsingDiagonalWalkHitSplit.steps, isingLeapfrogChoiceSteps,
      w.1.1.2] at hlen
    omega
  have hprefixQ : isingLeapfrogChoiceRun R p (w.1.1.1.take j) = q := by
    have hdecomp : w.1.1.1 = w.1.1.1.take j ++ w.1.1.1.drop j :=
      (List.take_append_drop j w.1.1.1).symm
    have hfull : isingLeapfrogChoiceRun R p w.1.1.1 =
        isingLeapfrogChoiceRun R p (w.1.1.1.take j) := by
      calc
        _ = isingLeapfrogChoiceRun R p
            (w.1.1.1.take j ++ w.1.1.1.drop j) := by rw [← hdecomp]
        _ = isingLeapfrogChoiceRun R
            (isingLeapfrogChoiceRun R p (w.1.1.1.take j))
              (w.1.1.1.drop j) := isingLeapfrogChoiceRun_append_full ..
        _ = _ :=
          isingLeapfrogChoiceRun_of_boundary_endpointFailure R _ hb _
    exact hfull.symm.trans w.2
  have hvalid : split.Valid := by
    unfold IsingDiagonalWalkHitSplit.Valid
    rw [firstHitSplit_steps hsplit]
    exact isingLeapfrogChoiceSteps_valid w.1.1.1
  have hpx : (isingLeapfrogBoxInt p).1 = (level : Int) - 1 := by omega
  have hpxNat : p.1.1 = level - 1 := by
    unfold isingLeapfrogBoxInt at hstart
    dsimp at hstart
    omega
  let xbits := (w.1.1.1.take j).map Prod.fst
  let ybits := (w.1.1.1.take j).map Prod.snd
  have hxlen : xbits.length = j := by simp [xbits, w.1.1.2, hjT]
  have hylen : ybits.length = j := by simp [ybits, w.1.1.2, hjT]
  have hxfree : ∀ l, l < xbits.length →
      lineFreeEndpoint
          (((⟨level - 1, by omega⟩ : IsingLineBox level).1 : Nat) : Int)
          (xbits.take l) ≠ 0 ∧
        lineFreeEndpoint
          (((⟨level - 1, by omega⟩ : IsingLineBox level).1 : Nat) : Int)
          (xbits.take l) ≠ level := by
    intro l hl
    have hlj : l < j := by simpa [hxlen] using hl
    have hexec : IsingLeapfrogChoiceExecValid R p (w.1.1.1.take l) := by
      intro r hr
      rw [List.length_take] at hr
      have hrl : r < l := by omega
      simpa [List.take_take, Nat.min_eq_left hrl.le] using
        hminimal r (hrl.trans hlj)
    have hrunl := choiceExecValid_run_boxInt_eq_endpoint R p
      (w.1.1.1.take l) hexec
    have hrawx :
        (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
          (isingLeapfrogChoiceSteps (w.1.1.1.take l))).1 =
        lineFreeEndpoint
          (((⟨level - 1, by omega⟩ : IsingLineBox level).1 : Nat) : Int)
          (xbits.take l) := by
      calc
        _ = lineFreeEndpoint (isingLeapfrogBoxInt p).1
            ((w.1.1.1.take l).map Prod.fst) :=
          (lineFreeEndpoint_choiceHorizontal_full
            (w.1.1.1.take l) (isingLeapfrogBoxInt p)).symm
        _ = _ := by
          unfold isingLeapfrogBoxInt
          dsimp
          rw [hpxNat]
          simp [xbits, List.map_take, List.take_take,
            Nat.min_eq_left hlj.le]
    have hrunx := congrArg Prod.fst hrunl
    change ((isingLeapfrogChoiceRun R p (w.1.1.1.take l)).1.1 : Int) =
      (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceSteps (w.1.1.1.take l))).1 at hrunx
    constructor
    · intro heq
      have hb0 := hminimal l hlj
      apply hb0
      unfold isingLeapfrogBoxBoundary
      left
      rw [hrawx] at hrunx
      exact_mod_cast hrunx.trans heq
    · intro heq
      have hfirst := (firstHitSplit_firstHit hsplit).endpoint_take_fst_lt
        split hvalid hstartLt l (by omega)
      have hsteps := congrArg (fun z : List (Int × Int) => z.take l)
        (firstHitSplit_steps hsplit)
      have hprefix : split.before.take l =
          (isingLeapfrogChoiceSteps w.1.1.1).take l := by
        simpa [IsingDiagonalWalkHitSplit.steps,
          List.take_append_of_le_length (show l ≤ split.before.length by omega)]
          using hsteps
      rw [hprefix] at hfirst
      have hfirst' : (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
          (isingLeapfrogChoiceSteps (w.1.1.1.take l))).1 < level := by
        simpa [isingLeapfrogChoiceSteps, List.map_take] using hfirst
      rw [hrawx, heq] at hfirst'
      omega
  have hlineEnd : isingLineChoiceRun level
      (⟨level - 1, by omega⟩ : IsingLineBox level) xbits = ⟨0, by omega⟩ := by
    apply Fin.ext
    have hrunLine := lineChoiceRun_val_eq_lineFreeEndpoint level
      (⟨level - 1, by omega⟩ : IsingLineBox level) xbits hxfree
    have hlineInt : ((isingLineChoiceRun level
        (⟨level - 1, by omega⟩ : IsingLineBox level) xbits).1 : Int) = 0 := by
      rw [hrunLine]
      have hfreeJ := lineFreeEndpoint_choiceHorizontal_full
        (w.1.1.1.take j) (isingLeapfrogBoxInt p)
      have hrawJ := congrArg Prod.fst hrun
      change ((isingLeapfrogChoiceRun R p (w.1.1.1.take j)).1.1 : Int) =
        (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
          (isingLeapfrogChoiceSteps (w.1.1.1.take j))).1 at hrawJ
      have hstartInt : (isingLeapfrogBoxInt p).1 =
          ((level - 1 : Nat) : Int) := by
        unfold isingLeapfrogBoxInt
        dsimp
        rw [hpxNat]
      change lineFreeEndpoint ((level - 1 : Nat) : Int) xbits = 0
      rw [show xbits = (w.1.1.1.take j).map Prod.fst by rfl,
        ← hstartInt, hfreeJ, ← hrawJ, hprefixQ]
      exact_mod_cast hqLeft
    change (isingLineChoiceRun level
      (⟨level - 1, by omega⟩ : IsingLineBox level) xbits).1 = 0
    exact_mod_cast hlineInt
  let xword : IsingLineFarFirstBoundaryFamily level j :=
    ⟨xbits, hxlen, hlineEnd, by
      intro l hl
      unfold isingLineBoxBoundary
      have hf := hxfree l (by simpa [hxlen] using hl)
      have hrunLine := lineChoiceRun_val_eq_lineFreeEndpoint level
        (⟨level - 1, by omega⟩ : IsingLineBox level) (xbits.take l) (by
          intro r hr
          have hrlSmall : r < l := by
            rw [List.length_take] at hr
            omega
          have hrl : r < xbits.length := by
            omega
          simpa [List.take_take, Nat.min_eq_left hrlSmall.le] using
            hxfree r hrl)
      intro hbLine
      rcases hbLine with hb0 | hbR
      · apply hf.1
        rw [← hrunLine]
        exact_mod_cast hb0
      · apply hf.2
        rw [← hrunLine]
        exact_mod_cast hbR⟩
  let yword : VerticalChoicePathFamily j
      (isingLeapfrogBoxInt p).2 (isingLeapfrogBoxInt q).2 :=
    ⟨ybits, hylen, by
      rw [lineFreeEndpoint_choiceVertical_full]
      have hry := congrArg Prod.snd hrun
      rw [hprefixQ] at hry
      simpa [ybits] using hry.symm⟩
  let tail : {tail : List (Bool × Bool) // tail.length = t - j} :=
    ⟨w.1.1.1.drop j, by simp [w.1.1.2, hjT]⟩
  refine ⟨⟨⟨j, by omega⟩, xword, yword, tail⟩, ?_⟩
  apply Subtype.ext
  change (((w.1.1.1.take j).map Prod.fst).zip
      ((w.1.1.1.take j).map Prod.snd)) ++ w.1.1.1.drop j = w.1.1.1
  rw [prodBits_zip_self_endpointFailure]
  exact List.take_append_drop _ w.1.1.1

private noncomputable def sourceFailureOutputFarCover
    (R level t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hqLeft : q.1.1 = 0) :
    IsingSourceFailureOutputAtFamily R t p q (level : Int) →
      IsingEndpointFarEscapeWitnessFamily level t
        (isingLeapfrogBoxInt p).2 (isingLeapfrogBoxInt q).2 := fun w =>
  Classical.choose
    (exists_sourceFailureOutputFarCover R level t p q hstart hqLeft w)

private theorem sourceFailureOutputFarCover_value
    (R level t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hqLeft : q.1.1 = 0)
    (w : IsingSourceFailureOutputAtFamily R t p q (level : Int)) :
    endpointFarEscapeWitnessValue level t
      (isingLeapfrogBoxInt p).2 (isingLeapfrogBoxInt q).2
      (sourceFailureOutputFarCover R level t p q hstart hqLeft w) = w.1.1 := by
  exact Classical.choose_spec
    (exists_sourceFailureOutputFarCover R level t p q hstart hqLeft w)

private theorem sourceFailureOutputFarCover_injective
    (R level t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hqLeft : q.1.1 = 0) :
    Function.Injective
      (sourceFailureOutputFarCover R level t p q hstart hqLeft) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  rw [← sourceFailureOutputFarCover_value R level t p q hstart hqLeft a,
    ← sourceFailureOutputFarCover_value R level t p q hstart hqLeft b, h]



theorem sourceFailureOutputAt_left_diffusive_weight_le
    (R level rho : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hqLeft : q.1.1 = 0) (hρ : 0 < rho) (hlevel : rho ≤ level) :
    Nat.card (IsingSourceFailureOutputAtFamily
          R (rho * rho) p q (level : Int)) /
        (4 : Real) ^ (rho * rho) ≤
      468 / (rho : Real) ^ 2 := by
  have hcard := Nat.card_le_card_of_injective
    (sourceFailureOutputFarCover R level (rho * rho) p q hstart hqLeft)
    (sourceFailureOutputFarCover_injective
      R level (rho * rho) p q hstart hqLeft)
  have hcardReal :
      (Nat.card (IsingSourceFailureOutputAtFamily
        R (rho * rho) p q (level : Int)) : Real) ≤
      Nat.card (IsingEndpointFarEscapeWitnessFamily level (rho * rho)
        (isingLeapfrogBoxInt p).2 (isingLeapfrogBoxInt q).2) := by
    exact_mod_cast hcard
  exact (div_le_div_of_nonneg_right hcardReal (by positivity)).trans
    (endpointFarEscapeWitness_diffusive_weight_le rho level
      (isingLeapfrogBoxInt p).2 (isingLeapfrogBoxInt q).2 hρ hlevel)

private theorem sourceFailureOutputAt_right_card_eq_zero
    (R level t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hlevelR : level < R) (hqRight : q.1.1 = R) :
    Nat.card (IsingSourceFailureOutputAtFamily R t p q (level : Int)) = 0 := by
  apply Nat.card_eq_zero.mpr
  left
  constructor
  intro w
  have hstartLt : (isingLeapfrogBoxInt p).1 < (level : Int) := by omega
  rcases sourceFailure_boundary_data R t p (level : Int) hstartLt w.1 with
    ⟨split, j, hsplit, hj, hb, hminimal, hxlt, hrun⟩
  have hjT : j <= t := by
    have hlen := congrArg List.length (firstHitSplit_steps hsplit)
    simp [IsingDiagonalWalkHitSplit.steps, isingLeapfrogChoiceSteps,
      w.1.1.2] at hlen
    omega
  have hprefixQ : isingLeapfrogChoiceRun R p (w.1.1.1.take j) = q := by
    have hdecomp : w.1.1.1 = w.1.1.1.take j ++ w.1.1.1.drop j :=
      (List.take_append_drop j w.1.1.1).symm
    have hfull : isingLeapfrogChoiceRun R p w.1.1.1 =
        isingLeapfrogChoiceRun R p (w.1.1.1.take j) := by
      calc
        _ = isingLeapfrogChoiceRun R p
            (w.1.1.1.take j ++ w.1.1.1.drop j) := by rw [← hdecomp]
        _ = isingLeapfrogChoiceRun R
            (isingLeapfrogChoiceRun R p (w.1.1.1.take j))
              (w.1.1.1.drop j) := isingLeapfrogChoiceRun_append_full ..
        _ = _ :=
          isingLeapfrogChoiceRun_of_boundary_endpointFailure R _ hb _
    exact hfull.symm.trans w.2
  have hx := congrArg Prod.fst hrun
  rw [hprefixQ] at hx
  change ((q.1.1 : Nat) : Int) =
    (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
      (isingLeapfrogChoiceSteps (w.1.1.1.take j))).1 at hx
  have hqInt : ((q.1.1 : Nat) : Int) = R := by exact_mod_cast hqRight
  rw [hqInt] at hx
  omega



theorem sourceFailureOutputAt_boundary_diffusive_weight_le
    (R level rho : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hleft : rho <= level) (hlevelR : level < R)
    (hbottom : rho <= p.2.1) (htop : p.2.1 + rho <= R)
    (hqBoundary : isingLeapfrogBoxBoundary R q) :
    Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q
        (level : Int)) / (4 : Real) ^ (rho * rho) <=
      468 / (rho : Real) ^ 2 := by
  unfold isingLeapfrogBoxBoundary at hqBoundary
  rcases hqBoundary with hqLeft | hqRight | hqBottom | hqTop
  · exact sourceFailureOutputAt_left_diffusive_weight_le R level rho p q
      hstart hqLeft hρ hleft
  · rw [sourceFailureOutputAt_right_card_eq_zero R level (rho * rho) p q
      hstart hlevelR (by omega)]
    have hnonneg : 0 <= (468 : Real) / (rho : Real) ^ 2 := by positivity
    simpa using hnonneg
  · exact (sourceFailureOutputAt_vertical_diffusive_weight_le R level rho p q
      hstart hρ hbottom htop (Or.inl hqBottom)).trans (by
        apply div_le_div_of_nonneg_right (by norm_num)
        positivity)
  · exact (sourceFailureOutputAt_vertical_diffusive_weight_le R level rho p q
      hstart hρ hbottom htop (Or.inr (by omega))).trans (by
        apply div_le_div_of_nonneg_right (by norm_num)
        positivity)


def IsingMirrorFailureOutputAtFamily
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :=
  {w : IsingStoppedCouplingMirrorFailureFamily R t p p' level //
    isingLeapfrogChoiceRun R p'
      (isingLeapfrogCouplingChoiceTransform t
        (isingLeapfrogBoxInt p) level w.1).1 = q}

noncomputable instance isingMirrorFailureOutputAtFamily_finite
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Finite (IsingMirrorFailureOutputAtFamily R t p p' q level) := by
  exact Finite.of_injective Subtype.val Subtype.val_injective

private def mirrorFailureOutputReflectX
    (R t level : Nat) (p p' q : IsingLeapfrogBox R)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hlevelR : level <= R) :
    IsingMirrorFailureOutputAtFamily R t p p' q (level : Int) ->
      IsingSourceFailureOutputAtFamily R t
        (isingLeapfrogBoxReflectX R p') (isingLeapfrogBoxReflectX R q)
        ((R - level : Nat) : Int) := fun w => by
  refine ⟨mirrorFailureReflectX R t level p p' hmirror hlevelR w.1, ?_⟩
  change isingLeapfrogChoiceRun R (isingLeapfrogBoxReflectX R p')
      (isingLeapfrogFlipXChoices
        (isingLeapfrogCouplingChoiceTransform t
          (isingLeapfrogBoxInt p) (level : Int) w.1.1).1) =
    isingLeapfrogBoxReflectX R q
  rw [choiceRun_reflectX, w.2]

private theorem mirrorFailureOutputReflectX_injective
    (R t level : Nat) (p p' q : IsingLeapfrogBox R)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hlevelR : level <= R) :
    Function.Injective
      (mirrorFailureOutputReflectX R t level p p' q hmirror hlevelR) := by
  intro a b hab
  apply Subtype.ext
  exact mirrorFailureReflectX_injective R t level p p' hmirror hlevelR
    (congrArg Subtype.val hab)



theorem mirrorFailureOutputAt_boundary_diffusive_weight_le
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hlevel : 0 < level)
    (hright : level + rho <= R)
    (hbottom : rho <= p'.2.1) (htop : p'.2.1 + rho <= R)
    (hqBoundary : isingLeapfrogBoxBoundary R q) :
    Nat.card (IsingMirrorFailureOutputAtFamily R (rho * rho) p p' q
        (level : Int)) / (4 : Real) ^ (rho * rho) <=
      468 / (rho : Real) ^ 2 := by
  have hlevelR : level <= R := by omega
  have hcard := Nat.card_le_card_of_injective
    (mirrorFailureOutputReflectX R (rho * rho) level p p' q hmirror hlevelR)
    (mirrorFailureOutputReflectX_injective R (rho * rho) level p p' q
      hmirror hlevelR)
  have hcardReal :
      (Nat.card (IsingMirrorFailureOutputAtFamily R (rho * rho) p p' q
        (level : Int)) : Real) <=
      Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho)
        (isingLeapfrogBoxReflectX R p') (isingLeapfrogBoxReflectX R q)
        ((R - level : Nat) : Int)) := by exact_mod_cast hcard
  have hp'x : (isingLeapfrogBoxInt p').1 = (level : Int) + 1 := by
    rw [hmirror]
    unfold reflectedEndpoint
    dsimp
    omega
  have hrefStart :
      (isingLeapfrogBoxInt (isingLeapfrogBoxReflectX R p')).1 + 1 =
        (R - level : Nat) := by
    rw [boxInt_reflectX]
    dsimp
    have hcast : ((R - level : Nat) : Int) = (R : Int) - level := by
      rw [Nat.cast_sub hlevelR]
    rw [hcast, hp'x]
    omega
  have hrefBottom : rho <= (isingLeapfrogBoxReflectX R p').2.1 := by
    simpa [isingLeapfrogBoxReflectX] using hbottom
  have hrefTop : (isingLeapfrogBoxReflectX R p').2.1 + rho <= R := by
    simpa [isingLeapfrogBoxReflectX] using htop
  have hrefBoundary : isingLeapfrogBoxBoundary R
      (isingLeapfrogBoxReflectX R q) :=
    (isingLeapfrogBoxBoundary_reflectX_iff R q).2 hqBoundary
  calc
    _ <= Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho)
        (isingLeapfrogBoxReflectX R p') (isingLeapfrogBoxReflectX R q)
        ((R - level : Nat) : Int)) / (4 : Real) ^ (rho * rho) :=
      div_le_div_of_nonneg_right hcardReal (by positivity)
    _ <= 468 / (rho : Real) ^ 2 :=
      sourceFailureOutputAt_boundary_diffusive_weight_le R (R - level) rho
        (isingLeapfrogBoxReflectX R p') (isingLeapfrogBoxReflectX R q)
        hrefStart hρ (by omega) (by omega) hrefBottom hrefTop hrefBoundary

private theorem sourceFailure_implies_mirrorFailure_of_rightHalf
    (R level t : Nat) (p p' : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hlevelR : level < R) (hhalf : R <= 2 * level)
    (w : IsingStoppedCouplingSourceFailureFamily R t p (level : Int)) :
    IsingStoppedCouplingMirrorFailure R p p' (level : Int) w.1 := by
  have hstartLt : (isingLeapfrogBoxInt p).1 < (level : Int) := by omega
  rcases sourceFailure_boundary_data R t p (level : Int) hstartLt w with
    ⟨split, j, hsplit, hj, hb, hminimal, hxlt, hrun⟩
  unfold IsingStoppedCouplingMirrorFailure
  refine ⟨split, hsplit, ?_⟩
  intro hmirrorValid
  let w' := isingLeapfrogCouplingChoiceTransform t
    (isingLeapfrogBoxInt p) (level : Int) w.1
  have hbeforeT : split.before.length <= t := by
    have hlen := congrArg List.length (firstHitSplit_steps hsplit)
    simp [IsingDiagonalWalkHitSplit.steps, isingLeapfrogChoiceSteps,
      w.1.2] at hlen
    omega
  have hmirrorValidJ : IsingLeapfrogChoiceExecValid R p' (w'.1.take j) := by
    intro r hr
    have hrj : r < j := by
      dsimp [w'] at hr
      rw [List.length_take] at hr
      omega
    have hw' : (isingLeapfrogCouplingChoiceTransform t
        (isingLeapfrogBoxInt p) (level : Int) w.1).1.length = t :=
      (isingLeapfrogCouplingChoiceTransform t
        (isingLeapfrogBoxInt p) (level : Int) w.1).2
    have hrBefore : r < (List.take split.before.length
        (isingLeapfrogCouplingChoiceTransform t
          (isingLeapfrogBoxInt p) (level : Int) w.1).1).length := by
      rw [List.length_take, hw']
      omega
    have hv := hmirrorValid r hrBefore
    simpa [w', List.take_take, Nat.min_eq_left hrj.le,
      Nat.min_eq_left (show r <= split.before.length by omega)] using hv
  have hmirrorRun := choiceExecValid_run_boxInt_eq_endpoint R p'
    (w'.1.take j) hmirrorValidJ
  have hbeforeSteps := couplingChoiceTransform_take_steps_of_some t
    (isingLeapfrogBoxInt p) (level : Int) w.1 split hsplit
  have hmirrorSteps : isingLeapfrogChoiceSteps (w'.1.take j) =
      split.reflectPrefix.steps.take j := by
    calc
      _ = (isingLeapfrogChoiceSteps (w'.1.take split.before.length)).take j := by
        simp [isingLeapfrogChoiceSteps, List.map_take, List.take_take,
          Nat.min_eq_left hj.le]
      _ = (split.before.map reflectIncrement).take j := by rw [hbeforeSteps]
      _ = _ := by
        unfold IsingDiagonalWalkHitSplit.reflectPrefix
          IsingDiagonalWalkHitSplit.steps
        rw [List.take_append_of_le_length (by simpa using hj.le)]
  have hsourceSteps : split.steps.take j =
      isingLeapfrogChoiceSteps (w.1.1.take j) := by
    have hs := congrArg (fun path : List (Int × Int) => path.take j)
      (firstHitSplit_steps hsplit)
    simpa [isingLeapfrogChoiceSteps, List.map_take] using hs
  have hmx := congrArg Prod.fst hmirrorRun
  change ((isingLeapfrogChoiceRun R p' (w'.1.take j)).1.1 : Int) =
    (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p')
      (isingLeapfrogChoiceSteps (w'.1.take j))).1 at hmx
  rw [hmirror, hmirrorSteps,
    reflectPrefix_endpoint_take_fst_of_le_before split j hj.le,
    hsourceSteps] at hmx
  have hmy := congrArg Prod.snd hmirrorRun
  change ((isingLeapfrogChoiceRun R p' (w'.1.take j)).2.1 : Int) =
    (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p')
      (isingLeapfrogChoiceSteps (w'.1.take j))).2 at hmy
  rw [hmirror, hmirrorSteps,
    reflectPrefix_endpoint_take_snd_of_le_before split j hj.le,
    hsourceSteps] at hmy
  have hsx := congrArg Prod.fst hrun
  have hsy := congrArg Prod.snd hrun
  change ((isingLeapfrogChoiceRun R p (w.1.1.take j)).1.1 : Int) =
    (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
      (isingLeapfrogChoiceSteps (w.1.1.take j))).1 at hsx
  change ((isingLeapfrogChoiceRun R p (w.1.1.take j)).2.1 : Int) =
    (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
      (isingLeapfrogChoiceSteps (w.1.1.take j))).2 at hsy
  have hnot := hmirrorValid j (by
    rw [List.length_take]
    have hw' : (isingLeapfrogCouplingChoiceTransform t
        (isingLeapfrogBoxInt p) (level : Int) w.1).1.length = t :=
      (isingLeapfrogCouplingChoiceTransform t
        (isingLeapfrogBoxInt p) (level : Int) w.1).2
    omega)
  have hnot' : ¬ isingLeapfrogBoxBoundary R
      (isingLeapfrogChoiceRun R p' (w'.1.take j)) := by
    simpa [w', List.take_take, Nat.min_eq_left hj.le] using hnot
  apply hnot'
  unfold isingLeapfrogBoxBoundary at hb ⊢
  rcases hb with hx0 | hxR | hy0 | hyR
  · right; left
    have hsourceZero : ((isingLeapfrogChoiceRun R p
        (w.1.1.take j)).1.1 : Int) = 0 := by exact_mod_cast hx0
    have hmirrorX : ((isingLeapfrogChoiceRun R p'
        (w'.1.take j)).1.1 : Int) = 2 * level := by
      rw [hmx, ← hsx, hsourceZero]
      ring
    have hmirrorXNat : (isingLeapfrogChoiceRun R p'
        (w'.1.take j)).1.1 = R := by
      have hle : (isingLeapfrogChoiceRun R p'
          (w'.1.take j)).1.1 <= R := by
        exact Nat.le_of_lt_succ
          (isingLeapfrogChoiceRun R p' (w'.1.take j)).1.2
      have hleInt : (((isingLeapfrogChoiceRun R p'
          (w'.1.take j)).1.1 : Nat) : Int) <= R := by exact_mod_cast hle
      have hhalfInt : (R : Int) <= 2 * level := by exact_mod_cast hhalf
      have heqInt : (((isingLeapfrogChoiceRun R p'
          (w'.1.take j)).1.1 : Nat) : Int) = R := by omega
      exact_mod_cast heqInt
    omega
  · exfalso
    have hsourceRNat : (isingLeapfrogChoiceRun R p
        (w.1.1.take j)).1.1 = R := by omega
    have hsourceR : ((isingLeapfrogChoiceRun R p
        (w.1.1.take j)).1.1 : Int) = R := by exact_mod_cast hsourceRNat
    rw [hsx] at hsourceR
    omega
  · right; right; left
    have hsourceY : ((isingLeapfrogChoiceRun R p
        (w.1.1.take j)).2.1 : Int) = 0 := by exact_mod_cast hy0
    have hmirrorY : ((isingLeapfrogChoiceRun R p'
        (w'.1.take j)).2.1 : Int) = 0 := by rw [hmy, ← hsy, hsourceY]
    exact_mod_cast hmirrorY
  · right; right; right
    have hsourceY : ((isingLeapfrogChoiceRun R p
        (w.1.1.take j)).2.1 : Int) = R := by
      have : (isingLeapfrogChoiceRun R p (w.1.1.take j)).2.1 = R := by omega
      exact_mod_cast this
    have hmirrorY : ((isingLeapfrogChoiceRun R p'
        (w'.1.take j)).2.1 : Int) = R := by rw [hmy, ← hsy, hsourceY]
    have : (isingLeapfrogChoiceRun R p' (w'.1.take j)).2.1 = R := by
      exact_mod_cast hmirrorY
    omega

private def alignedFailureOutputValue
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Sum (IsingSourceFailureOutputAtFamily R t p q level)
      (IsingMirrorFailureOutputAtFamily R t p p' q level) ->
      IsingLeapfrogChoiceStringFamily t
  | Sum.inl w => w.1.1
  | Sum.inr w => w.1.1

private theorem exists_sourceFailureAtAlignedCover_of_rightHalf
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hlevelR : level < R) (hhalf : R <= 2 * level)
    (w : IsingStoppedCouplingSourceFailureAtFamily R t p p' q
      (level : Int)) :
    exists z : Sum (IsingSourceFailureOutputAtFamily R t p q (level : Int))
        (IsingMirrorFailureOutputAtFamily R t p p' q (level : Int)),
      alignedFailureOutputValue R t p p' q (level : Int) z = w.1 := by
  rcases w.2.2 with hsourceOutput | hmirrorOutput
  · exact ⟨Sum.inl ⟨⟨w.1, w.2.1⟩, hsourceOutput⟩, rfl⟩
  · let ws : IsingStoppedCouplingSourceFailureFamily R t p (level : Int) :=
      ⟨w.1, w.2.1⟩
    have hm := sourceFailure_implies_mirrorFailure_of_rightHalf R level t p p'
      hstart hmirror hlevelR hhalf ws
    exact ⟨Sum.inr ⟨⟨w.1, hm⟩, hmirrorOutput⟩, rfl⟩

private noncomputable def sourceFailureAtAlignedCover_of_rightHalf
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hlevelR : level < R) (hhalf : R <= 2 * level) :
    IsingStoppedCouplingSourceFailureAtFamily R t p p' q (level : Int) ->
      Sum (IsingSourceFailureOutputAtFamily R t p q (level : Int))
        (IsingMirrorFailureOutputAtFamily R t p p' q (level : Int)) := fun w =>
  Classical.choose (exists_sourceFailureAtAlignedCover_of_rightHalf R level t
    p p' q hstart hmirror hlevelR hhalf w)

private theorem sourceFailureAtAlignedCover_of_rightHalf_value
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hlevelR : level < R) (hhalf : R <= 2 * level)
    (w : IsingStoppedCouplingSourceFailureAtFamily R t p p' q
      (level : Int)) :
    alignedFailureOutputValue R t p p' q (level : Int)
      (sourceFailureAtAlignedCover_of_rightHalf R level t p p' q hstart
        hmirror hlevelR hhalf w) = w.1 := by
  exact Classical.choose_spec
    (exists_sourceFailureAtAlignedCover_of_rightHalf R level t p p' q
      hstart hmirror hlevelR hhalf w)

private theorem sourceFailureAtAlignedCover_of_rightHalf_injective
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hlevelR : level < R) (hhalf : R <= 2 * level) :
    Function.Injective (sourceFailureAtAlignedCover_of_rightHalf R level t
      p p' q hstart hmirror hlevelR hhalf) := by
  intro a b hab
  apply Subtype.ext
  rw [← sourceFailureAtAlignedCover_of_rightHalf_value R level t p p' q
      hstart hmirror hlevelR hhalf a,
    ← sourceFailureAtAlignedCover_of_rightHalf_value R level t p p' q
      hstart hmirror hlevelR hhalf b, hab]

theorem sourceFailureAt_boundary_diffusive_weight_le_of_rightHalf
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hleft : rho <= level) (hlevelR : level < R)
    (hright : level + rho <= R) (hhalf : R <= 2 * level)
    (hbottom : rho <= p.2.1) (htop : p.2.1 + rho <= R)
    (hbottom' : rho <= p'.2.1) (htop' : p'.2.1 + rho <= R)
    (hqBoundary : isingLeapfrogBoxBoundary R q) :
    Nat.card (IsingStoppedCouplingSourceFailureAtFamily R (rho * rho)
        p p' q (level : Int)) / (4 : Real) ^ (rho * rho) <=
      936 / (rho : Real) ^ 2 := by
  have hcard := Nat.card_le_card_of_injective
    (sourceFailureAtAlignedCover_of_rightHalf R level (rho * rho) p p' q
      hstart hmirror hlevelR hhalf)
    (sourceFailureAtAlignedCover_of_rightHalf_injective R level (rho * rho)
      p p' q hstart hmirror hlevelR hhalf)
  rw [Nat.card_sum] at hcard
  have hcardReal :
      (Nat.card (IsingStoppedCouplingSourceFailureAtFamily R (rho * rho)
        p p' q (level : Int)) : Real) <=
      Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q
        (level : Int)) +
      Nat.card (IsingMirrorFailureOutputAtFamily R (rho * rho) p p' q
        (level : Int)) := by exact_mod_cast hcard
  calc
    _ <= (Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q
          (level : Int)) +
        Nat.card (IsingMirrorFailureOutputAtFamily R (rho * rho) p p' q
          (level : Int))) / (4 : Real) ^ (rho * rho) :=
      div_le_div_of_nonneg_right hcardReal (by positivity)
    _ = Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q
          (level : Int)) / (4 : Real) ^ (rho * rho) +
        Nat.card (IsingMirrorFailureOutputAtFamily R (rho * rho) p p' q
          (level : Int)) / (4 : Real) ^ (rho * rho) := by rw [add_div]
    _ <= 468 / (rho : Real) ^ 2 + 468 / (rho : Real) ^ 2 :=
      add_le_add
        (sourceFailureOutputAt_boundary_diffusive_weight_le R level rho p q
          hstart hρ hleft hlevelR hbottom htop hqBoundary)
        (mirrorFailureOutputAt_boundary_diffusive_weight_le R level rho
          p p' q hstart hmirror hρ (lt_of_lt_of_le hρ hleft) hright
          hbottom' htop' hqBoundary)
    _ = 936 / (rho : Real) ^ 2 := by ring




def IsingMirrorOnlySourceOutputAtFamily
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :=
  {w : IsingLeapfrogChoiceStringFamily t //
    IsingStoppedCouplingMirrorFailure R p p' level w /\
      ¬ IsingStoppedCouplingSourceFailure R p level w /\
      isingLeapfrogChoiceRun R p w.1 = q}

noncomputable instance isingMirrorOnlySourceOutputAtFamily_finite
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Finite (IsingMirrorOnlySourceOutputAtFamily R t p p' q level) := by
  exact Finite.of_injective Subtype.val Subtype.val_injective



def IsingLineFirstEndpointFamily
    (n k : Nat) (start target : IsingLineBox n) :=
  {ys : List Bool // ys.length = k /\
    isingLineChoiceRun n start ys = target /\
    forall l, l < k -> ¬ isingLineBoxBoundary n
      (isingLineChoiceRun n start (ys.take l))}

noncomputable instance isingLineFirstEndpointFamily_finite
    (n k : Nat) (start target : IsingLineBox n) :
    Finite (IsingLineFirstEndpointFamily n k start target) := by
  letI : Fintype {ys : List Bool // ys.length = k} :=
    (List.finite_length_eq Bool k).fintype
  exact Finite.of_injective
    (fun w : IsingLineFirstEndpointFamily n k start target =>
      (⟨w.1, w.2.1⟩ : {ys : List Bool // ys.length = k}))
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg
        (fun z : {ys : List Bool // ys.length = k} => z.1) h)

private def endpointFailureLineStep (b : Bool) : Int :=
  if b then 1 else -1

private theorem lineFreeEndpoint_eq_start_add_sum_endpointFailure
    (start : Int) (bs : List Bool) :
    lineFreeEndpoint start bs =
      start + (bs.map endpointFailureLineStep).sum := by
  induction bs generalizing start with
  | nil => simp [lineFreeEndpoint]
  | cons b bs ih =>
      rw [lineFreeEndpoint, ih]
      simp [endpointFailureLineStep]
      ring

private theorem endpointFailureLineStep_not (b : Bool) :
    endpointFailureLineStep (!b) = -endpointFailureLineStep b := by
  cases b <;> simp [endpointFailureLineStep]

private theorem sum_map_lineStep_not_endpointFailure (bs : List Bool) :
    ((bs.map (!.)).map endpointFailureLineStep).sum =
      -(bs.map endpointFailureLineStep).sum := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
      simp only [List.map_cons, List.sum_cons, endpointFailureLineStep_not]
      rw [ih]
      ring

private theorem sum_map_lineStep_reverse_endpointFailure (bs : List Bool) :
    (bs.reverse.map endpointFailureLineStep).sum =
      (bs.map endpointFailureLineStep).sum := by
  rw [List.map_reverse, List.sum_reverse]

private theorem sum_map_lineStep_reverse_not_endpointFailure (bs : List Bool) :
    ((bs.reverse.map (!.)).map endpointFailureLineStep).sum =
      -(bs.map endpointFailureLineStep).sum := by
  rw [sum_map_lineStep_not_endpointFailure,
    sum_map_lineStep_reverse_endpointFailure]

private theorem lineFirstEndpoint_free_prefix
    (n k : Nat) (start target : IsingLineBox n)
    (w : IsingLineFirstEndpointFamily n k start target) :
    forall l, l <= k ->
      ((isingLineChoiceRun n start (w.1.take l)).1 : Int) =
        lineFreeEndpoint (start.1 : Int) (w.1.take l) := by
  intro l hl
  induction l using Nat.strong_induction_on with
  | h l ih =>
      apply lineChoiceRun_val_eq_lineFreeEndpoint
      intro r hr
      have hrl : r < l := by
        rw [List.length_take, w.2.1] at hr
        omega
      have hrk : r < k := lt_of_lt_of_le hrl hl
      have hrunInterior := w.2.2.2 r hrk
      have hrunFree := ih r hrl (by omega)
      have htake : (w.1.take l).take r = w.1.take r := by
        simp [List.take_take, Nat.min_eq_left hrl.le]
      rw [htake]
      constructor
      · intro hzero
        apply hrunInterior
        unfold isingLineBoxBoundary
        left
        have hcast :
            ((isingLineChoiceRun n start (w.1.take r)).1 : Int) = 0 := by
          rw [hrunFree, hzero]
        exact_mod_cast hcast
      · intro hn
        apply hrunInterior
        unfold isingLineBoxBoundary
        right
        have hcast :
            ((isingLineChoiceRun n start (w.1.take r)).1 : Int) = n := by
          rw [hrunFree, hn]
        exact_mod_cast hcast

private theorem lineFirstEndpoint_time_pos
    (n k : Nat) (start target : IsingLineBox n)
    (hstart : ¬ isingLineBoxBoundary n start)
    (htarget : isingLineBoxBoundary n target)
    (w : IsingLineFirstEndpointFamily n k start target) :
    0 < k := by
  by_contra hk
  have hk0 : k = 0 := by omega
  have hout := w.2.2.1
  subst k
  have hwNil : w.1 = [] := List.eq_nil_of_length_eq_zero w.2.1
  rw [hwNil] at hout
  simp [isingLineChoiceRun] at hout
  subst target
  exact hstart htarget

private theorem lineFirstEndpoint_dropLast_data
    (n k : Nat) (start target : IsingLineBox n)
    (w : IsingLineFirstEndpointFamily n k start target)
    (hk : 0 < k) :
    let pref := w.1.dropLast
    pref.length = k - 1 /\
      lineFreeEndpoint (start.1 : Int) pref =
        ((isingLineChoiceRun n start pref).1 : Int) /\
      (forall l, l <= pref.length ->
        lineFreeEndpoint (start.1 : Int) (pref.take l) ≠ 0 /\
        lineFreeEndpoint (start.1 : Int) (pref.take l) ≠ n) := by
  let pref := w.1.dropLast
  have hprefLen : pref.length = k - 1 := by
    dsimp [pref]
    rw [List.length_dropLast, w.2.1]
  have hprefTake : w.1.take (k - 1) = pref := by
    dsimp [pref]
    rw [List.dropLast_eq_take, w.2.1]
  have hfree := lineFirstEndpoint_free_prefix n k start target w (k - 1) (by omega)
  rw [hprefTake] at hfree
  refine ⟨hprefLen, hfree.symm, ?_⟩
  intro l hl
  change l <= pref.length at hl
  have hlk : l < k := by omega
  have hrunInterior := w.2.2.2 l hlk
  have htake : pref.take l = w.1.take l := by
    rw [← hprefTake, List.take_take]
    simp [Nat.min_eq_left (by omega : l <= k - 1)]
  have hrunFree := lineFirstEndpoint_free_prefix n k start target w l hlk.le
  rw [← htake] at hrunFree
  constructor
  · intro hzero
    apply hrunInterior
    unfold isingLineBoxBoundary
    left
    change lineFreeEndpoint (start.1 : Int) (pref.take l) = 0 at hzero
    have : ((isingLineChoiceRun n start (w.1.take l)).1 : Int) = 0 := by
      rw [← htake, hrunFree, hzero]
    exact_mod_cast this
  · intro hn
    apply hrunInterior
    unfold isingLineBoxBoundary
    right
    change lineFreeEndpoint (start.1 : Int) (pref.take l) = n at hn
    have : ((isingLineChoiceRun n start (w.1.take l)).1 : Int) = n := by
      rw [← htake, hrunFree, hn]
    exact_mod_cast this

private theorem lineFirstEndpoint_left_dropLast
    (n k : Nat) (start target : IsingLineBox n)
    (w : IsingLineFirstEndpointFamily n k start target)
    (hk : 0 < k) (htarget : target.1 = 0) :
    lineFreeEndpoint (start.1 : Int) w.1.dropLast = 1 /\
      w.1 = w.1.dropLast ++ [false] := by
  let pref := w.1.dropLast
  have hwNe : w.1 ≠ [] := by
    intro hw
    have hlen := w.2.1
    rw [hw] at hlen
    simp at hlen
    omega
  have hdecomp := List.dropLast_append_getLast hwNe
  have hdata := lineFirstEndpoint_dropLast_data n k start target w hk
  dsimp only at hdata
  have hprefFree := hdata.2.1
  have hprefNonneg : 0 <= lineFreeEndpoint (start.1 : Int) pref := by
    rw [hprefFree]
    positivity
  have hfullFree := lineFirstEndpoint_free_prefix n k start target w k le_rfl
  have htake : w.1.take k = w.1 := by
    simpa [w.2.1] using List.take_all w.1
  rw [htake, w.2.2.1] at hfullFree
  have hfullZero : lineFreeEndpoint (start.1 : Int) w.1 = 0 := by
    rw [← hfullFree]
    exact_mod_cast htarget
  rw [← hdecomp,
    lineFreeEndpoint_append_endpointFailure] at hfullZero
  change lineFreeEndpoint (lineFreeEndpoint (start.1 : Int) pref)
    [w.1.getLast hwNe] = 0 at hfullZero
  have hlast : w.1.getLast hwNe = false := by
    cases h : w.1.getLast hwNe
    · rfl
    · simp [lineFreeEndpoint, h] at hfullZero
      omega
  constructor
  · rw [hlast] at hfullZero
    change lineFreeEndpoint (start.1 : Int) pref - 1 = 0 at hfullZero
    change lineFreeEndpoint (start.1 : Int) pref = 1
    omega
  · simpa [pref, hlast] using hdecomp.symm

private theorem lineFirstEndpoint_right_dropLast
    (n k : Nat) (start target : IsingLineBox n)
    (w : IsingLineFirstEndpointFamily n k start target)
    (hk : 0 < k) (htarget : target.1 = n) :
    lineFreeEndpoint (start.1 : Int) w.1.dropLast = (n : Int) - 1 /\
      w.1 = w.1.dropLast ++ [true] := by
  let pref := w.1.dropLast
  have hwNe : w.1 ≠ [] := by
    intro hw
    have hlen := w.2.1
    rw [hw] at hlen
    simp at hlen
    omega
  have hdecomp := List.dropLast_append_getLast hwNe
  have hdata := lineFirstEndpoint_dropLast_data n k start target w hk
  dsimp only at hdata
  have hprefFree := hdata.2.1
  have hprefLe : lineFreeEndpoint (start.1 : Int) pref <= n := by
    rw [hprefFree]
    exact_mod_cast Nat.lt_succ_iff.mp (isingLineChoiceRun n start pref).2
  have hfullFree := lineFirstEndpoint_free_prefix n k start target w k le_rfl
  have htake : w.1.take k = w.1 := by
    simpa [w.2.1] using List.take_all w.1
  rw [htake, w.2.2.1] at hfullFree
  have hfullRight : lineFreeEndpoint (start.1 : Int) w.1 = n := by
    rw [← hfullFree]
    exact_mod_cast htarget
  rw [← hdecomp,
    lineFreeEndpoint_append_endpointFailure] at hfullRight
  change lineFreeEndpoint (lineFreeEndpoint (start.1 : Int) pref)
    [w.1.getLast hwNe] = n at hfullRight
  have hlast : w.1.getLast hwNe = true := by
    cases h : w.1.getLast hwNe
    · simp [lineFreeEndpoint, h] at hfullRight
      omega
    · rfl
  constructor
  · rw [hlast] at hfullRight
    change lineFreeEndpoint (start.1 : Int) pref + 1 = n at hfullRight
    change lineFreeEndpoint (start.1 : Int) pref = (n : Int) - 1
    omega
  · simpa [pref, hlast] using hdecomp.symm

private def lineFirstEndpointLeftToNoHit
    (n k : Nat) (start target : IsingLineBox n)
    (hk : 0 < k) (htarget : target.1 = 0) :
    IsingLineFirstEndpointFamily n k start target ->
      IsingHorizontalNoHitEndpointFamily (k - 1) 0 (-(start.1 : Int)) :=
  fun w => by
    let pref := w.1.dropLast
    let word := pref.reverse
    have hdata := lineFirstEndpoint_dropLast_data n k start target w hk
    dsimp only at hdata
    have hprefLen : pref.length = k - 1 := hdata.1
    have hprefEnd := (lineFirstEndpoint_left_dropLast n k start target
      w hk htarget).1
    have hprefSum :
        (start.1 : Int) + (pref.map endpointFailureLineStep).sum = 1 := by
      rw [← lineFreeEndpoint_eq_start_add_sum_endpointFailure]
      exact hprefEnd
    refine ⟨⟨word, ?_, ?_⟩, ?_⟩
    · simp [word, hprefLen]
    · intro r hr hhit
      have hrPref : r <= pref.length := by omega
      let cut := pref.length - r
      let a := pref.take cut
      let s := pref.drop cut
      have hcut : cut <= pref.length := Nat.sub_le _ _
      have hdecomp : a ++ s = pref := by
        exact List.take_append_drop cut pref
      have hsum :
          (pref.map endpointFailureLineStep).sum =
            (a.map endpointFailureLineStep).sum +
              (s.map endpointFailureLineStep).sum := by
        rw [← hdecomp, List.map_append, List.sum_append]
      have hpos := hdata.2.2 cut hcut
      have hposEq :
          lineFreeEndpoint (start.1 : Int) a =
            (start.1 : Int) + (a.map endpointFailureLineStep).sum :=
        lineFreeEndpoint_eq_start_add_sum_endpointFailure _ _
      have htake : word.take r = s.reverse := by
        dsimp [word, s, cut]
        rw [List.take_reverse]
      change lineFreeEndpoint (-1) (word.take r) = 0 at hhit
      rw [htake, lineFreeEndpoint_eq_start_add_sum_endpointFailure,
        sum_map_lineStep_reverse_endpointFailure] at hhit
      rw [hposEq] at hpos
      exact hpos.1 (by linarith)
    · dsimp [word]
      rw [lineFreeEndpoint_eq_start_add_sum_endpointFailure,
        sum_map_lineStep_reverse_endpointFailure]
      linarith

private theorem lineFirstEndpointLeftToNoHit_injective
    (n k : Nat) (start target : IsingLineBox n)
    (hk : 0 < k) (htarget : target.1 = 0) :
    Function.Injective
      (lineFirstEndpointLeftToNoHit n k start target hk htarget) := by
  intro a b hab
  have hword := congrArg
    (fun z : IsingHorizontalNoHitEndpointFamily (k - 1) 0
      (-(start.1 : Int)) => z.1.1) hab
  change a.1.dropLast.reverse = b.1.dropLast.reverse at hword
  have hdrop : a.1.dropLast = b.1.dropLast :=
    List.reverse_injective hword
  apply Subtype.ext
  rw [(lineFirstEndpoint_left_dropLast n k start target a hk htarget).2,
    (lineFirstEndpoint_left_dropLast n k start target b hk htarget).2,
    hdrop]

private def lineFirstEndpointRightToNoHit
    (n k : Nat) (start target : IsingLineBox n)
    (hk : 0 < k) (htarget : target.1 = n) :
    IsingLineFirstEndpointFamily n k start target ->
      IsingHorizontalNoHitEndpointFamily (k - 1) n (start.1 : Int) :=
  fun w => by
    let pref := w.1.dropLast
    let word := pref.reverse.map (!.)
    have hdata := lineFirstEndpoint_dropLast_data n k start target w hk
    dsimp only at hdata
    have hprefLen : pref.length = k - 1 := hdata.1
    have hprefEnd := (lineFirstEndpoint_right_dropLast n k start target
      w hk htarget).1
    have hprefSum :
        (start.1 : Int) + (pref.map endpointFailureLineStep).sum =
          (n : Int) - 1 := by
      rw [← lineFreeEndpoint_eq_start_add_sum_endpointFailure]
      exact hprefEnd
    refine ⟨⟨word, ?_, ?_⟩, ?_⟩
    · simp [word, hprefLen]
    · intro r hr hhit
      have hrPref : r <= pref.length := by omega
      let cut := pref.length - r
      let a := pref.take cut
      let s := pref.drop cut
      have hcut : cut <= pref.length := Nat.sub_le _ _
      have hdecomp : a ++ s = pref := by
        exact List.take_append_drop cut pref
      have hsum :
          (pref.map endpointFailureLineStep).sum =
            (a.map endpointFailureLineStep).sum +
              (s.map endpointFailureLineStep).sum := by
        rw [← hdecomp, List.map_append, List.sum_append]
      have hpos := hdata.2.2 cut hcut
      have hposEq :
          lineFreeEndpoint (start.1 : Int) a =
            (start.1 : Int) + (a.map endpointFailureLineStep).sum :=
        lineFreeEndpoint_eq_start_add_sum_endpointFailure _ _
      have htake : word.take r = s.reverse.map (!.) := by
        dsimp [word, s, cut]
        rw [← List.map_take, List.take_reverse]
      change lineFreeEndpoint ((n : Int) - 1) (word.take r) = n at hhit
      rw [htake, lineFreeEndpoint_eq_start_add_sum_endpointFailure,
        sum_map_lineStep_reverse_not_endpointFailure] at hhit
      rw [hposEq] at hpos
      exact hpos.2 (by linarith)
    · dsimp [word]
      rw [lineFreeEndpoint_eq_start_add_sum_endpointFailure,
        sum_map_lineStep_reverse_not_endpointFailure]
      linarith

private theorem lineFirstEndpointRightToNoHit_injective
    (n k : Nat) (start target : IsingLineBox n)
    (hk : 0 < k) (htarget : target.1 = n) :
    Function.Injective
      (lineFirstEndpointRightToNoHit n k start target hk htarget) := by
  intro a b hab
  have hword := congrArg
    (fun z : IsingHorizontalNoHitEndpointFamily (k - 1) n
      (start.1 : Int) => z.1.1) hab
  change a.1.dropLast.reverse.map (!.) =
    b.1.dropLast.reverse.map (!.) at hword
  have hnotInjective : Function.Injective (fun b : Bool => !b) := by
    intro x y h
    cases x <;> cases y <;> simp at h ⊢
  have hreverse : a.1.dropLast.reverse = b.1.dropLast.reverse :=
    (Function.Injective.list_map hnotInjective) hword
  have hdrop : a.1.dropLast = b.1.dropLast :=
    List.reverse_injective hreverse
  apply Subtype.ext
  rw [(lineFirstEndpoint_right_dropLast n k start target a hk htarget).2,
    (lineFirstEndpoint_right_dropLast n k start target b hk htarget).2,
    hdrop]



theorem lineFirstEndpoint_boundary_weight_le
    (n k : Nat) (start target : IsingLineBox n)
    (hk : 0 < k) (htarget : isingLineBoxBoundary n target) :
    Nat.card (IsingLineFirstEndpointFamily n k start target) /
        (2 : Real) ^ k <= 2 / (k : Real) := by
  rcases htarget with hleft | hright
  · have hcard : Nat.card (IsingLineFirstEndpointFamily n k start target) <=
        Nat.card (IsingHorizontalNoHitEndpointFamily
          (k - 1) 0 (-(start.1 : Int))) :=
      Nat.card_le_card_of_injective
        (lineFirstEndpointLeftToNoHit n k start target hk hleft)
        (lineFirstEndpointLeftToNoHit_injective n k start target hk hleft)
    have hballot := horizontalNoHitEndpoint_weight_le
      (k - 1) 0 (-(start.1 : Int))
    have hpow : (2 : Real) ^ k = 2 * (2 : Real) ^ (k - 1) := by
      calc
        _ = (2 : Real) ^ ((k - 1) + 1) := by congr 1; omega
        _ = _ := by rw [pow_add]; norm_num; ring
    calc
      _ <= Nat.card (IsingHorizontalNoHitEndpointFamily
          (k - 1) 0 (-(start.1 : Int))) / (2 : Real) ^ k := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast hcard
      _ = (1 / 2 : Real) *
          (Nat.card (IsingHorizontalNoHitEndpointFamily
            (k - 1) 0 (-(start.1 : Int))) / (2 : Real) ^ (k - 1)) := by
        rw [hpow]
        ring
      _ <= (1 / 2 : Real) * (4 / (k : Real)) := by
        apply mul_le_mul_of_nonneg_left
        · have hkCast : (((k - 1 : Nat) : Real) + 1) = (k : Real) := by
            exact_mod_cast (show k - 1 + 1 = k by omega)
          rw [hkCast] at hballot
          exact hballot
        · norm_num
      _ = 2 / (k : Real) := by ring
  · have hcard : Nat.card (IsingLineFirstEndpointFamily n k start target) <=
        Nat.card (IsingHorizontalNoHitEndpointFamily
          (k - 1) n (start.1 : Int)) :=
      Nat.card_le_card_of_injective
        (lineFirstEndpointRightToNoHit n k start target hk hright)
        (lineFirstEndpointRightToNoHit_injective n k start target hk hright)
    have hballot := horizontalNoHitEndpoint_weight_le
      (k - 1) n (start.1 : Int)
    have hpow : (2 : Real) ^ k = 2 * (2 : Real) ^ (k - 1) := by
      calc
        _ = (2 : Real) ^ ((k - 1) + 1) := by congr 1; omega
        _ = _ := by rw [pow_add]; norm_num; ring
    calc
      _ <= Nat.card (IsingHorizontalNoHitEndpointFamily
          (k - 1) n (start.1 : Int)) / (2 : Real) ^ k := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast hcard
      _ = (1 / 2 : Real) *
          (Nat.card (IsingHorizontalNoHitEndpointFamily
            (k - 1) n (start.1 : Int)) / (2 : Real) ^ (k - 1)) := by
        rw [hpow]
        ring
      _ <= (1 / 2 : Real) * (4 / (k : Real)) := by
        apply mul_le_mul_of_nonneg_left
        · have hkCast : (((k - 1 : Nat) : Real) + 1) = (k : Real) := by
            exact_mod_cast (show k - 1 + 1 = k by omega)
          rw [hkCast] at hballot
          exact hballot
        · norm_num
      _ = 2 / (k : Real) := by ring





def IsingOrderedFarEndpointFamily
    (m n t : Nat) (start target : IsingLineBox n)
    (markX targetX : Int) :=
  Sigma fun k : Fin (t + 1) =>
    Sigma fun j : Fin k =>
      IsingLineFarFirstBoundaryFamily m j ×
        IsingLineFirstEndpointFamily n k start target ×
        VerticalChoicePathFamily (k - j) markX targetX ×
        {tail : List (Bool × Bool) // tail.length = t - k}

noncomputable instance isingOrderedFarEndpointFamily_finite
    (m n t : Nat) (start target : IsingLineBox n)
    (markX targetX : Int) :
    Finite (IsingOrderedFarEndpointFamily m n t start target markX targetX) := by
  letI (k : Fin (t + 1)) : Fintype (Fin k) := inferInstance
  letI (k : Fin (t + 1)) (j : Fin k) :
      Fintype (IsingLineFarFirstBoundaryFamily m j) := Fintype.ofFinite _
  letI (k : Fin (t + 1)) :
      Fintype (IsingLineFirstEndpointFamily n k start target) :=
    Fintype.ofFinite _
  letI (k : Fin (t + 1)) (j : Fin k) :
      Fintype (VerticalChoicePathFamily (k - j) markX targetX) :=
    Fintype.ofFinite _
  letI (k : Fin (t + 1)) :
      Fintype {tail : List (Bool × Bool) // tail.length = t - k} :=
    (List.finite_length_eq (Bool × Bool) (t - k)).fintype
  unfold IsingOrderedFarEndpointFamily
  infer_instance


theorem natCard_orderedFarEndpoint_eq_sum
    (m n t : Nat) (start target : IsingLineBox n)
    (markX targetX : Int) :
    Nat.card (IsingOrderedFarEndpointFamily
        m n t start target markX targetX) =
      ∑ k : Fin (t + 1), ∑ j : Fin k,
        Nat.card (IsingLineFarFirstBoundaryFamily m j) *
        Nat.card (IsingLineFirstEndpointFamily n k start target) *
        Nat.card (VerticalChoicePathFamily (k - j) markX targetX) *
        4 ^ (t - (k : Nat)) := by
  letI (k : Fin (t + 1)) : Fintype (Fin k) := inferInstance
  letI (k : Fin (t + 1)) (j : Fin k) :
      Fintype (IsingLineFarFirstBoundaryFamily m j) := Fintype.ofFinite _
  letI (k : Fin (t + 1)) :
      Fintype (IsingLineFirstEndpointFamily n k start target) :=
    Fintype.ofFinite _
  letI (k : Fin (t + 1)) (j : Fin k) :
      Fintype (VerticalChoicePathFamily (k - j) markX targetX) :=
    Fintype.ofFinite _
  letI (k : Fin (t + 1)) :
      Fintype {tail : List (Bool × Bool) // tail.length = t - k} :=
    (List.finite_length_eq (Bool × Bool) (t - k)).fintype
  unfold IsingOrderedFarEndpointFamily
  rw [Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.card_prod, Nat.card_prod, Nat.card_prod]
  have htail : Nat.card
      {tail : List (Bool × Bool) // tail.length = t - (k : Nat)} =
      4 ^ (t - (k : Nat)) := by
    change Nat.card (List.Vector (Bool × Bool) (t - (k : Nat))) =
      4 ^ (t - (k : Nat))
    rw [Nat.card_congr
        (Equiv.vectorEquivFin (Bool × Bool) (t - (k : Nat))),
      Nat.card_eq_fintype_card, Fintype.card_fun]
    norm_num
  rw [htail]
  ring


theorem orderedFarEndpoint_weight_eq_sum
    (m n t : Nat) (start target : IsingLineBox n)
    (markX targetX : Int) :
    Nat.card (IsingOrderedFarEndpointFamily
        m n t start target markX targetX) / (4 : Real) ^ t =
      ∑ k : Fin (t + 1), ∑ j : Fin k,
        (Nat.card (IsingLineFarFirstBoundaryFamily m j) /
          (2 : Real) ^ (j : Nat)) *
        (Nat.card (IsingLineFirstEndpointFamily n k start target) /
          (2 : Real) ^ (k : Nat)) *
        (Nat.card (VerticalChoicePathFamily (k - j) markX targetX) /
          (2 : Real) ^ ((k : Nat) - (j : Nat))) := by
  rw [natCard_orderedFarEndpoint_eq_sum]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : (j : Nat) <= (k : Nat) := Nat.le_of_lt j.isLt
  have hfourT : (4 : Real) ^ t =
      (4 : Real) ^ (k : Nat) * (4 : Real) ^ (t - (k : Nat)) := by
    calc
      _ = (4 : Real) ^ ((k : Nat) + (t - (k : Nat))) := by
        congr 1
        exact (Nat.add_sub_of_le (Nat.le_of_lt_succ k.isLt)).symm
      _ = _ := pow_add _ _ _
  have htwoK : (4 : Real) ^ (k : Nat) =
      (2 : Real) ^ (k : Nat) * (2 : Real) ^ (k : Nat) := by
    rw [show (4 : Real) = 2 * 2 by norm_num, mul_pow]
  have hsplitK : (2 : Real) ^ (k : Nat) =
      (2 : Real) ^ (j : Nat) *
        (2 : Real) ^ ((k : Nat) - (j : Nat)) := by
    calc
      _ = (2 : Real) ^ ((j : Nat) + ((k : Nat) - (j : Nat))) := by
        congr 1
        omega
      _ = _ := pow_add _ _ _
  rw [hfourT, htwoK, hsplitK]
  field_simp




theorem orderedFarEndpoint_weight_le
    (m n t : Nat) (start target : IsingLineBox n)
    (markX targetX : Int) (hm : 0 < m) (ht : t <= m * m)
    (htarget : isingLineBoxBoundary n target) :
    Nat.card (IsingOrderedFarEndpointFamily
        m n t start target markX targetX) / (4 : Real) ^ t <=
      7488 / (m : Real) ^ 2 := by
  let b : Nat -> Real := fun j =>
    Nat.card (IsingLineFarFirstBoundaryFamily m j) / (2 : Real) ^ j
  let v : Nat -> Real := fun k =>
    Nat.card (IsingLineFirstEndpointFamily n k start target) / (2 : Real) ^ k
  let h : Nat -> Real := fun r =>
    Nat.card (VerticalChoicePathFamily r markX targetX) / (2 : Real) ^ r
  have hb0 (j : Nat) : 0 <= b j := by
    dsimp [b]
    positivity
  have hv (k : Nat) (hk : 0 < k) : v k <= 2 / (k : Real) := by
    exact lineFirstEndpoint_boundary_weight_le n k start target hk htarget
  have hh (r : Nat) : h r <= 2 / Real.sqrt (r + 1 : Real) := by
    dsimp [h]
    rw [← isingLineBinomialKernel_eq_natCard_verticalChoicePath_div]
    let K := isingLineBinomialKernel r markX targetX
    have hK0 : 0 <= K := isingLineBinomialKernel_nonneg _ _ _
    have hrad : 0 <= 2 / (r + 1 : Real) := by positivity
    have hK : K <= Real.sqrt (2 / (r + 1 : Real)) := by
      rw [Real.le_sqrt hK0 hrad]
      exact isingLineBinomialKernel_sq_le r markX targetX
    calc
      K <= Real.sqrt (2 / (r + 1 : Real)) := hK
      _ <= 2 / Real.sqrt (r + 1 : Real) := by
        rw [Real.sqrt_div (by positivity)]
        apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
        rw [Real.sqrt_le_iff]
        norm_num
  have hfactor :
      Nat.card (IsingOrderedFarEndpointFamily
          m n t start target markX targetX) / (4 : Real) ^ t =
        ∑ k ∈ Finset.range (t + 1), ∑ j ∈ Finset.range k,
          b j * v k * h (k - j) := by
    rw [orderedFarEndpoint_weight_eq_sum]
    change (∑ k : Fin (t + 1), ∑ j : Fin k,
      b (j : Nat) * v (k : Nat) * h ((k : Nat) - (j : Nat))) = _
    rw [Fin.sum_univ_eq_sum_range
      (fun k : Nat => ∑ j : Fin k, b (j : Nat) * v k * h (k - (j : Nat)))
      (t + 1)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Fin.sum_univ_eq_sum_range
      (fun j : Nat => b j * v k * h (k - j)) k]
  rw [hfactor]
  calc
    (∑ k ∈ Finset.range (t + 1), ∑ j ∈ Finset.range k,
        b j * v k * h (k - j)) <=
        ∑ k ∈ Finset.range (t + 1), ∑ j ∈ Finset.range k,
          b j * (2 / (k : Real)) *
            (2 / Real.sqrt ((k - j + 1 : Nat) : Real)) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hbk : 0 <= b j := hb0 j
      calc
        b j * v k * h (k - j) <=
            b j * (2 / (k : Real)) * h (k - j) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left (hv k (by omega)) hbk
          · dsimp [h]
            positivity
        _ <= b j * (2 / (k : Real)) *
            (2 / Real.sqrt ((k - j + 1 : Nat) : Real)) := by
          have hh' : h (k - j) <=
              2 / Real.sqrt ((k - j + 1 : Nat) : Real) := by
            simpa [Nat.cast_add, Nat.cast_one] using hh (k - j)
          apply mul_le_mul_of_nonneg_left hh'
          exact mul_nonneg hbk (by positivity)
    _ = ∑ j ∈ Finset.range (t + 1), b j *
          (∑ l ∈ Finset.range (t - j),
            (2 / ((j + l + 1 : Nat) : Real)) *
              (2 / Real.sqrt ((l + 2 : Nat) : Real))) := by
      let f : Nat -> Nat -> Real := fun j l =>
        b j * ((2 / ((j + l + 1 : Nat) : Real)) *
          (2 / Real.sqrt ((l + 2 : Nat) : Real)))
      rw [Finset.sum_range_succ']
      simp only [Finset.sum_range_zero, sum_empty, add_zero]
      calc
        (∑ k ∈ Finset.range t, ∑ j ∈ Finset.range (k + 1),
            b j * (2 / ((k + 1 : Nat) : Real)) *
              (2 / Real.sqrt ((k + 1 - j + 1 : Nat) : Real))) =
            ∑ k ∈ Finset.range t, ∑ j ∈ Finset.range (k + 1),
              f j (k - j) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro j hj
          have hjk : j <= k := by
            have := Finset.mem_range.mp hj
            omega
          have hden : j + (k - j) + 1 = k + 1 := by omega
          have hgap : k + 1 - j + 1 = k - j + 2 := by omega
          dsimp [f]
          rw [hden, hgap]
          ring
        _ = ∑ j ∈ Finset.range t, ∑ l ∈ Finset.range (t - j),
              f j l := Finset.sum_range_diag_flip t f
        _ = ∑ j ∈ Finset.range (t + 1), b j *
              (∑ l ∈ Finset.range (t - j),
                (2 / ((j + l + 1 : Nat) : Real)) *
                  (2 / Real.sqrt ((l + 2 : Nat) : Real))) := by
          rw [Finset.sum_range_succ]
          simp [f, Finset.mul_sum]
    _ <= 16 * (∑ j ∈ Finset.range (t + 1),
          (2 / Real.sqrt ((j + 1 : Nat) : Real)) * b j) :=
      orderedFarFirstEndpoint_swapped_convolution_le t b hb0
    _ <= 16 * (468 / (m : Real) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa [b, Nat.cast_add, Nat.cast_one] using
        endpointKernel_farFirstBoundary_sum_le m t hm ht
    _ = 7488 / (m : Real) ^ 2 := by ring

theorem orderedFarEndpoint_diffusive_weight_le
    (rho m n : Nat) (start target : IsingLineBox n)
    (markX targetX : Int) (hρ : 0 < rho) (hρm : rho <= m)
    (htarget : isingLineBoxBoundary n target) :
    Nat.card (IsingOrderedFarEndpointFamily
        m n (rho * rho) start target markX targetX) /
        (4 : Real) ^ (rho * rho) <=
      7488 / (rho : Real) ^ 2 := by
  have hm : 0 < m := lt_of_lt_of_le hρ hρm
  have ht : rho * rho <= m * m := Nat.mul_self_le_mul_self hρm
  have hmain := orderedFarEndpoint_weight_le m n (rho * rho)
    start target markX targetX hm ht htarget
  have hsq : (rho : Real) ^ 2 <= (m : Real) ^ 2 := by
    exact_mod_cast (show rho ^ 2 <= m ^ 2 by
      simpa [pow_two] using ht)
  exact hmain.trans
    (div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq)

private def endpointFailureAlignedOrResidualValue
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Sum (IsingSourceFailureOutputAtFamily R t p q level)
      (Sum (IsingMirrorFailureOutputAtFamily R t p p' q level)
        (IsingMirrorOnlySourceOutputAtFamily R t p p' q level)) ->
      IsingLeapfrogChoiceStringFamily t
  | Sum.inl w => w.1.1
  | Sum.inr (Sum.inl w) => w.1.1
  | Sum.inr (Sum.inr w) => w.1

private theorem exists_mirrorFailureAtAlignedOrResidualCover
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int)
    (w : IsingStoppedCouplingMirrorFailureAtFamily R t p p' q level) :
    exists z : Sum (IsingSourceFailureOutputAtFamily R t p q level)
        (Sum (IsingMirrorFailureOutputAtFamily R t p p' q level)
          (IsingMirrorOnlySourceOutputAtFamily R t p p' q level)),
      endpointFailureAlignedOrResidualValue R t p p' q level z = w.1 := by
  rcases w.2.2 with hsourceOutput | hmirrorOutput
  · by_cases hs : IsingStoppedCouplingSourceFailure R p level w.1
    · exact ⟨Sum.inl ⟨⟨w.1, hs⟩, hsourceOutput⟩, rfl⟩
    · exact ⟨Sum.inr (Sum.inr ⟨w.1, w.2.1, hs, hsourceOutput⟩), rfl⟩
  · exact ⟨Sum.inr (Sum.inl ⟨⟨w.1, w.2.1⟩, hmirrorOutput⟩), rfl⟩

private noncomputable def mirrorFailureAtAlignedOrResidualCover
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    IsingStoppedCouplingMirrorFailureAtFamily R t p p' q level ->
      Sum (IsingSourceFailureOutputAtFamily R t p q level)
        (Sum (IsingMirrorFailureOutputAtFamily R t p p' q level)
          (IsingMirrorOnlySourceOutputAtFamily R t p p' q level)) := fun w =>
  Classical.choose
    (exists_mirrorFailureAtAlignedOrResidualCover R t p p' q level w)

private theorem mirrorFailureAtAlignedOrResidualCover_value
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int)
    (w : IsingStoppedCouplingMirrorFailureAtFamily R t p p' q level) :
    endpointFailureAlignedOrResidualValue R t p p' q level
      (mirrorFailureAtAlignedOrResidualCover R t p p' q level w) = w.1 := by
  exact Classical.choose_spec
    (exists_mirrorFailureAtAlignedOrResidualCover R t p p' q level w)

private theorem mirrorFailureAtAlignedOrResidualCover_injective
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Function.Injective
      (mirrorFailureAtAlignedOrResidualCover R t p p' q level) := by
  intro a b hab
  apply Subtype.ext
  rw [← mirrorFailureAtAlignedOrResidualCover_value R t p p' q level a,
    ← mirrorFailureAtAlignedOrResidualCover_value R t p p' q level b, hab]

theorem natCard_mirrorFailureAt_le_aligned_add_residual
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Nat.card (IsingStoppedCouplingMirrorFailureAtFamily R t p p' q level) <=
      Nat.card (IsingSourceFailureOutputAtFamily R t p q level) +
        Nat.card (IsingMirrorFailureOutputAtFamily R t p p' q level) +
        Nat.card (IsingMirrorOnlySourceOutputAtFamily R t p p' q level) := by
  calc
    _ <= Nat.card (Sum (IsingSourceFailureOutputAtFamily R t p q level)
        (Sum (IsingMirrorFailureOutputAtFamily R t p p' q level)
          (IsingMirrorOnlySourceOutputAtFamily R t p p' q level))) :=
      Nat.card_le_card_of_injective
        (mirrorFailureAtAlignedOrResidualCover R t p p' q level)
        (mirrorFailureAtAlignedOrResidualCover_injective R t p p' q level)
    _ = _ := by rw [Nat.card_sum, Nat.card_sum]; omega

theorem choiceRun_boundary_output_data_endpointFailure
    (R t : Nat) (p q : IsingLeapfrogBox R)
    (hq : isingLeapfrogBoxBoundary R q)
    (w : IsingLeapfrogChoiceStringFamily t)
    (hout : isingLeapfrogChoiceRun R p w.1 = q) :
    exists k, k <= t /\
      isingLeapfrogChoiceRun R p (w.1.take k) = q /\
      forall l, l < k -> ¬ isingLeapfrogBoxBoundary R
        (isingLeapfrogChoiceRun R p (w.1.take l)) := by
  let hex : exists k, k <= t /\ isingLeapfrogBoxBoundary R
      (isingLeapfrogChoiceRun R p (w.1.take k)) := by
    refine ⟨t, le_refl _, ?_⟩
    have ht : w.1.take t = w.1 := by
      simpa [w.2] using (List.take_all w.1)
    rw [ht, hout]
    exact hq
  let k := Nat.find hex
  have hkSpec := Nat.find_spec hex
  have hminimal : forall l, l < k -> ¬ isingLeapfrogBoxBoundary R
      (isingLeapfrogChoiceRun R p (w.1.take l)) := by
    intro l hl hb
    exact Nat.find_min hex hl ⟨by omega, hb⟩
  have hkOutput : isingLeapfrogChoiceRun R p (w.1.take k) = q := by
    have hdecomp : w.1 = w.1.take k ++ w.1.drop k :=
      (List.take_append_drop k w.1).symm
    have hfull : isingLeapfrogChoiceRun R p w.1 =
        isingLeapfrogChoiceRun R p (w.1.take k) := by
      calc
        _ = isingLeapfrogChoiceRun R p (w.1.take k ++ w.1.drop k) := by
          rw [← hdecomp]
        _ = isingLeapfrogChoiceRun R
            (isingLeapfrogChoiceRun R p (w.1.take k)) (w.1.drop k) :=
          isingLeapfrogChoiceRun_append_full ..
        _ = _ := isingLeapfrogChoiceRun_of_boundary_endpointFailure R _
          hkSpec.2 _
    exact hfull.symm.trans hout
  exact ⟨k, hkSpec.1, hkOutput, hminimal⟩

theorem mirrorOnly_firstBoundary_right
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (w : IsingMirrorOnlySourceOutputAtFamily R t p p' q (level : Int)) :
    exists (split : IsingDiagonalWalkHitSplit (isingLeapfrogBoxInt p)
        (level : Int)) (j : Nat),
      isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p) (level : Int)
        (isingLeapfrogChoiceSteps w.1.1) = some split /\
      j < split.before.length /\
      (isingLeapfrogChoiceRun R p'
        ((isingLeapfrogCouplingChoiceTransform t (isingLeapfrogBoxInt p)
          (level : Int) w.1).1.take j)).1.1 = R /\
      ((isingLeapfrogChoiceRun R p (w.1.1.take j)).1.1 : Int) =
        2 * (level : Int) - R /\
      (forall l, l < j ->
        2 * (level : Int) - R <
            ((isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 : Int) /\
          ((isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 : Int) < level) /\
      (forall l, l < j -> ¬ isingLeapfrogBoxBoundary R
        (isingLeapfrogChoiceRun R p'
          ((isingLeapfrogCouplingChoiceTransform t (isingLeapfrogBoxInt p)
            (level : Int) w.1).1.take l))) /\
      IsingLeapfrogChoiceExecValid R p (w.1.1.take split.before.length) := by
  rcases w.2.1 with ⟨split, hsplit, hmirrorNotValid⟩
  have hsourceValid : IsingLeapfrogChoiceExecValid R p
      (w.1.1.take split.before.length) := by
    by_contra hnot
    exact w.2.2.1 ⟨split, hsplit, hnot⟩
  let w' := isingLeapfrogCouplingChoiceTransform t
    (isingLeapfrogBoxInt p) (level : Int) w.1
  have hex : exists j, j < (w'.1.take split.before.length).length /\
      isingLeapfrogBoxBoundary R
        (isingLeapfrogChoiceRun R p' ((w'.1.take split.before.length).take j)) := by
    unfold IsingLeapfrogChoiceExecValid at hmirrorNotValid
    push_neg at hmirrorNotValid
    exact hmirrorNotValid
  let j := Nat.find hex
  have hjSpec := Nat.find_spec hex
  have hbeforeT : split.before.length <= t := by
    have hlen := congrArg List.length (firstHitSplit_steps hsplit)
    simp [IsingDiagonalWalkHitSplit.steps, isingLeapfrogChoiceSteps,
      w.1.2] at hlen
    omega
  have hj : j < split.before.length := by
    have hj' := hjSpec.1
    change j < (w'.1.take split.before.length).length at hj'
    rw [List.length_take] at hj'
    have hw' : (isingLeapfrogCouplingChoiceTransform t
        (isingLeapfrogBoxInt p) (level : Int) w.1).1.length = t :=
      (isingLeapfrogCouplingChoiceTransform t
        (isingLeapfrogBoxInt p) (level : Int) w.1).2
    change w'.1.length = t at hw'
    omega
  have hmirrorBoundary : isingLeapfrogBoxBoundary R
      (isingLeapfrogChoiceRun R p' (w'.1.take j)) := by
    have hb := hjSpec.2
    change isingLeapfrogBoxBoundary R
      (isingLeapfrogChoiceRun R p' ((w'.1.take split.before.length).take j)) at hb
    simpa [List.take_take, Nat.min_eq_left hj.le] using hb
  have hmirrorMinimal : forall r, r < j ->
      ¬ isingLeapfrogBoxBoundary R
        (isingLeapfrogChoiceRun R p' (w'.1.take r)) := by
    intro r hr hb
    apply Nat.find_min hex hr
    refine ⟨?_, ?_⟩
    · rw [List.length_take]
      have hw' : w'.1.length = t := w'.2
      omega
    · simpa [List.take_take,
        Nat.min_eq_left (show r <= split.before.length by omega)] using hb
  have hmirrorValidJ : IsingLeapfrogChoiceExecValid R p' (w'.1.take j) := by
    intro r hr
    have hrj : r < j := by
      rw [List.length_take] at hr
      omega
    simpa [List.take_take, Nat.min_eq_left hrj.le] using
      hmirrorMinimal r hrj
  have hsourceValidJ : IsingLeapfrogChoiceExecValid R p (w.1.1.take j) := by
    intro r hr
    have hrj : r < j := by
      rw [List.length_take] at hr
      omega
    have hs := hsourceValid r (by
      rw [List.length_take]
      have hw : w.1.1.length = t := w.1.2
      omega)
    simpa [List.take_take, Nat.min_eq_left hrj.le,
      Nat.min_eq_left (show r <= split.before.length by omega)] using hs
  have hvalid : split.Valid := by
    unfold IsingDiagonalWalkHitSplit.Valid
    rw [firstHitSplit_steps hsplit]
    exact isingLeapfrogChoiceSteps_valid w.1.1
  have hsourceLt := (firstHitSplit_firstHit hsplit).endpoint_take_fst_lt
    split hvalid (by omega : (isingLeapfrogBoxInt p).1 < (level : Int)) j hj
  have hsourceBeforeSteps : split.before.take j =
      isingLeapfrogChoiceSteps (w.1.1.take j) := by
    have hs := congrArg (fun path : List (Int × Int) => path.take j)
      (firstHitSplit_steps hsplit)
    simpa [IsingDiagonalWalkHitSplit.steps,
      List.take_append_of_le_length hj.le,
      isingLeapfrogChoiceSteps, List.map_take] using hs
  rw [hsourceBeforeSteps] at hsourceLt
  have hsourceSteps : split.steps.take j =
      isingLeapfrogChoiceSteps (w.1.1.take j) := by
    have hs := congrArg (fun path : List (Int × Int) => path.take j)
      (firstHitSplit_steps hsplit)
    simpa [isingLeapfrogChoiceSteps, List.map_take] using hs
  have hsourceRun := choiceExecValid_run_boxInt_eq_endpoint R p
    (w.1.1.take j) hsourceValidJ
  have hmirrorRun := choiceExecValid_run_boxInt_eq_endpoint R p'
    (w'.1.take j) hmirrorValidJ
  have hbeforeSteps := couplingChoiceTransform_take_steps_of_some t
    (isingLeapfrogBoxInt p) (level : Int) w.1 split hsplit
  have hmirrorSteps : isingLeapfrogChoiceSteps (w'.1.take j) =
      split.reflectPrefix.steps.take j := by
    calc
      _ = (isingLeapfrogChoiceSteps (w'.1.take split.before.length)).take j := by
        simp [isingLeapfrogChoiceSteps, List.map_take, List.take_take,
          Nat.min_eq_left hj.le]
      _ = (split.before.map reflectIncrement).take j := by rw [hbeforeSteps]
      _ = _ := by
        unfold IsingDiagonalWalkHitSplit.reflectPrefix
          IsingDiagonalWalkHitSplit.steps
        rw [List.take_append_of_le_length (by simpa using hj.le)]
  have hmx := congrArg Prod.fst hmirrorRun
  change ((isingLeapfrogChoiceRun R p' (w'.1.take j)).1.1 : Int) =
    (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p')
      (isingLeapfrogChoiceSteps (w'.1.take j))).1 at hmx
  rw [hmirror, hmirrorSteps,
    reflectPrefix_endpoint_take_fst_of_le_before split j hj.le,
    hsourceSteps] at hmx
  have hmy := congrArg Prod.snd hmirrorRun
  change ((isingLeapfrogChoiceRun R p' (w'.1.take j)).2.1 : Int) =
    (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p')
      (isingLeapfrogChoiceSteps (w'.1.take j))).2 at hmy
  rw [hmirror, hmirrorSteps,
    reflectPrefix_endpoint_take_snd_of_le_before split j hj.le,
    hsourceSteps] at hmy
  have hsx := congrArg Prod.fst hsourceRun
  have hsy := congrArg Prod.snd hsourceRun
  change ((isingLeapfrogChoiceRun R p (w.1.1.take j)).1.1 : Int) =
    (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
      (isingLeapfrogChoiceSteps (w.1.1.take j))).1 at hsx
  change ((isingLeapfrogChoiceRun R p (w.1.1.take j)).2.1 : Int) =
    (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
      (isingLeapfrogChoiceSteps (w.1.1.take j))).2 at hsy
  have hsourceBetween : forall l, l < j ->
      2 * (level : Int) - R <
          ((isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 : Int) /\
        ((isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 : Int) < level := by
    intro l hl
    have hlBefore : l < split.before.length := hl.trans hj
    have hsourceValidL : IsingLeapfrogChoiceExecValid R p (w.1.1.take l) := by
      intro r hr
      have hrl : r < l := by
        rw [List.length_take] at hr
        omega
      have hs := hsourceValid r (by
        rw [List.length_take]
        have hw : w.1.1.length = t := w.1.2
        omega)
      change ¬ isingLeapfrogBoxBoundary R
        (isingLeapfrogChoiceRun R p ((w.1.1.take l).take r))
      change ¬ isingLeapfrogBoxBoundary R
        (isingLeapfrogChoiceRun R p
          ((w.1.1.take split.before.length).take r)) at hs
      rw [List.take_take, Nat.min_eq_left hrl.le]
      rw [List.take_take,
        Nat.min_eq_left (show r <= split.before.length by omega)] at hs
      exact hs
    have hmirrorValidL : IsingLeapfrogChoiceExecValid R p' (w'.1.take l) := by
      intro r hr
      have hrl : r < l := by
        rw [List.length_take] at hr
        omega
      simpa [List.take_take, Nat.min_eq_left hrl.le] using
        hmirrorMinimal r (hrl.trans hl)
    have hsourceStepsL : split.steps.take l =
        isingLeapfrogChoiceSteps (w.1.1.take l) := by
      have hs := congrArg (fun path : List (Int × Int) => path.take l)
        (firstHitSplit_steps hsplit)
      simpa [isingLeapfrogChoiceSteps, List.map_take] using hs
    have hsourceBeforeStepsL : split.before.take l =
        isingLeapfrogChoiceSteps (w.1.1.take l) := by
      have hs := congrArg (fun path : List (Int × Int) => path.take l)
        (firstHitSplit_steps hsplit)
      simpa [IsingDiagonalWalkHitSplit.steps,
        List.take_append_of_le_length hlBefore.le,
        isingLeapfrogChoiceSteps, List.map_take] using hs
    have hmirrorStepsL : isingLeapfrogChoiceSteps (w'.1.take l) =
        split.reflectPrefix.steps.take l := by
      calc
        _ = (isingLeapfrogChoiceSteps
            (w'.1.take split.before.length)).take l := by
          simp [isingLeapfrogChoiceSteps, List.map_take, List.take_take,
            Nat.min_eq_left hlBefore.le]
        _ = (split.before.map reflectIncrement).take l := by rw [hbeforeSteps]
        _ = _ := by
          unfold IsingDiagonalWalkHitSplit.reflectPrefix
            IsingDiagonalWalkHitSplit.steps
          rw [List.take_append_of_le_length (by simpa using hlBefore.le)]
    have hsourceRunL := choiceExecValid_run_boxInt_eq_endpoint R p
      (w.1.1.take l) hsourceValidL
    have hmirrorRunL := choiceExecValid_run_boxInt_eq_endpoint R p'
      (w'.1.take l) hmirrorValidL
    have hmxL := congrArg Prod.fst hmirrorRunL
    change ((isingLeapfrogChoiceRun R p' (w'.1.take l)).1.1 : Int) =
      (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p')
        (isingLeapfrogChoiceSteps (w'.1.take l))).1 at hmxL
    rw [hmirror, hmirrorStepsL,
      reflectPrefix_endpoint_take_fst_of_le_before split l hlBefore.le,
      hsourceStepsL] at hmxL
    have hsxL := congrArg Prod.fst hsourceRunL
    change ((isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 : Int) =
      (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceSteps (w.1.1.take l))).1 at hsxL
    have hmirrorNot := hmirrorMinimal l hl
    have hmirrorLtR : ((isingLeapfrogChoiceRun R p'
        (w'.1.take l)).1.1 : Int) < R := by
      have hle : (isingLeapfrogChoiceRun R p' (w'.1.take l)).1.1 <= R := by
        omega
      have hne : (isingLeapfrogChoiceRun R p' (w'.1.take l)).1.1 ≠ R := by
        intro heq
        apply hmirrorNot
        unfold isingLeapfrogBoxBoundary
        right; left
        omega
      exact_mod_cast (lt_of_le_of_ne hle hne)
    have hsourceLtL := (firstHitSplit_firstHit hsplit).endpoint_take_fst_lt
      split hvalid (by omega : (isingLeapfrogBoxInt p).1 < (level : Int))
      l hlBefore
    rw [hmxL, ← hsxL] at hmirrorLtR
    rw [hsourceBeforeStepsL, ← hsxL] at hsourceLtL
    exact ⟨by omega, hsourceLtL⟩
  unfold isingLeapfrogBoxBoundary at hmirrorBoundary
  rcases hmirrorBoundary with hx0 | hxR | hy0 | hyR
  · exfalso
    have hmirrorZero : ((isingLeapfrogChoiceRun R p'
        (w'.1.take j)).1.1 : Int) = 0 := by exact_mod_cast hx0
    have hsourceNonneg : 0 <= ((isingLeapfrogChoiceRun R p
        (w.1.1.take j)).1.1 : Int) := by positivity
    rw [hmx, ← hsx] at hmirrorZero
    omega
  · refine ⟨split, j, hsplit, hj, ?_, ?_, hsourceBetween, ?_, hsourceValid⟩
    · have hxRNat : (isingLeapfrogChoiceRun R p' (w'.1.take j)).1.1 = R := by
        omega
      simpa [w'] using hxRNat
    · have hmirrorR : ((isingLeapfrogChoiceRun R p'
          (w'.1.take j)).1.1 : Int) = R := by
        have hxRNat : (isingLeapfrogChoiceRun R p' (w'.1.take j)).1.1 = R := by
          omega
        exact_mod_cast hxRNat
      rw [hmx, ← hsx] at hmirrorR
      omega
    · intro l hl
      simpa [w'] using hmirrorMinimal l hl
  · exfalso
    have hmirrorY : ((isingLeapfrogChoiceRun R p'
        (w'.1.take j)).2.1 : Int) = 0 := by exact_mod_cast hy0
    have hsourceY : ((isingLeapfrogChoiceRun R p
        (w.1.1.take j)).2.1 : Int) = 0 := by
      rw [hmy, ← hsy] at hmirrorY
      exact hmirrorY
    have hsourceBoundary : isingLeapfrogBoxBoundary R
        (isingLeapfrogChoiceRun R p (w.1.1.take j)) := by
      unfold isingLeapfrogBoxBoundary
      right; right; left
      exact_mod_cast hsourceY
    exact (hsourceValid j (by
      rw [List.length_take]
      have hw : w.1.1.length = t := w.1.2
      omega)) (by
      simpa [List.take_take, Nat.min_eq_left hj.le] using hsourceBoundary)
  · exfalso
    have hmirrorYNat : (isingLeapfrogChoiceRun R p'
        (w'.1.take j)).2.1 = R := by omega
    have hmirrorY : ((isingLeapfrogChoiceRun R p'
        (w'.1.take j)).2.1 : Int) = R := by exact_mod_cast hmirrorYNat
    have hsourceY : ((isingLeapfrogChoiceRun R p
        (w.1.1.take j)).2.1 : Int) = R := by
      rw [hmy, ← hsy] at hmirrorY
      exact hmirrorY
    have hsourceYNat : (isingLeapfrogChoiceRun R p
        (w.1.1.take j)).2.1 = R := by exact_mod_cast hsourceY
    have hsourceBoundary : isingLeapfrogBoxBoundary R
        (isingLeapfrogChoiceRun R p (w.1.1.take j)) := by
      unfold isingLeapfrogBoxBoundary
      right; right; right
      omega
    exact (hsourceValid j (by
      rw [List.length_take]
      have hw : w.1.1.length = t := w.1.2
      omega)) (by
      simpa [List.take_take, Nat.min_eq_left hj.le] using hsourceBoundary)




theorem mirrorOnly_ordered_boundary_marks
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hq : isingLeapfrogBoxBoundary R q)
    (w : IsingMirrorOnlySourceOutputAtFamily R t p p' q (level : Int)) :
    exists (split : IsingDiagonalWalkHitSplit (isingLeapfrogBoxInt p)
        (level : Int)) (j k : Nat),
      isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p) (level : Int)
        (isingLeapfrogChoiceSteps w.1.1) = some split /\
      j < k /\ k <= t /\
      (isingLeapfrogChoiceRun R p'
        ((isingLeapfrogCouplingChoiceTransform t (isingLeapfrogBoxInt p)
          (level : Int) w.1).1.take j)).1.1 = R /\
      ((isingLeapfrogChoiceRun R p (w.1.1.take j)).1.1 : Int) =
        2 * (level : Int) - R /\
      (forall l, l < j ->
        2 * (level : Int) - R <
            ((isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 : Int) /\
          ((isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 : Int) < level) /\
      (forall l, l < j -> ¬ isingLeapfrogBoxBoundary R
        (isingLeapfrogChoiceRun R p'
          ((isingLeapfrogCouplingChoiceTransform t (isingLeapfrogBoxInt p)
            (level : Int) w.1).1.take l))) /\
      isingLeapfrogChoiceRun R p (w.1.1.take k) = q /\
      (forall l, l < k -> ¬ isingLeapfrogBoxBoundary R
        (isingLeapfrogChoiceRun R p (w.1.1.take l))) := by
  rcases mirrorOnly_firstBoundary_right R level t p p' q hstart hmirror w with
    ⟨split, j, hsplit, hj, hjRight, hjSource, hjBetween, hjMinimal,
      hsourceValid⟩
  rcases choiceRun_boundary_output_data_endpointFailure R t p q hq w.1
    w.2.2.2 with ⟨k, hkT, hkOutput, hkMinimal⟩
  have hjk : j < k := by
    by_contra hnot
    have hkj : k <= j := by omega
    have hbeforeT : split.before.length <= t := by
      have hlen := congrArg List.length (firstHitSplit_steps hsplit)
      simp [IsingDiagonalWalkHitSplit.steps, isingLeapfrogChoiceSteps,
        w.1.2] at hlen
      omega
    have hsourceNotBoundary := hsourceValid k (by
      rw [List.length_take]
      rw [w.1.2]
      omega)
    apply hsourceNotBoundary
    have hq' := hq
    rw [← hkOutput] at hq'
    simpa [List.take_take, Nat.min_eq_left (hkj.trans hj.le)] using hq'
  exact ⟨split, j, k, hsplit, hjk, hkT, hjRight, hjSource, hjBetween,
    hjMinimal,
    hkOutput, hkMinimal⟩

private theorem choiceRun_take_coordinates_eq_lineFree
    (R t k : Nat) (p : IsingLeapfrogBox R)
    (w : IsingLeapfrogChoiceStringFamily t)
    (hkT : k <= t)
    (hminimal : forall l, l < k -> ¬ isingLeapfrogBoxBoundary R
      (isingLeapfrogChoiceRun R p (w.1.take l)))
    (l : Nat) (hl : l <= k) :
    ((isingLeapfrogChoiceRun R p (w.1.take l)).1.1 : Int) =
        lineFreeEndpoint (isingLeapfrogBoxInt p).1
          ((w.1.take l).map Prod.fst) /\
      ((isingLeapfrogChoiceRun R p (w.1.take l)).2.1 : Int) =
        lineFreeEndpoint (isingLeapfrogBoxInt p).2
          ((w.1.take l).map Prod.snd) := by
  have hvalid : IsingLeapfrogChoiceExecValid R p (w.1.take l) := by
    intro r hr
    have hrl : r < l := by
      rw [List.length_take, w.2] at hr
      omega
    have hmain := hminimal r (hrl.trans_le hl)
    simpa [List.take_take, Nat.min_eq_left hrl.le] using hmain
  have hrun := choiceExecValid_run_boxInt_eq_endpoint R p (w.1.take l) hvalid
  constructor
  · have hx := congrArg Prod.fst hrun
    change ((isingLeapfrogChoiceRun R p (w.1.take l)).1.1 : Int) =
      (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceSteps (w.1.take l))).1 at hx
    rw [← lineFreeEndpoint_choiceHorizontal_full] at hx
    exact hx
  · have hy := congrArg Prod.snd hrun
    change ((isingLeapfrogChoiceRun R p (w.1.take l)).2.1 : Int) =
      (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceSteps (w.1.take l))).2 at hy
    rw [← lineFreeEndpoint_choiceVertical_full] at hy
    exact hy

private def orderedFarEndpointValue
    (m n t : Nat) (start target : IsingLineBox n)
    (markX targetX : Int) :
    IsingOrderedFarEndpointFamily m n t start target markX targetX ->
      IsingLeapfrogChoiceStringFamily t := fun z => by
  let xs := z.2.2.1.1 ++ z.2.2.2.2.1.1 ++ z.2.2.2.2.2.1.map Prod.fst
  let ys := z.2.2.2.1.1 ++ z.2.2.2.2.2.1.map Prod.snd
  refine ⟨xs.zip ys, ?_⟩
  have hx : xs.length = t := by
    dsimp [xs]
    rw [List.length_append, List.length_append, List.length_map,
      z.2.2.1.2.1, z.2.2.2.2.1.2.1, z.2.2.2.2.2.2]
    omega
  have hy : ys.length = t := by
    dsimp [ys]
    rw [List.length_append, List.length_map,
      z.2.2.2.1.2.1, z.2.2.2.2.2.2]
    omega
  rw [List.length_zip, hx, hy, min_self]

def IsingOrderedFarHorizontalEndpointFamily
    (m R t : Nat) (mark target : IsingLineBox R)
    (startY targetY : Int) :=
  Sigma fun k : Fin (t + 1) =>
    Sigma fun j : Fin k =>
      IsingLineFarFirstBoundaryFamily m j ×
        IsingLineFirstEndpointFamily R (k - j) mark target ×
        VerticalChoicePathFamily k startY targetY ×
        {tail : List (Bool × Bool) // tail.length = t - k}

private def orderedFarHorizontalEndpointValue
    (m R t : Nat) (mark target : IsingLineBox R)
    (startY targetY : Int) :
    IsingOrderedFarHorizontalEndpointFamily m R t mark target startY targetY ->
      IsingLeapfrogChoiceStringFamily t := fun z => by
  let xs := z.2.2.1.1 ++ z.2.2.2.1.1 ++ z.2.2.2.2.2.1.map Prod.fst
  let ys := z.2.2.2.2.1.1 ++ z.2.2.2.2.2.1.map Prod.snd
  refine ⟨xs.zip ys, ?_⟩
  have hx : xs.length = t := by
    dsimp [xs]
    rw [List.length_append, List.length_append, List.length_map,
      z.2.2.1.2.1, z.2.2.2.1.2.1, z.2.2.2.2.2.2]
    omega
  have hy : ys.length = t := by
    dsimp [ys]
    rw [List.length_append, List.length_map,
      z.2.2.2.2.1.2.1, z.2.2.2.2.2.2]
    omega
  rw [List.length_zip, hx, hy, min_self]

private theorem exists_mirrorOnlyOrderedCover
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hlevelR : level <= R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hq : isingLeapfrogBoxBoundary R q)
    (w : IsingMirrorOnlySourceOutputAtFamily R t p p' q (level : Int)) :
    exists z : IsingOrderedFarEndpointFamily (R - level) R t p.2 q.2
        (2 * (level : Int) - R) (q.1 : Int),
      orderedFarEndpointValue (R - level) R t p.2 q.2
        (2 * (level : Int) - R) (q.1 : Int) z = w.1 /\
      forall hhalf : R <= 2 * level,
        exists zh : IsingOrderedFarHorizontalEndpointFamily (R - level) R t
            ⟨2 * level - R, by omega⟩ q.1
            (p.2.1 : Int) (q.2.1 : Int),
          orderedFarHorizontalEndpointValue (R - level) R t
            ⟨2 * level - R, by omega⟩ q.1
            (p.2.1 : Int) (q.2.1 : Int) zh = w.1 := by
  rcases mirrorOnly_ordered_boundary_marks R level t p p' q hstart hmirror hq w with
    ⟨split, j, k, hsplit, hjk, hkT, hjRight, hjSource, hjBetween,
      hjMirrorMinimal, hkOutput, hkMinimal⟩
  have hlevelLtR : level < R := by
    have hx := congrArg Prod.fst hmirror
    change (p'.1.1 : Int) = 2 * (level : Int) - (p.1.1 : Int) at hx
    have hp'Le : p'.1.1 <= R := by omega
    have hpX : (p.1.1 : Int) + 1 = level := hstart
    exact_mod_cast (show level < R by omega)
  have hcoord (l : Nat) (hl : l <= k) :=
    choiceRun_take_coordinates_eq_lineFree R t k p w.1 hkT hkMinimal l hl
  let xbits := (w.1.1.take j).map Prod.fst
  let ybits := (w.1.1.take k).map Prod.snd
  let midbits := ((w.1.1.drop j).take (k - j)).map Prod.fst
  let tail := w.1.1.drop k
  have hxlen : xbits.length = j := by
    dsimp [xbits]
    simp [w.1.2]
    omega
  have hylen : ybits.length = k := by
    dsimp [ybits]
    simp [w.1.2, hkT]
  have hmidlen : midbits.length = k - j := by
    dsimp [midbits]
    rw [List.length_map, List.length_take, List.length_drop, w.1.2]
    omega
  have htailLen : tail.length = t - k := by
    dsimp [tail]
    rw [List.length_drop, w.1.2]
  have hxTake (l : Nat) (hl : l <= j) :
      xbits.take l = (w.1.1.take l).map Prod.fst := by
    dsimp [xbits]
    rw [← List.map_take, List.take_take, Nat.min_eq_left hl]
  have hyTake (l : Nat) (hl : l <= k) :
      ybits.take l = (w.1.1.take l).map Prod.snd := by
    dsimp [ybits]
    rw [← List.map_take, List.take_take, Nat.min_eq_left hl]
  have hlineTranslate (l : Nat) (hl : l <= j) :
      lineFreeEndpoint (((R - level) - 1 : Nat) : Int) (xbits.take l) =
        lineFreeEndpoint (isingLeapfrogBoxInt p).1
            ((w.1.1.take l).map Prod.fst) +
          ((R : Int) - 2 * level) := by
    have htr := lineFreeEndpoint_translate (xbits.take l)
      (isingLeapfrogBoxInt p).1 (((R - level) - 1 : Nat) : Int)
    rw [hxTake l hl] at htr
    rw [hxTake l hl]
    rw [htr]
    have hcastR : ((R - level : Nat) : Int) = (R : Int) - level := by
      rw [Nat.cast_sub hlevelR]
    have hcastPos : ((((R - level) - 1 : Nat) : Int)) =
        (R : Int) - level - 1 := by
      rw [Nat.cast_sub (show 1 <= R - level by omega), hcastR]
      norm_num
    rw [hcastPos]
    omega
  have hxInterior (l : Nat) (hl : l < j) :
      0 < lineFreeEndpoint (((R - level) - 1 : Nat) : Int)
          (xbits.take l) /\
        lineFreeEndpoint (((R - level) - 1 : Nat) : Int)
          (xbits.take l) < (R - level : Nat) := by
    have hc := hcoord l (hl.le.trans hjk.le)
    have hb := hjBetween l hl
    have htr := hlineTranslate l hl.le
    rw [← hc.1] at htr
    have hcast : ((R - level : Nat) : Int) = (R : Int) - level := by
      rw [Nat.cast_sub hlevelR]
    exact ⟨by omega, by rw [hcast]; omega⟩
  have hxFree (l : Nat) (hl : l <= j) :
      ((isingLineChoiceRun (R - level)
        ⟨(R - level) - 1, by omega⟩ (xbits.take l)).1 : Int) =
        lineFreeEndpoint (((R - level) - 1 : Nat) : Int)
          (xbits.take l) := by
    apply lineChoiceRun_val_eq_lineFreeEndpoint
    intro r hr
    have hrl : r < l := by
      rw [List.length_take, hxlen] at hr
      omega
    have hi := hxInterior r (hrl.trans_le hl)
    have htake : (xbits.take l).take r = xbits.take r := by
      simp [List.take_take, Nat.min_eq_left hrl.le]
    rw [htake]
    exact ⟨ne_of_gt hi.1, ne_of_lt hi.2⟩
  have hxEnd : lineFreeEndpoint (((R - level) - 1 : Nat) : Int) xbits = 0 := by
    have htr := hlineTranslate j le_rfl
    have htakeAll : xbits.take j = xbits := by
      simpa [hxlen] using List.take_all xbits
    rw [htakeAll] at htr
    have hc := (hcoord j hjk.le).1
    rw [← hc, hjSource] at htr
    linarith
  let xfar : IsingLineFarFirstBoundaryFamily (R - level) j := ⟨xbits,
    hxlen, by
      apply Fin.ext
      have hrun := hxFree j le_rfl
      have htakeAll : xbits.take j = xbits := by
        simpa [hxlen] using List.take_all xbits
      rw [htakeAll] at hrun
      change (isingLineChoiceRun (R - level)
        ⟨(R - level) - 1, by omega⟩ xbits).1 = 0
      exact_mod_cast hrun.trans hxEnd,
    by
      intro l hl
      have hi := hxInterior l hl
      have hrun := hxFree l hl.le
      intro hb
      unfold isingLineBoxBoundary at hb
      rcases hb with hb | hb <;> exact (by omega)⟩
  have hyInterior (l : Nat) (hl : l < k) :
      lineFreeEndpoint (isingLeapfrogBoxInt p).2 (ybits.take l) ≠ 0 /\
        lineFreeEndpoint (isingLeapfrogBoxInt p).2 (ybits.take l) ≠ R := by
    have hc := hcoord l hl.le
    have hnot := hkMinimal l hl
    rw [hyTake l hl.le, ← hc.2]
    constructor
    · intro hzero
      apply hnot
      unfold isingLeapfrogBoxBoundary
      right; right; left
      exact_mod_cast hzero
    · intro hright
      apply hnot
      unfold isingLeapfrogBoxBoundary
      right; right; right
      omega
  have hyFree (l : Nat) (hl : l <= k) :
      ((isingLineChoiceRun R p.2 (ybits.take l)).1 : Int) =
        lineFreeEndpoint (isingLeapfrogBoxInt p).2 (ybits.take l) := by
    apply lineChoiceRun_val_eq_lineFreeEndpoint
    intro r hr
    have hrl : r < l := by
      rw [List.length_take, hylen] at hr
      omega
    have hi := hyInterior r (hrl.trans_le hl)
    have htake : (ybits.take l).take r = ybits.take r := by
      simp [List.take_take, Nat.min_eq_left hrl.le]
    simpa [htake] using hi
  have hyEnd : lineFreeEndpoint (isingLeapfrogBoxInt p).2 ybits = q.2.1 := by
    have hc := (hcoord k le_rfl).2
    rw [hkOutput] at hc
    have htakeAll : ybits.take k = ybits := by
      simpa [hylen] using List.take_all ybits
    have hyEq := hyTake k le_rfl
    rw [htakeAll] at hyEq
    rw [← hyEq] at hc
    exact hc.symm
  let yfirst : IsingLineFirstEndpointFamily R k p.2 q.2 := ⟨ybits,
    hylen, by
      apply Fin.ext
      have hrun := hyFree k le_rfl
      have htakeAll : ybits.take k = ybits := by
        simpa [hylen] using List.take_all ybits
      rw [htakeAll] at hrun
      change (isingLineChoiceRun R p.2 ybits).1 = q.2.1
      exact_mod_cast hrun.trans hyEnd,
    by
      intro l hl
      have hi := hyInterior l hl
      have hrun := hyFree l hl.le
      intro hb
      unfold isingLineBoxBoundary at hb
      rcases hb with hb | hb <;> exact (by omega)⟩
  have hprefixDecomp :
      (w.1.1.take j).map Prod.fst ++ midbits =
        (w.1.1.take k).map Prod.fst := by
    dsimp [midbits]
    rw [← List.map_append, ← List.take_add]
    congr 2
    omega
  have hmidEnd : lineFreeEndpoint (2 * (level : Int) - R) midbits = q.1 := by
    have hjc := (hcoord j hjk.le).1
    have hkc := (hcoord k le_rfl).1
    rw [hjSource] at hjc
    rw [hkOutput] at hkc
    calc
      lineFreeEndpoint (2 * (level : Int) - R) midbits =
          lineFreeEndpoint
            (lineFreeEndpoint (isingLeapfrogBoxInt p).1
              ((w.1.1.take j).map Prod.fst)) midbits := by rw [← hjc]
      _ = lineFreeEndpoint (isingLeapfrogBoxInt p).1
          ((w.1.1.take j).map Prod.fst ++ midbits) :=
        (lineFreeEndpoint_append_endpointFailure ..).symm
      _ = _ := by rw [hprefixDecomp, ← hkc]
  let xmid : VerticalChoicePathFamily (k - j)
      (2 * (level : Int) - R) (q.1 : Int) := ⟨midbits, hmidlen, hmidEnd⟩
  let z : IsingOrderedFarEndpointFamily (R - level) R t p.2 q.2
      (2 * (level : Int) - R) (q.1 : Int) :=
    ⟨⟨k, by omega⟩, ⟨⟨j, hjk⟩, xfar, yfirst, xmid, ⟨tail, htailLen⟩⟩⟩
  have hxFull :
      (w.1.1.take j).map Prod.fst ++
          ((w.1.1.drop j).take (k - j)).map Prod.fst ++
          (w.1.1.drop k).map Prod.fst = w.1.1.map Prod.fst := by
    rw [hprefixDecomp]
    rw [← List.map_append, List.take_append_drop]
  have hyFull :
      (w.1.1.take k).map Prod.snd ++ (w.1.1.drop k).map Prod.snd =
        w.1.1.map Prod.snd := by
    rw [← List.map_append, List.take_append_drop]
  refine ⟨z, ?_, ?_⟩
  · apply Subtype.ext
    dsimp [orderedFarEndpointValue, z, xfar, yfirst, xmid, tail,
      xbits, ybits, midbits]
    rw [hxFull, hyFull, prodBits_zip_self_endpointFailure]
  · intro hhalf
    let mark : IsingLineBox R := ⟨2 * level - R, by omega⟩
    have hmarkCast : (mark.1 : Int) = 2 * (level : Int) - R := by
      dsimp [mark]
      rw [Nat.cast_sub hhalf]
      push_cast
      ring
    have hmidTake (l : Nat) (hl : l <= k - j) :
        midbits.take l = ((w.1.1.drop j).take l).map Prod.fst := by
      dsimp [midbits]
      rw [← List.map_take, List.take_take, Nat.min_eq_left hl]
    have hprefixAt (l : Nat) (hl : l <= k - j) :
        (w.1.1.take j).map Prod.fst ++
            ((w.1.1.drop j).take l).map Prod.fst =
          (w.1.1.take (j + l)).map Prod.fst := by
      rw [← List.map_append, ← List.take_add]
    have hsegment (l : Nat) (hl : l <= k - j) :
        lineFreeEndpoint (mark.1 : Int) (midbits.take l) =
          lineFreeEndpoint (isingLeapfrogBoxInt p).1
            ((w.1.1.take (j + l)).map Prod.fst) := by
      have hjc := (hcoord j hjk.le).1
      rw [hjSource] at hjc
      calc
        lineFreeEndpoint (mark.1 : Int) (midbits.take l) =
            lineFreeEndpoint
              (lineFreeEndpoint (isingLeapfrogBoxInt p).1
                ((w.1.1.take j).map Prod.fst)) (midbits.take l) := by
          rw [hmarkCast, hjc]
        _ = lineFreeEndpoint (isingLeapfrogBoxInt p).1
            ((w.1.1.take j).map Prod.fst ++ midbits.take l) :=
          (lineFreeEndpoint_append_endpointFailure ..).symm
        _ = _ := by rw [hmidTake l hl, hprefixAt l hl]
    have hmidInterior (l : Nat) (hl : l < k - j) :
        lineFreeEndpoint (mark.1 : Int) (midbits.take l) ≠ 0 /\
          lineFreeEndpoint (mark.1 : Int) (midbits.take l) ≠ R := by
      have hjl : j + l < k := by omega
      have hc := hcoord (j + l) hjl.le
      have hnot := hkMinimal (j + l) hjl
      rw [hsegment l hl.le, ← hc.1]
      constructor
      · intro hzero
        apply hnot
        unfold isingLeapfrogBoxBoundary
        left
        exact_mod_cast hzero
      · intro hright
        apply hnot
        unfold isingLeapfrogBoxBoundary
        right; left
        omega
    have hmidFree (l : Nat) (hl : l <= k - j) :
        ((isingLineChoiceRun R mark (midbits.take l)).1 : Int) =
          lineFreeEndpoint (mark.1 : Int) (midbits.take l) := by
      apply lineChoiceRun_val_eq_lineFreeEndpoint
      intro r hr
      have hrl : r < l := by
        rw [List.length_take, hmidlen] at hr
        omega
      have hi := hmidInterior r (hrl.trans_le hl)
      have htake : (midbits.take l).take r = midbits.take r := by
        simp [List.take_take, Nat.min_eq_left hrl.le]
      simpa [htake] using hi
    let xfirst : IsingLineFirstEndpointFamily R (k - j) mark q.1 :=
      ⟨midbits, hmidlen, by
        apply Fin.ext
        have hrun := hmidFree (k - j) le_rfl
        have htakeAll : midbits.take (k - j) = midbits := by
          simpa [hmidlen] using List.take_all midbits
        rw [htakeAll] at hrun
        change (isingLineChoiceRun R mark midbits).1 = q.1.1
        have hint : ((isingLineChoiceRun R mark midbits).1 : Int) =
            (q.1.1 : Int) :=
          hrun.trans (by simpa [hmarkCast] using hmidEnd)
        exact Int.ofNat_inj.mp hint,
      by
        intro l hl
        have hi := hmidInterior l hl
        have hrun := hmidFree l hl.le
        intro hb
        unfold isingLineBoxBoundary at hb
        rcases hb with hb | hb <;> exact (by omega)⟩
    let yfree : VerticalChoicePathFamily k (p.2.1 : Int) (q.2.1 : Int) :=
      ⟨ybits, hylen, hyEnd⟩
    let zh : IsingOrderedFarHorizontalEndpointFamily (R - level) R t
        mark q.1 (p.2.1 : Int) (q.2.1 : Int) :=
      ⟨⟨k, by omega⟩, ⟨⟨j, hjk⟩, xfar, xfirst, yfree,
        ⟨tail, htailLen⟩⟩⟩
    refine ⟨zh, ?_⟩
    apply Subtype.ext
    dsimp [orderedFarHorizontalEndpointValue, zh, xfar, xfirst, yfree,
      tail, xbits, ybits, midbits]
    rw [hxFull, hyFull, prodBits_zip_self_endpointFailure]

private noncomputable def mirrorOnlyOrderedCover
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hlevelR : level <= R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hq : isingLeapfrogBoxBoundary R q) :
    IsingMirrorOnlySourceOutputAtFamily R t p p' q (level : Int) ->
      IsingOrderedFarEndpointFamily (R - level) R t p.2 q.2
        (2 * (level : Int) - R) (q.1 : Int) := fun w =>
  Classical.choose
    (exists_mirrorOnlyOrderedCover R level t p p' q hlevelR hstart hmirror hq w)

private theorem mirrorOnlyOrderedCover_value
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hlevelR : level <= R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hq : isingLeapfrogBoxBoundary R q)
    (w : IsingMirrorOnlySourceOutputAtFamily R t p p' q (level : Int)) :
    orderedFarEndpointValue (R - level) R t p.2 q.2
        (2 * (level : Int) - R) (q.1 : Int)
        (mirrorOnlyOrderedCover R level t p p' q hlevelR hstart hmirror hq w) =
      w.1 := by
  exact (Classical.choose_spec
    (exists_mirrorOnlyOrderedCover R level t p p' q hlevelR hstart hmirror hq w)).1

private theorem mirrorOnlyOrderedCover_injective
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hlevelR : level <= R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hq : isingLeapfrogBoxBoundary R q) :
    Function.Injective
      (mirrorOnlyOrderedCover R level t p p' q hlevelR hstart hmirror hq) := by
  intro a b hab
  apply Subtype.ext
  rw [← mirrorOnlyOrderedCover_value R level t p p' q hlevelR hstart hmirror hq a,
    ← mirrorOnlyOrderedCover_value R level t p p' q hlevelR hstart hmirror hq b,
    hab]

theorem natCard_mirrorOnlySourceOutputAt_le_orderedFarEndpoint
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hlevelR : level <= R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hq : isingLeapfrogBoxBoundary R q) :
    Nat.card (IsingMirrorOnlySourceOutputAtFamily
        R t p p' q (level : Int)) <=
      Nat.card (IsingOrderedFarEndpointFamily (R - level) R t p.2 q.2
        (2 * (level : Int) - R) (q.1 : Int)) :=
  Nat.card_le_card_of_injective
    (mirrorOnlyOrderedCover R level t p p' q hlevelR hstart hmirror hq)
    (mirrorOnlyOrderedCover_injective R level t p p' q
      hlevelR hstart hmirror hq)

theorem mirrorOnlySourceOutputAt_vertical_diffusive_weight_le
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hright : level + rho <= R)
    (hqVertical : q.2.1 = 0 ∨ q.2.1 = R) :
    Nat.card (IsingMirrorOnlySourceOutputAtFamily
        R (rho * rho) p p' q (level : Int)) /
        (4 : Real) ^ (rho * rho) <=
      7488 / (rho : Real) ^ 2 := by
  have hlevelR : level <= R := by omega
  have hq : isingLeapfrogBoxBoundary R q := by
    unfold isingLeapfrogBoxBoundary
    rcases hqVertical with hq | hq
    · right; right; left; exact hq
    · right; right; right; omega
  have hcard := natCard_mirrorOnlySourceOutputAt_le_orderedFarEndpoint
    R level (rho * rho) p p' q hlevelR hstart hmirror hq
  have hden : 0 <= (4 : Real) ^ (rho * rho) := by positivity
  calc
    Nat.card (IsingMirrorOnlySourceOutputAtFamily
        R (rho * rho) p p' q (level : Int)) /
        (4 : Real) ^ (rho * rho) <=
      Nat.card (IsingOrderedFarEndpointFamily (R - level) R (rho * rho)
        p.2 q.2 (2 * (level : Int) - R) (q.1 : Int)) /
        (4 : Real) ^ (rho * rho) := by
      apply div_le_div_of_nonneg_right _ hden
      exact_mod_cast hcard
    _ <= 7488 / (rho : Real) ^ 2 := by
      apply orderedFarEndpoint_diffusive_weight_le rho (R - level) R p.2 q.2
        (2 * (level : Int) - R) (q.1 : Int) hρ (by omega)
      unfold isingLineBoxBoundary
      exact hqVertical

noncomputable instance isingOrderedFarHorizontalEndpointFamily_finite
    (m R t : Nat) (mark target : IsingLineBox R)
    (startY targetY : Int) :
    Finite (IsingOrderedFarHorizontalEndpointFamily
      m R t mark target startY targetY) := by
  letI (k : Fin (t + 1)) : Fintype (Fin k) := inferInstance
  letI (k : Fin (t + 1)) (j : Fin k) :
      Fintype (IsingLineFarFirstBoundaryFamily m j) := Fintype.ofFinite _
  letI (k : Fin (t + 1)) (j : Fin k) :
      Fintype (IsingLineFirstEndpointFamily R (k - j) mark target) :=
    Fintype.ofFinite _
  letI (k : Fin (t + 1)) :
      Fintype (VerticalChoicePathFamily k startY targetY) := Fintype.ofFinite _
  letI (k : Fin (t + 1)) :
      Fintype {tail : List (Bool × Bool) // tail.length = t - k} :=
    (List.finite_length_eq (Bool × Bool) (t - k)).fintype
  unfold IsingOrderedFarHorizontalEndpointFamily
  infer_instance

theorem orderedFarHorizontalEndpoint_weight_eq_sum
    (m R t : Nat) (mark target : IsingLineBox R)
    (startY targetY : Int) :
    Nat.card (IsingOrderedFarHorizontalEndpointFamily
        m R t mark target startY targetY) / (4 : Real) ^ t =
      ∑ k : Fin (t + 1), ∑ j : Fin k,
        (Nat.card (IsingLineFarFirstBoundaryFamily m j) /
          (2 : Real) ^ (j : Nat)) *
        (Nat.card (IsingLineFirstEndpointFamily R (k - j) mark target) /
          (2 : Real) ^ ((k : Nat) - (j : Nat))) *
        (Nat.card (VerticalChoicePathFamily k startY targetY) /
          (2 : Real) ^ (k : Nat)) := by
  letI (k : Fin (t + 1)) : Fintype (Fin k) := inferInstance
  letI (k : Fin (t + 1)) (j : Fin k) :
      Fintype (IsingLineFarFirstBoundaryFamily m j) := Fintype.ofFinite _
  letI (k : Fin (t + 1)) (j : Fin k) :
      Fintype (IsingLineFirstEndpointFamily R (k - j) mark target) :=
    Fintype.ofFinite _
  letI (k : Fin (t + 1)) :
      Fintype (VerticalChoicePathFamily k startY targetY) := Fintype.ofFinite _
  letI (k : Fin (t + 1)) :
      Fintype {tail : List (Bool × Bool) // tail.length = t - k} :=
    (List.finite_length_eq (Bool × Bool) (t - k)).fintype
  have hcard : Nat.card (IsingOrderedFarHorizontalEndpointFamily
      m R t mark target startY targetY) =
      ∑ k : Fin (t + 1), ∑ j : Fin k,
        Nat.card (IsingLineFarFirstBoundaryFamily m j) *
        Nat.card (IsingLineFirstEndpointFamily R (k - j) mark target) *
        Nat.card (VerticalChoicePathFamily k startY targetY) *
        4 ^ (t - (k : Nat)) := by
    unfold IsingOrderedFarHorizontalEndpointFamily
    rw [Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.card_prod, Nat.card_prod, Nat.card_prod]
    have htail : Nat.card
        {tail : List (Bool × Bool) // tail.length = t - (k : Nat)} =
        4 ^ (t - (k : Nat)) := by
      change Nat.card (List.Vector (Bool × Bool) (t - (k : Nat))) =
        4 ^ (t - (k : Nat))
      rw [Nat.card_congr
          (Equiv.vectorEquivFin (Bool × Bool) (t - (k : Nat))),
        Nat.card_eq_fintype_card, Fintype.card_fun]
      norm_num
    rw [htail]
    ring
  rw [hcard]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : (j : Nat) <= (k : Nat) := Nat.le_of_lt j.isLt
  have hfourT : (4 : Real) ^ t =
      (4 : Real) ^ (k : Nat) * (4 : Real) ^ (t - (k : Nat)) := by
    calc
      _ = (4 : Real) ^ ((k : Nat) + (t - (k : Nat))) := by
        congr 1
        exact (Nat.add_sub_of_le (Nat.le_of_lt_succ k.isLt)).symm
      _ = _ := pow_add _ _ _
  have htwoK : (4 : Real) ^ (k : Nat) =
      (2 : Real) ^ (k : Nat) * (2 : Real) ^ (k : Nat) := by
    rw [show (4 : Real) = 2 * 2 by norm_num, mul_pow]
  have hsplitK : (2 : Real) ^ (k : Nat) =
      (2 : Real) ^ (j : Nat) *
        (2 : Real) ^ ((k : Nat) - (j : Nat)) := by
    calc
      _ = (2 : Real) ^ ((j : Nat) + ((k : Nat) - (j : Nat))) := by
        congr 1
        omega
      _ = _ := pow_add _ _ _
  rw [hfourT, htwoK, hsplitK]
  field_simp

private def LineFirstEndpointExtension
    (n N : Nat) (start target : IsingLineBox n) :=
  Sigma fun r : Fin (N + 1) =>
    IsingLineFirstEndpointFamily n r start target ×
      {tail : List Bool // tail.length = N - r}

private def lineFirstEndpointExtend
    (n N : Nat) (start target : IsingLineBox n) :
    LineFirstEndpointExtension n N start target ->
      {bs : List Bool // bs.length = N} := fun z =>
  ⟨z.2.1.1 ++ z.2.2.1, by
    rw [List.length_append, z.2.1.2.1, z.2.2.2]
    omega⟩

private theorem lineFirstEndpointExtend_injective
    (n N : Nat) (start target : IsingLineBox n)
    (htarget : isingLineBoxBoundary n target) :
    Function.Injective (lineFirstEndpointExtend n N start target) := by
  rintro ⟨ar, ap, atail⟩ ⟨br, bp, btail⟩ hab
  have hfull : ap.1 ++ atail.1 = bp.1 ++ btail.1 :=
    congrArg Subtype.val hab
  have hr : (ar : Nat) = br := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hbavoid := bp.2.2.2 (ar : Nat) hlt
      apply hbavoid
      have ht := congrArg (fun z : List Bool => z.take (ar : Nat)) hfull
      have haTake : (ap.1 ++ atail.1).take (ar : Nat) = ap.1 := by
        simpa [ap.2.1] using (List.take_left (l₁ := ap.1) (l₂ := atail.1))
      have hbTake : (bp.1 ++ btail.1).take (ar : Nat) =
          bp.1.take (ar : Nat) := by
        apply List.take_append_of_le_length
        rw [bp.2.1]
        omega
      change (ap.1 ++ atail.1).take (ar : Nat) =
        (bp.1 ++ btail.1).take (ar : Nat) at ht
      rw [haTake, hbTake] at ht
      rw [← ht, ap.2.2.1]
      exact htarget
    · have haavoid := ap.2.2.2 (br : Nat) hgt
      apply haavoid
      have ht := congrArg (fun z : List Bool => z.take (br : Nat)) hfull
      have haTake : (ap.1 ++ atail.1).take (br : Nat) =
          ap.1.take (br : Nat) := by
        apply List.take_append_of_le_length
        rw [ap.2.1]
        omega
      have hbTake : (bp.1 ++ btail.1).take (br : Nat) = bp.1 := by
        simpa [bp.2.1] using (List.take_left (l₁ := bp.1) (l₂ := btail.1))
      change (ap.1 ++ atail.1).take (br : Nat) =
        (bp.1 ++ btail.1).take (br : Nat) at ht
      rw [haTake, hbTake] at ht
      rw [ht, bp.2.2.1]
      exact htarget
  have hrSubtype : ar = br := Fin.ext hr
  subst br
  have hpref : ap.1 = bp.1 := by
    have ht := congrArg (fun z : List Bool => z.take (ar : Nat)) hfull
    simpa [ap.2.1, bp.2.1] using ht
  have htail : atail.1 = btail.1 := by
    have hd := congrArg (fun z : List Bool => z.drop (ar : Nat)) hfull
    simpa [ap.2.1, bp.2.1] using hd
  have hap : ap = bp := Subtype.ext hpref
  have hat : atail = btail := Subtype.ext htail
  subst bp
  subst btail
  rfl



theorem lineFirstEndpoint_partial_weight_le_one
    (n N : Nat) (start target : IsingLineBox n)
    (htarget : isingLineBoxBoundary n target) :
    (∑ r ∈ Finset.range (N + 1),
      (Nat.card (IsingLineFirstEndpointFamily n r start target) : Real) /
        (2 : Real) ^ r) <= 1 := by
  letI (r : Fin (N + 1)) :
      Fintype (IsingLineFirstEndpointFamily n r start target) :=
    Fintype.ofFinite _
  letI (r : Fin (N + 1)) :
      Fintype {tail : List Bool // tail.length = N - r} :=
    (List.finite_length_eq Bool (N - r)).fintype
  have hcard : Nat.card (LineFirstEndpointExtension n N start target) <=
      Nat.card {bs : List Bool // bs.length = N} :=
    Nat.card_le_card_of_injective
      (lineFirstEndpointExtend n N start target)
      (lineFirstEndpointExtend_injective n N start target htarget)
  have hext : Nat.card (LineFirstEndpointExtension n N start target) =
      ∑ r : Fin (N + 1),
        Nat.card (IsingLineFirstEndpointFamily n r start target) *
          2 ^ (N - (r : Nat)) := by
    unfold LineFirstEndpointExtension
    rw [Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Nat.card_prod]
    congr 1
    change Nat.card (List.Vector Bool (N - (r : Nat))) =
      2 ^ (N - (r : Nat))
    rw [Nat.card_congr (Equiv.vectorEquivFin Bool (N - (r : Nat))),
      Nat.card_eq_fintype_card, Fintype.card_fun]
    simp
  have htargetCard : Nat.card {bs : List Bool // bs.length = N} = 2 ^ N := by
    change Nat.card (List.Vector Bool N) = 2 ^ N
    rw [Nat.card_congr (Equiv.vectorEquivFin Bool N),
      Nat.card_eq_fintype_card, Fintype.card_fun]
    simp
  have hreal :
      (∑ r : Fin (N + 1),
        (Nat.card (IsingLineFirstEndpointFamily n r start target) : Real) *
          (2 : Real) ^ (N - (r : Nat))) <= (2 : Real) ^ N := by
    exact_mod_cast (show
      (∑ r : Fin (N + 1),
        Nat.card (IsingLineFirstEndpointFamily n r start target) *
          2 ^ (N - (r : Nat))) <= 2 ^ N by
      rw [← hext, ← htargetCard]
      exact hcard)
  have htwo : 0 < (2 : Real) ^ N := by positivity
  rw [← Fin.sum_univ_eq_sum_range
    (fun r : Nat =>
      (Nat.card (IsingLineFirstEndpointFamily n r start target) : Real) /
        (2 : Real) ^ r) (N + 1)]
  calc
    (∑ r : Fin (N + 1),
        (Nat.card (IsingLineFirstEndpointFamily n r start target) : Real) /
          (2 : Real) ^ (r : Nat)) =
      (∑ r : Fin (N + 1),
        (Nat.card (IsingLineFirstEndpointFamily n r start target) : Real) *
          (2 : Real) ^ (N - (r : Nat))) / (2 : Real) ^ N := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r hr
      have hrN : (r : Nat) <= N := Nat.le_of_lt_succ r.isLt
      have hpow : (2 : Real) ^ N =
          (2 : Real) ^ (r : Nat) * (2 : Real) ^ (N - (r : Nat)) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hpow]
      field_simp
    _ <= (2 : Real) ^ N / (2 : Real) ^ N :=
      div_le_div_of_nonneg_right hreal htwo.le
    _ = 1 := by field_simp

theorem orderedFarHorizontalEndpoint_weight_le
    (m R t : Nat) (mark target : IsingLineBox R)
    (startY targetY : Int) (hm : 0 < m) (ht : t <= m * m)
    (htarget : isingLineBoxBoundary R target) :
    Nat.card (IsingOrderedFarHorizontalEndpointFamily
        m R t mark target startY targetY) / (4 : Real) ^ t <=
      468 / (m : Real) ^ 2 := by
  let b : Nat -> Real := fun j =>
    Nat.card (IsingLineFarFirstBoundaryFamily m j) / (2 : Real) ^ j
  let a : Nat -> Real := fun r =>
    Nat.card (IsingLineFirstEndpointFamily R r mark target) / (2 : Real) ^ r
  let y : Nat -> Real := fun k =>
    Nat.card (VerticalChoicePathFamily k startY targetY) / (2 : Real) ^ k
  have hb0 (j : Nat) : 0 <= b j := by dsimp [b]; positivity
  have ha0 (r : Nat) : 0 <= a r := by dsimp [a]; positivity
  have hy (k : Nat) : y k <= 2 / Real.sqrt (k + 1 : Real) := by
    dsimp [y]
    rw [← isingLineBinomialKernel_eq_natCard_verticalChoicePath_div]
    let K := isingLineBinomialKernel k startY targetY
    have hK0 : 0 <= K := isingLineBinomialKernel_nonneg _ _ _
    have hrad : 0 <= 2 / (k + 1 : Real) := by positivity
    have hK : K <= Real.sqrt (2 / (k + 1 : Real)) := by
      rw [Real.le_sqrt hK0 hrad]
      exact isingLineBinomialKernel_sq_le k startY targetY
    calc
      K <= Real.sqrt (2 / (k + 1 : Real)) := hK
      _ <= 2 / Real.sqrt (k + 1 : Real) := by
        rw [Real.sqrt_div (by positivity)]
        apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
        rw [Real.sqrt_le_iff]
        norm_num
  have hfactor :
      Nat.card (IsingOrderedFarHorizontalEndpointFamily
          m R t mark target startY targetY) / (4 : Real) ^ t =
        ∑ k ∈ Finset.range (t + 1), ∑ j ∈ Finset.range k,
          b j * a (k - j) * y k := by
    rw [orderedFarHorizontalEndpoint_weight_eq_sum]
    change (∑ k : Fin (t + 1), ∑ j : Fin k,
      b (j : Nat) * a ((k : Nat) - (j : Nat)) * y (k : Nat)) = _
    rw [Fin.sum_univ_eq_sum_range
      (fun k : Nat => ∑ j : Fin k, b (j : Nat) * a (k - (j : Nat)) * y k)
      (t + 1)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Fin.sum_univ_eq_sum_range
      (fun j : Nat => b j * a (k - j) * y k) k]
  rw [hfactor]
  calc
    (∑ k ∈ Finset.range (t + 1), ∑ j ∈ Finset.range k,
        b j * a (k - j) * y k) <=
      ∑ k ∈ Finset.range (t + 1), ∑ j ∈ Finset.range k,
        b j * a (k - j) *
          (2 / Real.sqrt ((j + 1 : Nat) : Real)) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hyjk : y k <= 2 / Real.sqrt ((j + 1 : Nat) : Real) := by
        calc
          y k <= 2 / Real.sqrt (k + 1 : Real) := hy k
          _ <= 2 / Real.sqrt ((j + 1 : Nat) : Real) := by
            apply div_le_div_of_nonneg_left (by norm_num)
              (Real.sqrt_pos.2 (by positivity))
            exact Real.sqrt_le_sqrt (by
              exact_mod_cast (show j + 1 <= k + 1 by omega))
      exact mul_le_mul_of_nonneg_left hyjk
        (mul_nonneg (hb0 j) (ha0 (k - j)))
    _ = ∑ j ∈ Finset.range t,
        b j * (2 / Real.sqrt ((j + 1 : Nat) : Real)) *
          (∑ l ∈ Finset.range (t - j), a (l + 1)) := by
      let f : Nat -> Nat -> Real := fun j l =>
        b j * (2 / Real.sqrt ((j + 1 : Nat) : Real)) * a (l + 1)
      rw [Finset.sum_range_succ']
      simp only [Finset.sum_range_zero, add_zero]
      calc
        (∑ k ∈ Finset.range t, ∑ j ∈ Finset.range (k + 1),
            b j * a (k + 1 - j) *
              (2 / Real.sqrt ((j + 1 : Nat) : Real))) =
          ∑ k ∈ Finset.range t, ∑ j ∈ Finset.range (k + 1),
            f j (k - j) := by
            apply Finset.sum_congr rfl
            intro k hk
            apply Finset.sum_congr rfl
            intro j hj
            have hjk : j <= k := by
              have := Finset.mem_range.mp hj
              omega
            dsimp [f]
            have hidx : k + 1 - j = k - j + 1 := by omega
            rw [hidx]
            ring
        _ = ∑ j ∈ Finset.range t, ∑ l ∈ Finset.range (t - j),
            f j l := Finset.sum_range_diag_flip t f
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j hj
          dsimp [f]
          rw [Finset.mul_sum]
    _ <= ∑ j ∈ Finset.range t,
        b j * (2 / Real.sqrt ((j + 1 : Nat) : Real)) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_of_le_one_right
      · exact mul_nonneg (hb0 j) (by positivity)
      · have hmass := lineFirstEndpoint_partial_weight_le_one
          R (t - j) mark target htarget
        have hhead : (∑ l ∈ Finset.range (t - j), a (l + 1)) <=
            ∑ r ∈ Finset.range (t - j + 1), a r := by
          rw [Finset.sum_range_succ']
          exact le_add_of_nonneg_right (ha0 0)
        exact hhead.trans (by simpa [a] using hmass)
    _ <= ∑ j ∈ Finset.range (t + 1),
        (2 / Real.sqrt ((j + 1 : Nat) : Real)) * b j := by
      calc
        _ = ∑ j ∈ Finset.range t,
            (2 / Real.sqrt ((j + 1 : Nat) : Real)) * b j := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ <= _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.range_mono (by omega)
          · intro j hj hj'
            exact mul_nonneg (by positivity) (hb0 j)
    _ <= 468 / (m : Real) ^ 2 := by
      simpa [b, Nat.cast_add, Nat.cast_one] using
        endpointKernel_farFirstBoundary_sum_le m t hm ht

private noncomputable def mirrorOnlyOrderedHorizontalCover
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hlevelR : level <= R) (hhalf : R <= 2 * level)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hq : isingLeapfrogBoxBoundary R q) :
    IsingMirrorOnlySourceOutputAtFamily R t p p' q (level : Int) ->
      IsingOrderedFarHorizontalEndpointFamily (R - level) R t
        ⟨2 * level - R, by omega⟩ q.1 (p.2.1 : Int) (q.2.1 : Int) := fun w =>
  Classical.choose ((Classical.choose_spec
    (exists_mirrorOnlyOrderedCover R level t p p' q
      hlevelR hstart hmirror hq w)).2 hhalf)

private theorem mirrorOnlyOrderedHorizontalCover_value
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hlevelR : level <= R) (hhalf : R <= 2 * level)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hq : isingLeapfrogBoxBoundary R q)
    (w : IsingMirrorOnlySourceOutputAtFamily R t p p' q (level : Int)) :
    orderedFarHorizontalEndpointValue (R - level) R t
        ⟨2 * level - R, by omega⟩ q.1 (p.2.1 : Int) (q.2.1 : Int)
        (mirrorOnlyOrderedHorizontalCover R level t p p' q
          hlevelR hhalf hstart hmirror hq w) = w.1 := by
  exact Classical.choose_spec ((Classical.choose_spec
    (exists_mirrorOnlyOrderedCover R level t p p' q
      hlevelR hstart hmirror hq w)).2 hhalf)

private theorem mirrorOnlyOrderedHorizontalCover_injective
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hlevelR : level <= R) (hhalf : R <= 2 * level)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hq : isingLeapfrogBoxBoundary R q) :
    Function.Injective (mirrorOnlyOrderedHorizontalCover R level t p p' q
      hlevelR hhalf hstart hmirror hq) := by
  intro a b hab
  apply Subtype.ext
  rw [← mirrorOnlyOrderedHorizontalCover_value R level t p p' q
      hlevelR hhalf hstart hmirror hq a,
    ← mirrorOnlyOrderedHorizontalCover_value R level t p p' q
      hlevelR hhalf hstart hmirror hq b, hab]

theorem natCard_mirrorOnlySourceOutputAt_le_orderedFarHorizontalEndpoint
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hlevelR : level <= R) (hhalf : R <= 2 * level)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hq : isingLeapfrogBoxBoundary R q) :
    Nat.card (IsingMirrorOnlySourceOutputAtFamily
        R t p p' q (level : Int)) <=
      Nat.card (IsingOrderedFarHorizontalEndpointFamily (R - level) R t
        ⟨2 * level - R, by omega⟩ q.1 (p.2.1 : Int) (q.2.1 : Int)) :=
  Nat.card_le_card_of_injective
    (mirrorOnlyOrderedHorizontalCover R level t p p' q
      hlevelR hhalf hstart hmirror hq)
    (mirrorOnlyOrderedHorizontalCover_injective R level t p p' q
      hlevelR hhalf hstart hmirror hq)

theorem mirrorOnlySourceOutputAt_horizontal_diffusive_weight_le
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hright : level + rho <= R)
    (hhalf : R <= 2 * level)
    (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
    Nat.card (IsingMirrorOnlySourceOutputAtFamily
        R (rho * rho) p p' q (level : Int)) /
        (4 : Real) ^ (rho * rho) <=
      468 / (rho : Real) ^ 2 := by
  have hlevelR : level <= R := by omega
  have hq : isingLeapfrogBoxBoundary R q := by
    unfold isingLeapfrogBoxBoundary
    rcases hqHorizontal with hq | hq
    · left; exact hq
    · right; left; omega
  have hcard :=
    natCard_mirrorOnlySourceOutputAt_le_orderedFarHorizontalEndpoint
      R level (rho * rho) p p' q hlevelR hhalf hstart hmirror hq
  have hm : 0 < R - level := by omega
  have hρm : rho <= R - level := by omega
  have ht : rho * rho <= (R - level) * (R - level) :=
    Nat.mul_self_le_mul_self hρm
  have hordered := orderedFarHorizontalEndpoint_weight_le
    (R - level) R (rho * rho) ⟨2 * level - R, by omega⟩ q.1
      (p.2.1 : Int) (q.2.1 : Int) hm ht (by
        unfold isingLineBoxBoundary
        exact hqHorizontal)
  have hsq : (rho : Real) ^ 2 <= ((R - level : Nat) : Real) ^ 2 := by
    exact_mod_cast (show rho ^ 2 <= (R - level) ^ 2 by
      simpa [pow_two] using ht)
  calc
    Nat.card (IsingMirrorOnlySourceOutputAtFamily
        R (rho * rho) p p' q (level : Int)) /
        (4 : Real) ^ (rho * rho) <=
      Nat.card (IsingOrderedFarHorizontalEndpointFamily (R - level) R
        (rho * rho) ⟨2 * level - R, by omega⟩ q.1
        (p.2.1 : Int) (q.2.1 : Int)) /
        (4 : Real) ^ (rho * rho) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hcard
    _ <= 468 / ((R - level : Nat) : Real) ^ 2 := hordered
    _ <= 468 / (rho : Real) ^ 2 := by
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq

theorem mirrorOnlySourceOutputAt_boundary_diffusive_weight_le
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hright : level + rho <= R)
    (hhalf : R <= 2 * level)
    (hqBoundary : isingLeapfrogBoxBoundary R q) :
    Nat.card (IsingMirrorOnlySourceOutputAtFamily
        R (rho * rho) p p' q (level : Int)) /
        (4 : Real) ^ (rho * rho) <=
      7488 / (rho : Real) ^ 2 := by
  unfold isingLeapfrogBoxBoundary at hqBoundary
  rcases hqBoundary with hqLeft | hqRight | hqBottom | hqTop
  · exact (mirrorOnlySourceOutputAt_horizontal_diffusive_weight_le
      R level rho p p' q hstart hmirror hρ hright hhalf (Or.inl hqLeft)).trans
        (by
          apply div_le_div_of_nonneg_right (by norm_num)
          positivity)
  · exact (mirrorOnlySourceOutputAt_horizontal_diffusive_weight_le
      R level rho p p' q hstart hmirror hρ hright hhalf
        (Or.inr (by omega))).trans (by
          apply div_le_div_of_nonneg_right (by norm_num)
          positivity)
  · exact mirrorOnlySourceOutputAt_vertical_diffusive_weight_le
      R level rho p p' q hstart hmirror hρ hright (Or.inl hqBottom)
  · exact mirrorOnlySourceOutputAt_vertical_diffusive_weight_le
      R level rho p p' q hstart hmirror hρ hright (Or.inr (by omega))

theorem mirrorFailureAt_boundary_diffusive_weight_le_of_rightHalf
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hleft : rho <= level)
    (hright : level + rho <= R) (hhalf : R <= 2 * level)
    (hbottom : rho <= p.2.1) (htop : p.2.1 + rho <= R)
    (hbottom' : rho <= p'.2.1) (htop' : p'.2.1 + rho <= R)
    (hqBoundary : isingLeapfrogBoxBoundary R q) :
    Nat.card (IsingStoppedCouplingMirrorFailureAtFamily
        R (rho * rho) p p' q (level : Int)) /
        (4 : Real) ^ (rho * rho) <=
      8424 / (rho : Real) ^ 2 := by
  have hcard := natCard_mirrorFailureAt_le_aligned_add_residual
    R (rho * rho) p p' q (level : Int)
  have hcardReal :
      (Nat.card (IsingStoppedCouplingMirrorFailureAtFamily
        R (rho * rho) p p' q (level : Int)) : Real) <=
      Nat.card (IsingSourceFailureOutputAtFamily
        R (rho * rho) p q (level : Int)) +
      Nat.card (IsingMirrorFailureOutputAtFamily
        R (rho * rho) p p' q (level : Int)) +
      Nat.card (IsingMirrorOnlySourceOutputAtFamily
        R (rho * rho) p p' q (level : Int)) := by
    exact_mod_cast hcard
  have hsource := sourceFailureOutputAt_boundary_diffusive_weight_le
    R level rho p q hstart hρ hleft (by omega) hbottom htop hqBoundary
  have hmirrorBound := mirrorFailureOutputAt_boundary_diffusive_weight_le
    R level rho p p' q hstart hmirror hρ (lt_of_lt_of_le hρ hleft)
      hright hbottom' htop' hqBoundary
  have hresidual := mirrorOnlySourceOutputAt_boundary_diffusive_weight_le
    R level rho p p' q hstart hmirror hρ hright hhalf hqBoundary
  calc
    Nat.card (IsingStoppedCouplingMirrorFailureAtFamily
        R (rho * rho) p p' q (level : Int)) /
        (4 : Real) ^ (rho * rho) <=
      (Nat.card (IsingSourceFailureOutputAtFamily
          R (rho * rho) p q (level : Int)) +
       Nat.card (IsingMirrorFailureOutputAtFamily
          R (rho * rho) p p' q (level : Int)) +
       Nat.card (IsingMirrorOnlySourceOutputAtFamily
          R (rho * rho) p p' q (level : Int))) /
        (4 : Real) ^ (rho * rho) :=
      div_le_div_of_nonneg_right hcardReal (by positivity)
    _ = Nat.card (IsingSourceFailureOutputAtFamily
          R (rho * rho) p q (level : Int)) / (4 : Real) ^ (rho * rho) +
        Nat.card (IsingMirrorFailureOutputAtFamily
          R (rho * rho) p p' q (level : Int)) / (4 : Real) ^ (rho * rho) +
        Nat.card (IsingMirrorOnlySourceOutputAtFamily
          R (rho * rho) p p' q (level : Int)) / (4 : Real) ^ (rho * rho) := by
      ring
    _ <= 468 / (rho : Real) ^ 2 + 468 / (rho : Real) ^ 2 +
        7488 / (rho : Real) ^ 2 := add_le_add (add_le_add hsource hmirrorBound)
      hresidual
    _ = 8424 / (rho : Real) ^ 2 := by ring

def IsingSourceChoiceNoHitOutputAtFamily
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int) :=
  {w : IsingLeapfrogChoiceStringFamily t //
    (forall k, k <= t -> lineFreeEndpoint (isingLeapfrogBoxInt p).1
      ((w.1.map Prod.fst).take k) ≠ level) /\
    isingLeapfrogChoiceRun R p w.1 = q}

def IsingMirrorChoiceNoHitOutputAtFamily
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :=
  {w : IsingLeapfrogChoiceStringFamily t //
    (forall k, k <= t -> lineFreeEndpoint (isingLeapfrogBoxInt p).1
      ((w.1.map Prod.fst).take k) ≠ level) /\
    isingLeapfrogChoiceRun R p'
      (isingLeapfrogCouplingChoiceTransform t
        (isingLeapfrogBoxInt p) level w).1 = q}

noncomputable instance isingSourceChoiceNoHitOutputAtFamily_finite
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int) :
    Finite (IsingSourceChoiceNoHitOutputAtFamily R t p q level) := by
  exact Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance isingMirrorChoiceNoHitOutputAtFamily_finite
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Finite (IsingMirrorChoiceNoHitOutputAtFamily R t p p' q level) := by
  exact Finite.of_injective Subtype.val Subtype.val_injective

private def endpointFarEscapeValue
    (m t : Nat) (start target : Int) :
    IsingEndpointFarEscapeWitnessFamily m t start target ->
      IsingLeapfrogChoiceStringFamily t := fun z => by
  let pref := z.2.1.1.zip z.2.2.1.1
  refine ⟨pref ++ z.2.2.2.1, ?_⟩
  rw [List.length_append, List.length_zip, z.2.1.2.1,
    z.2.2.1.2.1, z.2.2.2.2]
  simp
  omega

private theorem lineFreeEndpoint_lt_of_avoids
    (start level : Int) (bs : List Bool) (hstart : start < level)
    (havoid : forall k, k <= bs.length ->
      lineFreeEndpoint start (bs.take k) ≠ level) :
    lineFreeEndpoint start bs < level := by
  induction bs generalizing start with
  | nil => simpa [lineFreeEndpoint] using hstart
  | cons b bs ih =>
      let next := start + if b then 1 else -1
      have hnextLe : next <= level := by
        dsimp [next]
        cases b <;> simp <;> omega
      have hnextNe : next ≠ level := by
        have h := havoid 1 (by simp)
        simpa [lineFreeEndpoint, next] using h
      have htail : forall k, k <= bs.length ->
          lineFreeEndpoint next (bs.take k) ≠ level := by
        intro k hk
        have h := havoid (k + 1) (by simp; omega)
        simpa [lineFreeEndpoint, next, List.take_succ_cons] using h
      exact ih next (lt_of_le_of_ne hnextLe hnextNe) htail

private theorem exists_sourceNoHitHorizontalCover
    (R level t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hqLeft : q.1.1 = 0)
    (w : IsingSourceChoiceNoHitOutputAtFamily R t p q (level : Int)) :
    exists z : IsingEndpointFarEscapeWitnessFamily level t
        (p.2.1 : Int) (q.2.1 : Int),
      endpointFarEscapeValue level t (p.2.1 : Int) (q.2.1 : Int) z = w.1 := by
  have hq : isingLeapfrogBoxBoundary R q := by
    unfold isingLeapfrogBoxBoundary
    left
    exact hqLeft
  rcases choiceRun_boundary_output_data_endpointFailure R t p q hq w.1 w.2.2 with
    ⟨k, hkT, hkOutput, hkMinimal⟩
  have hlevelPos : 0 < level := by
    have hpNonneg : 0 <= (isingLeapfrogBoxInt p).1 := by
      unfold isingLeapfrogBoxInt
      dsimp
      exact_mod_cast Nat.zero_le p.1.1
    omega
  have hstartX : ((level - 1 : Nat) : Int) =
      (isingLeapfrogBoxInt p).1 := by
    rw [Nat.cast_sub hlevelPos]
    norm_num
    omega
  have hcoord (l : Nat) (hl : l <= k) :=
    choiceRun_take_coordinates_eq_lineFree R t k p w.1 hkT hkMinimal l hl
  let xbits := (w.1.1.take k).map Prod.fst
  let ybits := (w.1.1.take k).map Prod.snd
  let tail := w.1.1.drop k
  have hxlen : xbits.length = k := by
    dsimp [xbits]
    simp [w.1.2, hkT]
  have hylen : ybits.length = k := by
    dsimp [ybits]
    simp [w.1.2, hkT]
  have htail : tail.length = t - k := by
    dsimp [tail]
    rw [List.length_drop, w.1.2]
  have hxTake (l : Nat) (hl : l <= k) :
      xbits.take l = (w.1.1.take l).map Prod.fst := by
    dsimp [xbits]
    rw [← List.map_take, List.take_take, Nat.min_eq_left hl]
  have hxInterior (l : Nat) (hl : l < k) :
      0 < lineFreeEndpoint ((level - 1 : Nat) : Int) (xbits.take l) /\
        lineFreeEndpoint ((level - 1 : Nat) : Int) (xbits.take l) < level := by
    have hc := (hcoord l hl.le).1
    have hnot := hkMinimal l hl
    rw [hxTake l hl.le]
    rw [hstartX, ← hc]
    have hpos : 0 < (isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 := by
      have hne : (isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 ≠ 0 := by
        intro heq
        apply hnot
        unfold isingLeapfrogBoxBoundary
        left
        exact heq
      omega
    have hltFree : lineFreeEndpoint (isingLeapfrogBoxInt p).1
        ((w.1.1.take l).map Prod.fst) < level := by
      apply lineFreeEndpoint_lt_of_avoids
      · omega
      · intro r hr
        have hrl : r <= l := by
          rw [List.length_map, List.length_take, w.1.2] at hr
          omega
        have hav := w.2.1 r (hrl.trans (hl.le.trans hkT))
        simpa [← List.map_take, List.take_take, Nat.min_eq_left hrl] using hav
    have hlt : ((isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 : Int) <
        level := by rw [hc]; exact hltFree
    exact ⟨by exact_mod_cast hpos, hlt⟩
  have hxFree (l : Nat) (hl : l <= k) :
      ((isingLineChoiceRun level ⟨level - 1, by omega⟩
        (xbits.take l)).1 : Int) =
      lineFreeEndpoint ((level - 1 : Nat) : Int) (xbits.take l) := by
    apply lineChoiceRun_val_eq_lineFreeEndpoint
    intro r hr
    have hrl : r < l := by rw [List.length_take, hxlen] at hr; omega
    have hi := hxInterior r (hrl.trans_le hl)
    have ht : (xbits.take l).take r = xbits.take r := by
      simp [List.take_take, Nat.min_eq_left hrl.le]
    rw [ht]
    exact ⟨ne_of_gt hi.1, ne_of_lt hi.2⟩
  have hxEnd : lineFreeEndpoint ((level - 1 : Nat) : Int) xbits = 0 := by
    have hc := (hcoord k le_rfl).1
    rw [hkOutput] at hc
    have htake : xbits.take k = xbits := by simpa [hxlen] using List.take_all xbits
    have hxEq := hxTake k le_rfl
    rw [htake] at hxEq
    rw [hstartX, hxEq, ← hc]
    exact_mod_cast hqLeft
  let xfar : IsingLineFarFirstBoundaryFamily level k := ⟨xbits, hxlen, by
    apply Fin.ext
    have hrun := hxFree k le_rfl
    have ht : xbits.take k = xbits := by simpa [hxlen] using List.take_all xbits
    rw [ht] at hrun
    change (isingLineChoiceRun level ⟨level - 1, by omega⟩ xbits).1 = 0
    exact_mod_cast hrun.trans hxEnd, by
      intro l hl
      have hi := hxInterior l hl
      have hrun := hxFree l hl.le
      intro hb
      unfold isingLineBoxBoundary at hb
      rcases hb with hb | hb <;> exact (by omega)⟩
  have hyEnd : lineFreeEndpoint (p.2.1 : Int) ybits = q.2.1 := by
    have hc := (hcoord k le_rfl).2
    rw [hkOutput] at hc
    exact hc.symm
  let ypref : VerticalChoicePathFamily k (p.2.1 : Int) (q.2.1 : Int) :=
    ⟨ybits, hylen, hyEnd⟩
  let z : IsingEndpointFarEscapeWitnessFamily level t
      (p.2.1 : Int) (q.2.1 : Int) :=
    ⟨⟨k, by omega⟩, xfar, ypref, ⟨tail, htail⟩⟩
  refine ⟨z, ?_⟩
  apply Subtype.ext
  dsimp [endpointFarEscapeValue, z, xfar, ypref, xbits, ybits, tail]
  rw [prodBits_zip_self_endpointFailure, List.take_append_drop]

private noncomputable def sourceNoHitHorizontalCover
    (R level t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hqLeft : q.1.1 = 0) :
    IsingSourceChoiceNoHitOutputAtFamily R t p q (level : Int) ->
      IsingEndpointFarEscapeWitnessFamily level t
        (p.2.1 : Int) (q.2.1 : Int) := fun w =>
  Classical.choose (exists_sourceNoHitHorizontalCover
    R level t p q hstart hqLeft w)

private theorem sourceNoHitHorizontalCover_value
    (R level t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hqLeft : q.1.1 = 0)
    (w : IsingSourceChoiceNoHitOutputAtFamily R t p q (level : Int)) :
    endpointFarEscapeValue level t (p.2.1 : Int) (q.2.1 : Int)
        (sourceNoHitHorizontalCover R level t p q hstart hqLeft w) = w.1 := by
  exact Classical.choose_spec
    (exists_sourceNoHitHorizontalCover R level t p q hstart hqLeft w)

private theorem sourceNoHitHorizontalCover_injective
    (R level t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hqLeft : q.1.1 = 0) :
    Function.Injective
      (sourceNoHitHorizontalCover R level t p q hstart hqLeft) := by
  intro a b hab
  apply Subtype.ext
  rw [← sourceNoHitHorizontalCover_value R level t p q hstart hqLeft a,
    ← sourceNoHitHorizontalCover_value R level t p q hstart hqLeft b,
    hab]

private theorem isEmpty_sourceNoHitOutput_right
    (R level t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hlevelR : level <= R)
    (hqRight : q.1.1 = R) :
    IsEmpty (IsingSourceChoiceNoHitOutputAtFamily R t p q (level : Int)) := by
  constructor
  intro w
  have hq : isingLeapfrogBoxBoundary R q := by
    unfold isingLeapfrogBoxBoundary
    right; left
    omega
  rcases choiceRun_boundary_output_data_endpointFailure R t p q hq w.1 w.2.2 with
    ⟨k, hkT, hkOutput, hkMinimal⟩
  have hcoord := choiceRun_take_coordinates_eq_lineFree
    R t k p w.1 hkT hkMinimal k le_rfl
  have hbelow : lineFreeEndpoint (isingLeapfrogBoxInt p).1
      ((w.1.1.take k).map Prod.fst) < level := by
    apply lineFreeEndpoint_lt_of_avoids
    · omega
    · intro r hr
      have hrk : r <= k := by
        rw [List.length_map, List.length_take, w.1.2] at hr
        omega
      have hav := w.2.1 r (hrk.trans hkT)
      simpa [← List.map_take, List.take_take, Nat.min_eq_left hrk] using hav
  rw [← hcoord.1, hkOutput] at hbelow
  have : ((q.1.1 : Nat) : Int) = R := by exact_mod_cast hqRight
  omega

theorem sourceChoiceNoHitOutputAt_horizontal_diffusive_weight_le
    (R level rho : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hleft : rho <= level) (hlevelR : level <= R)
    (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
    Nat.card (IsingSourceChoiceNoHitOutputAtFamily
        R (rho * rho) p q (level : Int)) /
        (4 : Real) ^ (rho * rho) <=
      468 / (rho : Real) ^ 2 := by
  rcases hqHorizontal with hqLeft | hqRight
  · have hcard := Nat.card_le_card_of_injective
        (sourceNoHitHorizontalCover R level (rho * rho) p q hstart hqLeft)
        (sourceNoHitHorizontalCover_injective R level (rho * rho)
          p q hstart hqLeft)
    calc
      Nat.card (IsingSourceChoiceNoHitOutputAtFamily
          R (rho * rho) p q (level : Int)) / (4 : Real) ^ (rho * rho) <=
        Nat.card (IsingEndpointFarEscapeWitnessFamily level (rho * rho)
          (p.2.1 : Int) (q.2.1 : Int)) / (4 : Real) ^ (rho * rho) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast hcard
      _ <= 468 / (rho : Real) ^ 2 :=
        endpointFarEscapeWitness_diffusive_weight_le rho level
          (p.2.1 : Int) (q.2.1 : Int) hρ hleft
  · letI := isEmpty_sourceNoHitOutput_right
      R level (rho * rho) p q hstart hlevelR hqRight
    simp only [Nat.card_of_isEmpty, Nat.cast_zero, zero_div]
    positivity

private theorem exists_sourceNoHitVerticalCover
    (R level rho t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hbottom : rho <= p.2.1)
    (htop : p.2.1 + rho <= R)
    (hqVertical : q.2.1 = 0 ∨ q.2.1 = R)
    (w : IsingSourceChoiceNoHitOutputAtFamily R t p q (level : Int)) :
    exists u : IsingTailDependentEndpointRaceFamily rho t (level : Int)
        (sourceEndpointRaceTarget R t rho p q),
      tailDependentEndpointRaceValue R t rho p q (level : Int) u = w.1 := by
  have hq : isingLeapfrogBoxBoundary R q := by
    unfold isingLeapfrogBoxBoundary
    rcases hqVertical with hq | hq
    · right; right; left; exact hq
    · right; right; right; omega
  rcases choiceRun_boundary_output_data_endpointFailure R t p q hq w.1 w.2.2 with
    ⟨k, hkT, hkOutput, hkMinimal⟩
  have hcoord (l : Nat) (hl : l <= k) :=
    choiceRun_take_coordinates_eq_lineFree R t k p w.1 hkT hkMinimal l hl
  have hyEnd : lineFreeEndpoint (isingLeapfrogBoxInt p).2
      ((w.1.1.take k).map Prod.snd) = q.2.1 := by
    rw [← (hcoord k le_rfl).2, hkOutput]
  have hbottomInt : (rho : Int) <= (isingLeapfrogBoxInt p).2 := by
    unfold isingLeapfrogBoxInt
    dsimp
    exact_mod_cast hbottom
  have htopInt : (isingLeapfrogBoxInt p).2 + (rho : Int) <= R := by
    unfold isingLeapfrogBoxInt
    dsimp
    exact_mod_cast htop
  let hex : exists s, s <= k /\
      (lineFreeEndpoint (isingLeapfrogBoxInt p).2
          ((w.1.1.take s).map Prod.snd) = (isingLeapfrogBoxInt p).2 - rho ∨
       lineFreeEndpoint (isingLeapfrogBoxInt p).2
          ((w.1.1.take s).map Prod.snd) = (isingLeapfrogBoxInt p).2 + rho) := by
    rcases hqVertical with hqBottom | hqTop
    · have hend : (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
          (isingLeapfrogChoiceSteps (w.1.1.take k))).2 <=
          (isingLeapfrogBoxInt p).2 - rho := by
        rw [← lineFreeEndpoint_choiceVertical_full, hyEnd]
        have hq0 : ((q.2.1 : Nat) : Int) = 0 := by exact_mod_cast hqBottom
        rw [hq0]
        omega
      rcases exists_vertical_barrier_prefix_lower rho hρ
        (isingLeapfrogBoxInt p) (w.1.1.take k)
        hbottomInt hend with ⟨s, hs, heq⟩
      exact ⟨s, le_trans hs (List.length_take_le ..), Or.inl (by
        simpa [List.take_take,
          Nat.min_eq_left (le_trans hs (List.length_take_le ..))] using heq)⟩
    · have hend : (isingLeapfrogBoxInt p).2 + rho <=
          (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
            (isingLeapfrogChoiceSteps (w.1.1.take k))).2 := by
        rw [← lineFreeEndpoint_choiceVertical_full, hyEnd]
        have hqR : ((q.2.1 : Nat) : Int) = R := by exact_mod_cast hqTop
        rw [hqR]
        omega
      rcases exists_vertical_barrier_prefix rho hρ
        (isingLeapfrogBoxInt p) (w.1.1.take k) k
        (by simp [hkT]) hbottomInt hend with ⟨s, hs, heq⟩
      exact ⟨s, le_trans hs (List.length_take_le ..), Or.inr (by
        simpa [List.take_take,
          Nat.min_eq_left (le_trans hs (List.length_take_le ..))] using heq)⟩
  let s := Nat.find hex
  have hsSpec := Nat.find_spec hex
  have hsK : s <= k := hsSpec.1
  have hsT : s <= t := hsK.trans hkT
  have havoid : forall l, l < s ->
      lineFreeEndpoint (isingLeapfrogBoxInt p).2
          ((w.1.1.take l).map Prod.snd) ≠ (isingLeapfrogBoxInt p).2 - rho /\
      lineFreeEndpoint (isingLeapfrogBoxInt p).2
          ((w.1.1.take l).map Prod.snd) ≠ (isingLeapfrogBoxInt p).2 + rho := by
    intro l hl
    constructor <;> intro heq
    · exact (Nat.find_min hex hl) ⟨by omega, Or.inl heq⟩
    · exact (Nat.find_min hex hl) ⟨by omega, Or.inr heq⟩
  have hverticalFree (l : Nat) (hl : l < s) :
      lineFreeEndpoint (rho : Int)
          (((w.1.1.take s).map Prod.snd).take l) ≠ 0 /\
        lineFreeEndpoint (rho : Int)
          (((w.1.1.take s).map Prod.snd).take l) ≠ (2 * rho : Nat) := by
    have ha := havoid l hl
    have htr := lineFreeEndpoint_translate
      ((w.1.1.take l).map Prod.snd) (isingLeapfrogBoxInt p).2 (rho : Int)
    have ht : ((w.1.1.take s).map Prod.snd).take l =
        (w.1.1.take l).map Prod.snd := by
      simp [← List.map_take, List.take_take, Nat.min_eq_left hl.le]
    rw [ht, htr]
    constructor <;> intro heq
    · apply ha.1; omega
    · apply ha.2; push_cast at heq; omega
  have hverticalEnd : lineFreeEndpoint (rho : Int)
      ((w.1.1.take s).map Prod.snd) = 0 ∨
      lineFreeEndpoint (rho : Int) ((w.1.1.take s).map Prod.snd) =
        (2 * rho : Nat) := by
    have htr := lineFreeEndpoint_translate
      ((w.1.1.take s).map Prod.snd) (isingLeapfrogBoxInt p).2 (rho : Int)
    rw [htr]
    rcases hsSpec.2 with hs | hs
    · left; rw [hs]; ring
    · right; rw [hs]; push_cast; ring
  have hverticalFree' : forall l,
      l < ((w.1.1.take s).map Prod.snd).length ->
      lineFreeEndpoint (rho : Int)
          (((w.1.1.take s).map Prod.snd).take l) ≠ 0 /\
        lineFreeEndpoint (rho : Int)
          (((w.1.1.take s).map Prod.snd).take l) ≠ (2 * rho : Nat) := by
    intro l hl
    apply hverticalFree l
    simpa [w.1.2, hsT] using hl
  have hlineEnd := lineChoiceRun_val_eq_lineFreeEndpoint (2 * rho)
    (⟨rho, by omega⟩ : IsingLineBox (2 * rho))
    ((w.1.1.take s).map Prod.snd) hverticalFree'
  let vword : IsingLineFirstBoundaryFamily rho s :=
    ⟨(w.1.1.take s).map Prod.snd, by simp [w.1.2, hsT], by
      unfold isingLineBoxBoundary
      have hendInt :
          ((isingLineChoiceRun (2 * rho) ⟨rho, by omega⟩
              ((w.1.1.take s).map Prod.snd)).1 : Int) = 0 ∨
            ((isingLineChoiceRun (2 * rho) ⟨rho, by omega⟩
              ((w.1.1.take s).map Prod.snd)).1 : Int) = (2 * rho : Nat) := by
        rw [hlineEnd]
        exact hverticalEnd
      exact_mod_cast hendInt, by
      intro l hl
      have hfreeL : forall r, r <
          (((w.1.1.take s).map Prod.snd).take l).length ->
          lineFreeEndpoint (rho : Int)
              ((((w.1.1.take s).map Prod.snd).take l).take r) ≠ 0 /\
            lineFreeEndpoint (rho : Int)
              ((((w.1.1.take s).map Prod.snd).take l).take r) ≠
                (2 * rho : Nat) := by
        intro r hr
        have hrl : r < l := lt_of_lt_of_le hr (List.length_take_le ..)
        have hrs : r < s := hrl.trans hl
        have hrs' : r <= min l s := Nat.le_min.mpr ⟨hrl.le, hrs.le⟩
        simpa [List.take_take, Nat.min_eq_left hrs', Nat.min_eq_left hrs.le] using
          hverticalFree r hrs
      have hrun := lineChoiceRun_val_eq_lineFreeEndpoint (2 * rho)
        (⟨rho, by omega⟩ : IsingLineBox (2 * rho))
        (((w.1.1.take s).map Prod.snd).take l) hfreeL
      have hnot := hverticalFree l hl
      intro hb
      unfold isingLineBoxBoundary at hb
      rcases hb with hb | hb
      · apply hnot.1; rw [← hrun]; exact_mod_cast hb
      · apply hnot.2; rw [← hrun]; exact_mod_cast hb⟩
  let tail : IsingEndpointRaceTail t ⟨s, by omega⟩ :=
    ⟨w.1.1.drop s, by simp [w.1.2, hsT]⟩
  have hstop : firstVerticalBoundaryTimeEndpointFailure R
      (isingLeapfrogBoxInt p).2 (w.1.1.map Prod.snd) = k := by
    apply firstVerticalBoundaryTimeEndpointFailure_eq
    · simpa [w.1.2] using hkT
    · rw [← List.map_take, hyEnd]
      rcases hqVertical with hq0 | hqR
      · left; exact_mod_cast hq0
      · right; exact_mod_cast hqR
    · intro l hl
      have hc := hcoord l hl.le
      have hnot := hkMinimal l hl
      constructor
      · intro h0
        apply hnot
        unfold isingLeapfrogBoxBoundary
        right; right; left
        rw [← List.map_take, ← hc.2] at h0
        exact_mod_cast h0
      · intro hR
        apply hnot
        unfold isingLeapfrogBoxBoundary
        right; right; right
        rw [← List.map_take, ← hc.2] at hR
        have hR' : (isingLeapfrogChoiceRun R p (w.1.1.take l)).2.1 = R := by
          exact_mod_cast hR
        omega
  have hxPrefix : (w.1.1.map Prod.fst).take k =
      (w.1.1.take s).map Prod.fst ++
        ((w.1.1.drop s).map Prod.fst).take (k - s) := by
    rw [← List.map_take, ← List.map_take, ← List.map_append,
      ← List.take_add]
    congr 2
    omega
  have hxRaw : lineFreeEndpoint (isingLeapfrogBoxInt p).1
      ((w.1.1.map Prod.fst).take k) = q.1 := by
    rw [← List.map_take]
    exact (hcoord k le_rfl).1.symm.trans (by rw [hkOutput])
  have hendpoint : lineFreeEndpoint ((level : Int) - 1)
      ((w.1.1.take s).map Prod.fst) =
      sourceEndpointRaceTarget R t rho p q ⟨s, by omega⟩ vword tail := by
    have hstartX : (isingLeapfrogBoxInt p).1 = (level : Int) - 1 := by omega
    have hxRaw' : lineFreeEndpoint ((level : Int) - 1)
        ((w.1.1.map Prod.fst).take k) = q.1 := by
      rw [← hstartX]
      exact hxRaw
    rw [hxPrefix, lineFreeEndpoint_append_endpointFailure] at hxRaw'
    have htr := lineFreeEndpoint_translate
      (((w.1.1.drop s).map Prod.fst).take (k - s)) 0
      (lineFreeEndpoint ((level : Int) - 1)
        ((w.1.1.take s).map Prod.fst))
    unfold sourceEndpointRaceTarget
    dsimp only [vword, tail]
    rw [← List.map_append, List.take_append_drop, hstop]
    rw [htr] at hxRaw'
    change lineFreeEndpoint ((level : Int) - 1)
        ((w.1.1.take s).map Prod.fst) =
      (q.1.1 : Int) - lineFreeEndpoint 0
        (((w.1.1.drop s).map Prod.fst).take (k - s))
    linarith
  let hword : IsingHorizontalNoHitEndpointFamily s (level : Int)
      (sourceEndpointRaceTarget R t rho p q ⟨s, by omega⟩ vword tail) :=
    ⟨⟨(w.1.1.take s).map Prod.fst, by simp [w.1.2, hsT], by
      intro r hr
      have hrs : r <= s := by simpa [w.1.2, hsT] using hr
      have hav := w.2.1 r (hrs.trans hsT)
      have hstartX : (isingLeapfrogBoxInt p).1 = (level : Int) - 1 := by omega
      have hav' : lineFreeEndpoint ((level : Int) - 1)
          ((w.1.1.map Prod.fst).take r) ≠ level := by
        rw [← hstartX]
        exact hav
      simpa [← List.map_take, List.take_take, Nat.min_eq_left hrs] using hav'⟩,
      hendpoint⟩
  let u : IsingTailDependentEndpointRaceFamily rho t (level : Int)
      (sourceEndpointRaceTarget R t rho p q) :=
    ⟨⟨s, by omega⟩, vword, tail, hword⟩
  refine ⟨u, ?_⟩
  apply Subtype.ext
  dsimp [tailDependentEndpointRaceValue, u, hword, vword, tail]
  rw [prodBits_zip_self_endpointFailure, List.take_append_drop]

private noncomputable def sourceNoHitVerticalCover
    (R level rho t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hbottom : rho <= p.2.1)
    (htop : p.2.1 + rho <= R)
    (hqVertical : q.2.1 = 0 ∨ q.2.1 = R) :
    IsingSourceChoiceNoHitOutputAtFamily R t p q (level : Int) →
      IsingTailDependentEndpointRaceFamily rho t (level : Int)
        (sourceEndpointRaceTarget R t rho p q) := fun w =>
  Classical.choose (exists_sourceNoHitVerticalCover R level rho t p q hstart
    hρ hbottom htop hqVertical w)

private theorem sourceNoHitVerticalCover_value
    (R level rho t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hbottom : rho <= p.2.1)
    (htop : p.2.1 + rho <= R)
    (hqVertical : q.2.1 = 0 ∨ q.2.1 = R)
    (w : IsingSourceChoiceNoHitOutputAtFamily R t p q (level : Int)) :
    tailDependentEndpointRaceValue R t rho p q (level : Int)
      (sourceNoHitVerticalCover R level rho t p q hstart hρ hbottom htop
        hqVertical w) = w.1 := by
  exact Classical.choose_spec (exists_sourceNoHitVerticalCover R level rho t
    p q hstart hρ hbottom htop hqVertical w)

private theorem sourceNoHitVerticalCover_injective
    (R level rho t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hbottom : rho <= p.2.1)
    (htop : p.2.1 + rho <= R)
    (hqVertical : q.2.1 = 0 ∨ q.2.1 = R) :
    Function.Injective
      (sourceNoHitVerticalCover R level rho t p q hstart hρ hbottom htop
        hqVertical) := by
  intro a b hab
  apply Subtype.ext
  rw [← sourceNoHitVerticalCover_value R level rho t p q hstart hρ hbottom
      htop hqVertical a,
    ← sourceNoHitVerticalCover_value R level rho t p q hstart hρ hbottom
      htop hqVertical b, hab]

theorem sourceChoiceNoHitOutputAt_vertical_diffusive_weight_le
    (R level rho : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hbottom : rho <= p.2.1)
    (htop : p.2.1 + rho <= R)
    (hqVertical : q.2.1 = 0 ∨ q.2.1 = R) :
    Nat.card (IsingSourceChoiceNoHitOutputAtFamily
        R (rho * rho) p q (level : Int)) /
        (4 : Real) ^ (rho * rho) <=
      24 / (rho : Real) ^ 2 := by
  have hcard := Nat.card_le_card_of_injective
    (sourceNoHitVerticalCover R level rho (rho * rho) p q hstart hρ hbottom
      htop hqVertical)
    (sourceNoHitVerticalCover_injective R level rho (rho * rho) p q hstart hρ
      hbottom htop hqVertical)
  have hcardReal :
      (Nat.card (IsingSourceChoiceNoHitOutputAtFamily
        R (rho * rho) p q (level : Int)) : Real) <=
      Nat.card (IsingTailDependentEndpointRaceFamily rho (rho * rho)
        (level : Int) (sourceEndpointRaceTarget R (rho * rho) rho p q)) := by
    exact_mod_cast hcard
  exact (div_le_div_of_nonneg_right hcardReal (by positivity)).trans
    (tailDependentEndpointRace_diffusive_weight_le rho rho (level : Int)
      (sourceEndpointRaceTarget R (rho * rho) rho p q) hρ (le_refl _))

theorem sourceChoiceNoHitOutputAt_boundary_diffusive_weight_le
    (R level rho : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hleft : rho <= level) (hlevelR : level <= R)
    (hbottom : rho <= p.2.1) (htop : p.2.1 + rho <= R)
    (hqBoundary : isingLeapfrogBoxBoundary R q) :
    Nat.card (IsingSourceChoiceNoHitOutputAtFamily
        R (rho * rho) p q (level : Int)) /
        (4 : Real) ^ (rho * rho) <=
      468 / (rho : Real) ^ 2 := by
  unfold isingLeapfrogBoxBoundary at hqBoundary
  rcases hqBoundary with hqLeft | hqRight | hqBottom | hqTop
  · exact sourceChoiceNoHitOutputAt_horizontal_diffusive_weight_le
      R level rho p q hstart hρ hleft hlevelR (Or.inl hqLeft)
  · exact sourceChoiceNoHitOutputAt_horizontal_diffusive_weight_le
      R level rho p q hstart hρ hleft hlevelR (Or.inr (by omega))
  · exact (sourceChoiceNoHitOutputAt_vertical_diffusive_weight_le
      R level rho p q hstart hρ hbottom htop (Or.inl hqBottom)).trans (by
        apply div_le_div_of_nonneg_right (by norm_num)
        positivity)
  · exact (sourceChoiceNoHitOutputAt_vertical_diffusive_weight_le
      R level rho p q hstart hρ hbottom htop (Or.inr (by omega))).trans (by
        apply div_le_div_of_nonneg_right (by norm_num)
        positivity)

private theorem firstHitSplit_eq_none_of_choice_noHit
    {start : Int × Int} {level : Int} {path : List (Int × Int)}
    (havoid : forall k, k <= path.length ->
      (isingDiagonalWalkEndpoint start (path.take k)).1 ≠ level) :
    isingDiagonalWalkFirstHitSplit? start level path = none := by
  cases hsplit : isingDiagonalWalkFirstHitSplit? start level path with
  | none => rfl
  | some split =>
      exfalso
      have hsteps := firstHitSplit_steps hsplit
      have hk : split.before.length <= path.length := by
        rw [← hsteps]
        simp [IsingDiagonalWalkHitSplit.steps]
      exact (havoid split.before.length hk) (by
        have htake : path.take split.before.length = split.before := by
          rw [← hsteps]
          simp [IsingDiagonalWalkHitSplit.steps]
        rw [htake]
        exact split.hit)

private theorem flipX_encode_reflected_choiceSteps (bs : List (Bool × Bool)) :
    isingLeapfrogFlipXChoices
        (isingLeapfrogEncodeSteps
          ((isingLeapfrogChoiceSteps bs).map reflectIncrement)) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      change
        ((!(isingLeapfrogEncodeStep
            (reflectIncrement (isingLeapfrogChoiceStep b))).1,
          (isingLeapfrogEncodeStep
            (reflectIncrement (isingLeapfrogChoiceStep b))).2) ::
          isingLeapfrogFlipXChoices
            (isingLeapfrogEncodeSteps
              ((isingLeapfrogChoiceSteps bs).map reflectIncrement))) = b :: bs
      rw [ih]
      rcases b with ⟨bx, byy⟩
      cases bx <;> cases byy <;>
        simp [isingLeapfrogChoiceStep, isingLeapfrogEncodeStep,
          reflectIncrement]

private theorem couplingChoiceTransform_flipX_eq_of_noHit
    (t : Nat) (start : Int × Int) (level : Int)
    (w : IsingLeapfrogChoiceStringFamily t)
    (havoid : forall k, k <= t -> lineFreeEndpoint start.1
      ((w.1.map Prod.fst).take k) ≠ level) :
    isingLeapfrogFlipXChoices
        (isingLeapfrogCouplingChoiceTransform t start level w).1 = w.1 := by
  have hnone : isingDiagonalWalkFirstHitSplit? start level
      (isingLeapfrogChoiceSteps w.1) = none := by
    apply firstHitSplit_eq_none_of_choice_noHit
    intro k hk
    have hkt : k <= t := by
      simpa [isingLeapfrogChoiceSteps, w.2] using hk
    have hw := havoid k hkt
    rw [show (isingLeapfrogChoiceSteps w.1).take k =
        isingLeapfrogChoiceSteps (w.1.take k) by
          simp [isingLeapfrogChoiceSteps, List.map_take]]
    rw [← lineFreeEndpoint_choiceHorizontal_full]
    simpa [List.map_take] using hw
  unfold isingLeapfrogCouplingChoiceTransform
  dsimp only
  unfold isingDiagonalWalkCouplingReflectSteps
  rw [hnone]
  exact flipX_encode_reflected_choiceSteps w.1

private def mirrorNoHitOutputReflectX
    (R t level : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hlevelR : level <= R) :
    IsingMirrorChoiceNoHitOutputAtFamily R t p p' q (level : Int) ->
      IsingSourceChoiceNoHitOutputAtFamily R t
        (isingLeapfrogBoxReflectX R p') (isingLeapfrogBoxReflectX R q)
        ((R - level : Nat) : Int) := fun w => by
  have hp'x : (isingLeapfrogBoxInt p').1 = (level : Int) + 1 := by
    rw [hmirror]
    unfold reflectedEndpoint
    dsimp
    omega
  have hrefStart :
      (isingLeapfrogBoxInt (isingLeapfrogBoxReflectX R p')).1 + 1 =
        (R - level : Nat) := by
    rw [boxInt_reflectX]
    dsimp
    have hcast : ((R - level : Nat) : Int) = (R : Int) - level := by
      rw [Nat.cast_sub hlevelR]
    rw [hcast, hp'x]
    omega
  refine ⟨w.1, ?_, ?_⟩
  · intro k hk hnewHit
    apply w.2.1 k hk
    have htranslate := lineFreeEndpoint_translate
      ((w.1.1.map Prod.fst).take k) (isingLeapfrogBoxInt p).1
      (isingLeapfrogBoxInt (isingLeapfrogBoxReflectX R p')).1
    rw [hnewHit] at htranslate
    linarith
  · have hflip := couplingChoiceTransform_flipX_eq_of_noHit t
      (isingLeapfrogBoxInt p) (level : Int) w.1 w.2.1
    change isingLeapfrogChoiceRun R (isingLeapfrogBoxReflectX R p') w.1.1 =
      isingLeapfrogBoxReflectX R q
    rw [← hflip, choiceRun_reflectX, w.2.2]

private theorem mirrorNoHitOutputReflectX_injective
    (R t level : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hlevelR : level <= R) :
    Function.Injective
      (mirrorNoHitOutputReflectX R t level p p' q hstart hmirror hlevelR) := by
  intro a b hab
  apply Subtype.ext
  have hv := congrArg
    (fun z : IsingSourceChoiceNoHitOutputAtFamily R t
      (isingLeapfrogBoxReflectX R p') (isingLeapfrogBoxReflectX R q)
      ((R - level : Nat) : Int) => z.1) hab
  exact hv

theorem mirrorChoiceNoHitOutputAt_boundary_diffusive_weight_le
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hright : level + rho <= R)
    (hbottom : rho <= p'.2.1) (htop : p'.2.1 + rho <= R)
    (hqBoundary : isingLeapfrogBoxBoundary R q) :
    Nat.card (IsingMirrorChoiceNoHitOutputAtFamily
        R (rho * rho) p p' q (level : Int)) /
        (4 : Real) ^ (rho * rho) <=
      468 / (rho : Real) ^ 2 := by
  have hlevelR : level <= R := by omega
  have hcard := Nat.card_le_card_of_injective
    (mirrorNoHitOutputReflectX R (rho * rho) level p p' q hstart hmirror
      hlevelR)
    (mirrorNoHitOutputReflectX_injective R (rho * rho) level p p' q hstart
      hmirror hlevelR)
  have hcardReal :
      (Nat.card (IsingMirrorChoiceNoHitOutputAtFamily
        R (rho * rho) p p' q (level : Int)) : Real) <=
      Nat.card (IsingSourceChoiceNoHitOutputAtFamily R (rho * rho)
        (isingLeapfrogBoxReflectX R p') (isingLeapfrogBoxReflectX R q)
        ((R - level : Nat) : Int)) := by
    exact_mod_cast hcard
  have hp'x : (isingLeapfrogBoxInt p').1 = (level : Int) + 1 := by
    rw [hmirror]
    unfold reflectedEndpoint
    dsimp
    omega
  have hrefStart :
      (isingLeapfrogBoxInt (isingLeapfrogBoxReflectX R p')).1 + 1 =
        (R - level : Nat) := by
    rw [boxInt_reflectX]
    dsimp
    have hcast : ((R - level : Nat) : Int) = (R : Int) - level := by
      rw [Nat.cast_sub hlevelR]
    rw [hcast, hp'x]
    omega
  have hrefBottom : rho <= (isingLeapfrogBoxReflectX R p').2.1 := by
    simpa [isingLeapfrogBoxReflectX] using hbottom
  have hrefTop : (isingLeapfrogBoxReflectX R p').2.1 + rho <= R := by
    simpa [isingLeapfrogBoxReflectX] using htop
  have hrefBoundary : isingLeapfrogBoxBoundary R
      (isingLeapfrogBoxReflectX R q) :=
    (isingLeapfrogBoxBoundary_reflectX_iff R q).2 hqBoundary
  exact (div_le_div_of_nonneg_right hcardReal (by positivity)).trans
    (sourceChoiceNoHitOutputAt_boundary_diffusive_weight_le R (R - level) rho
      (isingLeapfrogBoxReflectX R p') (isingLeapfrogBoxReflectX R q)
      hrefStart hρ (by omega) (Nat.sub_le ..) hrefBottom hrefTop hrefBoundary)

private noncomputable def choiceNoHitAtOutputCover
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    IsingLeapfrogChoiceNoHitAtFamily R t p p' q level ->
      Sum (IsingSourceChoiceNoHitOutputAtFamily R t p q level)
        (IsingMirrorChoiceNoHitOutputAtFamily R t p p' q level) := fun w => by
  classical
  by_cases hs : isingLeapfrogChoiceRun R p w.1.1 = q
  · exact Sum.inl ⟨w.1, w.2.1, hs⟩
  · exact Sum.inr ⟨w.1, w.2.1, w.2.2.resolve_left hs⟩

private def choiceNoHitAtOutputCoverValue
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Sum (IsingSourceChoiceNoHitOutputAtFamily R t p q level)
        (IsingMirrorChoiceNoHitOutputAtFamily R t p p' q level) ->
      IsingLeapfrogChoiceStringFamily t :=
  Sum.elim (fun w => w.1) (fun w => w.1)

private theorem choiceNoHitAtOutputCover_value
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int)
    (w : IsingLeapfrogChoiceNoHitAtFamily R t p p' q level) :
    choiceNoHitAtOutputCoverValue R t p p' q level
      (choiceNoHitAtOutputCover R t p p' q level w) = w.1 := by
  classical
  by_cases hs : isingLeapfrogChoiceRun R p w.1.1 = q
  · simp [choiceNoHitAtOutputCover, hs, choiceNoHitAtOutputCoverValue]
  · simp [choiceNoHitAtOutputCover, hs, choiceNoHitAtOutputCoverValue]

private theorem choiceNoHitAtOutputCover_injective
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Function.Injective (choiceNoHitAtOutputCover R t p p' q level) := by
  intro a b hab
  apply Subtype.ext
  rw [← choiceNoHitAtOutputCover_value R t p p' q level a,
    ← choiceNoHitAtOutputCover_value R t p p' q level b, hab]

theorem natCard_choiceNoHitAt_le_source_add_mirror
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Nat.card (IsingLeapfrogChoiceNoHitAtFamily R t p p' q level) <=
      Nat.card (IsingSourceChoiceNoHitOutputAtFamily R t p q level) +
        Nat.card (IsingMirrorChoiceNoHitOutputAtFamily R t p p' q level) := by
  calc
    _ <= Nat.card
        (Sum (IsingSourceChoiceNoHitOutputAtFamily R t p q level)
          (IsingMirrorChoiceNoHitOutputAtFamily R t p p' q level)) :=
      Nat.card_le_card_of_injective
        (choiceNoHitAtOutputCover R t p p' q level)
        (choiceNoHitAtOutputCover_injective R t p p' q level)
    _ = _ := Nat.card_sum

theorem choiceNoHitAt_boundary_diffusive_weight_le_of_rightHalf
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hleft : rho <= level)
    (hright : level + rho <= R)
    (hbottom : rho <= p.2.1) (htop : p.2.1 + rho <= R)
    (hbottom' : rho <= p'.2.1) (htop' : p'.2.1 + rho <= R)
    (hqBoundary : isingLeapfrogBoxBoundary R q) :
    Nat.card (IsingLeapfrogChoiceNoHitAtFamily
        R (rho * rho) p p' q (level : Int)) /
        (4 : Real) ^ (rho * rho) <=
      936 / (rho : Real) ^ 2 := by
  have hcard := natCard_choiceNoHitAt_le_source_add_mirror
    R (rho * rho) p p' q (level : Int)
  have hcardReal :
      (Nat.card (IsingLeapfrogChoiceNoHitAtFamily
        R (rho * rho) p p' q (level : Int)) : Real) <=
      Nat.card (IsingSourceChoiceNoHitOutputAtFamily
        R (rho * rho) p q (level : Int)) +
      Nat.card (IsingMirrorChoiceNoHitOutputAtFamily
        R (rho * rho) p p' q (level : Int)) := by
    exact_mod_cast hcard
  have hsource := sourceChoiceNoHitOutputAt_boundary_diffusive_weight_le
    R level rho p q hstart hρ hleft (by omega) hbottom htop hqBoundary
  have hmirrorBound := mirrorChoiceNoHitOutputAt_boundary_diffusive_weight_le
    R level rho p p' q hstart hmirror hρ hright hbottom' htop' hqBoundary
  calc
    _ <= (Nat.card (IsingSourceChoiceNoHitOutputAtFamily
          R (rho * rho) p q (level : Int)) +
        Nat.card (IsingMirrorChoiceNoHitOutputAtFamily
          R (rho * rho) p p' q (level : Int))) /
          (4 : Real) ^ (rho * rho) :=
      div_le_div_of_nonneg_right hcardReal (by positivity)
    _ = Nat.card (IsingSourceChoiceNoHitOutputAtFamily
          R (rho * rho) p q (level : Int)) / (4 : Real) ^ (rho * rho) +
        Nat.card (IsingMirrorChoiceNoHitOutputAtFamily
          R (rho * rho) p p' q (level : Int)) / (4 : Real) ^ (rho * rho) := by
      rw [add_div]
    _ <= 468 / (rho : Real) ^ 2 + 468 / (rho : Real) ^ 2 :=
      add_le_add hsource hmirrorBound
    _ = 936 / (rho : Real) ^ 2 := by ring

theorem isingLeapfrogStoppedKernel_reflectedStart_boundary_diffusive_abs_le_of_rightHalf
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hleft : rho <= level)
    (hright : level + rho <= R) (hhalf : R <= 2 * level)
    (hbottom : rho <= p.2.1) (htop : p.2.1 + rho <= R)
    (hbottom' : rho <= p'.2.1) (htop' : p'.2.1 + rho <= R)
    (hqBoundary : isingLeapfrogBoxBoundary R q) :
    |isingLeapfrogStoppedKernel R (rho * rho) p q -
        isingLeapfrogStoppedKernel R (rho * rho) p' q| <=
      10296 / (rho : Real) ^ 2 := by
  have hnoHit := choiceNoHitAt_boundary_diffusive_weight_le_of_rightHalf
    R level rho p p' q hstart hmirror hρ hleft hright hbottom htop
      hbottom' htop' hqBoundary
  have hsource := sourceFailureAt_boundary_diffusive_weight_le_of_rightHalf
    R level rho p p' q hstart hmirror hρ hleft (by omega) hright hhalf
      hbottom htop hbottom' htop' hqBoundary
  have hmirrorFailure := mirrorFailureAt_boundary_diffusive_weight_le_of_rightHalf
    R level rho p p' q hstart hmirror hρ hleft hright hhalf hbottom htop
      hbottom' htop' hqBoundary
  apply isingLeapfrogStoppedKernel_reflectedStart_abs_le_of_endpointFailures
    R (rho * rho) p p' q (level : Int) hmirror
  calc
    ((Nat.card (IsingLeapfrogChoiceNoHitAtFamily
          R (rho * rho) p p' q (level : Int)) +
        Nat.card (IsingStoppedCouplingSourceFailureAtFamily
          R (rho * rho) p p' q (level : Int)) +
        Nat.card (IsingStoppedCouplingMirrorFailureAtFamily
          R (rho * rho) p p' q (level : Int)) : Nat) : Real) /
        (4 : Real) ^ (rho * rho) =
      Nat.card (IsingLeapfrogChoiceNoHitAtFamily
          R (rho * rho) p p' q (level : Int)) / (4 : Real) ^ (rho * rho) +
      Nat.card (IsingStoppedCouplingSourceFailureAtFamily
          R (rho * rho) p p' q (level : Int)) / (4 : Real) ^ (rho * rho) +
      Nat.card (IsingStoppedCouplingMirrorFailureAtFamily
          R (rho * rho) p p' q (level : Int)) / (4 : Real) ^ (rho * rho) := by
        push_cast
        ring
    _ <= 936 / (rho : Real) ^ 2 + 936 / (rho : Real) ^ 2 +
        8424 / (rho : Real) ^ 2 :=
      add_le_add (add_le_add hnoHit hsource) hmirrorFailure
    _ = 10296 / (rho : Real) ^ 2 := by ring

theorem sourceFailureOutputAt_horizontal_diffusive_weight_le
    (R level rho : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hleft : rho <= level) (hlevelR : level < R)
    (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
    Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q
        (level : Int)) / (4 : Real) ^ (rho * rho) <=
      468 / (rho : Real) ^ 2 := by
  rcases hqHorizontal with hqLeft | hqRight
  · exact sourceFailureOutputAt_left_diffusive_weight_le R level rho p q
      hstart hqLeft hρ hleft
  · rw [sourceFailureOutputAt_right_card_eq_zero R level (rho * rho) p q
      hstart hlevelR hqRight]
    have hnonneg : 0 <= (468 : Real) / (rho : Real) ^ 2 := by positivity
    simpa using hnonneg

theorem mirrorFailureOutputAt_horizontal_diffusive_weight_le
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hleft : rho <= level)
    (hright : level + rho <= R)
    (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
    Nat.card (IsingMirrorFailureOutputAtFamily R (rho * rho) p p' q
        (level : Int)) / (4 : Real) ^ (rho * rho) <=
      468 / (rho : Real) ^ 2 := by
  have hlevelR : level <= R := by omega
  have hcard := Nat.card_le_card_of_injective
    (mirrorFailureOutputReflectX R (rho * rho) level p p' q hmirror hlevelR)
    (mirrorFailureOutputReflectX_injective R (rho * rho) level p p' q
      hmirror hlevelR)
  have hcardReal :
      (Nat.card (IsingMirrorFailureOutputAtFamily R (rho * rho) p p' q
        (level : Int)) : Real) <=
      Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho)
        (isingLeapfrogBoxReflectX R p') (isingLeapfrogBoxReflectX R q)
        ((R - level : Nat) : Int)) := by exact_mod_cast hcard
  have hp'x : (isingLeapfrogBoxInt p').1 = (level : Int) + 1 := by
    rw [hmirror]
    unfold reflectedEndpoint
    dsimp
    omega
  have hrefStart :
      (isingLeapfrogBoxInt (isingLeapfrogBoxReflectX R p')).1 + 1 =
        (R - level : Nat) := by
    rw [boxInt_reflectX]
    dsimp
    have hcast : ((R - level : Nat) : Int) = (R : Int) - level := by
      rw [Nat.cast_sub hlevelR]
    rw [hcast, hp'x]
    omega
  have hrefHorizontal :
      (isingLeapfrogBoxReflectX R q).1.1 = 0 ∨
        (isingLeapfrogBoxReflectX R q).1.1 = R := by
    rcases hqHorizontal with hq0 | hqR
    · right
      simp [isingLeapfrogBoxReflectX, hq0]
    · left
      simp [isingLeapfrogBoxReflectX, hqR]
  exact (div_le_div_of_nonneg_right hcardReal (by positivity)).trans
    (sourceFailureOutputAt_horizontal_diffusive_weight_le R (R - level) rho
      (isingLeapfrogBoxReflectX R p') (isingLeapfrogBoxReflectX R q)
      hrefStart hρ (by omega) (by omega) hrefHorizontal)

theorem sourceFailureAt_horizontal_diffusive_weight_le_of_rightHalf
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hleft : rho <= level) (hlevelR : level < R)
    (hright : level + rho <= R) (hhalf : R <= 2 * level)
    (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
    Nat.card (IsingStoppedCouplingSourceFailureAtFamily R (rho * rho)
        p p' q (level : Int)) / (4 : Real) ^ (rho * rho) <=
      936 / (rho : Real) ^ 2 := by
  have hcard := Nat.card_le_card_of_injective
    (sourceFailureAtAlignedCover_of_rightHalf R level (rho * rho) p p' q
      hstart hmirror hlevelR hhalf)
    (sourceFailureAtAlignedCover_of_rightHalf_injective R level (rho * rho)
      p p' q hstart hmirror hlevelR hhalf)
  rw [Nat.card_sum] at hcard
  have hcardReal :
      (Nat.card (IsingStoppedCouplingSourceFailureAtFamily R (rho * rho)
        p p' q (level : Int)) : Real) <=
      Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q
        (level : Int)) +
      Nat.card (IsingMirrorFailureOutputAtFamily R (rho * rho) p p' q
        (level : Int)) := by exact_mod_cast hcard
  calc
    _ <= (Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q
          (level : Int)) +
        Nat.card (IsingMirrorFailureOutputAtFamily R (rho * rho) p p' q
          (level : Int))) / (4 : Real) ^ (rho * rho) :=
      div_le_div_of_nonneg_right hcardReal (by positivity)
    _ = Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q
          (level : Int)) / (4 : Real) ^ (rho * rho) +
        Nat.card (IsingMirrorFailureOutputAtFamily R (rho * rho) p p' q
          (level : Int)) / (4 : Real) ^ (rho * rho) := by rw [add_div]
    _ <= 468 / (rho : Real) ^ 2 + 468 / (rho : Real) ^ 2 := add_le_add
      (sourceFailureOutputAt_horizontal_diffusive_weight_le R level rho p q
        hstart hρ hleft hlevelR hqHorizontal)
      (mirrorFailureOutputAt_horizontal_diffusive_weight_le R level rho p p' q
        hstart hmirror hρ hleft hright hqHorizontal)
    _ = 936 / (rho : Real) ^ 2 := by ring

theorem mirrorFailureAt_horizontal_diffusive_weight_le_of_rightHalf
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hleft : rho <= level)
    (hright : level + rho <= R) (hhalf : R <= 2 * level)
    (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
    Nat.card (IsingStoppedCouplingMirrorFailureAtFamily R (rho * rho)
        p p' q (level : Int)) / (4 : Real) ^ (rho * rho) <=
      1404 / (rho : Real) ^ 2 := by
  have hcard := natCard_mirrorFailureAt_le_aligned_add_residual
    R (rho * rho) p p' q (level : Int)
  have hcardReal :
      (Nat.card (IsingStoppedCouplingMirrorFailureAtFamily R (rho * rho)
        p p' q (level : Int)) : Real) <=
      Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q
        (level : Int)) +
      Nat.card (IsingMirrorFailureOutputAtFamily R (rho * rho) p p' q
        (level : Int)) +
      Nat.card (IsingMirrorOnlySourceOutputAtFamily R (rho * rho) p p' q
        (level : Int)) := by exact_mod_cast hcard
  have hsource := sourceFailureOutputAt_horizontal_diffusive_weight_le
    R level rho p q hstart hρ hleft (by omega) hqHorizontal
  have hmirrorBound := mirrorFailureOutputAt_horizontal_diffusive_weight_le
    R level rho p p' q hstart hmirror hρ hleft hright hqHorizontal
  have hresidual := mirrorOnlySourceOutputAt_horizontal_diffusive_weight_le
    R level rho p p' q hstart hmirror hρ hright hhalf hqHorizontal
  calc
    _ <= (Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q
          (level : Int)) +
        Nat.card (IsingMirrorFailureOutputAtFamily R (rho * rho) p p' q
          (level : Int)) +
        Nat.card (IsingMirrorOnlySourceOutputAtFamily R (rho * rho) p p' q
          (level : Int))) / (4 : Real) ^ (rho * rho) :=
      div_le_div_of_nonneg_right hcardReal (by positivity)
    _ = Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q
          (level : Int)) / (4 : Real) ^ (rho * rho) +
        Nat.card (IsingMirrorFailureOutputAtFamily R (rho * rho) p p' q
          (level : Int)) / (4 : Real) ^ (rho * rho) +
        Nat.card (IsingMirrorOnlySourceOutputAtFamily R (rho * rho) p p' q
          (level : Int)) / (4 : Real) ^ (rho * rho) := by ring
    _ <= 468 / (rho : Real) ^ 2 + 468 / (rho : Real) ^ 2 +
        468 / (rho : Real) ^ 2 :=
      add_le_add (add_le_add hsource hmirrorBound) hresidual
    _ = 1404 / (rho : Real) ^ 2 := by ring

theorem mirrorChoiceNoHitOutputAt_horizontal_diffusive_weight_le
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hright : level + rho <= R)
    (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
    Nat.card (IsingMirrorChoiceNoHitOutputAtFamily R (rho * rho) p p' q
        (level : Int)) / (4 : Real) ^ (rho * rho) <=
      468 / (rho : Real) ^ 2 := by
  have hlevelR : level <= R := by omega
  have hcard := Nat.card_le_card_of_injective
    (mirrorNoHitOutputReflectX R (rho * rho) level p p' q hstart hmirror
      hlevelR)
    (mirrorNoHitOutputReflectX_injective R (rho * rho) level p p' q hstart
      hmirror hlevelR)
  have hcardReal :
      (Nat.card (IsingMirrorChoiceNoHitOutputAtFamily R (rho * rho) p p' q
        (level : Int)) : Real) <=
      Nat.card (IsingSourceChoiceNoHitOutputAtFamily R (rho * rho)
        (isingLeapfrogBoxReflectX R p') (isingLeapfrogBoxReflectX R q)
        ((R - level : Nat) : Int)) := by exact_mod_cast hcard
  have hp'x : (isingLeapfrogBoxInt p').1 = (level : Int) + 1 := by
    rw [hmirror]
    unfold reflectedEndpoint
    dsimp
    omega
  have hrefStart :
      (isingLeapfrogBoxInt (isingLeapfrogBoxReflectX R p')).1 + 1 =
        (R - level : Nat) := by
    rw [boxInt_reflectX]
    dsimp
    have hcast : ((R - level : Nat) : Int) = (R : Int) - level := by
      rw [Nat.cast_sub hlevelR]
    rw [hcast, hp'x]
    omega
  have hrefHorizontal :
      (isingLeapfrogBoxReflectX R q).1.1 = 0 ∨
        (isingLeapfrogBoxReflectX R q).1.1 = R := by
    rcases hqHorizontal with hq0 | hqR
    · right; simp [isingLeapfrogBoxReflectX, hq0]
    · left; simp [isingLeapfrogBoxReflectX, hqR]
  exact (div_le_div_of_nonneg_right hcardReal (by positivity)).trans
    (sourceChoiceNoHitOutputAt_horizontal_diffusive_weight_le R (R - level)
      rho (isingLeapfrogBoxReflectX R p') (isingLeapfrogBoxReflectX R q)
      hrefStart hρ (by omega) (Nat.sub_le ..) hrefHorizontal)

theorem choiceNoHitAt_horizontal_diffusive_weight_le_of_rightHalf
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hleft : rho <= level)
    (hright : level + rho <= R)
    (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
    Nat.card (IsingLeapfrogChoiceNoHitAtFamily R (rho * rho) p p' q
        (level : Int)) / (4 : Real) ^ (rho * rho) <=
      936 / (rho : Real) ^ 2 := by
  have hcard := natCard_choiceNoHitAt_le_source_add_mirror
    R (rho * rho) p p' q (level : Int)
  have hcardReal :
      (Nat.card (IsingLeapfrogChoiceNoHitAtFamily R (rho * rho) p p' q
        (level : Int)) : Real) <=
      Nat.card (IsingSourceChoiceNoHitOutputAtFamily R (rho * rho) p q
        (level : Int)) +
      Nat.card (IsingMirrorChoiceNoHitOutputAtFamily R (rho * rho) p p' q
        (level : Int)) := by exact_mod_cast hcard
  calc
    _ <= (Nat.card (IsingSourceChoiceNoHitOutputAtFamily R (rho * rho) p q
          (level : Int)) +
        Nat.card (IsingMirrorChoiceNoHitOutputAtFamily R (rho * rho) p p' q
          (level : Int))) / (4 : Real) ^ (rho * rho) :=
      div_le_div_of_nonneg_right hcardReal (by positivity)
    _ = Nat.card (IsingSourceChoiceNoHitOutputAtFamily R (rho * rho) p q
          (level : Int)) / (4 : Real) ^ (rho * rho) +
        Nat.card (IsingMirrorChoiceNoHitOutputAtFamily R (rho * rho) p p' q
          (level : Int)) / (4 : Real) ^ (rho * rho) := by rw [add_div]
    _ <= 468 / (rho : Real) ^ 2 + 468 / (rho : Real) ^ 2 := add_le_add
      (sourceChoiceNoHitOutputAt_horizontal_diffusive_weight_le R level rho
        p q hstart hρ hleft (by omega) hqHorizontal)
      (mirrorChoiceNoHitOutputAt_horizontal_diffusive_weight_le R level rho
        p p' q hstart hmirror hρ hright hqHorizontal)
    _ = 936 / (rho : Real) ^ 2 := by ring

theorem isingLeapfrogStoppedKernel_reflectedStart_horizontalEndpoint_diffusive_abs_le_of_rightHalf
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hleft : rho <= level)
    (hright : level + rho <= R) (hhalf : R <= 2 * level)
    (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
    |isingLeapfrogStoppedKernel R (rho * rho) p q -
        isingLeapfrogStoppedKernel R (rho * rho) p' q| <=
      3276 / (rho : Real) ^ 2 := by
  have hnoHit := choiceNoHitAt_horizontal_diffusive_weight_le_of_rightHalf
    R level rho p p' q hstart hmirror hρ hleft hright hqHorizontal
  have hsource := sourceFailureAt_horizontal_diffusive_weight_le_of_rightHalf
    R level rho p p' q hstart hmirror hρ hleft (by omega) hright hhalf
      hqHorizontal
  have hmirrorFailure :=
    mirrorFailureAt_horizontal_diffusive_weight_le_of_rightHalf
      R level rho p p' q hstart hmirror hρ hleft hright hhalf hqHorizontal
  apply isingLeapfrogStoppedKernel_reflectedStart_abs_le_of_endpointFailures
    R (rho * rho) p p' q (level : Int) hmirror
  calc
    ((Nat.card (IsingLeapfrogChoiceNoHitAtFamily R (rho * rho) p p' q
          (level : Int)) +
        Nat.card (IsingStoppedCouplingSourceFailureAtFamily R (rho * rho)
          p p' q (level : Int)) +
        Nat.card (IsingStoppedCouplingMirrorFailureAtFamily R (rho * rho)
          p p' q (level : Int)) : Nat) : Real) /
        (4 : Real) ^ (rho * rho) =
      Nat.card (IsingLeapfrogChoiceNoHitAtFamily R (rho * rho) p p' q
          (level : Int)) / (4 : Real) ^ (rho * rho) +
      Nat.card (IsingStoppedCouplingSourceFailureAtFamily R (rho * rho)
          p p' q (level : Int)) / (4 : Real) ^ (rho * rho) +
      Nat.card (IsingStoppedCouplingMirrorFailureAtFamily R (rho * rho)
          p p' q (level : Int)) / (4 : Real) ^ (rho * rho) := by
        push_cast
        ring
    _ <= 936 / (rho : Real) ^ 2 + 936 / (rho : Real) ^ 2 +
        1404 / (rho : Real) ^ 2 :=
      add_le_add (add_le_add hnoHit hsource) hmirrorFailure
    _ = 3276 / (rho : Real) ^ 2 := by ring

end

end StatMech.Universality
