/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicReflectionEstimates







namespace StatMech.Universality

open Finset
open IsingDiagonalWalkHitSplit

noncomputable section


def isingLeapfrogChoiceNext (R : Nat) (p : IsingLeapfrogBox R)
    (b : Bool × Bool) : IsingLeapfrogBox R :=
  if hp : isingLeapfrogBoxBoundary R p then p
  else match b with
    | (false, false) => isingLeapfrogSW R p
    | (true, false) => isingLeapfrogSE R p hp
    | (false, true) => isingLeapfrogNW R p hp
    | (true, true) => isingLeapfrogNE R p hp


def isingLeapfrogChoiceRun (R : Nat) :
    IsingLeapfrogBox R → List (Bool × Bool) → IsingLeapfrogBox R
  | p, [] => p
  | p, b :: bs =>
      isingLeapfrogChoiceRun R (isingLeapfrogChoiceNext R p b) bs


def IsingLeapfrogStoppedChoicePathFamily (R t : Nat)
    (p q : IsingLeapfrogBox R) :=
  {bs : List (Bool × Bool) //
    bs.length = t ∧ isingLeapfrogChoiceRun R p bs = q}

noncomputable instance isingLeapfrogStoppedChoicePathFamily_finite
    (R t : Nat) (p q : IsingLeapfrogBox R) :
    Finite (IsingLeapfrogStoppedChoicePathFamily R t p q) := by
  letI : Fintype {bs : List (Bool × Bool) // bs.length = t} :=
    (List.finite_length_eq (Bool × Bool) t).fintype
  exact Finite.of_injective
    (fun w : IsingLeapfrogStoppedChoicePathFamily R t p q =>
      (⟨w.1, w.2.1⟩ : {bs : List (Bool × Bool) // bs.length = t}))
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg
        (fun z : {bs : List (Bool × Bool) // bs.length = t} => z.1) h)

private def stoppedChoicePathFamilySuccEquiv (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    IsingLeapfrogStoppedChoicePathFamily R (t + 1) p q ≃
      Σ b : Bool × Bool,
        IsingLeapfrogStoppedChoicePathFamily R t
          (isingLeapfrogChoiceNext R p b) q where
  toFun w := by
    rcases w with ⟨bs, hlen, hend⟩
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
        exact ⟨b, ⟨bs, by simpa using hlen, by
          simpa [isingLeapfrogChoiceRun] using hend⟩⟩
  invFun w := ⟨w.1 :: w.2.1, by simp [w.2.2.1], by
    simpa [isingLeapfrogChoiceRun] using w.2.2.2⟩
  left_inv w := by
    rcases w with ⟨bs, hlen, hend⟩
    cases bs with
    | nil => simp at hlen
    | cons b bs => rfl
  right_inv w := by
    rcases w with ⟨b, bs, hlen, hend⟩
    rfl

private def stoppedChoicePathFamilyZeroSelfEquiv (R : Nat)
    (p : IsingLeapfrogBox R) :
    IsingLeapfrogStoppedChoicePathFamily R 0 p p ≃ ULift.{1, 0} Unit where
  toFun _ := ⟨Unit.unit⟩
  invFun _ := ⟨[], rfl, rfl⟩
  left_inv w := by
    apply Subtype.ext
    exact (List.eq_nil_of_length_eq_zero w.2.1).symm
  right_inv _ := rfl

private def stoppedChoicePathFamilyZeroNeEquiv (R : Nat)
    (p q : IsingLeapfrogBox R) (hpq : p ≠ q) :
    IsingLeapfrogStoppedChoicePathFamily R 0 p q ≃ Empty where
  toFun w := by
    have hnil : w.1 = [] := List.eq_nil_of_length_eq_zero w.2.1
    have : p = q := by simpa [hnil, isingLeapfrogChoiceRun] using w.2.2
    exact (hpq this).elim
  invFun e := e.elim
  left_inv w := (hpq (by
    have hnil : w.1 = [] := List.eq_nil_of_length_eq_zero w.2.1
    simpa [hnil, isingLeapfrogChoiceRun] using w.2.2)).elim
  right_inv e := e.elim



theorem isingLeapfrogStoppedKernel_eq_natCard_choicePath_div
    (R t : Nat) (p q : IsingLeapfrogBox R) :
    isingLeapfrogStoppedKernel R t p q =
      Nat.card (IsingLeapfrogStoppedChoicePathFamily R t p q) /
        (4 : Real) ^ t := by
  induction t generalizing p with
  | zero =>
      by_cases hpq : p = q
      · subst q
        rw [Nat.card_congr (stoppedChoicePathFamilyZeroSelfEquiv R p)]
        simp [isingLeapfrogStoppedKernel]
      · rw [Nat.card_congr
          (stoppedChoicePathFamilyZeroNeEquiv R p q hpq)]
        simp [isingLeapfrogStoppedKernel, hpq]
  | succ t ih =>
      rw [isingLeapfrogStoppedKernel_succ]
      rw [Nat.card_congr (stoppedChoicePathFamilySuccEquiv R t p q),
        Nat.card_sigma, Fintype.sum_prod_type]
      by_cases hp : isingLeapfrogBoxBoundary R p
      · simp only [dif_pos hp, isingLeapfrogChoiceNext, hp, ↓reduceDIte]
        rw [ih]
        simp
        rw [pow_succ]
        ring
      · simp only [dif_neg hp, isingLeapfrogChoiceNext, hp, ↓reduceDIte]
        rw [ih, ih, ih, ih]
        simp
        push_cast
        rw [pow_succ]
        ring



def IsingLeapfrogKilledChoiceValid (R : Nat) :
    IsingLeapfrogBox R → List (Bool × Bool) → Prop
  | p, [] => ¬ isingLeapfrogBoxBoundary R p
  | p, b :: bs =>
      ¬ isingLeapfrogBoxBoundary R p ∧
        IsingLeapfrogKilledChoiceValid R
          (isingLeapfrogChoiceNext R p b) bs

def IsingLeapfrogKilledChoicePathFamily (R t : Nat)
    (p q : IsingLeapfrogBox R) :=
  {bs : List (Bool × Bool) //
    bs.length = t ∧ IsingLeapfrogKilledChoiceValid R p bs ∧
      isingLeapfrogChoiceRun R p bs = q}

noncomputable instance isingLeapfrogKilledChoicePathFamily_finite
    (R t : Nat) (p q : IsingLeapfrogBox R) :
    Finite (IsingLeapfrogKilledChoicePathFamily R t p q) := by
  letI : Fintype {bs : List (Bool × Bool) // bs.length = t} :=
    (List.finite_length_eq (Bool × Bool) t).fintype
  exact Finite.of_injective
    (fun w : IsingLeapfrogKilledChoicePathFamily R t p q =>
      (⟨w.1, w.2.1⟩ : {bs : List (Bool × Bool) // bs.length = t}))
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg
        (fun z : {bs : List (Bool × Bool) // bs.length = t} => z.1) h)

theorem IsingLeapfrogKilledChoiceValid.start_not_boundary
    (R : Nat) (p : IsingLeapfrogBox R) (bs : List (Bool × Bool))
    (h : IsingLeapfrogKilledChoiceValid R p bs) :
    ¬ isingLeapfrogBoxBoundary R p := by
  cases bs with
  | nil => exact h
  | cons b bs => exact h.1

theorem IsingLeapfrogKilledChoiceValid.endpoint_not_boundary
    (R : Nat) (p : IsingLeapfrogBox R) (bs : List (Bool × Bool))
    (h : IsingLeapfrogKilledChoiceValid R p bs) :
    ¬ isingLeapfrogBoxBoundary R (isingLeapfrogChoiceRun R p bs) := by
  induction bs generalizing p with
  | nil => exact h
  | cons b bs ih =>
      exact ih (isingLeapfrogChoiceNext R p b) h.2

private def killedChoicePathFamilyEmptyEquiv
    (R t : Nat) (p q : IsingLeapfrogBox R)
    (h : ∀ w : IsingLeapfrogKilledChoicePathFamily R t p q, False) :
    IsingLeapfrogKilledChoicePathFamily R t p q ≃ Empty where
  toFun w := (h w).elim
  invFun e := e.elim
  left_inv w := (h w).elim
  right_inv e := e.elim

private def killedChoicePathFamilySuccEquiv (R t : Nat)
    (p q : IsingLeapfrogBox R) (hp : ¬ isingLeapfrogBoxBoundary R p) :
    IsingLeapfrogKilledChoicePathFamily R (t + 1) p q ≃
      Σ b : Bool × Bool,
        IsingLeapfrogKilledChoicePathFamily R t
          (isingLeapfrogChoiceNext R p b) q where
  toFun w := by
    rcases w with ⟨bs, hlen, hvalid, hend⟩
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
        exact ⟨b, ⟨bs, by simpa using hlen, hvalid.2, by
          simpa [isingLeapfrogChoiceRun] using hend⟩⟩
  invFun w := ⟨w.1 :: w.2.1, by simp [w.2.2.1],
    ⟨hp, w.2.2.2.1⟩, by
      simpa [isingLeapfrogChoiceRun] using w.2.2.2.2⟩
  left_inv w := by
    rcases w with ⟨bs, hlen, hvalid, hend⟩
    cases bs with
    | nil => simp at hlen
    | cons b bs => rfl
  right_inv w := by
    rcases w with ⟨b, bs, hlen, hvalid, hend⟩
    rfl

private def killedChoicePathFamilyZeroSelfEquiv (R : Nat)
    (p : IsingLeapfrogBox R) (hp : ¬ isingLeapfrogBoxBoundary R p) :
    IsingLeapfrogKilledChoicePathFamily R 0 p p ≃ ULift.{1, 0} Unit where
  toFun _ := ⟨Unit.unit⟩
  invFun _ := ⟨[], rfl, hp, rfl⟩
  left_inv w := by
    apply Subtype.ext
    exact (List.eq_nil_of_length_eq_zero w.2.1).symm
  right_inv _ := rfl



theorem isingLeapfrogKilledKernel_eq_natCard_choicePath_div
    (R t : Nat) (p q : IsingLeapfrogBox R) :
    isingLeapfrogKilledKernel R t p q =
      Nat.card (IsingLeapfrogKilledChoicePathFamily R t p q) /
        (4 : Real) ^ t := by
  induction t generalizing p with
  | zero =>
      by_cases hq : isingLeapfrogBoxBoundary R q
      · have hempty :
            ∀ w : IsingLeapfrogKilledChoicePathFamily R 0 p q, False := by
          intro w
          have hfinal := w.2.2.1.endpoint_not_boundary R p w.1
          have : ¬ isingLeapfrogBoxBoundary R q := by
            simpa [w.2.2.2] using hfinal
          exact this hq
        rw [Nat.card_congr
          (killedChoicePathFamilyEmptyEquiv R 0 p q hempty)]
        simp [isingLeapfrogKilledKernel, hq]
      · by_cases hpq : p = q
        · subst q
          rw [Nat.card_congr (killedChoicePathFamilyZeroSelfEquiv R p hq)]
          simp [isingLeapfrogKilledKernel, hq, isingLeapfrogStoppedKernel]
        · rw [Nat.card_congr (killedChoicePathFamilyEmptyEquiv R 0 p q
              (fun w => hpq (by
                have hnil : w.1 = [] :=
                  List.eq_nil_of_length_eq_zero w.2.1
                simpa [hnil, isingLeapfrogChoiceRun] using w.2.2.2)))]
          simp [isingLeapfrogKilledKernel, hq, isingLeapfrogStoppedKernel,
            hpq]
  | succ t ih =>
      by_cases hq : isingLeapfrogBoxBoundary R q
      · have hempty :
            ∀ w : IsingLeapfrogKilledChoicePathFamily R (t + 1) p q,
              False := by
          intro w
          have hfinal := w.2.2.1.endpoint_not_boundary R p w.1
          have : ¬ isingLeapfrogBoxBoundary R q := by
            simpa [w.2.2.2] using hfinal
          exact this hq
        rw [Nat.card_congr
          (killedChoicePathFamilyEmptyEquiv R (t + 1) p q hempty)]
        simp [isingLeapfrogKilledKernel, hq]
      · by_cases hp : isingLeapfrogBoxBoundary R p
        · rw [Nat.card_congr (killedChoicePathFamilyEmptyEquiv R (t + 1)
              p q (fun w =>
                w.2.2.1.start_not_boundary R p w.1 hp))]
          simp [isingLeapfrogKilledKernel, hq,
            isingLeapfrogStoppedKernel_of_boundary R (t + 1) p q hp,
            show p ≠ q from fun hpq => hq (hpq ▸ hp)]
        · rw [Nat.card_congr
              (killedChoicePathFamilySuccEquiv R t p q hp),
            Nat.card_sigma, Fintype.sum_prod_type]
          simp only [isingLeapfrogKilledKernel, if_neg hq,
            isingLeapfrogStoppedKernel, dif_neg hp,
            isingLeapfrogChoiceNext, hp, ↓reduceDIte]
          have hSW := ih (isingLeapfrogSW R p)
          have hSE := ih (isingLeapfrogSE R p hp)
          have hNW := ih (isingLeapfrogNW R p hp)
          have hNE := ih (isingLeapfrogNE R p hp)
          simp only [isingLeapfrogKilledKernel, if_neg hq] at hSW hSE hNW hNE
          rw [hSW, hSE, hNW, hNE]
          simp
          push_cast
          rw [pow_succ]
          ring

def isingLeapfrogChoiceStep (b : Bool × Bool) : Int × Int :=
  (if b.1 then 1 else -1, if b.2 then 1 else -1)

def isingLeapfrogChoiceSteps (bs : List (Bool × Bool)) : List (Int × Int) :=
  bs.map isingLeapfrogChoiceStep

def isingLeapfrogBoxInt {R : Nat} (p : IsingLeapfrogBox R) : Int × Int :=
  ((p.1.1 : Int), (p.2.1 : Int))

theorem isingLeapfrogChoiceSteps_valid (bs : List (Bool × Bool)) :
    IsingDiagonalWalkStepsValid (isingLeapfrogChoiceSteps bs) := by
  intro d hd
  simp only [isingLeapfrogChoiceSteps, List.mem_map] at hd
  rcases hd with ⟨b, hb, rfl⟩
  cases b with
  | mk bx byy =>
      cases bx <;> cases byy <;> simp [isingLeapfrogChoiceStep]

private theorem isingLeapfrogBoxInt_choiceNext
    (R : Nat) (p : IsingLeapfrogBox R) (b : Bool × Bool)
    (hp : ¬ isingLeapfrogBoxBoundary R p) :
    isingLeapfrogBoxInt (isingLeapfrogChoiceNext R p b) =
      isingDiagonalWalkNext (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceStep b) := by
  rcases b with ⟨bx, byy⟩
  cases bx <;> cases byy <;>
    simp only [isingLeapfrogChoiceNext, hp, ↓reduceDIte]
  all_goals
    apply Prod.ext <;>
      simp [isingLeapfrogBoxInt, isingLeapfrogChoiceStep,
        isingDiagonalWalkNext, isingLeapfrogSW, isingLeapfrogSE,
        isingLeapfrogNW, isingLeapfrogNE, isingLeapfrogWest,
        isingLeapfrogEast, isingLeapfrogSouth, isingLeapfrogNorth] <;>
      unfold isingLeapfrogBoxBoundary at hp <;> omega

theorem IsingLeapfrogKilledChoiceValid.run_boxInt_eq_endpoint
    (R : Nat) (p : IsingLeapfrogBox R) (bs : List (Bool × Bool))
    (h : IsingLeapfrogKilledChoiceValid R p bs) :
    isingLeapfrogBoxInt (isingLeapfrogChoiceRun R p bs) =
      isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceSteps bs) := by
  induction bs generalizing p with
  | nil =>
      simp [isingLeapfrogChoiceRun, isingLeapfrogChoiceSteps,
        isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement]
  | cons b bs ih =>
      rw [show isingLeapfrogChoiceRun R p (b :: bs) =
          isingLeapfrogChoiceRun R (isingLeapfrogChoiceNext R p b) bs by
        rfl]
      rw [ih (isingLeapfrogChoiceNext R p b) h.2]
      rw [isingLeapfrogBoxInt_choiceNext R p b h.1]
      unfold isingLeapfrogChoiceSteps isingDiagonalWalkEndpoint
        isingDiagonalWalkNext isingDiagonalWalkDisplacement
      apply Prod.ext <;> simp <;> ring

theorem IsingLeapfrogKilledChoiceValid.take
    (R : Nat) (p : IsingLeapfrogBox R) (bs : List (Bool × Bool))
    (h : IsingLeapfrogKilledChoiceValid R p bs) (k : Nat) :
    IsingLeapfrogKilledChoiceValid R p (bs.take k) := by
  induction bs generalizing p k with
  | nil => simpa using h
  | cons b bs ih =>
      cases k with
      | zero => exact h.1
      | succ k =>
          exact ⟨h.1, ih (isingLeapfrogChoiceNext R p b) h.2 k⟩

private theorem isingLeapfrogBoxInt_inOpenBox_iff
    (R : Nat) (p : IsingLeapfrogBox R) :
    InOpenBox R (isingLeapfrogBoxInt p) ↔
      ¬ isingLeapfrogBoxBoundary R p := by
  unfold InOpenBox isingLeapfrogBoxInt isingLeapfrogBoxBoundary
  simp only [Prod.fst, Prod.snd]
  constructor
  · intro h
    omega
  · intro h
    have hx := p.1.2
    have hy := p.2.2
    push_cast
    omega

theorem IsingLeapfrogKilledChoiceValid.staysInOpenBox
    (R : Nat) (p : IsingLeapfrogBox R) (bs : List (Bool × Bool))
    (h : IsingLeapfrogKilledChoiceValid R p bs) :
    StaysInOpenBox R (isingLeapfrogBoxInt p)
      (isingLeapfrogChoiceSteps bs) := by
  intro k hk
  have htake := h.take R p bs k
  have hrun := htake.run_boxInt_eq_endpoint R p (bs.take k)
  have hopen : InOpenBox R
      (isingLeapfrogBoxInt (isingLeapfrogChoiceRun R p (bs.take k))) :=
    (isingLeapfrogBoxInt_inOpenBox_iff R _).2
      (htake.endpoint_not_boundary R p (bs.take k))
  rw [hrun] at hopen
  simpa [isingLeapfrogChoiceSteps, List.map_take] using hopen

def isingLeapfrogEncodeStep (d : Int × Int) : Bool × Bool :=
  (decide (d.1 = 1), decide (d.2 = 1))

def isingLeapfrogEncodeSteps (path : List (Int × Int)) :
    List (Bool × Bool) :=
  path.map isingLeapfrogEncodeStep

private theorem choiceStep_encodeStep_of_valid (d : Int × Int)
    (hd : (d.1 = 1 ∨ d.1 = -1) ∧ (d.2 = 1 ∨ d.2 = -1)) :
    isingLeapfrogChoiceStep (isingLeapfrogEncodeStep d) = d := by
  rcases hd with ⟨hdx | hdx, hdy | hdy⟩ <;>
    apply Prod.ext <;>
    simp [isingLeapfrogChoiceStep, isingLeapfrogEncodeStep, hdx, hdy]

theorem choiceSteps_encodeSteps_of_valid (path : List (Int × Int))
    (hvalid : IsingDiagonalWalkStepsValid path) :
    isingLeapfrogChoiceSteps (isingLeapfrogEncodeSteps path) = path := by
  induction path with
  | nil => rfl
  | cons d path ih =>
      have hd := hvalid d (by simp)
      have htail : IsingDiagonalWalkStepsValid path := by
        intro e he
        exact hvalid e (by simp [he])
      change isingLeapfrogChoiceStep (isingLeapfrogEncodeStep d) ::
          isingLeapfrogChoiceSteps (isingLeapfrogEncodeSteps path) = d :: path
      rw [choiceStep_encodeStep_of_valid d hd, ih htail]

theorem killedChoiceValid_encodeSteps_of_stays
    (R : Nat) (p : IsingLeapfrogBox R) (path : List (Int × Int))
    (hvalid : IsingDiagonalWalkStepsValid path)
    (hstays : StaysInOpenBox R (isingLeapfrogBoxInt p) path) :
    IsingLeapfrogKilledChoiceValid R p
      (isingLeapfrogEncodeSteps path) := by
  induction path generalizing p with
  | nil =>
      have h0 := hstays 0 (by simp)
      simpa [isingLeapfrogEncodeSteps] using
        (isingLeapfrogBoxInt_inOpenBox_iff R p).1 (by
          simpa [isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement]
            using h0)
  | cons d path ih =>
      have hd := hvalid d (by simp)
      have htailValid : IsingDiagonalWalkStepsValid path := by
        intro e he
        exact hvalid e (by simp [he])
      have h0 := hstays 0 (by simp)
      have hp : ¬ isingLeapfrogBoxBoundary R p :=
        (isingLeapfrogBoxInt_inOpenBox_iff R p).1 (by
          simpa [isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement]
            using h0)
      let b := isingLeapfrogEncodeStep d
      have hstep := isingLeapfrogBoxInt_choiceNext R p b hp
      rw [choiceStep_encodeStep_of_valid d hd] at hstep
      have htailStays : StaysInOpenBox R
          (isingLeapfrogBoxInt (isingLeapfrogChoiceNext R p b)) path := by
        intro k hk
        have horig := hstays (k + 1) (by simp; omega)
        rw [show (d :: path).take (k + 1) = d :: path.take k by
          simp [List.take_succ_cons]] at horig
        rw [hstep]
        have hend : isingDiagonalWalkEndpoint
            (isingDiagonalWalkNext (isingLeapfrogBoxInt p) d)
              (path.take k) =
            isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
              (d :: path.take k) := by
          unfold isingDiagonalWalkEndpoint isingDiagonalWalkNext
            isingDiagonalWalkDisplacement
          apply Prod.ext <;> simp <;> ring
        rw [hend]
        exact horig
      have htail := ih (isingLeapfrogChoiceNext R p b) htailValid htailStays
      exact ⟨hp, by simpa [isingLeapfrogEncodeSteps, b] using htail⟩

theorem isingLeapfrogBoxInt_injective {R : Nat} :
    Function.Injective (@isingLeapfrogBoxInt R) := by
  intro p q h
  unfold isingLeapfrogBoxInt at h
  apply Prod.ext <;> apply Fin.ext
  · exact Int.ofNat_inj.mp (congrArg Prod.fst h)
  · exact Int.ofNat_inj.mp (congrArg Prod.snd h)

private theorem encodeStep_choiceStep (b : Bool × Bool) :
    isingLeapfrogEncodeStep (isingLeapfrogChoiceStep b) = b := by
  rcases b with ⟨bx, byy⟩
  cases bx <;> cases byy <;>
    simp [isingLeapfrogEncodeStep, isingLeapfrogChoiceStep]

theorem encodeSteps_choiceSteps (bs : List (Bool × Bool)) :
    isingLeapfrogEncodeSteps (isingLeapfrogChoiceSteps bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      change isingLeapfrogEncodeStep (isingLeapfrogChoiceStep b) ::
          isingLeapfrogEncodeSteps (isingLeapfrogChoiceSteps bs) = b :: bs
      rw [encodeStep_choiceStep, ih]


def IsingLeapfrogKilledChoiceFirstHitFamily (R t : Nat)
    (p q : IsingLeapfrogBox R) (level : Int) :=
  {z : IsingLeapfrogKilledChoicePathFamily R t p q ×
      IsingDiagonalWalkHitSplit (isingLeapfrogBoxInt p) level //
    isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p) level
      (isingLeapfrogChoiceSteps z.1.1) = some z.2}

noncomputable instance isingLeapfrogKilledChoiceFirstHitFamily_finite
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int) :
    Finite (IsingLeapfrogKilledChoiceFirstHitFamily R t p q level) := by
  letI : Fintype {bs : List (Bool × Bool) // bs.length = t} :=
    (List.finite_length_eq (Bool × Bool) t).fintype
  exact Finite.of_injective
    (fun z : IsingLeapfrogKilledChoiceFirstHitFamily R t p q level =>
      (⟨z.1.1.1, z.1.1.2.1⟩ : {bs : List (Bool × Bool) //
        bs.length = t}))
    (by
      intro a b h
      have hbits : a.1.1.1 = b.1.1.1 := congrArg
        (fun z : {bs : List (Bool × Bool) // bs.length = t} => z.1) h
      have ha := a.2
      have hb := b.2
      have hsplits : a.1.2 = b.1.2 := by
        apply Option.some.inj
        rw [← ha, ← hb, hbits]
      apply Subtype.ext
      apply Prod.ext
      · exact Subtype.ext hbits
      · exact hsplits)



noncomputable def killedChoiceFirstHitFamilyEquiv
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int) :
    IsingLeapfrogKilledChoiceFirstHitFamily R t p q level ≃
      SurvivingFirstHitFamily R (isingLeapfrogBoxInt p) level t
        (isingLeapfrogBoxInt q) where
  toFun z := by
    let w := z.1.1
    let split := z.1.2
    have hsteps := firstHitSplit_steps z.2
    have hfirst := firstHitSplit_firstHit z.2
    have hvalid : z.1.2.Valid := by
      unfold IsingDiagonalWalkHitSplit.Valid
      rw [hsteps]
      exact isingLeapfrogChoiceSteps_valid w.1
    have hlength : z.1.2.steps.length = t := by
      rw [hsteps]
      simpa [isingLeapfrogChoiceSteps] using w.2.1
    have hendpoint : z.1.2.endpoint = isingLeapfrogBoxInt q := by
      unfold endpoint
      rw [hsteps]
      have hrun := w.2.2.1.run_boxInt_eq_endpoint R p w.1
      rw [w.2.2.2] at hrun
      exact hrun.symm
    have hstays : StaysInOpenBox R (isingLeapfrogBoxInt p) z.1.2.steps := by
      rw [hsteps]
      exact w.2.2.1.staysInOpenBox R p w.1
    exact ⟨⟨split, hfirst, hvalid, hlength, hendpoint⟩, hstays⟩
  invFun z := by
    let bs := isingLeapfrogEncodeSteps z.1.1.steps
    have hvalid := z.1.2.2.1
    have hdecode := choiceSteps_encodeSteps_of_valid z.1.1.steps hvalid
    have hkilled := killedChoiceValid_encodeSteps_of_stays R p z.1.1.steps
      hvalid z.2
    have hrunBox : isingLeapfrogChoiceRun R p bs = q := by
      have hrun := hkilled.run_boxInt_eq_endpoint R p bs
      rw [hdecode] at hrun
      have hend := z.1.2.2.2.2
      unfold endpoint at hend
      rw [hend] at hrun
      exact isingLeapfrogBoxInt_injective hrun
    let w : IsingLeapfrogKilledChoicePathFamily R t p q :=
      ⟨bs, by simpa [bs, isingLeapfrogEncodeSteps] using z.1.2.2.2.1,
        hkilled, hrunBox⟩
    refine ⟨⟨w, z.1.1⟩, ?_⟩
    rw [show isingLeapfrogChoiceSteps w.1 = z.1.1.steps by
      exact hdecode]
    exact firstHitSplit_eq_some z.1.1 z.1.2.1
  left_inv z := by
    rcases z with ⟨⟨w, split⟩, hz⟩
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      change isingLeapfrogEncodeSteps split.steps = w.1
      rw [firstHitSplit_steps hz, encodeSteps_choiceSteps]
    · rfl
  right_inv z := by
    apply Subtype.ext
    rfl

theorem natCard_killedChoiceFirstHitFamily_eq_surviving
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int) :
    Nat.card (IsingLeapfrogKilledChoiceFirstHitFamily R t p q level) =
      Nat.card (SurvivingFirstHitFamily R (isingLeapfrogBoxInt p) level t
        (isingLeapfrogBoxInt q)) :=
  Nat.card_congr (killedChoiceFirstHitFamilyEquiv R t p q level)


def IsingLeapfrogKilledChoiceNoHitFamily (R t : Nat)
    (p q : IsingLeapfrogBox R) (level : Int) :=
  {w : IsingLeapfrogKilledChoicePathFamily R t p q //
    isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p) level
      (isingLeapfrogChoiceSteps w.1) = none}

noncomputable instance isingLeapfrogKilledChoiceNoHitFamily_finite
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int) :
    Finite (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) :=
  Finite.of_injective Subtype.val Subtype.val_injective

private noncomputable def killedChoicePathFamilyHitNoHit
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int) :
    IsingLeapfrogKilledChoicePathFamily R t p q →
      IsingLeapfrogKilledChoiceFirstHitFamily R t p q level ⊕
        IsingLeapfrogKilledChoiceNoHitFamily R t p q level := fun w => by
  let o := isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p) level
    (isingLeapfrogChoiceSteps w.1)
  by_cases hnone : o = none
  · exact Sum.inr ⟨w, hnone⟩
  · have his : o.isSome = true :=
      Option.ne_none_iff_isSome.mp hnone
    exact Sum.inl ⟨⟨w, o.get his⟩, (Option.some_get his).symm⟩



noncomputable def killedChoicePathFamilyHitNoHitEquiv
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int) :
    IsingLeapfrogKilledChoicePathFamily R t p q ≃
      IsingLeapfrogKilledChoiceFirstHitFamily R t p q level ⊕
        IsingLeapfrogKilledChoiceNoHitFamily R t p q level where
  toFun := killedChoicePathFamilyHitNoHit R t p q level
  invFun z := z.elim (fun w => w.1.1) (fun w => w.1)
  left_inv w := by
    unfold killedChoicePathFamilyHitNoHit
    dsimp only
    split <;> rfl
  right_inv z := by
    rcases z with w | w
    · unfold killedChoicePathFamilyHitNoHit
      dsimp only
      have hne : isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p)
          level (isingLeapfrogChoiceSteps w.1.1.1) ≠ none := by
        rw [w.2]
        simp
      simp [hne]
      congr 1
      apply Prod.ext
      · rfl
      · apply Option.some.inj
        rw [← w.2]
        exact Option.some_get _
    · unfold killedChoicePathFamilyHitNoHit
      dsimp only
      simp [w.2]

theorem natCard_killedChoicePathFamily_eq_hit_add_noHit
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int) :
    Nat.card (IsingLeapfrogKilledChoicePathFamily R t p q) =
      Nat.card (IsingLeapfrogKilledChoiceFirstHitFamily R t p q level) +
        Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) := by
  rw [Nat.card_congr (killedChoicePathFamilyHitNoHitEquiv R t p q level),
    Nat.card_sum]



theorem isingLeapfrogKilledKernel_eq_survivingFirstHit_add_noHit
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int) :
    isingLeapfrogKilledKernel R t p q =
      Nat.card (SurvivingFirstHitFamily R (isingLeapfrogBoxInt p) level t
          (isingLeapfrogBoxInt q)) / (4 : Real) ^ t +
        Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) /
          (4 : Real) ^ t := by
  rw [isingLeapfrogKilledKernel_eq_natCard_choicePath_div,
    natCard_killedChoicePathFamily_eq_hit_add_noHit,
    natCard_killedChoiceFirstHitFamily_eq_surviving]
  push_cast
  ring

private theorem abs_natCast_sub_eq_natDist (a b : Nat) :
    |(a : Real) - (b : Real)| = Nat.dist a b := by
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hab))]
    rw [Nat.dist_eq_sub_of_le hab]
    rw [Nat.cast_sub hab]
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hba))]
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hba]
    rw [Nat.cast_sub hba]



theorem isingLeapfrogKilledKernel_reflectedStart_abs_le
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p)) :
    |isingLeapfrogKilledKernel R t p q -
        isingLeapfrogKilledKernel R t p' q| ≤
      (Nat.dist
          (Nat.card (SurvivingFirstHitFamily R (isingLeapfrogBoxInt p)
            level t (isingLeapfrogBoxInt q)))
          (Nat.card (SurvivingFirstHitFamily R
            (reflectedEndpoint level (isingLeapfrogBoxInt p)) level t
            (isingLeapfrogBoxInt q))) : Real) / (4 : Real) ^ t +
        Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) /
          (4 : Real) ^ t +
        Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p' q level) /
          (4 : Real) ^ t := by
  rw [isingLeapfrogKilledKernel_eq_survivingFirstHit_add_noHit,
    isingLeapfrogKilledKernel_eq_survivingFirstHit_add_noHit]
  rw [hmirror]
  let A := Nat.card (SurvivingFirstHitFamily R (isingLeapfrogBoxInt p)
    level t (isingLeapfrogBoxInt q))
  let B := Nat.card (SurvivingFirstHitFamily R
    (reflectedEndpoint level (isingLeapfrogBoxInt p)) level t
    (isingLeapfrogBoxInt q))
  let C := Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level)
  let D := Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p' q level)
  have hden : 0 < (4 : Real) ^ t := by positivity
  calc
    |((A : Real) / 4 ^ t + (C : Real) / 4 ^ t) -
        ((B : Real) / 4 ^ t + (D : Real) / 4 ^ t)| =
        |((A : Real) - B) / 4 ^ t + ((C : Real) - D) / 4 ^ t| := by
      congr 1
      ring
    _ ≤ |((A : Real) - B) / 4 ^ t| +
        |((C : Real) - D) / 4 ^ t| := abs_add_le _ _
    _ = (Nat.dist A B : Real) / 4 ^ t +
        |((C : Real) - D)| / 4 ^ t := by
      simp only [abs_div, abs_of_pos hden]
      rw [abs_natCast_sub_eq_natDist A B]
    _ ≤ (Nat.dist A B : Real) / 4 ^ t +
        (C : Real) / 4 ^ t + (D : Real) / 4 ^ t := by
      have hCD : |(C : Real) - D| ≤ C + D := by
        rw [abs_sub_le_iff]
        have hC0 : (0 : Real) ≤ C := by positivity
        have hD0 : (0 : Real) ≤ D := by positivity
        constructor <;> linarith
      have hdiv := div_le_div_of_nonneg_right hCD hden.le
      calc
        _ ≤ (Nat.dist A B : Real) / 4 ^ t +
            ((C : Real) + D) / 4 ^ t :=
          add_le_add (le_refl _) hdiv
        _ = _ := by ring



theorem killedChoiceNoHitFamily_weight_le_free
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int) :
    Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) /
        (4 : Real) ^ t ≤
      2 / (t + 1 : Real) := by
  have hcard :
      Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) ≤
        Nat.card (IsingLeapfrogKilledChoicePathFamily R t p q) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hcardReal :
      (Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) :
        Real) ≤
      Nat.card (IsingLeapfrogKilledChoicePathFamily R t p q) := by
    exact_mod_cast hcard
  calc
    Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) /
        (4 : Real) ^ t ≤
      Nat.card (IsingLeapfrogKilledChoicePathFamily R t p q) /
        (4 : Real) ^ t :=
      div_le_div_of_nonneg_right hcardReal (by positivity)
    _ = isingLeapfrogKilledKernel R t p q := by
      rw [isingLeapfrogKilledKernel_eq_natCard_choicePath_div]
    _ ≤ 2 / (t + 1 : Real) :=
      isingLeapfrogKilledKernel_le R t p q



theorem isingLeapfrogKilledKernel_reflectedStart_diffusive_abs_le
    (R level ρ : Nat) (p p' q : IsingLeapfrogBox R)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < ρ) (hleft : ρ + 1 ≤ level)
    (hright : level + 1 + ρ ≤ R) :
    |isingLeapfrogKilledKernel R (ρ * ρ) p q -
        isingLeapfrogKilledKernel R (ρ * ρ) p' q| ≤
      8 / (ρ : Real) ^ 2 := by
  have hdecomp := isingLeapfrogKilledKernel_reflectedStart_abs_le R
    (ρ * ρ) p p' q (level : Int) hmirror
  have hhit := survivingFirstHitFamily_diffusive_weight_dist_le R level ρ
    (isingLeapfrogBoxInt p) (isingLeapfrogBoxInt q) hstart hρ hleft hright
  have hno := killedChoiceNoHitFamily_weight_le_free R (ρ * ρ) p q
    (level : Int)
  have hno' := killedChoiceNoHitFamily_weight_le_free R (ρ * ρ) p' q
    (level : Int)
  norm_num [Nat.cast_add, Nat.cast_mul] at hno hno'
  have hρsq : 0 < (ρ : Real) ^ 2 := by positivity
  have hnoBound :
      Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R (ρ * ρ) p q
          (level : Int)) / (4 : Real) ^ (ρ * ρ) ≤
        2 / (ρ : Real) ^ 2 := by
    refine le_trans hno (div_le_div_of_nonneg_left (by norm_num) hρsq ?_)
    nlinarith
  have hnoBound' :
      Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R (ρ * ρ) p' q
          (level : Int)) / (4 : Real) ^ (ρ * ρ) ≤
        2 / (ρ : Real) ^ 2 := by
    refine le_trans hno' (div_le_div_of_nonneg_left (by norm_num) hρsq ?_)
    nlinarith
  calc
    _ ≤ _ := hdecomp
    _ ≤ 4 / (ρ : Real) ^ 2 + 2 / (ρ : Real) ^ 2 +
        2 / (ρ : Real) ^ 2 := add_le_add (add_le_add hhit hnoBound) hnoBound'
    _ = 8 / (ρ : Real) ^ 2 := by ring



theorem firstHitSplit_none_endpoint_fst_ne
    {start : Int × Int} {level : Int} {path : List (Int × Int)}
    (hnone : isingDiagonalWalkFirstHitSplit? start level path = none) :
    ∀ k, k ≤ path.length →
      (isingDiagonalWalkEndpoint start (path.take k)).1 ≠ level := by
  induction path generalizing start with
  | nil =>
      intro k hk
      have hk0 : k = 0 := by simp_all
      subst k
      by_cases hs : start.1 = level
      · simp [isingDiagonalWalkFirstHitSplit?, hs] at hnone
      · simpa [isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement]
          using hs
  | cons d path ih =>
      by_cases hs : start.1 = level
      · simp [isingDiagonalWalkFirstHitSplit?, hs] at hnone
      · have htail : isingDiagonalWalkFirstHitSplit?
            (isingDiagonalWalkNext start d) level path = none := by
          cases hrec : isingDiagonalWalkFirstHitSplit?
              (isingDiagonalWalkNext start d) level path with
          | none => rfl
          | some split =>
              simp [isingDiagonalWalkFirstHitSplit?, hs, hrec] at hnone
        intro k hk
        cases k with
        | zero =>
            simpa [isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement]
              using hs
        | succ k =>
            have hkTail : k ≤ path.length := by simpa using hk
            have hne := ih htail k hkTail
            simpa [isingDiagonalWalkEndpoint, isingDiagonalWalkNext,
              isingDiagonalWalkDisplacement, add_assoc] using hne

private theorem lineFreeEndpoint_choiceHorizontal
    (bs : List (Bool × Bool)) (start : Int × Int) :
    lineFreeEndpoint start.1 (bs.map Prod.fst) =
      (isingDiagonalWalkEndpoint start
        (isingLeapfrogChoiceSteps bs)).1 := by
  induction bs generalizing start with
  | nil =>
      simp [lineFreeEndpoint,
        isingLeapfrogChoiceSteps, isingDiagonalWalkEndpoint,
        isingDiagonalWalkDisplacement]
  | cons b bs ih =>
      have hih := ih (isingDiagonalWalkNext start
        (isingLeapfrogChoiceStep b))
      rcases b with ⟨bx, byy⟩
      cases bx <;> cases byy <;>
        simp [lineFreeEndpoint,
          isingLeapfrogChoiceSteps, isingLeapfrogChoiceStep,
          isingDiagonalWalkEndpoint, isingDiagonalWalkNext,
          isingDiagonalWalkDisplacement, add_assoc] at hih ⊢ <;>
        linarith



def IsingLeapfrogKilledChoiceNoHitAll (R t : Nat)
    (p : IsingLeapfrogBox R) (level : Int) :=
  {w : {bs : List (Bool × Bool) //
      bs.length = t ∧ IsingLeapfrogKilledChoiceValid R p bs} //
    isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p) level
      (isingLeapfrogChoiceSteps w.1) = none}

noncomputable instance isingLeapfrogKilledChoiceNoHitAll_finite
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :
    Finite (IsingLeapfrogKilledChoiceNoHitAll R t p level) := by
  letI : Fintype {bs : List (Bool × Bool) // bs.length = t} :=
    (List.finite_length_eq (Bool × Bool) t).fintype
  exact Finite.of_injective
    (fun w : IsingLeapfrogKilledChoiceNoHitAll R t p level =>
      (⟨w.1.1, w.1.2.1⟩ : {bs : List (Bool × Bool) //
        bs.length = t}))
    (by
      intro a b h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg
        (fun z : {bs : List (Bool × Bool) // bs.length = t} => z.1) h)

private def killedChoiceNoHitFiberEquiv
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int) :
    {w : IsingLeapfrogKilledChoiceNoHitAll R t p level //
      isingLeapfrogChoiceRun R p w.1.1 = q} ≃
        IsingLeapfrogKilledChoiceNoHitFamily R t p q level where
  toFun w := ⟨⟨w.1.1.1, w.1.1.2.1, w.1.1.2.2, w.2⟩, w.1.2⟩
  invFun w := ⟨⟨⟨w.1.1, w.1.2.1, w.1.2.2.1⟩, w.2⟩, w.1.2.2.2⟩
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

noncomputable def killedChoiceNoHitAllEquivSigma
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :
    IsingLeapfrogKilledChoiceNoHitAll R t p level ≃
      Σ q : IsingLeapfrogBox R,
        IsingLeapfrogKilledChoiceNoHitFamily R t p q level :=
  (Equiv.sigmaFiberEquiv (fun w : IsingLeapfrogKilledChoiceNoHitAll R t p
    level => isingLeapfrogChoiceRun R p w.1.1)).symm |>.trans
      (Equiv.sigmaCongrRight
        (fun q => killedChoiceNoHitFiberEquiv R t p q level))

theorem natCard_killedChoiceNoHitAll_eq_sum
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :
    Nat.card (IsingLeapfrogKilledChoiceNoHitAll R t p level) =
      ∑ q, Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) := by
  rw [Nat.card_congr (killedChoiceNoHitAllEquivSigma R t p level),
    Nat.card_sigma]


def IsingHorizontalNoHitFamily (t : Nat) (start level : Int) :=
  {bs : List Bool // bs.length = t ∧
    ∀ k, k ≤ t →
      lineFreeEndpoint start (bs.take k) ≠ level}

noncomputable instance isingHorizontalNoHitFamily_finite
    (t : Nat) (start level : Int) :
    Finite (IsingHorizontalNoHitFamily t start level) := by
  letI : Fintype {bs : List Bool // bs.length = t} :=
    (List.finite_length_eq Bool t).fintype
  exact Finite.of_injective
    (fun w : IsingHorizontalNoHitFamily t start level =>
      (⟨w.1, w.2.1⟩ : {bs : List Bool // bs.length = t}))
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg
        (fun z : {bs : List Bool // bs.length = t} => z.1) h)

private theorem prodBits_injective
    {a b : List (Bool × Bool)}
    (hx : a.map Prod.fst = b.map Prod.fst)
    (hy : a.map Prod.snd = b.map Prod.snd) : a = b := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => rfl
      | cons z b => simp at hx
  | cons z a ih =>
      cases b with
      | nil => simp at hx
      | cons w b =>
          simp only [List.map_cons, List.cons.injEq] at hx hy
          have hzw : z = w := Prod.ext hx.1 hy.1
          subst w
          congr 1
          exact ih hx.2 hy.2

private def killedChoiceNoHitAllProjection
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :
    IsingLeapfrogKilledChoiceNoHitAll R t p level →
      IsingHorizontalNoHitFamily t (isingLeapfrogBoxInt p).1 level ×
        {ys : List Bool // ys.length = t} := fun w =>
  ⟨⟨w.1.1.map Prod.fst, by simpa using w.1.2.1, by
      intro k hk hhit
      have hne := firstHitSplit_none_endpoint_fst_ne w.2 k (by
        simpa [isingLeapfrogChoiceSteps, w.1.2.1] using hk)
      apply hne
      calc
        (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
            ((isingLeapfrogChoiceSteps w.1.1).take k)).1 =
            (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
              (isingLeapfrogChoiceSteps (w.1.1.take k))).1 := by
                simp [isingLeapfrogChoiceSteps, List.map_take]
        _ = lineFreeEndpoint (isingLeapfrogBoxInt p).1
            ((w.1.1.take k).map Prod.fst) :=
          (lineFreeEndpoint_choiceHorizontal (w.1.1.take k)
            (isingLeapfrogBoxInt p)).symm
        _ = level := by simpa [List.map_take] using hhit⟩,
    ⟨w.1.1.map Prod.snd, by simpa using w.1.2.1⟩⟩

private theorem killedChoiceNoHitAllProjection_injective
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :
    Function.Injective (killedChoiceNoHitAllProjection R t p level) := by
  intro a b h
  have hx : a.1.1.map Prod.fst = b.1.1.map Prod.fst :=
    congrArg (fun z => z.1.1) h
  have hy : a.1.1.map Prod.snd = b.1.1.map Prod.snd :=
    congrArg (fun z => z.2.1) h
  apply Subtype.ext
  apply Subtype.ext
  exact prodBits_injective hx hy

theorem natCard_killedChoiceNoHitAll_le_horizontal_mul_pow
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :
    Nat.card (IsingLeapfrogKilledChoiceNoHitAll R t p level) ≤
      Nat.card (IsingHorizontalNoHitFamily t (isingLeapfrogBoxInt p).1 level) *
        2 ^ t := by
  calc
    _ ≤ Nat.card (IsingHorizontalNoHitFamily t
          (isingLeapfrogBoxInt p).1 level ×
        {ys : List Bool // ys.length = t}) :=
      Nat.card_le_card_of_injective
        (killedChoiceNoHitAllProjection R t p level)
        (killedChoiceNoHitAllProjection_injective R t p level)
    _ = _ := by
      rw [Nat.card_prod]
      congr 1
      change Nat.card (List.Vector Bool t) = 2 ^ t
      rw [Nat.card_congr (Equiv.vectorEquivFin Bool t),
        Nat.card_eq_fintype_card, Fintype.card_fun]
      simp

end

end StatMech.Universality
