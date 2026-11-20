/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicBallot









namespace StatMech.Universality

open Finset
open IsingDiagonalWalkHitSplit

noncomputable section

private theorem natCard_subtype_eq_sum_ite {Omega : Type} [Fintype Omega]
    (p : Omega → Prop) [DecidablePred p] :
    Nat.card {x : Omega // p x} = ∑ x : Omega, if p x then 1 else 0 := by
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card {x : Omega // p x} =
        Fintype.card (↑(Finset.univ.filter p)) :=
      Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by simp))
    _ = (Finset.univ.filter p).card := Fintype.card_coe _
    _ = ∑ x : Omega, if p x then 1 else 0 := by
      rw [Finset.card_filter]



theorem finiteUniformCoupling_fiber_l1_le
    {Omega A : Type} [Fintype Omega] [Fintype A] [DecidableEq A]
    (e : Omega ≃ Omega) (f g : Omega → A) :
    ∑ a : A, |((Nat.card {w : Omega // f w = a} : Nat) : Real) -
      ((Nat.card {w : Omega // g w = a} : Nat) : Real)| ≤
      2 * ((Nat.card {w : Omega // f w ≠ g (e w)} : Nat) : Real) := by
  classical
  have hfiber (a : A) :
      (((Nat.card {w : Omega // f w = a} : Nat) : Real) -
          ((Nat.card {w : Omega // g w = a} : Nat) : Real)) =
        ∑ w : Omega, ((if f w = a then 1 else 0) -
          (if g (e w) = a then 1 else 0) : Real) := by
    rw [natCard_subtype_eq_sum_ite, natCard_subtype_eq_sum_ite]
    push_cast
    rw [Finset.sum_sub_distrib]
    congr 1
    exact (Equiv.sum_comp e
      (fun w : Omega => if g w = a then (1 : Real) else 0)).symm
  rw [show (∑ a : A, |((Nat.card {w : Omega // f w = a} : Nat) : Real) -
      ((Nat.card {w : Omega // g w = a} : Nat) : Real)|) =
      ∑ a : A, |∑ w : Omega, ((if f w = a then 1 else 0) -
          (if g (e w) = a then 1 else 0) : Real)| by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hfiber a]]
  calc
    (∑ a : A, |∑ w : Omega, ((if f w = a then 1 else 0) -
          (if g (e w) = a then 1 else 0) : Real)|) ≤
        ∑ a : A, ∑ w : Omega, |((if f w = a then 1 else 0) -
          (if g (e w) = a then 1 else 0) : Real)| := by
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ w : Omega, ∑ a : A, |((if f w = a then 1 else 0) -
          (if g (e w) = a then 1 else 0) : Real)| := Finset.sum_comm
    _ = ∑ w : Omega, if f w ≠ g (e w) then (2 : Real) else 0 := by
      apply Finset.sum_congr rfl
      intro w hw
      by_cases h : f w = g (e w)
      · simp [h]
      · rw [if_pos h]
        calc
          (∑ a : A, |((if f w = a then 1 else 0) -
              (if g (e w) = a then 1 else 0) : Real)|) =
              ∑ a : A, ((if f w = a then 1 else 0) +
                (if g (e w) = a then 1 else 0) : Real) := by
            apply Finset.sum_congr rfl
            intro a ha
            by_cases hf : f w = a
            · have hg : g (e w) ≠ a := by
                intro hga
                exact h (hf.trans hga.symm)
              simp [hf, hg]
            · by_cases hg : g (e w) = a <;> simp [hf, hg]
          _ = (∑ a : A, (if f w = a then (1 : Real) else 0)) +
              ∑ a : A, (if g (e w) = a then (1 : Real) else 0) :=
            Finset.sum_add_distrib
          _ = 2 := by simp; norm_num
    _ = 2 * ((Nat.card {w : Omega // f w ≠ g (e w)} : Nat) : Real) := by
      rw [natCard_subtype_eq_sum_ite]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      by_cases h : f w ≠ g (e w) <;> simp [h]

private theorem firstHitSplit_eq_none_of_endpoint_fst_ne
    {start : Int × Int} {level : Int} {path : List (Int × Int)}
    (havoid : ∀ k, k ≤ path.length →
      (isingDiagonalWalkEndpoint start (path.take k)).1 ≠ level) :
    isingDiagonalWalkFirstHitSplit? start level path = none := by
  cases hsplit : isingDiagonalWalkFirstHitSplit? start level path with
  | none => rfl
  | some split =>
      exfalso
      have hsteps := firstHitSplit_steps hsplit
      have hk : split.before.length ≤ path.length := by
        rw [← hsteps]
        simp [IsingDiagonalWalkHitSplit.steps]
      exact (havoid split.before.length hk) (by
        have htake : path.take split.before.length = split.before := by
          rw [← hsteps]
          simp [IsingDiagonalWalkHitSplit.steps]
        rw [htake]
        exact split.hit)

private theorem reflectAll_endpoint_take_fst
    (path : List (Int × Int)) (start : Int × Int) (level : Int)
    (k : Nat) :
    (isingDiagonalWalkEndpoint (reflectedEndpoint level start)
      ((path.map reflectIncrement).take k)).1 =
        2 * level -
          (isingDiagonalWalkEndpoint start (path.take k)).1 := by
  rw [← List.map_take]
  unfold isingDiagonalWalkEndpoint reflectedEndpoint
    isingDiagonalWalkDisplacement
  simp only [List.map_map]
  have hneg :
      ((path.take k).map (fun d => -d.1)).sum =
        -((path.take k).map Prod.fst).sum := by
    induction path.take k with
    | nil => simp
    | cons d ds ih => simp [ih, add_comm]
  change (2 * level - start.1) +
      ((path.take k).map (fun d => -d.1)).sum =
    2 * level - (start.1 + ((path.take k).map Prod.fst).sum)
  rw [hneg]
  ring

private theorem reflectAll_valid (path : List (Int × Int))
    (hvalid : IsingDiagonalWalkStepsValid path) :
    IsingDiagonalWalkStepsValid (path.map reflectIncrement) := by
  intro d hd
  rcases List.mem_map.mp hd with ⟨e, he, rfl⟩
  have heValid := hvalid e he
  rcases heValid with ⟨hex, hey⟩
  constructor
  · rcases hex with hex | hex <;> simp [reflectIncrement, hex]
  · simpa [reflectIncrement] using hey

private theorem firstHitSplit_reflectAll_eq_none
    {start : Int × Int} {level : Int} {path : List (Int × Int)}
    (hnone : isingDiagonalWalkFirstHitSplit? start level path = none) :
    isingDiagonalWalkFirstHitSplit? (reflectedEndpoint level start) level
      (path.map reflectIncrement) = none := by
  apply firstHitSplit_eq_none_of_endpoint_fst_ne
  intro k hk heq
  have horig := firstHitSplit_none_endpoint_fst_ne hnone k (by simpa using hk)
  have hreflect := reflectAll_endpoint_take_fst path start level k
  rw [heq] at hreflect
  apply horig
  omega



def isingDiagonalWalkCouplingReflectSteps
    (start : Int × Int) (level : Int) (path : List (Int × Int)) :
    List (Int × Int) :=
  match isingDiagonalWalkFirstHitSplit? start level path with
  | some split => split.reflectPrefix.steps
  | none => path.map reflectIncrement

theorem couplingReflectSteps_length
    (start : Int × Int) (level : Int) (path : List (Int × Int)) :
    (isingDiagonalWalkCouplingReflectSteps start level path).length =
      path.length := by
  unfold isingDiagonalWalkCouplingReflectSteps
  cases hsplit : isingDiagonalWalkFirstHitSplit? start level path with
  | none => simp
  | some split =>
      rw [reflectPrefix_length, firstHitSplit_steps hsplit]

theorem couplingReflectSteps_valid
    (start : Int × Int) (level : Int) (path : List (Int × Int))
    (hvalid : IsingDiagonalWalkStepsValid path) :
    IsingDiagonalWalkStepsValid
      (isingDiagonalWalkCouplingReflectSteps start level path) := by
  unfold isingDiagonalWalkCouplingReflectSteps
  cases hsplit : isingDiagonalWalkFirstHitSplit? start level path with
  | none => exact reflectAll_valid path hvalid
  | some split =>
      apply reflectPrefix_valid
      unfold IsingDiagonalWalkHitSplit.Valid
      rw [firstHitSplit_steps hsplit]
      exact hvalid

theorem couplingReflectSteps_involutive
    (start : Int × Int) (level : Int) (path : List (Int × Int)) :
    isingDiagonalWalkCouplingReflectSteps (reflectedEndpoint level start) level
        (isingDiagonalWalkCouplingReflectSteps start level path) = path := by
  unfold isingDiagonalWalkCouplingReflectSteps
  cases hsplit : isingDiagonalWalkFirstHitSplit? start level path with
  | none =>
      rw [firstHitSplit_reflectAll_eq_none hsplit]
      simp [reflectIncrement, Function.comp_def]
  | some split =>
      have hreflect : isingDiagonalWalkFirstHitSplit?
          (reflectedEndpoint level start) level split.reflectPrefix.steps =
            some split.reflectPrefix :=
        firstHitSplit_eq_some split.reflectPrefix
          (reflectPrefix_firstHit split (firstHitSplit_firstHit hsplit))
      rw [hreflect]
      rw [← firstHitSplit_steps hsplit]
      simp [IsingDiagonalWalkHitSplit.steps, reflectPrefix, reflectIncrement,
        Function.comp_def]


def IsingLeapfrogChoiceStringFamily (t : Nat) :=
  {bs : List (Bool × Bool) // bs.length = t}

noncomputable instance isingLeapfrogChoiceStringFamily_finite (t : Nat) :
    Finite (IsingLeapfrogChoiceStringFamily t) :=
  List.finite_length_eq (Bool × Bool) t

def isingLeapfrogCouplingChoiceTransform
    (t : Nat) (start : Int × Int) (level : Int) :
    IsingLeapfrogChoiceStringFamily t → IsingLeapfrogChoiceStringFamily t :=
  fun w => ⟨isingLeapfrogEncodeSteps
    (isingDiagonalWalkCouplingReflectSteps start level
      (isingLeapfrogChoiceSteps w.1)), by
    simp [isingLeapfrogEncodeSteps, couplingReflectSteps_length,
      isingLeapfrogChoiceSteps, w.2]⟩

private theorem couplingChoiceTransform_steps
    (t : Nat) (start : Int × Int) (level : Int)
    (w : IsingLeapfrogChoiceStringFamily t) :
    isingLeapfrogChoiceSteps
        (isingLeapfrogCouplingChoiceTransform t start level w).1 =
      isingDiagonalWalkCouplingReflectSteps start level
        (isingLeapfrogChoiceSteps w.1) := by
  exact choiceSteps_encodeSteps_of_valid _
    (couplingReflectSteps_valid start level _
      (isingLeapfrogChoiceSteps_valid w.1))

theorem couplingChoiceTransform_involutive
    (t : Nat) (start : Int × Int) (level : Int) :
    Function.LeftInverse
      (isingLeapfrogCouplingChoiceTransform t (reflectedEndpoint level start)
        level)
      (isingLeapfrogCouplingChoiceTransform t start level) := by
  intro w
  apply Subtype.ext
  unfold isingLeapfrogCouplingChoiceTransform
  dsimp only
  have hdecode := choiceSteps_encodeSteps_of_valid
    (isingDiagonalWalkCouplingReflectSteps start level
      (isingLeapfrogChoiceSteps w.1))
    (couplingReflectSteps_valid start level _
      (isingLeapfrogChoiceSteps_valid w.1))
  rw [hdecode]
  rw [couplingReflectSteps_involutive]
  exact encodeSteps_choiceSteps w.1


def isingLeapfrogCouplingChoiceEquiv
    (t : Nat) (start : Int × Int) (level : Int) :
    IsingLeapfrogChoiceStringFamily t ≃ IsingLeapfrogChoiceStringFamily t where
  toFun := isingLeapfrogCouplingChoiceTransform t start level
  invFun := isingLeapfrogCouplingChoiceTransform t
    (reflectedEndpoint level start) level
  left_inv := couplingChoiceTransform_involutive t start level
  right_inv := by
    intro w
    have h := couplingChoiceTransform_involutive t
      (reflectedEndpoint level start) level w
    simpa [reflectedEndpoint] using h

theorem lineFreeEndpoint_choiceHorizontal_full
    (bs : List (Bool × Bool)) (start : Int × Int) :
    lineFreeEndpoint start.1 (bs.map Prod.fst) =
      (isingDiagonalWalkEndpoint start
        (isingLeapfrogChoiceSteps bs)).1 := by
  induction bs generalizing start with
  | nil =>
      simp [lineFreeEndpoint, isingLeapfrogChoiceSteps,
        isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement]
  | cons b bs ih =>
      have hih := ih (isingDiagonalWalkNext start
        (isingLeapfrogChoiceStep b))
      rcases b with ⟨bx, byy⟩
      cases bx <;> cases byy <;>
        simp [lineFreeEndpoint, isingLeapfrogChoiceSteps,
          isingLeapfrogChoiceStep, isingDiagonalWalkEndpoint,
          isingDiagonalWalkNext, isingDiagonalWalkDisplacement,
          add_assoc] at hih ⊢ <;> linarith



def IsingLeapfrogChoiceNoHitAll (t : Nat) (start level : Int) :=
  {w : IsingLeapfrogChoiceStringFamily t //
    ∀ k, k ≤ t →
      lineFreeEndpoint start ((w.1.take k).map Prod.fst) ≠ level}

noncomputable instance isingLeapfrogChoiceNoHitAll_finite
    (t : Nat) (start level : Int) :
    Finite (IsingLeapfrogChoiceNoHitAll t start level) := by
  exact Finite.of_injective
    (fun w : IsingLeapfrogChoiceNoHitAll t start level => w.1)
    Subtype.val_injective

private theorem prodBits_injective_full
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

private def choiceNoHitAllProjection
    (t : Nat) (start level : Int) :
    IsingLeapfrogChoiceNoHitAll t start level →
      IsingHorizontalNoHitFamily t start level ×
        {ys : List Bool // ys.length = t} := fun w =>
  ⟨⟨w.1.1.map Prod.fst, by simpa using w.1.2, by
      intro k hk
      simpa [List.map_take] using w.2 k hk⟩,
    ⟨w.1.1.map Prod.snd, by simpa using w.1.2⟩⟩

private theorem choiceNoHitAllProjection_injective
    (t : Nat) (start level : Int) :
    Function.Injective (choiceNoHitAllProjection t start level) := by
  intro a b h
  have hx : a.1.1.map Prod.fst = b.1.1.map Prod.fst :=
    congrArg (fun z => z.1.1) h
  have hy : a.1.1.map Prod.snd = b.1.1.map Prod.snd :=
    congrArg (fun z => z.2.1) h
  apply Subtype.ext
  apply Subtype.ext
  exact prodBits_injective_full hx hy

theorem natCard_choiceNoHitAll_le_horizontal_mul_pow
    (t : Nat) (start level : Int) :
    Nat.card (IsingLeapfrogChoiceNoHitAll t start level) ≤
      Nat.card (IsingHorizontalNoHitFamily t start level) * 2 ^ t := by
  calc
    _ ≤ Nat.card (IsingHorizontalNoHitFamily t start level ×
        {ys : List Bool // ys.length = t}) :=
      Nat.card_le_card_of_injective (choiceNoHitAllProjection t start level)
        (choiceNoHitAllProjection_injective t start level)
    _ = _ := by
      rw [Nat.card_prod]
      congr 1
      change Nat.card (List.Vector Bool t) = 2 ^ t
      rw [Nat.card_congr (Equiv.vectorEquivFin Bool t),
        Nat.card_eq_fintype_card, Fintype.card_fun]
      simp

private theorem sum_mul_eq_last_partial_add
    (a b : Nat → Real) (N : Nat) :
    (∑ k ∈ Finset.range (N + 1), a k * b k) =
      a N * (∑ k ∈ Finset.range (N + 1), b k) +
        ∑ k ∈ Finset.range N,
          (a k - a (k + 1)) * (∑ j ∈ Finset.range (k + 1), b j) := by
  induction N with
  | zero => simp
  | succ N ih =>
      calc
        (∑ k ∈ Finset.range (N + 1 + 1), a k * b k) =
            (∑ k ∈ Finset.range (N + 1), a k * b k) +
              a (N + 1) * b (N + 1) := by rw [Finset.sum_range_succ]
        _ = (a N * (∑ k ∈ Finset.range (N + 1), b k) +
              ∑ k ∈ Finset.range N,
                (a k - a (k + 1)) *
                  (∑ j ∈ Finset.range (k + 1), b j)) +
              a (N + 1) * b (N + 1) := by rw [ih]
        _ = a (N + 1) * (∑ k ∈ Finset.range (N + 1 + 1), b k) +
              ∑ k ∈ Finset.range (N + 1),
                (a k - a (k + 1)) *
                  (∑ j ∈ Finset.range (k + 1), b j) := by
            have hbSucc : (∑ k ∈ Finset.range (N + 1 + 1), b k) =
                (∑ k ∈ Finset.range (N + 1), b k) + b (N + 1) := by
              rw [Finset.sum_range_succ]
            have hdSucc :
                (∑ k ∈ Finset.range (N + 1),
                  (a k - a (k + 1)) *
                    (∑ j ∈ Finset.range (k + 1), b j)) =
                  (∑ k ∈ Finset.range N,
                    (a k - a (k + 1)) *
                      (∑ j ∈ Finset.range (k + 1), b j)) +
                    (a N - a (N + 1)) *
                      (∑ j ∈ Finset.range (N + 1), b j) := by
              rw [Finset.sum_range_succ]
            rw [hbSucc, hdSucc]
            ring

private theorem last_mul_add_sum_diff_eq_sum
    (a : Nat → Real) (N : Nat) :
    a N * (N + 1 : Nat) +
        ∑ k ∈ Finset.range N, (a k - a (k + 1)) * (k + 1 : Nat) =
      ∑ k ∈ Finset.range (N + 1), a k := by
  induction N with
  | zero => simp
  | succ N ih =>
      calc
        a (N + 1) * (N + 1 + 1 : Nat) +
              ∑ k ∈ Finset.range (N + 1),
                (a k - a (k + 1)) * (k + 1 : Nat) =
            a (N + 1) * (N + 1 + 1 : Nat) +
              ((∑ k ∈ Finset.range N,
                (a k - a (k + 1)) * (k + 1 : Nat)) +
                (a N - a (N + 1)) * (N + 1 : Nat)) := by
              rw [Finset.sum_range_succ]
        _ = (a N * (N + 1 : Nat) +
              ∑ k ∈ Finset.range N,
                (a k - a (k + 1)) * (k + 1 : Nat)) +
              a (N + 1) := by
            push_cast
            ring
        _ = (∑ k ∈ Finset.range (N + 1), a k) + a (N + 1) := by
            rw [ih]
        _ = ∑ k ∈ Finset.range (N + 1 + 1), a k := by
            exact (Finset.sum_range_succ a (N + 1)).symm



theorem antitoneWeight_sum_le_uniform
    (a b : Nat → Real) (N : Nat) (c : Real)
    (ha0 : ∀ k, k ≤ N → 0 ≤ a k)
    (hadec : ∀ k, k < N → a (k + 1) ≤ a k)
    (hb : ∀ k, k ≤ N →
      ∑ j ∈ Finset.range (k + 1), b j ≤ c * (k + 1 : Nat)) :
    (∑ k ∈ Finset.range (N + 1), a k * b k) ≤
      c * ∑ k ∈ Finset.range (N + 1), a k := by
  rw [sum_mul_eq_last_partial_add]
  calc
    a N * (∑ k ∈ Finset.range (N + 1), b k) +
        ∑ k ∈ Finset.range N,
          (a k - a (k + 1)) * (∑ j ∈ Finset.range (k + 1), b j) ≤
      a N * (c * (N + 1 : Nat)) +
        ∑ k ∈ Finset.range N,
          (a k - a (k + 1)) * (c * (k + 1 : Nat)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (hb N (le_refl _)) (ha0 N (le_refl _))
      · apply Finset.sum_le_sum
        intro k hk
        have hkN : k < N := Finset.mem_range.mp hk
        exact mul_le_mul_of_nonneg_left (hb k hkN.le)
          (sub_nonneg.mpr (hadec k hkN))
    _ = c * (a N * (N + 1 : Nat) +
        ∑ k ∈ Finset.range N,
          (a k - a (k + 1)) * (k + 1 : Nat)) := by
      rw [mul_add, Finset.mul_sum]
      apply congrArg₂ (· + ·) (by ring)
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = c * ∑ k ∈ Finset.range (N + 1), a k := by
      rw [last_mul_add_sum_diff_eq_sum]

private theorem one_div_sqrt_succ_le_twice_diff (k : Nat) :
    1 / Real.sqrt (k + 1 : Real) ≤
      2 * (Real.sqrt (k + 1 : Real) - Real.sqrt (k : Real)) := by
  have hk0 : 0 ≤ (k : Real) := by positivity
  have hk1 : 0 ≤ (k + 1 : Real) := by positivity
  have hA : 0 < Real.sqrt (k + 1 : Real) := Real.sqrt_pos.2 (by positivity)
  have hB : Real.sqrt (k : Real) ≤ Real.sqrt (k + 1 : Real) := by
    exact Real.sqrt_le_sqrt (by norm_num)
  have hprod :
      (Real.sqrt (k + 1 : Real) - Real.sqrt (k : Real)) *
        (Real.sqrt (k + 1 : Real) + Real.sqrt (k : Real)) = 1 := by
    rw [show (Real.sqrt (k + 1 : Real) - Real.sqrt (k : Real)) *
        (Real.sqrt (k + 1 : Real) + Real.sqrt (k : Real)) =
      Real.sqrt (k + 1 : Real) ^ 2 - Real.sqrt (k : Real) ^ 2 by ring]
    rw [Real.sq_sqrt hk1, Real.sq_sqrt hk0]
    norm_num
  apply (div_le_iff₀ hA).2
  calc
    1 = (Real.sqrt (k + 1 : Real) - Real.sqrt (k : Real)) *
        (Real.sqrt (k + 1 : Real) + Real.sqrt (k : Real)) := hprod.symm
    _ ≤ (Real.sqrt (k + 1 : Real) - Real.sqrt (k : Real)) *
        (2 * Real.sqrt (k + 1 : Real)) := by
      apply mul_le_mul_of_nonneg_left
      · linarith
      · linarith
    _ = 2 * (Real.sqrt (k + 1 : Real) - Real.sqrt (k : Real)) *
        Real.sqrt (k + 1 : Real) := by ring

theorem sum_one_div_sqrt_succ_le (N : Nat) :
    (∑ k ∈ Finset.range (N + 1), 1 / Real.sqrt (k + 1 : Real)) ≤
      2 * Real.sqrt (N + 1 : Real) := by
  calc
    _ ≤ ∑ k ∈ Finset.range (N + 1),
        2 * (Real.sqrt (k + 1 : Real) - Real.sqrt (k : Real)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact one_div_sqrt_succ_le_twice_diff k
    _ = 2 * ∑ k ∈ Finset.range (N + 1),
        (Real.sqrt (k + 1 : Real) - Real.sqrt (k : Real)) := by
      rw [Finset.mul_sum]
    _ = 2 * (Real.sqrt (N + 1 : Real) - Real.sqrt (0 : Real)) := by
      have htel := Finset.sum_range_sub
        (fun k : Nat => Real.sqrt (k : Real)) (N + 1)
      norm_num [Nat.cast_add, Nat.cast_one] at htel
      rw [Finset.sum_sub_distrib, htel]
      norm_num
    _ = 2 * Real.sqrt (N + 1 : Real) := by norm_num



theorem ballotWeight_firstHit_sum_le
    (rho N : Nat) (b : Nat → Real) (hρ : 0 < rho)
    (hN : N ≤ rho * rho)
    (hb : ∀ k, k ≤ N →
      ∑ j ∈ Finset.range (k + 1), b j ≤
        (k + 1 : Real) / (rho : Real) ^ 2) :
    (∑ k ∈ Finset.range (N + 1),
      (4 / Real.sqrt (k + 1 : Real)) * b k) ≤
        16 / (rho : Real) := by
  let a : Nat → Real := fun k => 4 / Real.sqrt (k + 1 : Real)
  let c : Real := 1 / (rho : Real) ^ 2
  have ha0 : ∀ k, k ≤ N → 0 ≤ a k := by
    intro k hk
    dsimp [a]
    positivity
  have hadec : ∀ k, k < N → a (k + 1) ≤ a k := by
    intro k hk
    dsimp [a]
    apply div_le_div_of_nonneg_left (by norm_num)
      (Real.sqrt_pos.2 (by positivity))
    exact Real.sqrt_le_sqrt (by norm_num)
  have hb' : ∀ k, k ≤ N →
      ∑ j ∈ Finset.range (k + 1), b j ≤ c * (k + 1 : Nat) := by
    intro k hk
    have h := hb k hk
    dsimp [c]
    calc
      _ ≤ (k + 1 : Real) / (rho : Real) ^ 2 := h
      _ = (1 / (rho : Real) ^ 2) * (k + 1 : Nat) := by
        push_cast
        ring
  have hmajor := antitoneWeight_sum_le_uniform a b N c ha0 hadec hb'
  have hsum :
      (∑ k ∈ Finset.range (N + 1), a k) ≤
        16 * (rho : Real) := by
    have hinv := sum_one_div_sqrt_succ_le N
    have hsqrt : Real.sqrt (N + 1 : Real) ≤ (rho + 1 : Nat) := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · have hNR : N + 1 ≤ (rho + 1) * (rho + 1) := by
          nlinarith
        have hNR' : (N + 1 : Real) ≤ ((rho + 1 : Nat) : Real) ^ 2 := by
          exact_mod_cast (show N + 1 ≤ (rho + 1) ^ 2 by
            simpa [pow_two] using hNR)
        exact hNR' 
    have hrho : (rho + 1 : Nat) ≤ 2 * rho := by omega
    have hsqrt' : Real.sqrt (N + 1 : Real) ≤ 2 * (rho : Real) := by
      exact le_trans hsqrt (by exact_mod_cast hrho)
    dsimp [a]
    calc
      (∑ k ∈ Finset.range (N + 1), 4 / Real.sqrt (k + 1 : Real)) =
          4 * ∑ k ∈ Finset.range (N + 1),
            1 / Real.sqrt (k + 1 : Real) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ 4 * (2 * Real.sqrt (N + 1 : Real)) :=
        mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ ≤ 16 * (rho : Real) := by nlinarith
  dsimp [a] at hmajor
  calc
    _ ≤ c * ∑ k ∈ Finset.range (N + 1), a k := hmajor
    _ ≤ c * (16 * (rho : Real)) := by
      apply mul_le_mul_of_nonneg_left hsum
      dsimp [c]
      positivity
    _ = 16 / (rho : Real) := by
      dsimp [c]
      have hρReal : (rho : Real) ≠ 0 := by positivity
      field_simp

private def isingLineCenteredSq (m : Nat) (q : IsingLineBox (2 * m)) : Real :=
  ((q.1 : Real) - (m : Real)) ^ 2

private theorem isingLineCenteredSq_step
    (m : Nat) (p : IsingLineBox (2 * m))
    (hp : ¬ isingLineBoxBoundary (2 * m) p) :
    isingLineCenteredSq m (isingLineWest (2 * m) p) +
        isingLineCenteredSq m (isingLineEast (2 * m) p hp) =
      2 * isingLineCenteredSq m p + 2 := by
  unfold isingLineCenteredSq isingLineWest isingLineEast
  have hp0 : 0 < p.1 := by
    unfold isingLineBoxBoundary at hp
    omega
  have hpR : p.1 < 2 * m := by
    unfold isingLineBoxBoundary at hp
    have hle := p.2
    omega
  push_cast
  rw [Nat.cast_sub hp0]
  ring

theorem isingLineStoppedMean_centeredSq_le
    (m t : Nat) (p : IsingLineBox (2 * m)) :
    isingLineStoppedMean (2 * m) t (isingLineCenteredSq m) p ≤
      isingLineCenteredSq m p + (t : Real) := by
  induction t generalizing p with
  | zero =>
      simp [isingLineStoppedMean, isingLineStoppedKernel]
  | succ t ih =>
      rw [isingLineStoppedMean_succ]
      by_cases hp : isingLineBoxBoundary (2 * m) p
      · rw [dif_pos hp]
        have h := ih p
        norm_num [Nat.cast_add, Nat.cast_one]
        linarith
      · rw [dif_neg hp]
        have hw := ih (isingLineWest (2 * m) p)
        have he := ih (isingLineEast (2 * m) p hp)
        have hs := isingLineCenteredSq_step m p hp
        norm_num [Nat.cast_add, Nat.cast_one]
        linarith



theorem isingLineStoppedKernel_center_boundary_le
    (m t : Nat) (hm : 0 < m) :
    isingLineStoppedKernel (2 * m) t ⟨m, by omega⟩ ⟨0, by omega⟩ +
        isingLineStoppedKernel (2 * m) t ⟨m, by omega⟩ ⟨2 * m, by omega⟩ ≤
      (t : Real) / (m : Real) ^ 2 := by
  have hmean := isingLineStoppedMean_centeredSq_le m t
    (⟨m, by omega⟩ : IsingLineBox (2 * m))
  have hmReal : 0 < (m : Real) ^ 2 := by positivity
  apply (le_div_iff₀ hmReal).2
  let center : IsingLineBox (2 * m) := ⟨m, by omega⟩
  let left : IsingLineBox (2 * m) := ⟨0, by omega⟩
  let right : IsingLineBox (2 * m) := ⟨2 * m, by omega⟩
  have hlr : left ≠ right := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [left, right] at hv
    omega
  have hboundary :
      (m : Real) ^ 2 *
          (isingLineStoppedKernel (2 * m) t center left +
            isingLineStoppedKernel (2 * m) t center right) ≤
        isingLineStoppedMean (2 * m) t (isingLineCenteredSq m) center := by
    calc
      _ = isingLineStoppedKernel (2 * m) t center left *
            isingLineCenteredSq m left +
          isingLineStoppedKernel (2 * m) t center right *
            isingLineCenteredSq m right := by
        simp [isingLineCenteredSq, left, right]
        ring
      _ = ∑ q ∈ {left, right},
          isingLineStoppedKernel (2 * m) t center q *
            isingLineCenteredSq m q := by
        rw [Finset.sum_pair hlr]
      _ ≤ ∑ q, isingLineStoppedKernel (2 * m) t center q *
          isingLineCenteredSq m q := by
        apply Finset.sum_le_univ_sum_of_nonneg
        intro q
        exact mul_nonneg (isingLineStoppedKernel_nonneg _ _ _ _)
          (sq_nonneg _)
      _ = _ := rfl
  have hmean' :
      isingLineStoppedMean (2 * m) t (isingLineCenteredSq m) center ≤
        (t : Real) := by
    simpa [center, isingLineCenteredSq] using hmean
  change (isingLineStoppedKernel (2 * m) t center left +
      isingLineStoppedKernel (2 * m) t center right) * (m : Real) ^ 2 ≤
        (t : Real)
  calc
    _ = (m : Real) ^ 2 *
        (isingLineStoppedKernel (2 * m) t center left +
          isingLineStoppedKernel (2 * m) t center right) := by ring
    _ ≤ isingLineStoppedMean (2 * m) t (isingLineCenteredSq m) center :=
      hboundary
    _ ≤ (t : Real) := hmean' 


private theorem isingLineChoiceRun_append (n : Nat) (p : IsingLineBox n)
    (a b : List Bool) :
    isingLineChoiceRun n p (a ++ b) =
      isingLineChoiceRun n (isingLineChoiceRun n p a) b := by
  induction a generalizing p with
  | nil => rfl
  | cons x a ih =>
      simp only [List.cons_append, isingLineChoiceRun]
      exact ih (isingLineChoiceNext n p x)

private theorem isingLineChoiceRun_of_boundary
    (n : Nat) (p : IsingLineBox n) (hp : isingLineBoxBoundary n p)
    (bs : List Bool) : isingLineChoiceRun n p bs = p := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [isingLineChoiceRun, isingLeapfrogChoiceNext]
      rw [show isingLineChoiceNext n p b = p by simp [isingLineChoiceNext, hp]]
      exact ih



def IsingLineFirstBoundaryFamily (m k : Nat) :=
  {ys : List Bool // ys.length = k ∧
    isingLineBoxBoundary (2 * m)
      (isingLineChoiceRun (2 * m) ⟨m, by omega⟩ ys) ∧
    ∀ j, j < k → ¬ isingLineBoxBoundary (2 * m)
      (isingLineChoiceRun (2 * m) ⟨m, by omega⟩ (ys.take j))}

noncomputable instance isingLineFirstBoundaryFamily_finite (m k : Nat) :
    Finite (IsingLineFirstBoundaryFamily m k) := by
  letI : Fintype {ys : List Bool // ys.length = k} :=
    (List.finite_length_eq Bool k).fintype
  exact Finite.of_injective
    (fun w : IsingLineFirstBoundaryFamily m k =>
      (⟨w.1, w.2.1⟩ : {ys : List Bool // ys.length = k}))
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg
        (fun z : {ys : List Bool // ys.length = k} => z.1) h)

private def IsingLineFirstBoundaryExtension (m K : Nat) :=
  Σ j : Fin (K + 1),
    IsingLineFirstBoundaryFamily m j ×
      {tail : List Bool // tail.length = K - j}


private def lineFirstBoundaryExtend (m K : Nat) :
    IsingLineFirstBoundaryExtension m K →
      {ys : List Bool // ys.length = K ∧
        isingLineBoxBoundary (2 * m)
          (isingLineChoiceRun (2 * m) ⟨m, by omega⟩ ys)} := fun w =>
  ⟨w.2.1.1 ++ w.2.2.1, by
      rw [List.length_append, w.2.1.2.1, w.2.2.2]
      omega,
    by
      rw [isingLineChoiceRun_append]
      rw [isingLineChoiceRun_of_boundary (2 * m) _ w.2.1.2.2.1]
      exact w.2.1.2.2.1⟩

private theorem lineFirstBoundaryExtend_injective (m K : Nat) :
    Function.Injective (lineFirstBoundaryExtend m K) := by
  rintro ⟨aj, ap, atail⟩ ⟨bj, bp, btail⟩ hab
  have hfull : ap.1 ++ atail.1 = bp.1 ++ btail.1 :=
    congrArg Subtype.val hab
  have hj : (aj : Nat) = bj := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hbavoid := bp.2.2.2 (aj : Nat) hlt
      apply hbavoid
      have ht := congrArg (fun z : List Bool => z.take (aj : Nat)) hfull
      change (ap.1 ++ atail.1).take (aj : Nat) =
        (bp.1 ++ btail.1).take (aj : Nat) at ht
      have haTake : (ap.1 ++ atail.1).take (aj : Nat) = ap.1 := by
        simpa [ap.2.1] using (List.take_left (l₁ := ap.1) (l₂ := atail.1))
      have hbTake : (bp.1 ++ btail.1).take (aj : Nat) = bp.1.take (aj : Nat) := by
        apply List.take_append_of_le_length
        rw [bp.2.1]
        omega
      rw [haTake, hbTake] at ht
      rw [← ht]
      exact ap.2.2.1
    · have haavoid := ap.2.2.2 (bj : Nat) hgt
      apply haavoid
      have ht := congrArg (fun z : List Bool => z.take (bj : Nat)) hfull
      change (ap.1 ++ atail.1).take (bj : Nat) =
        (bp.1 ++ btail.1).take (bj : Nat) at ht
      have haTake : (ap.1 ++ atail.1).take (bj : Nat) = ap.1.take (bj : Nat) := by
        apply List.take_append_of_le_length
        rw [ap.2.1]
        omega
      have hbTake : (bp.1 ++ btail.1).take (bj : Nat) = bp.1 := by
        simpa [bp.2.1] using (List.take_left (l₁ := bp.1) (l₂ := btail.1))
      rw [haTake, hbTake] at ht
      rw [ht]
      exact bp.2.2.1
  have hjSubtype : aj = bj := Fin.ext hj
  subst bj
  have hpref : ap.1 = bp.1 := by
    have ht := congrArg (fun z : List Bool => z.take (aj : Nat)) hfull
    simpa [ap.2.1, bp.2.1] using ht
  have htail : atail.1 = btail.1 := by
    have hd := congrArg (fun z : List Bool => z.drop (aj : Nat)) hfull
    simpa [ap.2.1, bp.2.1] using hd
  have hap : ap = bp := Subtype.ext hpref
  subst bp
  have hat : atail = btail := Subtype.ext htail
  subst btail
  rfl

noncomputable instance isingLineFirstBoundaryExtension_finite (m K : Nat) :
    Finite (IsingLineFirstBoundaryExtension m K) := by
  letI : Fintype {ys : List Bool // ys.length = K} :=
    (List.finite_length_eq Bool K).fintype
  exact Finite.of_injective
    (fun w : IsingLineFirstBoundaryExtension m K =>
      (⟨(lineFirstBoundaryExtend m K w).1,
        (lineFirstBoundaryExtend m K w).2.1⟩ :
        {ys : List Bool // ys.length = K}))
    (by
      intro a b h
      apply lineFirstBoundaryExtend_injective m K
      apply Subtype.ext
      exact congrArg
        (fun z : {ys : List Bool // ys.length = K} => z.1) h)

private def IsingLineBoundaryStringFamily (m K : Nat) :=
  {ys : List Bool // ys.length = K ∧
    isingLineBoxBoundary (2 * m)
      (isingLineChoiceRun (2 * m) ⟨m, by omega⟩ ys)}

noncomputable instance isingLineBoundaryStringFamily_finite (m K : Nat) :
    Finite (IsingLineBoundaryStringFamily m K) := by
  letI : Fintype {ys : List Bool // ys.length = K} :=
    (List.finite_length_eq Bool K).fintype
  exact Finite.of_injective
    (fun w : IsingLineBoundaryStringFamily m K =>
      (⟨w.1, w.2.1⟩ : {ys : List Bool // ys.length = K}))
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg
        (fun z : {ys : List Bool // ys.length = K} => z.1) h)

private def lineBoundaryStringToSum (m K : Nat) (hm : 0 < m) :
    IsingLineBoundaryStringFamily m K →
      IsingLineChoicePathFamily (2 * m) K ⟨m, by omega⟩ ⟨0, by omega⟩ ⊕
        IsingLineChoicePathFamily (2 * m) K ⟨m, by omega⟩
          ⟨2 * m, by omega⟩ := fun w => by
  by_cases hzero : (isingLineChoiceRun (2 * m) ⟨m, by omega⟩ w.1).1 = 0
  · exact Sum.inl ⟨w.1, w.2.1, Fin.ext hzero⟩
  · exact Sum.inr ⟨w.1, w.2.1, Fin.ext (by
      have hb := w.2.2
      unfold isingLineBoxBoundary at hb
      rcases hb with h | h
      · exact (hzero h).elim
      · exact h)⟩

private def lineBoundarySumToString (m K : Nat) :
    IsingLineChoicePathFamily (2 * m) K ⟨m, by omega⟩ ⟨0, by omega⟩ ⊕
        IsingLineChoicePathFamily (2 * m) K ⟨m, by omega⟩
          ⟨2 * m, by omega⟩ →
      IsingLineBoundaryStringFamily m K
  | Sum.inl w => ⟨w.1, w.2.1, by
      unfold isingLineBoxBoundary
      left
      simpa [w.2.2]⟩
  | Sum.inr w => ⟨w.1, w.2.1, by
      unfold isingLineBoxBoundary
      right
      simpa [w.2.2]⟩

private theorem lineBoundaryString_leftInverse (m K : Nat) (hm : 0 < m) :
    Function.LeftInverse (lineBoundarySumToString m K)
      (lineBoundaryStringToSum m K hm) := by
  intro w
  unfold lineBoundaryStringToSum
  by_cases hzero : (isingLineChoiceRun (2 * m) ⟨m, by omega⟩ w.1).1 = 0
  · rw [dif_pos hzero]
    rfl
  · rw [dif_neg hzero]
    rfl

private theorem lineBoundaryString_rightInverse (m K : Nat) (hm : 0 < m) :
    Function.RightInverse (lineBoundarySumToString m K)
      (lineBoundaryStringToSum m K hm) := by
  intro w
  cases w with
  | inl w =>
      unfold lineBoundarySumToString lineBoundaryStringToSum
      have hzero : (isingLineChoiceRun (2 * m) ⟨m, by omega⟩ w.1).1 = 0 := by
        simp [w.2.2]
      rw [dif_pos hzero]
      apply congrArg Sum.inl
      apply Subtype.ext
      rfl
  | inr w =>
      unfold lineBoundarySumToString lineBoundaryStringToSum
      have hne : (isingLineChoiceRun (2 * m) ⟨m, by omega⟩ w.1).1 ≠ 0 := by
        simp [w.2.2]
        omega
      rw [dif_neg hne]
      apply congrArg Sum.inr
      apply Subtype.ext
      rfl

private def lineBoundaryStringEquivSum (m K : Nat) (hm : 0 < m) :
    IsingLineBoundaryStringFamily m K ≃
      IsingLineChoicePathFamily (2 * m) K ⟨m, by omega⟩ ⟨0, by omega⟩ ⊕
        IsingLineChoicePathFamily (2 * m) K ⟨m, by omega⟩
          ⟨2 * m, by omega⟩ where
  toFun := lineBoundaryStringToSum m K hm
  invFun := lineBoundarySumToString m K
  left_inv := lineBoundaryString_leftInverse m K hm
  right_inv := lineBoundaryString_rightInverse m K hm

theorem lineFirstBoundary_partial_weight_le
    (m K : Nat) (hm : 0 < m) :
    (∑ j ∈ Finset.range (K + 1),
      (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) /
        (2 : Real) ^ j) ≤ (K : Real) / (m : Real) ^ 2 := by
  have hcard : Nat.card (IsingLineFirstBoundaryExtension m K) ≤
      Nat.card (IsingLineBoundaryStringFamily m K) :=
    Nat.card_le_card_of_injective (lineFirstBoundaryExtend m K)
      (lineFirstBoundaryExtend_injective m K)
  have hext : Nat.card (IsingLineFirstBoundaryExtension m K) =
      ∑ j : Fin (K + 1),
        Nat.card (IsingLineFirstBoundaryFamily m j) * 2 ^ (K - j) := by
    change Nat.card (Σ j : Fin (K + 1),
      IsingLineFirstBoundaryFamily m j ×
        {tail : List Bool // tail.length = K - j}) = _
    rw [Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.card_prod]
    congr 1
    change Nat.card (List.Vector Bool (K - (j : Nat))) = 2 ^ (K - (j : Nat))
    rw [Nat.card_congr (Equiv.vectorEquivFin Bool (K - (j : Nat))),
      Nat.card_eq_fintype_card, Fintype.card_fun]
    simp
  have hboundary : Nat.card (IsingLineBoundaryStringFamily m K) =
      Nat.card (IsingLineChoicePathFamily (2 * m) K
          ⟨m, by omega⟩ ⟨0, by omega⟩) +
        Nat.card (IsingLineChoicePathFamily (2 * m) K
          ⟨m, by omega⟩ ⟨2 * m, by omega⟩) := by
    rw [Nat.card_congr (lineBoundaryStringEquivSum m K hm), Nat.card_sum]
  have hweightedNat :
      (∑ j : Fin (K + 1),
        Nat.card (IsingLineFirstBoundaryFamily m j) * 2 ^ (K - j)) ≤
          Nat.card (IsingLineBoundaryStringFamily m K) := by
    rw [← hext]
    exact hcard
  have hweightedReal :
      (∑ j : Fin (K + 1),
        (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) *
          (2 : Real) ^ (K - j)) ≤
          (Nat.card (IsingLineBoundaryStringFamily m K) : Real) := by
    exact_mod_cast hweightedNat
  rw [Fin.sum_univ_eq_sum_range
    (fun j : Nat => (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) *
      (2 : Real) ^ (K - j)) (K + 1)] at hweightedReal
  have htwo : 0 < (2 : Real) ^ K := by positivity
  have hdiv := div_le_div_of_nonneg_right hweightedReal htwo.le
  have hcardReal :
      (∑ j ∈ Finset.range (K + 1),
        (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) /
          (2 : Real) ^ j) ≤
        ((Nat.card (IsingLineBoundaryStringFamily m K) : Real) /
          (2 : Real) ^ K) := by
    calc
      (∑ j ∈ Finset.range (K + 1),
        (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) /
          (2 : Real) ^ j) =
        (∑ j ∈ Finset.range (K + 1),
          (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) *
            (2 : Real) ^ (K - j)) / (2 : Real) ^ K := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j hj
        have hjK : j ≤ K := by
          have := Finset.mem_range.mp hj
          omega
        have hpow : (2 : Real) ^ K =
            (2 : Real) ^ j * (2 : Real) ^ (K - j) := by
          calc
            (2 : Real) ^ K = (2 : Real) ^ (j + (K - j)) := by
              congr 1
              omega
            _ = _ := pow_add _ _ _
        calc
          (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) /
              (2 : Real) ^ j =
            ((Nat.card (IsingLineFirstBoundaryFamily m j) : Real) *
              (2 : Real) ^ (K - j)) /
                ((2 : Real) ^ j * (2 : Real) ^ (K - j)) :=
              (mul_div_mul_right _ _ (by positivity)).symm
          _ = ((Nat.card (IsingLineFirstBoundaryFamily m j) : Real) *
              (2 : Real) ^ (K - j)) / (2 : Real) ^ K := by
            rw [hpow]
      _ ≤ _ := hdiv
  calc
    _ ≤ (Nat.card (IsingLineBoundaryStringFamily m K) : Real) /
          (2 : Real) ^ K := hcardReal
    _ = isingLineStoppedKernel (2 * m) K ⟨m, by omega⟩ ⟨0, by omega⟩ +
        isingLineStoppedKernel (2 * m) K ⟨m, by omega⟩
          ⟨2 * m, by omega⟩ := by
      rw [hboundary]
      push_cast
      rw [add_div]
      rw [isingLineStoppedKernel_eq_natCard_choicePath_div,
        isingLineStoppedKernel_eq_natCard_choicePath_div]
    _ ≤ (K : Real) / (m : Real) ^ 2 :=
      isingLineStoppedKernel_center_boundary_le m K hm




def IsingTransverseRaceWitnessFamily (m t : Nat) (level : Int) :=
  Σ j : Fin (t + 1),
    IsingHorizontalNoHitFamily j (level - 1) level ×
      IsingLineFirstBoundaryFamily m j ×
        {tail : List (Bool × Bool) // tail.length = t - j}

noncomputable instance isingTransverseRaceWitnessFamily_finite
    (m t : Nat) (level : Int) :
    Finite (IsingTransverseRaceWitnessFamily m t level) := by
  letI (j : Fin (t + 1)) :
      Fintype (IsingHorizontalNoHitFamily j (level - 1) level) :=
    Fintype.ofFinite _
  letI (j : Fin (t + 1)) :
      Fintype (IsingLineFirstBoundaryFamily m j) := Fintype.ofFinite _
  letI (j : Fin (t + 1)) :
      Fintype {tail : List (Bool × Bool) // tail.length = t - j} :=
    (List.finite_length_eq (Bool × Bool) (t - j)).fintype
  change Finite (Σ j : Fin (t + 1),
    IsingHorizontalNoHitFamily j (level - 1) level ×
      IsingLineFirstBoundaryFamily m j ×
        {tail : List (Bool × Bool) // tail.length = t - j})
  infer_instance

private theorem sqrt_ballot_le_four_div_sqrt (k : Nat) :
    2 * Real.sqrt (2 / (k + 1 : Real)) ≤
      4 / Real.sqrt (k + 1 : Real) := by
  have hs : 0 < Real.sqrt (k + 1 : Real) := Real.sqrt_pos.2 (by positivity)
  have hs2 : Real.sqrt (2 : Real) ≤ 2 := by
    rw [Real.sqrt_le_iff]
    norm_num
  rw [Real.sqrt_div (by positivity)]
  rw [show 2 * (Real.sqrt 2 / Real.sqrt (k + 1 : Real)) =
      (2 * Real.sqrt 2) / Real.sqrt (k + 1 : Real) by ring]
  exact (div_le_div_iff_of_pos_right hs).2 (by nlinarith)


theorem transverseRaceWitness_diffusive_weight_le
    (rho m : Nat) (level : Int) (hρ : 0 < rho) (hm : rho ≤ m) :
    Nat.card (IsingTransverseRaceWitnessFamily m (rho * rho) level) /
        (4 : Real) ^ (rho * rho) ≤ 16 / (rho : Real) := by
  let T := rho * rho
  let b : Nat → Real := fun j =>
    Nat.card (IsingLineFirstBoundaryFamily m j) / (2 : Real) ^ j
  have hcard : Nat.card (IsingTransverseRaceWitnessFamily m T level) =
      ∑ j : Fin (T + 1),
        Nat.card (IsingHorizontalNoHitFamily j (level - 1) level) *
          Nat.card (IsingLineFirstBoundaryFamily m j) * 4 ^ (T - j) := by
    letI (j : Fin (T + 1)) :
        Fintype (IsingHorizontalNoHitFamily j (level - 1) level) :=
      Fintype.ofFinite _
    letI (j : Fin (T + 1)) :
        Fintype (IsingLineFirstBoundaryFamily m j) := Fintype.ofFinite _
    letI (j : Fin (T + 1)) :
        Fintype {tail : List (Bool × Bool) // tail.length = T - j} :=
      (List.finite_length_eq (Bool × Bool) (T - j)).fintype
    change Nat.card (Σ j : Fin (T + 1),
      IsingHorizontalNoHitFamily j (level - 1) level ×
        IsingLineFirstBoundaryFamily m j ×
          {tail : List (Bool × Bool) // tail.length = T - j}) = _
    rw [Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro j hj
    have htail : Nat.card
        {tail : List (Bool × Bool) // tail.length = T - (j : Nat)} =
        4 ^ (T - (j : Nat)) := by
      change Nat.card (List.Vector (Bool × Bool) (T - (j : Nat))) =
        4 ^ (T - (j : Nat))
      rw [Nat.card_congr
          (Equiv.vectorEquivFin (Bool × Bool) (T - (j : Nat))),
        Nat.card_eq_fintype_card, Fintype.card_fun]
      norm_num
    calc
      Nat.card (IsingHorizontalNoHitFamily j (level - 1) level ×
          IsingLineFirstBoundaryFamily m j ×
            {tail : List (Bool × Bool) // tail.length = T - j}) =
        Nat.card (IsingHorizontalNoHitFamily j (level - 1) level) *
          (Nat.card (IsingLineFirstBoundaryFamily m j) *
            Nat.card {tail : List (Bool × Bool) // tail.length = T - j}) := by
          rw [Nat.card_prod, Nat.card_prod]
      _ = _ := by rw [htail]; ring
  have hmass :
      Nat.card (IsingTransverseRaceWitnessFamily m T level) /
          (4 : Real) ^ T =
        ∑ j ∈ Finset.range (T + 1),
          (Nat.card (IsingHorizontalNoHitFamily j (level - 1) level) /
              (2 : Real) ^ j) * b j := by
    rw [hcard]
    push_cast
    rw [Fin.sum_univ_eq_sum_range
      (fun j : Nat =>
        (Nat.card (IsingHorizontalNoHitFamily j (level - 1) level) : Real) *
          (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) *
            (4 : Real) ^ (T - j)) (T + 1)]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    have hjT : j ≤ T := by
      have := Finset.mem_range.mp hj
      omega
    have hfour : (4 : Real) ^ T =
        (4 : Real) ^ j * (4 : Real) ^ (T - j) := by
      calc
        (4 : Real) ^ T = (4 : Real) ^ (j + (T - j)) := by
          congr 1
          omega
        _ = _ := pow_add _ _ _
    have htwo : (4 : Real) ^ j = (2 : Real) ^ j * (2 : Real) ^ j := by
      rw [show (4 : Real) = 2 * 2 by norm_num, mul_pow]
    dsimp [b]
    rw [hfour, htwo]
    field_simp
  rw [show rho * rho = T by rfl, hmass]
  have hpoint (j : Nat) :
      Nat.card (IsingHorizontalNoHitFamily j (level - 1) level) /
          (2 : Real) ^ j ≤ 4 / Real.sqrt (j + 1 : Real) := by
    exact le_trans (horizontalNoHit_weight_le_sqrt j level)
      (sqrt_ballot_le_four_div_sqrt j)
  calc
    (∑ j ∈ Finset.range (T + 1),
      (Nat.card (IsingHorizontalNoHitFamily j (level - 1) level) /
        (2 : Real) ^ j) * b j) ≤
        ∑ j ∈ Finset.range (T + 1),
          (4 / Real.sqrt (j + 1 : Real)) * b j := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right (hpoint j)
      dsimp [b]
      positivity
    _ ≤ 16 / (rho : Real) := by
      apply ballotWeight_firstHit_sum_le rho T b hρ
      · dsimp [T]
        exact le_rfl
      · intro k hk
        have hfirst := lineFirstBoundary_partial_weight_le m k (lt_of_lt_of_le hρ hm)
        have hmReal : (rho : Real) ^ 2 ≤ (m : Real) ^ 2 := by
          nlinarith [show (rho : Real) ≤ (m : Real) by exact_mod_cast hm]
        calc
          (∑ j ∈ Finset.range (k + 1), b j) ≤
              (k : Real) / (m : Real) ^ 2 := by
            simpa [b] using hfirst
          _ ≤ (k + 1 : Real) / (rho : Real) ^ 2 := by
            apply div_le_div₀
            · positivity
            · norm_num
            · positivity
            · exact hmReal




def IsingLeapfrogHorizontalEscapeFamily (n t : Nat) :=
  {w : IsingLeapfrogChoiceStringFamily t //
    isingLineChoiceRun n ⟨n - 1, by omega⟩ (w.1.map Prod.fst) =
      (⟨0, by omega⟩ : IsingLineBox n)}

noncomputable instance isingLeapfrogHorizontalEscapeFamily_finite
    (n t : Nat) : Finite (IsingLeapfrogHorizontalEscapeFamily n t) := by
  exact Finite.of_injective
    (fun w : IsingLeapfrogHorizontalEscapeFamily n t => w.1)
    Subtype.val_injective

private def horizontalEscapeProjection (n t : Nat) :
    IsingLeapfrogHorizontalEscapeFamily n t →
      IsingLineChoicePathFamily n t ⟨n - 1, by omega⟩ ⟨0, by omega⟩ ×
        {ys : List Bool // ys.length = t} := fun w =>
  ⟨⟨w.1.1.map Prod.fst, by simpa using w.1.2, w.2⟩,
    ⟨w.1.1.map Prod.snd, by simpa using w.1.2⟩⟩

private theorem horizontalEscapeProjection_injective (n t : Nat) :
    Function.Injective (horizontalEscapeProjection n t) := by
  intro a b h
  have hx : a.1.1.map Prod.fst = b.1.1.map Prod.fst :=
    congrArg (fun z => z.1.1) h
  have hy : a.1.1.map Prod.snd = b.1.1.map Prod.snd :=
    congrArg (fun z => z.2.1) h
  apply Subtype.ext
  apply Subtype.ext
  exact prodBits_injective_full hx hy

theorem horizontalEscape_weight_le_inv (n t : Nat) (hn : 0 < n) :
    Nat.card (IsingLeapfrogHorizontalEscapeFamily n t) /
        (4 : Real) ^ t ≤ 1 / (n : Real) := by
  have hcard : Nat.card (IsingLeapfrogHorizontalEscapeFamily n t) ≤
      Nat.card (IsingLineChoicePathFamily n t
        ⟨n - 1, by omega⟩ ⟨0, by omega⟩) * 2 ^ t := by
    calc
      _ ≤ Nat.card (IsingLineChoicePathFamily n t
          ⟨n - 1, by omega⟩ ⟨0, by omega⟩ ×
          {ys : List Bool // ys.length = t}) :=
        Nat.card_le_card_of_injective (horizontalEscapeProjection n t)
          (horizontalEscapeProjection_injective n t)
      _ = _ := by
        rw [Nat.card_prod]
        congr 1
        change Nat.card (List.Vector Bool t) = 2 ^ t
        rw [Nat.card_congr (Equiv.vectorEquivFin Bool t),
          Nat.card_eq_fintype_card, Fintype.card_fun]
        simp
  have hcardReal :
      (Nat.card (IsingLeapfrogHorizontalEscapeFamily n t) : Real) ≤
        Nat.card (IsingLineChoicePathFamily n t
          ⟨n - 1, by omega⟩ ⟨0, by omega⟩) * (2 : Real) ^ t := by
    exact_mod_cast hcard
  have hfour : 0 < (4 : Real) ^ t := by positivity
  have hpow : (4 : Real) ^ t = (2 : Real) ^ t * (2 : Real) ^ t := by
    rw [show (4 : Real) = 2 * 2 by norm_num, mul_pow]
  calc
    _ ≤ (Nat.card (IsingLineChoicePathFamily n t
          ⟨n - 1, by omega⟩ ⟨0, by omega⟩) * (2 : Real) ^ t) /
          (4 : Real) ^ t := div_le_div_of_nonneg_right hcardReal hfour.le
    _ = Nat.card (IsingLineChoicePathFamily n t
          ⟨n - 1, by omega⟩ ⟨0, by omega⟩) / (2 : Real) ^ t := by
      rw [hpow]
      field_simp
    _ = isingLineStoppedKernel n t ⟨n - 1, by omega⟩ ⟨0, by omega⟩ := by
      rw [isingLineStoppedKernel_eq_natCard_choicePath_div]
    _ ≤ 1 / (n : Real) := isingLineStoppedKernel_left_of_rightNeighbor n t hn




theorem choiceNoHitAll_diffusive_weight_le
    (rho : Nat) (level : Int) (hρ : 0 < rho) :
    Nat.card (IsingLeapfrogChoiceNoHitAll (rho * rho) (level - 1) level) /
        (4 : Real) ^ (rho * rho) ≤ 4 / (rho : Real) := by
  have hcard := natCard_choiceNoHitAll_le_horizontal_mul_pow
    (rho * rho) (level - 1) level
  have hcardReal :
      (Nat.card (IsingLeapfrogChoiceNoHitAll (rho * rho)
          (level - 1) level) : Real) ≤
        Nat.card (IsingHorizontalNoHitFamily (rho * rho)
          (level - 1) level) * (2 : Real) ^ (rho * rho) := by
    exact_mod_cast hcard
  have hfour : 0 < (4 : Real) ^ (rho * rho) := by positivity
  have hpow : (4 : Real) ^ (rho * rho) =
      (2 : Real) ^ (rho * rho) * (2 : Real) ^ (rho * rho) := by
    rw [show (4 : Real) = 2 * 2 by norm_num, mul_pow]
  calc
    _ ≤ (Nat.card (IsingHorizontalNoHitFamily (rho * rho)
          (level - 1) level) * (2 : Real) ^ (rho * rho)) /
          (4 : Real) ^ (rho * rho) :=
      div_le_div_of_nonneg_right hcardReal hfour.le
    _ = Nat.card (IsingHorizontalNoHitFamily (rho * rho)
          (level - 1) level) / (2 : Real) ^ (rho * rho) := by
      rw [hpow]
      field_simp
    _ ≤ 4 / (rho : Real) :=
      horizontalNoHit_diffusive_weight_le rho level hρ



theorem isingLeapfrogChoiceRun_append_full
    (R : Nat) (p : IsingLeapfrogBox R) (a b : List (Bool × Bool)) :
    isingLeapfrogChoiceRun R p (a ++ b) =
      isingLeapfrogChoiceRun R (isingLeapfrogChoiceRun R p a) b := by
  induction a generalizing p with
  | nil => rfl
  | cons x a ih =>
      simp only [List.cons_append, isingLeapfrogChoiceRun]
      exact ih (isingLeapfrogChoiceNext R p x)

private theorem isingLeapfrogBoxInt_choiceNext_full
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


def IsingLeapfrogChoiceExecValid (R : Nat) (p : IsingLeapfrogBox R)
    (bs : List (Bool × Bool)) : Prop :=
  ∀ j, j < bs.length →
    ¬ isingLeapfrogBoxBoundary R
      (isingLeapfrogChoiceRun R p (bs.take j))

private theorem choiceExecValid_tail
    (R : Nat) (p : IsingLeapfrogBox R) (b : Bool × Bool)
    (bs : List (Bool × Bool))
    (h : IsingLeapfrogChoiceExecValid R p (b :: bs)) :
    IsingLeapfrogChoiceExecValid R (isingLeapfrogChoiceNext R p b) bs := by
  intro j hj
  have hmain := h (j + 1) (by simpa using hj)
  simpa [isingLeapfrogChoiceRun, List.take_succ_cons] using hmain

private theorem choiceExecValid_start
    (R : Nat) (p : IsingLeapfrogBox R) (b : Bool × Bool)
    (bs : List (Bool × Bool))
    (h : IsingLeapfrogChoiceExecValid R p (b :: bs)) :
    ¬ isingLeapfrogBoxBoundary R p := by
  have h0 := h 0 (by simp)
  simpa [isingLeapfrogChoiceRun] using h0

theorem choiceExecValid_run_boxInt_eq_endpoint
    (R : Nat) (p : IsingLeapfrogBox R) (bs : List (Bool × Bool))
    (h : IsingLeapfrogChoiceExecValid R p bs) :
    isingLeapfrogBoxInt (isingLeapfrogChoiceRun R p bs) =
      isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceSteps bs) := by
  induction bs generalizing p with
  | nil =>
      simp [isingLeapfrogChoiceRun, isingLeapfrogChoiceSteps,
        isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement]
  | cons b bs ih =>
      rw [show isingLeapfrogChoiceRun R p (b :: bs) =
          isingLeapfrogChoiceRun R (isingLeapfrogChoiceNext R p b) bs by rfl]
      rw [ih (isingLeapfrogChoiceNext R p b)
        (choiceExecValid_tail R p b bs h)]
      rw [isingLeapfrogBoxInt_choiceNext_full R p b
        (choiceExecValid_start R p b bs h)]
      unfold isingLeapfrogChoiceSteps isingDiagonalWalkEndpoint
        isingDiagonalWalkNext isingDiagonalWalkDisplacement
      apply Prod.ext <;> simp <;> ring

private theorem couplingChoiceTransform_drop_of_some
    (t : Nat) (start : Int × Int) (level : Int)
    (w : IsingLeapfrogChoiceStringFamily t)
    (split : IsingDiagonalWalkHitSplit start level)
    (hsplit : isingDiagonalWalkFirstHitSplit? start level
      (isingLeapfrogChoiceSteps w.1) = some split) :
    (isingLeapfrogCouplingChoiceTransform t start level w).1.drop
        split.before.length = w.1.drop split.before.length := by
  have hwencode : isingLeapfrogEncodeSteps
      (isingLeapfrogChoiceSteps w.1) = w.1 := encodeSteps_choiceSteps w.1
  unfold isingLeapfrogCouplingChoiceTransform
  dsimp only
  unfold isingDiagonalWalkCouplingReflectSteps
  rw [hsplit]
  rw [← firstHitSplit_steps hsplit] at hwencode
  unfold isingLeapfrogEncodeSteps at hwencode ⊢
  rw [← hwencode]
  simp [IsingDiagonalWalkHitSplit.steps, reflectPrefix]

theorem couplingChoiceTransform_take_steps_of_some
    (t : Nat) (start : Int × Int) (level : Int)
    (w : IsingLeapfrogChoiceStringFamily t)
    (split : IsingDiagonalWalkHitSplit start level)
    (hsplit : isingDiagonalWalkFirstHitSplit? start level
      (isingLeapfrogChoiceSteps w.1) = some split) :
    isingLeapfrogChoiceSteps
      ((isingLeapfrogCouplingChoiceTransform t start level w).1.take
        split.before.length) = split.before.map reflectIncrement := by
  rw [isingLeapfrogChoiceSteps, List.map_take]
  have hsteps : isingLeapfrogChoiceSteps
      (isingLeapfrogCouplingChoiceTransform t start level w).1 =
      isingDiagonalWalkCouplingReflectSteps start level
        (isingLeapfrogChoiceSteps w.1) := by
    exact choiceSteps_encodeSteps_of_valid _
      (couplingReflectSteps_valid start level _
        (isingLeapfrogChoiceSteps_valid w.1))
  change (isingLeapfrogChoiceSteps
    (isingLeapfrogCouplingChoiceTransform t start level w).1).take
      split.before.length = split.before.map reflectIncrement
  rw [hsteps]
  unfold isingDiagonalWalkCouplingReflectSteps
  rw [hsplit]
  simp [IsingDiagonalWalkHitSplit.steps, reflectPrefix]

private theorem choiceSteps_take_of_split
    (t : Nat) (start : Int × Int) (level : Int)
    (w : IsingLeapfrogChoiceStringFamily t)
    (split : IsingDiagonalWalkHitSplit start level)
    (hsplit : isingDiagonalWalkFirstHitSplit? start level
      (isingLeapfrogChoiceSteps w.1) = some split) :
    isingLeapfrogChoiceSteps (w.1.take split.before.length) = split.before := by
  have hs := firstHitSplit_steps hsplit
  have ht := congrArg (fun z : List (Int × Int) =>
    z.take split.before.length) hs
  simpa [IsingDiagonalWalkHitSplit.steps, isingLeapfrogChoiceSteps,
    List.map_take] using ht.symm



theorem stoppedCoupling_endpoints_eq_of_execValid_to_hit
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p))
    (w : IsingLeapfrogChoiceStringFamily t)
    (split : IsingDiagonalWalkHitSplit (isingLeapfrogBoxInt p) level)
    (hsplit : isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p) level
      (isingLeapfrogChoiceSteps w.1) = some split)
    (hsource : IsingLeapfrogChoiceExecValid R p
      (w.1.take split.before.length))
    (hmirrorValid : IsingLeapfrogChoiceExecValid R p'
      ((isingLeapfrogCouplingChoiceTransform t (isingLeapfrogBoxInt p)
        level w).1.take split.before.length)) :
    isingLeapfrogChoiceRun R p w.1 =
      isingLeapfrogChoiceRun R p'
        (isingLeapfrogCouplingChoiceTransform t
          (isingLeapfrogBoxInt p) level w).1 := by
  let w' := isingLeapfrogCouplingChoiceTransform t
    (isingLeapfrogBoxInt p) level w
  let k := split.before.length
  have hsourceSteps := choiceSteps_take_of_split t (isingLeapfrogBoxInt p)
    level w split hsplit
  have hmirrorSteps := couplingChoiceTransform_take_steps_of_some t
    (isingLeapfrogBoxInt p) level w split hsplit
  have hsourceEnd := choiceExecValid_run_boxInt_eq_endpoint R p
    (w.1.take k) hsource
  have hmirrorEnd := choiceExecValid_run_boxInt_eq_endpoint R p'
    (w'.1.take k) hmirrorValid
  have hfreeEnd : isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
      split.before =
    isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p')
      (split.before.map reflectIncrement) := by
    rw [hmirror]
    apply Prod.ext
    · have h := reflectPrefix_endpoint_take_fst_of_le_before split k (le_refl _)
      have hhit : (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
          split.before).1 = level := by
        simpa [isingDiagonalWalkEndpoint] using split.hit
      have h' : (isingDiagonalWalkEndpoint
          (reflectedEndpoint level (isingLeapfrogBoxInt p))
            (split.before.map reflectIncrement)).1 =
          2 * level - (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
            split.before).1 := by
        simpa [k, IsingDiagonalWalkHitSplit.steps, reflectPrefix] using h
      rw [h']
      omega
    · have h := reflectPrefix_endpoint_take_snd_of_le_before split k (le_refl _)
      simpa [k, IsingDiagonalWalkHitSplit.steps, reflectPrefix] using h.symm
  have hrunPrefix : isingLeapfrogChoiceRun R p (w.1.take k) =
      isingLeapfrogChoiceRun R p' (w'.1.take k) := by
    apply isingLeapfrogBoxInt_injective
    rw [hsourceEnd, hmirrorEnd, hsourceSteps, hmirrorSteps]
    exact hfreeEnd
  have hdrop := couplingChoiceTransform_drop_of_some t
    (isingLeapfrogBoxInt p) level w split hsplit
  rw [← List.take_append_drop k w.1,
    ← List.take_append_drop k w'.1,
    isingLeapfrogChoiceRun_append_full,
    isingLeapfrogChoiceRun_append_full,
    hrunPrefix, hdrop]


def isingLeapfrogStoppedChoicePathFiberEquiv
    (R t : Nat) (p q : IsingLeapfrogBox R) :
    IsingLeapfrogStoppedChoicePathFamily R t p q ≃
      {w : IsingLeapfrogChoiceStringFamily t //
        isingLeapfrogChoiceRun R p w.1 = q} where
  toFun w := ⟨⟨w.1, w.2.1⟩, w.2.2⟩
  invFun w := ⟨w.1.1, w.1.2, w.2⟩
  left_inv w := by rfl
  right_inv w := by rfl



def IsingLeapfrogStoppedCouplingBadFamily
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int) :=
  {w : IsingLeapfrogChoiceStringFamily t //
    isingLeapfrogChoiceRun R p w.1 ≠
      isingLeapfrogChoiceRun R p'
        (isingLeapfrogCouplingChoiceTransform t
          (isingLeapfrogBoxInt p) level w).1}

noncomputable instance isingLeapfrogStoppedCouplingBadFamily_finite
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int) :
    Finite (IsingLeapfrogStoppedCouplingBadFamily R t p p' level) := by
  exact Finite.of_injective
    (fun w : IsingLeapfrogStoppedCouplingBadFamily R t p p' level => w.1)
    Subtype.val_injective

def IsingStoppedCouplingSourceFailure
    (R : Nat) (p : IsingLeapfrogBox R) (level : Int)
    {t : Nat} (w : IsingLeapfrogChoiceStringFamily t) : Prop :=
  ∃ split : IsingDiagonalWalkHitSplit (isingLeapfrogBoxInt p) level,
    isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p) level
      (isingLeapfrogChoiceSteps w.1) = some split ∧
    ¬ IsingLeapfrogChoiceExecValid R p
      (w.1.take split.before.length)



def IsingStoppedCouplingSourceFailureFamily
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :=
  {w : IsingLeapfrogChoiceStringFamily t //
    IsingStoppedCouplingSourceFailure R p level w}

def IsingStoppedCouplingMirrorFailure
    (R : Nat) (p p' : IsingLeapfrogBox R) (level : Int)
    {t : Nat} (w : IsingLeapfrogChoiceStringFamily t) : Prop :=
  ∃ split : IsingDiagonalWalkHitSplit (isingLeapfrogBoxInt p) level,
    isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p) level
      (isingLeapfrogChoiceSteps w.1) = some split ∧
    ¬ IsingLeapfrogChoiceExecValid R p'
      ((isingLeapfrogCouplingChoiceTransform t
        (isingLeapfrogBoxInt p) level w).1.take split.before.length)



def IsingStoppedCouplingMirrorFailureFamily
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int) :=
  {w : IsingLeapfrogChoiceStringFamily t //
    IsingStoppedCouplingMirrorFailure R p p' level w}

noncomputable instance sourceFailureFamily_finite
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :
    Finite (IsingStoppedCouplingSourceFailureFamily R t p level) := by
  exact Finite.of_injective
    (fun w : IsingStoppedCouplingSourceFailureFamily R t p level => w.1)
    Subtype.val_injective

noncomputable instance mirrorFailureFamily_finite
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int) :
    Finite (IsingStoppedCouplingMirrorFailureFamily R t p p' level) := by
  exact Finite.of_injective
    (fun w : IsingStoppedCouplingMirrorFailureFamily R t p p' level => w.1)
    Subtype.val_injective

theorem stoppedCouplingBad_cases
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p))
    (w : IsingLeapfrogStoppedCouplingBadFamily R t p p' level) :
    (∀ k, k ≤ t →
      lineFreeEndpoint (isingLeapfrogBoxInt p).1
        ((w.1.1.map Prod.fst).take k) ≠ level) ∨
      IsingStoppedCouplingSourceFailure R p level w.1 ∨
        IsingStoppedCouplingMirrorFailure R p p' level w.1 := by
  classical
  cases hsplit : isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p) level
      (isingLeapfrogChoiceSteps w.1.1) with
  | none =>
      left
      intro k hk heq
      have hne := firstHitSplit_none_endpoint_fst_ne hsplit k (by
        simpa [isingLeapfrogChoiceSteps, w.1.2] using hk)
      apply hne
      calc
        (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
            ((isingLeapfrogChoiceSteps w.1.1).take k)).1 =
          (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
            (isingLeapfrogChoiceSteps (w.1.1.take k))).1 := by
              simp [isingLeapfrogChoiceSteps, List.map_take]
        _ = lineFreeEndpoint (isingLeapfrogBoxInt p).1
            ((w.1.1.map Prod.fst).take k) :=
          by simpa [List.map_take] using
            (lineFreeEndpoint_choiceHorizontal_full (w.1.1.take k)
              (isingLeapfrogBoxInt p)).symm
        _ = level := heq
  | some split =>
      right
      by_cases hs : IsingLeapfrogChoiceExecValid R p
        (w.1.1.take split.before.length)
      · by_cases hm : IsingLeapfrogChoiceExecValid R p'
          ((isingLeapfrogCouplingChoiceTransform t (isingLeapfrogBoxInt p)
            level w.1).1.take split.before.length)
        · exact (w.2 (stoppedCoupling_endpoints_eq_of_execValid_to_hit
            R t p p' level hmirror w.1 split hsplit hs hm)).elim
        · right
          exact ⟨split, hsplit, hm⟩
      · left
        exact ⟨split, hsplit, hs⟩

private def stoppedCouplingBadCover
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p)) :
    IsingLeapfrogStoppedCouplingBadFamily R t p p' level →
      IsingLeapfrogChoiceNoHitAll t (isingLeapfrogBoxInt p).1 level ⊕
        IsingStoppedCouplingSourceFailureFamily R t p level ⊕
          IsingStoppedCouplingMirrorFailureFamily R t p p' level := fun w => by
  classical
  by_cases hn : ∀ k, k ≤ t →
      lineFreeEndpoint (isingLeapfrogBoxInt p).1
        ((w.1.1.map Prod.fst).take k) ≠ level
  · exact Sum.inl ⟨w.1, by
      simpa [List.map_take] using hn⟩
  · by_cases hs : IsingStoppedCouplingSourceFailure R p level w.1
    · exact Sum.inr (Sum.inl ⟨w.1, hs⟩)
    · exact Sum.inr (Sum.inr ⟨w.1,
        (stoppedCouplingBad_cases R t p p' level hmirror w).resolve_left hn
          |>.resolve_left hs⟩)

private def stoppedCouplingBadCoverValue
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int) :
    IsingLeapfrogChoiceNoHitAll t (isingLeapfrogBoxInt p).1 level ⊕
        IsingStoppedCouplingSourceFailureFamily R t p level ⊕
          IsingStoppedCouplingMirrorFailureFamily R t p p' level →
      IsingLeapfrogChoiceStringFamily t :=
  Sum.elim (fun w => w.1) (Sum.elim (fun w => w.1) (fun w => w.1))

private theorem stoppedCouplingBadCoverValue_apply
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p))
    (w : IsingLeapfrogStoppedCouplingBadFamily R t p p' level) :
    stoppedCouplingBadCoverValue R t p p' level
      (stoppedCouplingBadCover R t p p' level hmirror w) = w.1 := by
  classical
  unfold stoppedCouplingBadCover
  by_cases hn : ∀ k, k ≤ t →
      lineFreeEndpoint (isingLeapfrogBoxInt p).1
        ((w.1.1.map Prod.fst).take k) ≠ level
  · rw [dif_pos hn]
    rfl
  · rw [dif_neg hn]
    by_cases hs : IsingStoppedCouplingSourceFailure R p level w.1
    · rw [dif_pos hs]
      rfl
    · rw [dif_neg hs]
      rfl

private theorem stoppedCouplingBadCover_injective
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p)) :
    Function.Injective
      (stoppedCouplingBadCover R t p p' level hmirror) := by
  intro a b hab
  apply Subtype.ext
  rw [← stoppedCouplingBadCoverValue_apply R t p p' level hmirror a,
    ← stoppedCouplingBadCoverValue_apply R t p p' level hmirror b, hab]



theorem natCard_stoppedCouplingBad_le_noHit_add_failures
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p)) :
    Nat.card (IsingLeapfrogStoppedCouplingBadFamily R t p p' level) ≤
      Nat.card (IsingLeapfrogChoiceNoHitAll t
        (isingLeapfrogBoxInt p).1 level) +
      Nat.card (IsingStoppedCouplingSourceFailureFamily R t p level) +
      Nat.card (IsingStoppedCouplingMirrorFailureFamily R t p p' level) := by
  calc
    _ ≤ Nat.card
        (IsingLeapfrogChoiceNoHitAll t (isingLeapfrogBoxInt p).1 level ⊕
          IsingStoppedCouplingSourceFailureFamily R t p level ⊕
            IsingStoppedCouplingMirrorFailureFamily R t p p' level) :=
      Nat.card_le_card_of_injective
        (stoppedCouplingBadCover R t p p' level hmirror)
        (stoppedCouplingBadCover_injective R t p p' level hmirror)
    _ = _ := by rw [Nat.card_sum, Nat.card_sum]; omega


private theorem exists_boundary_before_of_not_choiceExecValid
    (R : Nat) (p : IsingLeapfrogBox R) (bs : List (Bool × Bool))
    (h : ¬ IsingLeapfrogChoiceExecValid R p bs) :
    ∃ j, j < bs.length ∧ isingLeapfrogBoxBoundary R
      (isingLeapfrogChoiceRun R p (bs.take j)) := by
  unfold IsingLeapfrogChoiceExecValid at h
  push_neg at h
  exact h


theorem lineChoiceRun_val_eq_lineFreeEndpoint
    (n : Nat) (p : IsingLineBox n) (bs : List Bool)
    (hfree : ∀ j, j < bs.length →
      lineFreeEndpoint (p.1 : Int) (bs.take j) ≠ 0 ∧
        lineFreeEndpoint (p.1 : Int) (bs.take j) ≠ n) :
    ((isingLineChoiceRun n p bs).1 : Int) =
      lineFreeEndpoint (p.1 : Int) bs := by
  induction bs generalizing p with
  | nil => simp [isingLineChoiceRun, lineFreeEndpoint]
  | cons b bs ih =>
      have h0 := hfree 0 (by simp)
      have hp0 : p.1 ≠ 0 := by
        intro hp0
        apply h0.1
        simp [lineFreeEndpoint, hp0]
      have hpn : p.1 ≠ n := by
        intro hpn
        apply h0.2
        simp [lineFreeEndpoint, hpn]
      have hp : ¬ isingLineBoxBoundary n p := by
        exact fun h => h.elim hp0 hpn
      have hpPos : 0 < p.1 := by omega
      have hwestCast : ((p.1 - 1 : Nat) : Int) = (p.1 : Int) - 1 := by
        omega
      have htail : ∀ j, j < bs.length →
          lineFreeEndpoint
              ((isingLineChoiceNext n p b).1 : Int) (bs.take j) ≠ 0 ∧
            lineFreeEndpoint
              ((isingLineChoiceNext n p b).1 : Int) (bs.take j) ≠ n := by
        intro j hj
        have hmain := hfree (j + 1) (by simp; omega)
        cases b
        · simpa [isingLineChoiceNext, hp, isingLineWest,
            lineFreeEndpoint, List.take_succ_cons, hwestCast] using hmain
        · simpa [isingLineChoiceNext, hp, isingLineEast,
            lineFreeEndpoint, List.take_succ_cons] using hmain
      rw [show isingLineChoiceRun n p (b :: bs) =
          isingLineChoiceRun n (isingLineChoiceNext n p b) bs by rfl]
      rw [ih (isingLineChoiceNext n p b) htail]
      cases b
      · simp [isingLineChoiceNext, hp, isingLineWest,
          lineFreeEndpoint, hwestCast]
        congr 1 <;> ring
      · simp [isingLineChoiceNext, hp, isingLineEast,
          lineFreeEndpoint]

theorem sourceFailure_boundary_data
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int)
    (hstart : (isingLeapfrogBoxInt p).1 < level)
    (w : IsingStoppedCouplingSourceFailureFamily R t p level) :
    ∃ (split : IsingDiagonalWalkHitSplit (isingLeapfrogBoxInt p) level) (j : Nat),
      isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p) level
        (isingLeapfrogChoiceSteps w.1.1) = some split ∧
      j < split.before.length ∧
      isingLeapfrogBoxBoundary R
        (isingLeapfrogChoiceRun R p (w.1.1.take j)) ∧
      (∀ l, l < j → ¬ isingLeapfrogBoxBoundary R
        (isingLeapfrogChoiceRun R p (w.1.1.take l))) ∧
      (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceSteps (w.1.1.take j))).1 < level ∧
      isingLeapfrogBoxInt (isingLeapfrogChoiceRun R p (w.1.1.take j)) =
        isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
          (isingLeapfrogChoiceSteps (w.1.1.take j)) := by
  rcases w.2 with ⟨split, hsplit, hnot⟩
  have hex := exists_boundary_before_of_not_choiceExecValid R p
    (w.1.1.take split.before.length) hnot
  let j := Nat.find hex
  have hjSpec := Nat.find_spec hex
  have hbeforeLe : split.before.length ≤ w.1.1.length := by
    have hs := firstHitSplit_steps hsplit
    have hlen : split.steps.length = w.1.1.length := by
      rw [hs]
      simp [isingLeapfrogChoiceSteps]
    unfold IsingDiagonalWalkHitSplit.steps at hlen
    simp only [List.length_append] at hlen
    omega
  have hj : j < split.before.length := by
    exact lt_of_lt_of_le hjSpec.1 (List.length_take_le ..)
  have hjBoundary := hjSpec.2
  have hminimal : ∀ l, l < j → ¬ isingLeapfrogBoxBoundary R
      (isingLeapfrogChoiceRun R p (w.1.1.take l)) := by
    intro l hl hb
    have hpred : l < (w.1.1.take split.before.length).length ∧
        isingLeapfrogBoxBoundary R
          (isingLeapfrogChoiceRun R p
            ((w.1.1.take split.before.length).take l)) := by
      constructor
      · rw [List.length_take, Nat.min_eq_left hbeforeLe]
        omega
      · have hlbefore : l ≤ split.before.length := by omega
        rw [List.take_take, Nat.min_eq_left hlbefore]
        exact hb
    exact (Nat.find_min hex hl) hpred
  have hexec : IsingLeapfrogChoiceExecValid R p (w.1.1.take j) := by
    intro l hl
    rw [List.length_take, Nat.min_eq_left (by omega)] at hl
    simpa [List.take_take, Nat.min_eq_left hl.le] using hminimal l hl
  have hrun := choiceExecValid_run_boxInt_eq_endpoint R p (w.1.1.take j) hexec
  have hstepsTake : isingLeapfrogChoiceSteps (w.1.1.take j) =
      split.before.take j := by
    have hs := firstHitSplit_steps hsplit
    have ht := congrArg (fun z : List (Int × Int) => z.take j) hs
    simpa [IsingDiagonalWalkHitSplit.steps, isingLeapfrogChoiceSteps,
      List.map_take, List.take_append_of_le_length hj.le] using ht.symm
  have hjFind : Nat.find hex ≤ split.before.length := by
    simpa [j] using hj.le
  have hjBoundaryRaw : isingLeapfrogBoxBoundary R
      (isingLeapfrogChoiceRun R p (w.1.1.take j)) := by
    have hb := hjBoundary
    rw [List.take_take, Nat.min_eq_left hjFind] at hb
    simpa [j] using hb
  have hvalid : split.Valid := by
    unfold IsingDiagonalWalkHitSplit.Valid
    rw [firstHitSplit_steps hsplit]
    exact isingLeapfrogChoiceSteps_valid w.1.1
  have hxlt := (firstHitSplit_firstHit hsplit).endpoint_take_fst_lt split
    hvalid hstart j hj
  refine ⟨split, j, hsplit, hj, ?_, hminimal, ?_, hrun⟩
  · exact hjBoundaryRaw
  · rw [hstepsTake]
    exact hxlt

theorem lineFreeEndpoint_choiceVertical_full
    (bs : List (Bool × Bool)) (start : Int × Int) :
    lineFreeEndpoint start.2 (bs.map Prod.snd) =
      (isingDiagonalWalkEndpoint start
        (isingLeapfrogChoiceSteps bs)).2 := by
  induction bs generalizing start with
  | nil =>
      simp [lineFreeEndpoint, isingLeapfrogChoiceSteps,
        isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement]
  | cons b bs ih =>
      have hih := ih (isingDiagonalWalkNext start
        (isingLeapfrogChoiceStep b))
      rcases b with ⟨bx, byy⟩
      cases bx <;> cases byy <;>
        simp [lineFreeEndpoint, isingLeapfrogChoiceSteps,
          isingLeapfrogChoiceStep, isingDiagonalWalkEndpoint,
          isingDiagonalWalkNext, isingDiagonalWalkDisplacement,
          add_assoc] at hih ⊢ <;> linarith

theorem lineFreeEndpoint_translate
    (bs : List Bool) (a b : Int) :
    lineFreeEndpoint b bs = b + (lineFreeEndpoint a bs - a) := by
  induction bs generalizing a b with
  | nil => simp [lineFreeEndpoint]
  | cons x bs ih =>
      cases x
      · change lineFreeEndpoint (b - 1) bs =
          b + (lineFreeEndpoint (a - 1) bs - a)
        rw [ih (a - 1) (b - 1)]
        ring
      · change lineFreeEndpoint (b + 1) bs =
          b + (lineFreeEndpoint (a + 1) bs - a)
        rw [ih (a + 1) (b + 1)]
        ring

private theorem prodBits_zip_self (bs : List (Bool × Bool)) :
    (bs.map Prod.fst).zip (bs.map Prod.snd) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [ih]



def transverseRaceWitnessValue (m t : Nat) (level : Int) :
    IsingTransverseRaceWitnessFamily m t level →
      IsingLeapfrogChoiceStringFamily t := fun z =>
  ⟨(z.2.1.1.zip z.2.2.1.1) ++ z.2.2.2.1, by
    rw [List.length_append, List.length_zip, z.2.1.2.1, z.2.2.1.2.1,
      z.2.2.2.2]
    simp
    omega⟩

theorem exists_vertical_barrier_prefix
    (rho : Nat) (hρ : 0 < rho) (start : Int × Int)
    (bs : List (Bool × Bool)) (j : Nat) (hj : j ≤ bs.length)
    (hlower : (rho : Int) ≤ start.2)
    (hupper : start.2 + rho ≤
      (isingDiagonalWalkEndpoint start (isingLeapfrogChoiceSteps bs)).2)
    : ∃ s, s ≤ bs.length ∧
      lineFreeEndpoint start.2 ((bs.take s).map Prod.snd) = start.2 + rho := by
  let swap : Int × Int → Int × Int := fun z => (z.2, z.1)
  let path := (isingLeapfrogChoiceSteps bs).map swap
  have hvalid : IsingDiagonalWalkStepsValid path := by
    intro d hd
    rcases List.mem_map.mp hd with ⟨e, he, rfl⟩
    have he' := isingLeapfrogChoiceSteps_valid bs e he
    exact ⟨he'.2, he'.1⟩
  have hend : start.2 + rho ≤
      (isingDiagonalWalkEndpoint (start.2, start.1) path).1 := by
    have heq : (isingDiagonalWalkEndpoint (start.2, start.1) path).1 =
        (isingDiagonalWalkEndpoint start (isingLeapfrogChoiceSteps bs)).2 := by
      unfold path swap isingDiagonalWalkEndpoint isingDiagonalWalkDisplacement
      simp only [List.map_map]
      rfl
    rw [heq]
    exact hupper
  rcases exists_prefix_fst_eq_of_lt_of_le path (start.2, start.1)
    (start.2 + rho) hvalid (by omega) hend with ⟨s, hs, heq⟩
  refine ⟨s, ?_, ?_⟩
  · simpa [path, isingLeapfrogChoiceSteps] using hs
  · have heq' :
        (isingDiagonalWalkEndpoint start
          ((isingLeapfrogChoiceSteps bs).take s)).2 = start.2 + rho := by
      simpa [path, swap, List.map_take, isingDiagonalWalkEndpoint,
        isingDiagonalWalkDisplacement] using heq
    calc
      lineFreeEndpoint start.2 ((bs.take s).map Prod.snd) =
          (isingDiagonalWalkEndpoint start
            (isingLeapfrogChoiceSteps (bs.take s))).2 :=
        lineFreeEndpoint_choiceVertical_full (bs.take s) start
      _ = (isingDiagonalWalkEndpoint start
            ((isingLeapfrogChoiceSteps bs).take s)).2 := by
        simp [isingLeapfrogChoiceSteps, List.map_take]
      _ = start.2 + rho := heq'

theorem exists_vertical_barrier_prefix_lower
    (rho : Nat) (hρ : 0 < rho) (start : Int × Int)
    (bs : List (Bool × Bool))
    (hlower : (rho : Int) ≤ start.2)
    (hend : (isingDiagonalWalkEndpoint start
      (isingLeapfrogChoiceSteps bs)).2 ≤ start.2 - rho) :
    ∃ s, s ≤ bs.length ∧
      lineFreeEndpoint start.2 ((bs.take s).map Prod.snd) = start.2 - rho := by
  let swap : Int × Int → Int × Int := fun z => (z.2, z.1)
  let path := (isingLeapfrogChoiceSteps bs).map swap
  have hvalid : IsingDiagonalWalkStepsValid path := by
    intro d hd
    rcases List.mem_map.mp hd with ⟨e, he, rfl⟩
    have he' := isingLeapfrogChoiceSteps_valid bs e he
    exact ⟨he'.2, he'.1⟩
  have hend' : (isingDiagonalWalkEndpoint (start.2, start.1) path).1 ≤
      start.2 - rho := by
    have heq : (isingDiagonalWalkEndpoint (start.2, start.1) path).1 =
        (isingDiagonalWalkEndpoint start (isingLeapfrogChoiceSteps bs)).2 := by
      unfold path swap isingDiagonalWalkEndpoint isingDiagonalWalkDisplacement
      simp only [List.map_map]
      rfl
    rw [heq]
    exact hend
  rcases exists_prefix_fst_eq_of_ge_of_gt path (start.2, start.1)
    (start.2 - rho) hvalid (by omega) hend' with ⟨s, hs, heq⟩
  refine ⟨s, ?_, ?_⟩
  · simpa [path, isingLeapfrogChoiceSteps] using hs
  · have heq' :
        (isingDiagonalWalkEndpoint start
          ((isingLeapfrogChoiceSteps bs).take s)).2 = start.2 - rho := by
      simpa [path, swap, List.map_take, isingDiagonalWalkEndpoint,
        isingDiagonalWalkDisplacement] using heq
    calc
      lineFreeEndpoint start.2 ((bs.take s).map Prod.snd) =
          (isingDiagonalWalkEndpoint start
            (isingLeapfrogChoiceSteps (bs.take s))).2 :=
        lineFreeEndpoint_choiceVertical_full (bs.take s) start
      _ = (isingDiagonalWalkEndpoint start
            ((isingLeapfrogChoiceSteps bs).take s)).2 := by
        simp [isingLeapfrogChoiceSteps, List.map_take]
      _ = start.2 - rho := heq'

private theorem isingLineChoiceRun_append_source
    (n : Nat) (p : IsingLineBox n) (a b : List Bool) :
    isingLineChoiceRun n p (a ++ b) =
      isingLineChoiceRun n (isingLineChoiceRun n p a) b := by
  induction a generalizing p with
  | nil => rfl
  | cons x a ih =>
      simp only [List.cons_append, isingLineChoiceRun]
      exact ih (isingLineChoiceNext n p x)

private theorem isingLineChoiceRun_boundary_source
    (n : Nat) (p : IsingLineBox n) (hp : isingLineBoxBoundary n p)
    (bs : List Bool) : isingLineChoiceRun n p bs = p := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [isingLineChoiceRun]
      rw [show isingLineChoiceNext n p b = p by
        simp [isingLineChoiceNext, hp]]
      exact ih

theorem transverseWitness_of_barrier_exists
    (rho t : Nat) (level : Int) (hρ : 0 < rho)
    (start : Int × Int) (hstart : start.1 = level - 1) (w : IsingLeapfrogChoiceStringFamily t)
    (split : IsingDiagonalWalkHitSplit start level)
    (hsplit : isingDiagonalWalkFirstHitSplit? start level
      (isingLeapfrogChoiceSteps w.1) = some split)
    (j : Nat) (hj : j < split.before.length)
    (hex : ∃ s, s ≤ j ∧
      (lineFreeEndpoint start.2 ((w.1.take s).map Prod.snd) = start.2 - rho ∨
       lineFreeEndpoint start.2 ((w.1.take s).map Prod.snd) = start.2 + rho)) :
    ∃ z : IsingTransverseRaceWitnessFamily rho t level,
      transverseRaceWitnessValue rho t level z = w /\ (z.1 : Nat) <= j := by
  let s := Nat.find hex
  have hsSpec := Nat.find_spec hex
  have hsSpec' : s ≤ j ∧
      (lineFreeEndpoint start.2 ((w.1.take s).map Prod.snd) = start.2 - rho ∨
       lineFreeEndpoint start.2 ((w.1.take s).map Prod.snd) = start.2 + rho) := by
    simpa [s] using hsSpec
  have hsJ : s ≤ j := hsSpec'.1
  have hsT : s ≤ t := by
    have hbeforeLe : split.before.length ≤ t := by
      have hl := congrArg List.length (firstHitSplit_steps hsplit)
      simp [IsingDiagonalWalkHitSplit.steps, isingLeapfrogChoiceSteps, w.2] at hl
      omega
    omega
  have havoid : ∀ l, l < s →
      lineFreeEndpoint start.2 ((w.1.take l).map Prod.snd) ≠ start.2 - rho ∧
      lineFreeEndpoint start.2 ((w.1.take l).map Prod.snd) ≠ start.2 + rho := by
    intro l hl
    constructor <;> intro heq
    · exact (Nat.find_min hex hl) ⟨by omega, Or.inl heq⟩
    · exact (Nat.find_min hex hl) ⟨by omega, Or.inr heq⟩
  let hword : IsingHorizontalNoHitFamily s (level - 1) level :=
    ⟨(w.1.take s).map Prod.fst, by simp [w.2, hsT], by
      intro q hq heq
      have hqBefore : q < split.before.length := by omega
      have hfirst := firstHitSplit_firstHit hsplit q hqBefore
      apply hfirst
      have hsteps := congrArg (fun z : List (Int × Int) => z.take q)
        (firstHitSplit_steps hsplit)
      have hprefix : split.before.take q =
          (isingLeapfrogChoiceSteps w.1).take q := by
        simpa [IsingDiagonalWalkHitSplit.steps,
          List.take_append_of_le_length hqBefore.le] using hsteps
      calc
        (isingDiagonalWalkEndpoint start (split.before.take q)).1 =
            (isingDiagonalWalkEndpoint start
              ((isingLeapfrogChoiceSteps w.1).take q)).1 := by rw [hprefix]
        _ = (isingDiagonalWalkEndpoint start
              (isingLeapfrogChoiceSteps (w.1.take q))).1 := by
                simp [isingLeapfrogChoiceSteps, List.map_take]
        _ = lineFreeEndpoint start.1 ((w.1.take q).map Prod.fst) :=
          (lineFreeEndpoint_choiceHorizontal_full (w.1.take q) start).symm
        _ = lineFreeEndpoint (level - 1)
              (((w.1.take s).map Prod.fst).take q) := by
            rw [hstart]
            simp [List.map_take, List.take_take, Nat.min_eq_left hq]
        _ = level := heq⟩
  have hverticalFree : ∀ l, l < s →
      lineFreeEndpoint (rho : Int)
          (((w.1.take s).map Prod.snd).take l) ≠ 0 ∧
        lineFreeEndpoint (rho : Int)
          (((w.1.take s).map Prod.snd).take l) ≠ ((2 * rho : Nat) : Int) := by
    intro l hl
    have ha := havoid l hl
    have htranslate := lineFreeEndpoint_translate
      ((w.1.take l).map Prod.snd) start.2 (rho : Int)
    have htake : ((w.1.take s).map Prod.snd).take l =
        (w.1.take l).map Prod.snd := by
      simp [List.map_take, List.take_take, Nat.min_eq_left hl.le]
    rw [htake, htranslate]
    constructor <;> intro heq
    · apply ha.1
      omega
    · apply ha.2
      push_cast at heq
      omega
  have hverticalEnd :
      lineFreeEndpoint (rho : Int) ((w.1.take s).map Prod.snd) = 0 ∨
        lineFreeEndpoint (rho : Int) ((w.1.take s).map Prod.snd) =
          ((2 * rho : Nat) : Int) := by
    have htranslate := lineFreeEndpoint_translate
      ((w.1.take s).map Prod.snd) start.2 (rho : Int)
    rw [htranslate]
    rcases hsSpec'.2 with hs | hs
    · left; omega
    · right; push_cast; omega
  have hverticalFree' : ∀ l, l < ((w.1.take s).map Prod.snd).length →
      lineFreeEndpoint (rho : Int)
          (((w.1.take s).map Prod.snd).take l) ≠ 0 ∧
        lineFreeEndpoint (rho : Int)
          (((w.1.take s).map Prod.snd).take l) ≠ ((2 * rho : Nat) : Int) := by
    intro l hl
    apply hverticalFree l
    simpa [w.2, hsT] using hl
  have hlineEnd := lineChoiceRun_val_eq_lineFreeEndpoint (2 * rho)
    (⟨rho, by omega⟩ : IsingLineBox (2 * rho))
    ((w.1.take s).map Prod.snd) hverticalFree' 
  let vword : IsingLineFirstBoundaryFamily rho s :=
    ⟨(w.1.take s).map Prod.snd, by simp [w.2, hsT], by
      unfold isingLineBoxBoundary
      have he : ((isingLineChoiceRun (2 * rho)
          (⟨rho, by omega⟩ : IsingLineBox (2 * rho))
          ((w.1.take s).map Prod.snd)).1 : Int) = 0 ∨
        ((isingLineChoiceRun (2 * rho)
          (⟨rho, by omega⟩ : IsingLineBox (2 * rho))
          ((w.1.take s).map Prod.snd)).1 : Int) = ((2 * rho : Nat) : Int) := by
        rw [hlineEnd]
        exact hverticalEnd
      exact_mod_cast he, by
      intro l hl
      unfold isingLineBoxBoundary
      have hfreeL : ∀ q, q < l →
          lineFreeEndpoint (rho : Int)
              ((((w.1.take s).map Prod.snd).take l).take q) ≠ 0 ∧
            lineFreeEndpoint (rho : Int)
              ((((w.1.take s).map Prod.snd).take l).take q) ≠
                ((2 * rho : Nat) : Int) := by
        intro q hq
        have hqS : q ≤ s := by omega
        simpa only [List.take_take, Nat.min_eq_left hq.le,
          Nat.min_eq_left hqS] using hverticalFree q (by omega)
      have hfreeL' : ∀ q,
          q < (((w.1.take s).map Prod.snd).take l).length →
          lineFreeEndpoint (rho : Int)
              ((((w.1.take s).map Prod.snd).take l).take q) ≠ 0 ∧
            lineFreeEndpoint (rho : Int)
              ((((w.1.take s).map Prod.snd).take l).take q) ≠
                ((2 * rho : Nat) : Int) := by
        intro q hq
        apply hfreeL q
        rw [List.length_take] at hq
        omega
      have hrun := lineChoiceRun_val_eq_lineFreeEndpoint (2 * rho)
        (⟨rho, by omega⟩ : IsingLineBox (2 * rho))
        (((w.1.take s).map Prod.snd).take l) hfreeL'
      have hnot := hverticalFree l hl
      intro hb
      rcases hb with hb | hb
      · apply hnot.1
        rw [← hrun]
        exact_mod_cast hb
      · apply hnot.2
        rw [← hrun]
        exact_mod_cast hb⟩
  let tail : {tail : List (Bool × Bool) // tail.length = t - s} :=
    ⟨w.1.drop s, by simp [w.2, hsT]⟩
  let z : IsingTransverseRaceWitnessFamily rho t level :=
    ⟨⟨s, by omega⟩, hword, vword, tail⟩
  refine ⟨z, ?_, hsJ⟩
  · apply Subtype.ext
    dsimp [transverseRaceWitnessValue, z, hword, vword, tail]
    rw [prodBits_zip_self]
    exact List.take_append_drop s w.1



theorem sourceFailure_horizontal_or_transverse
    (R level rho t : Nat) (p : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hlevel : 0 < level) (hlevelR : level < R) (hρ : 0 < rho)
    (hbottom : rho ≤ p.2.1) (htop : p.2.1 + rho ≤ R)
    (w : IsingStoppedCouplingSourceFailureFamily R t p (level : Int)) :
    (∃ z : IsingLeapfrogHorizontalEscapeFamily level t, z.1 = w.1) ∨
      ∃ z : IsingTransverseRaceWitnessFamily rho t (level : Int),
        transverseRaceWitnessValue rho t (level : Int) z = w.1 := by
  have hstartLt : (isingLeapfrogBoxInt p).1 < (level : Int) := by omega
  rcases sourceFailure_boundary_data R t p (level : Int) hstartLt w with
    ⟨split, j, hsplit, hj, hb, hminimal, hxlt, hrun⟩
  have hvalid : split.Valid := by
    unfold IsingDiagonalWalkHitSplit.Valid
    rw [firstHitSplit_steps hsplit]
    exact isingLeapfrogChoiceSteps_valid w.1.1
  have hfirst := firstHitSplit_firstHit hsplit
  have hpx : p.1.1 = level - 1 := by
    unfold isingLeapfrogBoxInt at hstart
    dsimp at hstart
    push_cast at hstart
    omega
  have hjT : j ≤ t := by
    have hl := congrArg List.length (firstHitSplit_steps hsplit)
    simp [IsingDiagonalWalkHitSplit.steps, isingLeapfrogChoiceSteps, w.1.2] at hl
    omega
  have horizontal_of_xzero
      (hxzero : (isingLeapfrogChoiceRun R p (w.1.1.take j)).1.1 = 0) :
      ∃ z : IsingLeapfrogHorizontalEscapeFamily level t, z.1 = w.1 := by
    have hfree : ∀ l, l < ((w.1.1.take j).map Prod.fst).length →
        lineFreeEndpoint ((⟨level - 1, by omega⟩ : IsingLineBox level).1 : Int)
            (((w.1.1.take j).map Prod.fst).take l) ≠ 0 ∧
          lineFreeEndpoint ((⟨level - 1, by omega⟩ : IsingLineBox level).1 : Int)
            (((w.1.1.take j).map Prod.fst).take l) ≠ level := by
      intro l hl
      have hlj : l < j := by
        rw [List.length_map, List.length_take] at hl
        omega
      have hexec : IsingLeapfrogChoiceExecValid R p (w.1.1.take l) := by
        intro q hq
        rw [List.length_take] at hq
        have hql : q < l := by omega
        simpa [List.take_take, Nat.min_eq_left hql.le] using hminimal q (by omega)
      have hrunl := choiceExecValid_run_boxInt_eq_endpoint R p
        (w.1.1.take l) hexec
      have hrawx :
          (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
            (isingLeapfrogChoiceSteps (w.1.1.take l))).1 =
          lineFreeEndpoint ((⟨level - 1, by omega⟩ : IsingLineBox level).1 : Int)
            (((w.1.1.take j).map Prod.fst).take l) := by
        calc
          _ = lineFreeEndpoint (isingLeapfrogBoxInt p).1
              ((w.1.1.take l).map Prod.fst) :=
            (lineFreeEndpoint_choiceHorizontal_full (w.1.1.take l)
              (isingLeapfrogBoxInt p)).symm
          _ = _ := by
            unfold isingLeapfrogBoxInt
            dsimp
            rw [hpx]
            simp [List.map_take, List.take_take, Nat.min_eq_left hlj.le]
      have hrunx := congrArg Prod.fst hrunl
      change ((isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 : Int) =
        (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
          (isingLeapfrogChoiceSteps (w.1.1.take l))).1 at hrunx
      have hnbox := hminimal l hlj
      unfold isingLeapfrogBoxBoundary at hnbox
      constructor
      · intro heq
        apply hnbox
        left
        rw [hrawx] at hrunx
        have hz : ((isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 : Int) = 0 :=
          hrunx.trans heq
        exact_mod_cast hz
      · intro heq
        have hx := hfirst.endpoint_take_fst_lt split hvalid hstartLt l (by omega)
        have hsteps := congrArg (fun z : List (Int × Int) => z.take l)
          (firstHitSplit_steps hsplit)
        have hprefix : split.before.take l =
            (isingLeapfrogChoiceSteps w.1.1).take l := by
          simpa [IsingDiagonalWalkHitSplit.steps,
            List.take_append_of_le_length (show l ≤ split.before.length by omega)]
            using hsteps
        rw [hprefix] at hx
        have hx' : (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
            (isingLeapfrogChoiceSteps (w.1.1.take l))).1 < level := by
          simpa [isingLeapfrogChoiceSteps, List.map_take] using hx
        rw [hrawx] at hx'
        omega
    have hlinePrefix := lineChoiceRun_val_eq_lineFreeEndpoint level
      (⟨level - 1, by omega⟩ : IsingLineBox level)
      ((w.1.1.take j).map Prod.fst) hfree
    have hrawJ := congrArg Prod.fst hrun
    have hlinePrefixZero : isingLineChoiceRun level
        (⟨level - 1, by omega⟩ : IsingLineBox level)
          ((w.1.1.take j).map Prod.fst) = ⟨0, by omega⟩ := by
      apply Fin.ext
      have hlineInt : ((isingLineChoiceRun level
          (⟨level - 1, by omega⟩ : IsingLineBox level)
            ((w.1.1.take j).map Prod.fst)).1 : Int) = 0 := by
        rw [hlinePrefix]
        have hfreeJ := lineFreeEndpoint_choiceHorizontal_full
          (w.1.1.take j) (isingLeapfrogBoxInt p)
        have hrawJ' := congrArg Prod.fst hrun
        change ((isingLeapfrogChoiceRun R p (w.1.1.take j)).1.1 : Int) =
          (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
            (isingLeapfrogChoiceSteps (w.1.1.take j))).1 at hrawJ'
        have hstartInt : (isingLeapfrogBoxInt p).1 =
            ((level - 1 : Nat) : Int) := by
          unfold isingLeapfrogBoxInt
          dsimp
          exact_mod_cast hpx
        change lineFreeEndpoint ((level - 1 : Nat) : Int)
          ((w.1.1.take j).map Prod.fst) = 0
        rw [← hstartInt, hfreeJ, ← hrawJ']
        exact_mod_cast hxzero
      change (isingLineChoiceRun level
        (⟨level - 1, by omega⟩ : IsingLineBox level)
          ((w.1.1.take j).map Prod.fst)).1 = 0
      exact_mod_cast hlineInt
    let fullx := w.1.1.map Prod.fst
    have hdecomp : fullx = ((w.1.1.take j).map Prod.fst) ++
        ((w.1.1.drop j).map Prod.fst) := by
      dsimp [fullx]
      rw [← List.map_append, List.take_append_drop]
    have hlineFull : isingLineChoiceRun level
        (⟨level - 1, by omega⟩ : IsingLineBox level) fullx =
        ⟨0, by omega⟩ := by
      rw [hdecomp, isingLineChoiceRun_append_source, hlinePrefixZero]
      exact isingLineChoiceRun_boundary_source level ⟨0, by omega⟩
        (by simp [isingLineBoxBoundary]) _
    refine ⟨⟨w.1, ?_⟩, rfl⟩
    simpa [IsingLeapfrogHorizontalEscapeFamily, fullx, hpx] using hlineFull
  unfold isingLeapfrogBoxBoundary at hb
  rcases hb with hx0 | hxR | hy0 | hyR
  · exact Or.inl (horizontal_of_xzero hx0)
  · exfalso
    have hxrun := congrArg Prod.fst hrun
    change ((isingLeapfrogChoiceRun R p (w.1.1.take j)).1.1 : Int) =
      (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceSteps (w.1.1.take j))).1 at hxrun
    push_cast at hxR
    omega
  · right
    have hyEnd : (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceSteps (w.1.1.take j))).2 ≤
          (isingLeapfrogBoxInt p).2 - rho := by
      have hyrun := congrArg Prod.snd hrun
      change ((isingLeapfrogChoiceRun R p (w.1.1.take j)).2.1 : Int) =
        (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
          (isingLeapfrogChoiceSteps (w.1.1.take j))).2 at hyrun
      push_cast at hy0
      have hbottomInt : (rho : Int) ≤ (isingLeapfrogBoxInt p).2 := by
        unfold isingLeapfrogBoxInt
        dsimp
        exact_mod_cast hbottom
      omega
    rcases exists_vertical_barrier_prefix_lower rho hρ
      (isingLeapfrogBoxInt p) (w.1.1.take j) (by
        unfold isingLeapfrogBoxInt
        dsimp
        exact_mod_cast hbottom) hyEnd with ⟨s, hs, heq⟩
    rcases transverseWitness_of_barrier_exists rho t (level : Int) hρ
      (isingLeapfrogBoxInt p) (by omega) w.1 split hsplit j hj (by
        have hsJ : s ≤ j := le_trans hs (List.length_take_le ..)
        exact ⟨s, hsJ, Or.inl (by
          simpa [List.take_take, Nat.min_eq_left hsJ] using heq)⟩) with
      ⟨z, hz, hzj⟩
    exact ⟨z, hz⟩
  · right
    have hyEnd : (isingLeapfrogBoxInt p).2 + rho ≤
        (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
          (isingLeapfrogChoiceSteps (w.1.1.take j))).2 := by
      have hyrun := congrArg Prod.snd hrun
      change ((isingLeapfrogChoiceRun R p (w.1.1.take j)).2.1 : Int) =
        (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
          (isingLeapfrogChoiceSteps (w.1.1.take j))).2 at hyrun
      push_cast at hyR
      have htopInt : (isingLeapfrogBoxInt p).2 + (rho : Int) ≤ R := by
        unfold isingLeapfrogBoxInt
        dsimp
        exact_mod_cast htop
      omega
    rcases exists_vertical_barrier_prefix rho hρ
      (isingLeapfrogBoxInt p) (w.1.1.take j) j (by simp [hjT]) (by
        unfold isingLeapfrogBoxInt
        dsimp
        exact_mod_cast hbottom) hyEnd with ⟨s, hs, heq⟩
    rcases transverseWitness_of_barrier_exists rho t (level : Int) hρ
      (isingLeapfrogBoxInt p) (by omega) w.1 split hsplit j hj (by
        have hsJ : s ≤ j := le_trans hs (List.length_take_le ..)
        exact ⟨s, hsJ, Or.inr (by
          simpa [List.take_take, Nat.min_eq_left hsJ] using heq)⟩) with
      ⟨z, hz, hzj⟩
    exact ⟨z, hz⟩

private def sourceFailureCover
    (R level rho t : Nat) (p : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hlevel : 0 < level) (hlevelR : level < R) (hρ : 0 < rho)
    (hbottom : rho ≤ p.2.1) (htop : p.2.1 + rho ≤ R) :
    IsingStoppedCouplingSourceFailureFamily R t p (level : Int) →
      IsingLeapfrogHorizontalEscapeFamily level t ⊕
        IsingTransverseRaceWitnessFamily rho t (level : Int) := fun w => by
  classical
  by_cases hh : ∃ z : IsingLeapfrogHorizontalEscapeFamily level t, z.1 = w.1
  · exact Sum.inl (Classical.choose hh)
  · exact Sum.inr (Classical.choose
      ((sourceFailure_horizontal_or_transverse R level rho t p hstart hlevel
        hlevelR hρ hbottom htop w).resolve_left hh))

private def sourceFailureCoverValue (level rho t : Nat) :
    IsingLeapfrogHorizontalEscapeFamily level t ⊕
        IsingTransverseRaceWitnessFamily rho t (level : Int) →
      IsingLeapfrogChoiceStringFamily t
  | Sum.inl z => z.1
  | Sum.inr z => transverseRaceWitnessValue rho t (level : Int) z

private theorem sourceFailureCoverValue_apply
    (R level rho t : Nat) (p : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hlevel : 0 < level) (hlevelR : level < R) (hρ : 0 < rho)
    (hbottom : rho ≤ p.2.1) (htop : p.2.1 + rho ≤ R)
    (w : IsingStoppedCouplingSourceFailureFamily R t p (level : Int)) :
    sourceFailureCoverValue level rho t
      (sourceFailureCover R level rho t p hstart hlevel hlevelR hρ
        hbottom htop w) = w.1 := by
  classical
  unfold sourceFailureCover
  by_cases hh : ∃ z : IsingLeapfrogHorizontalEscapeFamily level t, z.1 = w.1
  · rw [dif_pos hh]
    exact (Classical.choose_spec hh)
  · rw [dif_neg hh]
    exact Classical.choose_spec
      ((sourceFailure_horizontal_or_transverse R level rho t p hstart hlevel
        hlevelR hρ hbottom htop w).resolve_left hh)

private theorem sourceFailureCover_injective
    (R level rho t : Nat) (p : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hlevel : 0 < level) (hlevelR : level < R) (hρ : 0 < rho)
    (hbottom : rho ≤ p.2.1) (htop : p.2.1 + rho ≤ R) :
    Function.Injective
      (sourceFailureCover R level rho t p hstart hlevel hlevelR hρ
        hbottom htop) := by
  intro a b hab
  apply Subtype.ext
  rw [← sourceFailureCoverValue_apply R level rho t p hstart hlevel hlevelR
      hρ hbottom htop a,
    ← sourceFailureCoverValue_apply R level rho t p hstart hlevel hlevelR
      hρ hbottom htop b,
    hab]

theorem natCard_sourceFailure_le_horizontal_add_transverse
    (R level rho t : Nat) (p : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hlevel : 0 < level) (hlevelR : level < R) (hρ : 0 < rho)
    (hbottom : rho ≤ p.2.1) (htop : p.2.1 + rho ≤ R) :
    Nat.card (IsingStoppedCouplingSourceFailureFamily R t p (level : Int)) ≤
      Nat.card (IsingLeapfrogHorizontalEscapeFamily level t) +
        Nat.card (IsingTransverseRaceWitnessFamily rho t (level : Int)) := by
  calc
    _ ≤ Nat.card (IsingLeapfrogHorizontalEscapeFamily level t ⊕
        IsingTransverseRaceWitnessFamily rho t (level : Int)) :=
      Nat.card_le_card_of_injective
        (sourceFailureCover R level rho t p hstart hlevel hlevelR hρ
          hbottom htop)
        (sourceFailureCover_injective R level rho t p hstart hlevel hlevelR hρ
          hbottom htop)
    _ = _ := by rw [Nat.card_sum]

theorem sourceFailure_diffusive_weight_le
    (R level rho : Nat) (p : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hleft : rho ≤ level) (hright : level < R)
    (hbottom : rho ≤ p.2.1) (htop : p.2.1 + rho ≤ R) :
    Nat.card (IsingStoppedCouplingSourceFailureFamily R (rho * rho) p
        (level : Int)) / (4 : Real) ^ (rho * rho) ≤ 17 / (rho : Real) := by
  have hlevel : 0 < level := lt_of_lt_of_le hρ hleft
  have hcard := natCard_sourceFailure_le_horizontal_add_transverse
    R level rho (rho * rho) p hstart hlevel hright hρ hbottom htop
  have hcardReal :
      (Nat.card (IsingStoppedCouplingSourceFailureFamily R (rho * rho) p
        (level : Int)) : Real) ≤
      Nat.card (IsingLeapfrogHorizontalEscapeFamily level (rho * rho)) +
        Nat.card (IsingTransverseRaceWitnessFamily rho (rho * rho)
          (level : Int)) := by exact_mod_cast hcard
  have hden : 0 < (4 : Real) ^ (rho * rho) := by positivity
  have hhor := horizontalEscape_weight_le_inv level (rho * rho) hlevel
  have htrans := transverseRaceWitness_diffusive_weight_le rho rho
    (level : Int) hρ (le_refl _)
  have hρReal : 0 < (rho : Real) := by positivity
  have hlevelReal : (rho : Real) ≤ level := by exact_mod_cast hleft
  have hinv : 1 / (level : Real) ≤ 1 / (rho : Real) :=
    one_div_le_one_div_of_le hρReal hlevelReal
  calc
    _ ≤ (Nat.card (IsingLeapfrogHorizontalEscapeFamily level (rho * rho)) +
        Nat.card (IsingTransverseRaceWitnessFamily rho (rho * rho)
          (level : Int))) / (4 : Real) ^ (rho * rho) :=
      div_le_div_of_nonneg_right hcardReal hden.le
    _ = Nat.card (IsingLeapfrogHorizontalEscapeFamily level (rho * rho)) /
          (4 : Real) ^ (rho * rho) +
        Nat.card (IsingTransverseRaceWitnessFamily rho (rho * rho)
          (level : Int)) / (4 : Real) ^ (rho * rho) := by rw [add_div]
    _ ≤ 1 / (level : Real) + 16 / (rho : Real) := add_le_add hhor htrans
    _ ≤ 1 / (rho : Real) + 16 / (rho : Real) := add_le_add hinv (le_refl _)
    _ = 17 / (rho : Real) := by ring


def isingLeapfrogFlipXChoices (bs : List (Bool × Bool)) : List (Bool × Bool) :=
  bs.map (fun b => (!b.1, b.2))

private theorem flipXChoices_involutive : Function.Involutive isingLeapfrogFlipXChoices := by
  intro bs
  unfold isingLeapfrogFlipXChoices
  simp [Function.comp_def]

private theorem flipXChoices_injective : Function.Injective isingLeapfrogFlipXChoices :=
  flipXChoices_involutive.injective

private theorem boxReflectX_choiceNext
    (R : Nat) (p : IsingLeapfrogBox R) (b : Bool × Bool) :
    isingLeapfrogBoxReflectX R (isingLeapfrogChoiceNext R p b) =
      isingLeapfrogChoiceNext R (isingLeapfrogBoxReflectX R p) (!b.1, b.2) := by
  by_cases hp : isingLeapfrogBoxBoundary R p
  · have hpr := (isingLeapfrogBoxBoundary_reflectX_iff R p).2 hp
    simp [isingLeapfrogChoiceNext, hp, hpr]
  · have hpr : ¬ isingLeapfrogBoxBoundary R (isingLeapfrogBoxReflectX R p) :=
      mt (isingLeapfrogBoxBoundary_reflectX_iff R p).mp hp
    rcases b with ⟨bx, byy⟩
    cases bx <;> cases byy <;>
      simp only [isingLeapfrogChoiceNext, hp, hpr, ↓reduceDIte,
        Bool.not_false, Bool.not_true]
    all_goals
      apply Prod.ext <;> apply Fin.ext <;>
        simp [isingLeapfrogBoxReflectX, isingLeapfrogSW, isingLeapfrogSE,
          isingLeapfrogNW, isingLeapfrogNE, isingLeapfrogWest,
          isingLeapfrogEast, isingLeapfrogSouth, isingLeapfrogNorth] <;>
        unfold isingLeapfrogBoxBoundary at hp <;> omega

theorem choiceRun_reflectX
    (R : Nat) (p : IsingLeapfrogBox R) (bs : List (Bool × Bool)) :
    isingLeapfrogChoiceRun R (isingLeapfrogBoxReflectX R p)
        (isingLeapfrogFlipXChoices bs) =
      isingLeapfrogBoxReflectX R (isingLeapfrogChoiceRun R p bs) := by
  induction bs generalizing p with
  | nil => rfl
  | cons b bs ih =>
      simp only [isingLeapfrogFlipXChoices, List.map_cons,
        isingLeapfrogChoiceRun]
      rw [← boxReflectX_choiceNext]
      exact ih (isingLeapfrogChoiceNext R p b)

private theorem choiceExecValid_reflectX_iff
    (R : Nat) (p : IsingLeapfrogBox R) (bs : List (Bool × Bool)) :
    IsingLeapfrogChoiceExecValid R (isingLeapfrogBoxReflectX R p)
        (isingLeapfrogFlipXChoices bs) ↔
      IsingLeapfrogChoiceExecValid R p bs := by
  constructor
  · intro h j hj
    have hj' : j < (isingLeapfrogFlipXChoices bs).length := by simpa [isingLeapfrogFlipXChoices] using hj
    have h' := h j hj'
    have htake : (isingLeapfrogFlipXChoices bs).take j =
        isingLeapfrogFlipXChoices (bs.take j) := by
      simp [isingLeapfrogFlipXChoices, List.map_take]
    rw [htake, choiceRun_reflectX] at h'
    exact mt (isingLeapfrogBoxBoundary_reflectX_iff R _).mpr h'
  · intro h j hj
    have h' := h j (by simpa [isingLeapfrogFlipXChoices] using hj)
    have htake : (isingLeapfrogFlipXChoices bs).take j =
        isingLeapfrogFlipXChoices (bs.take j) := by
      simp [isingLeapfrogFlipXChoices, List.map_take]
    rw [htake, choiceRun_reflectX]
    exact mt (isingLeapfrogBoxBoundary_reflectX_iff R _).mp h'

private theorem choiceSteps_flipX
    (bs : List (Bool × Bool)) :
    isingLeapfrogChoiceSteps (isingLeapfrogFlipXChoices bs) =
      (isingLeapfrogChoiceSteps bs).map reflectIncrement := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      rcases b with ⟨bx, byy⟩
      cases bx <;> cases byy <;>
        simp [isingLeapfrogFlipXChoices, isingLeapfrogChoiceSteps,
          isingLeapfrogChoiceStep, reflectIncrement, ih]

private theorem displacement_map_reflectIncrement (path : List (Int × Int)) :
    isingDiagonalWalkDisplacement (path.map reflectIncrement) =
      (-(isingDiagonalWalkDisplacement path).1,
        (isingDiagonalWalkDisplacement path).2) := by
  have hneg : (path.map (fun d => -d.1)).sum =
      -(path.map Prod.fst).sum := by
    induction path with
    | nil => simp
    | cons d path ih => simp [ih, add_comm]
  unfold isingDiagonalWalkDisplacement
  apply Prod.ext
  · simp only [List.map_map]
    change (path.map (fun d => -d.1)).sum = -(path.map Prod.fst).sum
    exact hneg
  · simp [Function.comp_def, reflectIncrement]

private def globalReflectHitSplit
    (R : Nat) {start : Int × Int} {level : Int}
    (split : IsingDiagonalWalkHitSplit start level) :
    IsingDiagonalWalkHitSplit ((R : Int) - start.1, start.2) ((R : Int) - level) where
  before := split.before.map reflectIncrement
  after := split.after.map reflectIncrement
  hit := by
    rw [displacement_map_reflectIncrement]
    have h := split.hit
    dsimp at h ⊢
    omega

private theorem globalReflectHitSplit_steps
    (R : Nat) {start : Int × Int} {level : Int}
    (split : IsingDiagonalWalkHitSplit start level) :
    (globalReflectHitSplit R split).steps = split.steps.map reflectIncrement := by
  unfold globalReflectHitSplit IsingDiagonalWalkHitSplit.steps
  exact List.map_append.symm

private theorem globalReflectHitSplit_firstHit
    (R : Nat) {start : Int × Int} {level : Int}
    (split : IsingDiagonalWalkHitSplit start level) (hfirst : split.FirstHit) :
    (globalReflectHitSplit R split).FirstHit := by
  intro k hk heq
  have hk' : k < split.before.length := by simpa [globalReflectHitSplit] using hk
  have horig := hfirst k hk'
  have href :
      (isingDiagonalWalkEndpoint ((R : Int) - start.1, start.2)
        (((globalReflectHitSplit R split).before).take k)).1 =
      (R : Int) -
        (isingDiagonalWalkEndpoint start (split.before.take k)).1 := by
    rw [show ((globalReflectHitSplit R split).before).take k =
        (split.before.take k).map reflectIncrement by
      simp [globalReflectHitSplit, List.map_take]]
    unfold isingDiagonalWalkEndpoint
    rw [displacement_map_reflectIncrement]
    ring
  rw [heq] at href
  apply horig
  omega

theorem boxInt_reflectX
    (R : Nat) (p : IsingLeapfrogBox R) :
    isingLeapfrogBoxInt (isingLeapfrogBoxReflectX R p) =
      ((R : Int) - (isingLeapfrogBoxInt p).1, (isingLeapfrogBoxInt p).2) := by
  unfold isingLeapfrogBoxInt isingLeapfrogBoxReflectX
  dsimp
  apply Prod.ext
  · push_cast
    omega
  · rfl

def sourceFailureReflectX
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Nat)
    (hlevelR : level ≤ R) :
    IsingStoppedCouplingSourceFailureFamily R t p (level : Int) →
      IsingStoppedCouplingSourceFailureFamily R t
        (isingLeapfrogBoxReflectX R p) ((R - level : Nat) : Int) := fun w => by
  let w' : IsingLeapfrogChoiceStringFamily t :=
    ⟨isingLeapfrogFlipXChoices w.1.1, by
      simp [isingLeapfrogFlipXChoices, w.1.2]⟩
  refine ⟨w', ?_⟩
  rcases w.2 with ⟨split, hsplit, hnot⟩
  let split' := globalReflectHitSplit R split
  unfold IsingStoppedCouplingSourceFailure
  have hlevel : ((R - level : Nat) : Int) = (R : Int) - level := by
    rw [Nat.cast_sub hlevelR]
  rw [boxInt_reflectX, hlevel]
  refine ⟨split', ?_, ?_⟩
  · have hpath : isingLeapfrogChoiceSteps w'.1 = split'.steps := by
      dsimp [w']
      rw [choiceSteps_flipX, globalReflectHitSplit_steps,
        firstHitSplit_steps hsplit]
    rw [hpath]
    exact firstHitSplit_eq_some split'
      (globalReflectHitSplit_firstHit R split (firstHitSplit_firstHit hsplit))
  · have hlen : split'.before.length = split.before.length := by
      simp [split', globalReflectHitSplit]
    rw [hlen]
    intro hvalid
    apply hnot
    apply (choiceExecValid_reflectX_iff R p (w.1.1.take split.before.length)).mp
    simpa [w', isingLeapfrogFlipXChoices, List.map_take] using hvalid

theorem sourceFailureReflectX_injective
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Nat)
    (hlevelR : level ≤ R) :
    Function.Injective (sourceFailureReflectX R t p level hlevelR) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact flipXChoices_injective (congrArg (fun z => z.1.1) h)

def mirrorFailureToSource
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p)) :
    IsingStoppedCouplingMirrorFailureFamily R t p p' level →
      IsingStoppedCouplingSourceFailureFamily R t p' level := fun w => by
  let w' := isingLeapfrogCouplingChoiceTransform t
    (isingLeapfrogBoxInt p) level w.1
  refine ⟨w', ?_⟩
  rcases w.2 with ⟨split, hsplit, hnot⟩
  unfold IsingStoppedCouplingSourceFailure
  rw [hmirror]
  refine ⟨split.reflectPrefix, ?_, ?_⟩
  · have hpath : isingLeapfrogChoiceSteps w'.1 = split.reflectPrefix.steps := by
      dsimp [w']
      have hsteps : isingLeapfrogChoiceSteps
          (isingLeapfrogCouplingChoiceTransform t (isingLeapfrogBoxInt p)
            level w.1).1 =
          isingDiagonalWalkCouplingReflectSteps (isingLeapfrogBoxInt p) level
            (isingLeapfrogChoiceSteps w.1.1) := by
        exact choiceSteps_encodeSteps_of_valid _
          (couplingReflectSteps_valid (isingLeapfrogBoxInt p) level _
            (isingLeapfrogChoiceSteps_valid w.1.1))
      rw [hsteps]
      unfold isingDiagonalWalkCouplingReflectSteps
      rw [hsplit]
    rw [hpath]
    exact firstHitSplit_eq_some split.reflectPrefix
      (reflectPrefix_firstHit split (firstHitSplit_firstHit hsplit))
  · simpa [w', reflectPrefix] using hnot

theorem mirrorFailureToSource_injective
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p)) :
    Function.Injective (mirrorFailureToSource R t p p' level hmirror) := by
  intro a b h
  apply Subtype.ext
  apply (isingLeapfrogCouplingChoiceEquiv t (isingLeapfrogBoxInt p) level).injective
  exact congrArg (fun z => z.1) h

def mirrorFailureReflectX
    (R t level : Nat) (p p' : IsingLeapfrogBox R)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hlevelR : level ≤ R) :
    IsingStoppedCouplingMirrorFailureFamily R t p p' (level : Int) →
      IsingStoppedCouplingSourceFailureFamily R t
        (isingLeapfrogBoxReflectX R p') ((R - level : Nat) : Int) :=
  fun w => sourceFailureReflectX R t p' level hlevelR
    (mirrorFailureToSource R t p p' (level : Int) hmirror w)

theorem mirrorFailureReflectX_injective
    (R t level : Nat) (p p' : IsingLeapfrogBox R)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hlevelR : level ≤ R) :
    Function.Injective
      (mirrorFailureReflectX R t level p p' hmirror hlevelR) :=
  (sourceFailureReflectX_injective R t p' level hlevelR).comp
    (mirrorFailureToSource_injective R t p p' (level : Int) hmirror)

theorem mirrorFailure_diffusive_weight_le
    (R level rho : Nat) (p p' : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hlevel : 0 < level)
    (hright : level + rho ≤ R)
    (hbottom : rho ≤ p'.2.1) (htop : p'.2.1 + rho ≤ R) :
    Nat.card (IsingStoppedCouplingMirrorFailureFamily R (rho * rho) p p'
        (level : Int)) / (4 : Real) ^ (rho * rho) ≤ 17 / (rho : Real) := by
  have hlevelR : level ≤ R := by omega
  have hcard : Nat.card (IsingStoppedCouplingMirrorFailureFamily R
      (rho * rho) p p' (level : Int)) ≤
      Nat.card (IsingStoppedCouplingSourceFailureFamily R (rho * rho)
        (isingLeapfrogBoxReflectX R p') ((R - level : Nat) : Int)) :=
    Nat.card_le_card_of_injective
      (mirrorFailureReflectX R (rho * rho) level p p' hmirror hlevelR)
      (mirrorFailureReflectX_injective R (rho * rho) level p p' hmirror hlevelR)
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
  have hrefLeft : rho ≤ R - level := by omega
  have hrefRight : R - level < R := by omega
  have hrefBottom : rho ≤ (isingLeapfrogBoxReflectX R p').2.1 := by
    simpa [isingLeapfrogBoxReflectX] using hbottom
  have hrefTop : (isingLeapfrogBoxReflectX R p').2.1 + rho ≤ R := by
    simpa [isingLeapfrogBoxReflectX] using htop
  have hsource := sourceFailure_diffusive_weight_le R (R - level) rho
    (isingLeapfrogBoxReflectX R p') hrefStart hρ hrefLeft hrefRight
      hrefBottom hrefTop
  have hcardReal :
      (Nat.card (IsingStoppedCouplingMirrorFailureFamily R (rho * rho) p p'
        (level : Int)) : Real) ≤
      Nat.card (IsingStoppedCouplingSourceFailureFamily R (rho * rho)
        (isingLeapfrogBoxReflectX R p') ((R - level : Nat) : Int)) := by
    exact_mod_cast hcard
  exact le_trans (div_le_div_of_nonneg_right hcardReal (by positivity)) hsource

theorem stoppedCouplingBad_diffusive_weight_le
    (R level rho : Nat) (p p' : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hleft : rho ≤ level) (hright : level + rho ≤ R)
    (hbottom : rho ≤ p.2.1) (htop : p.2.1 + rho ≤ R) :
    Nat.card (IsingLeapfrogStoppedCouplingBadFamily R (rho * rho) p p'
        (level : Int)) / (4 : Real) ^ (rho * rho) ≤ 38 / (rho : Real) := by
  have hcover := natCard_stoppedCouplingBad_le_noHit_add_failures R
    (rho * rho) p p' (level : Int) hmirror
  have hcoverReal :
      (Nat.card (IsingLeapfrogStoppedCouplingBadFamily R (rho * rho) p p'
        (level : Int)) : Real) ≤
      Nat.card (IsingLeapfrogChoiceNoHitAll (rho * rho)
        (isingLeapfrogBoxInt p).1 (level : Int)) +
      Nat.card (IsingStoppedCouplingSourceFailureFamily R (rho * rho) p
        (level : Int)) +
      Nat.card (IsingStoppedCouplingMirrorFailureFamily R (rho * rho) p p'
        (level : Int)) := by exact_mod_cast hcover
  have hnohit : Nat.card (IsingLeapfrogChoiceNoHitAll (rho * rho)
      (isingLeapfrogBoxInt p).1 (level : Int)) /
        (4 : Real) ^ (rho * rho) ≤ 4 / (rho : Real) := by
    have hx : (isingLeapfrogBoxInt p).1 = (level : Int) - 1 := by omega
    rw [hx]
    exact choiceNoHitAll_diffusive_weight_le rho (level : Int) hρ
  have hsource := sourceFailure_diffusive_weight_le R level rho p hstart hρ
    hleft (by omega) hbottom htop
  have hp'y : p'.2.1 = p.2.1 := by
    have hy := congrArg Prod.snd hmirror
    dsimp [isingLeapfrogBoxInt, reflectedEndpoint] at hy
    exact_mod_cast hy
  have hbottom' : rho ≤ p'.2.1 := by omega
  have htop' : p'.2.1 + rho ≤ R := by omega
  have hmirrorFail := mirrorFailure_diffusive_weight_le R level rho p p'
    hstart hmirror hρ (lt_of_lt_of_le hρ hleft) hright hbottom' htop'
  have hden : 0 < (4 : Real) ^ (rho * rho) := by positivity
  calc
    _ ≤ (Nat.card (IsingLeapfrogChoiceNoHitAll (rho * rho)
          (isingLeapfrogBoxInt p).1 (level : Int)) +
        Nat.card (IsingStoppedCouplingSourceFailureFamily R (rho * rho) p
          (level : Int)) +
        Nat.card (IsingStoppedCouplingMirrorFailureFamily R (rho * rho) p p'
          (level : Int))) / (4 : Real) ^ (rho * rho) :=
      div_le_div_of_nonneg_right hcoverReal hden.le
    _ = Nat.card (IsingLeapfrogChoiceNoHitAll (rho * rho)
          (isingLeapfrogBoxInt p).1 (level : Int)) /
          (4 : Real) ^ (rho * rho) +
        Nat.card (IsingStoppedCouplingSourceFailureFamily R (rho * rho) p
          (level : Int)) / (4 : Real) ^ (rho * rho) +
        Nat.card (IsingStoppedCouplingMirrorFailureFamily R (rho * rho) p p'
          (level : Int)) / (4 : Real) ^ (rho * rho) := by ring
    _ ≤ 4 / (rho : Real) + 17 / (rho : Real) + 17 / (rho : Real) :=
      add_le_add (add_le_add hnohit hsource) hmirrorFail
    _ = 38 / (rho : Real) := by ring



theorem isingLeapfrogStoppedKernel_reflectionCoupling_l1_le
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int) :
    ∑ q : IsingLeapfrogBox R,
      |isingLeapfrogStoppedKernel R t p q -
        isingLeapfrogStoppedKernel R t p' q| ≤
      2 * (Nat.card
        (IsingLeapfrogStoppedCouplingBadFamily R t p p' level) : Real) /
          (4 : Real) ^ t := by
  classical
  letI := Fintype.ofFinite (IsingLeapfrogChoiceStringFamily t)
  let e := isingLeapfrogCouplingChoiceEquiv t
    (isingLeapfrogBoxInt p) level
  let f : IsingLeapfrogChoiceStringFamily t → IsingLeapfrogBox R :=
    fun w => isingLeapfrogChoiceRun R p w.1
  let g : IsingLeapfrogChoiceStringFamily t → IsingLeapfrogBox R :=
    fun w => isingLeapfrogChoiceRun R p' w.1
  have hcount := finiteUniformCoupling_fiber_l1_le e f g
  have hden : 0 < (4 : Real) ^ t := by positivity
  have hfiber (q : IsingLeapfrogBox R) :
      Nat.card (IsingLeapfrogStoppedChoicePathFamily R t p q) =
        Nat.card {w : IsingLeapfrogChoiceStringFamily t // f w = q} := by
    exact Nat.card_congr
      (isingLeapfrogStoppedChoicePathFiberEquiv R t p q)
  have hfiber' (q : IsingLeapfrogBox R) :
      Nat.card (IsingLeapfrogStoppedChoicePathFamily R t p' q) =
        Nat.card {w : IsingLeapfrogChoiceStringFamily t // g w = q} := by
    exact Nat.card_congr
      (isingLeapfrogStoppedChoicePathFiberEquiv R t p' q)
  rw [show Nat.card
      (IsingLeapfrogStoppedCouplingBadFamily R t p p' level) =
      Nat.card {w : IsingLeapfrogChoiceStringFamily t // f w ≠ g (e w)} by
        rfl]
  simp_rw [isingLeapfrogStoppedKernel_eq_natCard_choicePath_div]
  simp_rw [hfiber, hfiber']
  calc
    (∑ q : IsingLeapfrogBox R,
      |((Nat.card {w : IsingLeapfrogChoiceStringFamily t // f w = q} : Real) /
          (4 : Real) ^ t) -
        ((Nat.card {w : IsingLeapfrogChoiceStringFamily t // g w = q} : Real) /
          (4 : Real) ^ t)|) =
      (∑ q : IsingLeapfrogBox R,
        |((Nat.card {w : IsingLeapfrogChoiceStringFamily t // f w = q} : Real) -
          (Nat.card {w : IsingLeapfrogChoiceStringFamily t // g w = q} : Real))|) /
            (4 : Real) ^ t := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro q hq
      rw [div_sub_div_same, abs_div, abs_of_pos hden]
    _ ≤ (2 * (Nat.card
        {w : IsingLeapfrogChoiceStringFamily t // f w ≠ g (e w)} : Real)) /
          (4 : Real) ^ t := by
      exact div_le_div_of_nonneg_right hcount hden.le



theorem isingLeapfrogStoppedKernel_reflectedStart_diffusive_l1_le
    (R level rho : Nat) (p p' : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hleft : rho ≤ level) (hright : level + rho ≤ R)
    (hbottom : rho ≤ p.2.1) (htop : p.2.1 + rho ≤ R) :
    (∑ q : IsingLeapfrogBox R,
      |isingLeapfrogStoppedKernel R (rho * rho) p q -
        isingLeapfrogStoppedKernel R (rho * rho) p' q|) ≤
      76 / (rho : Real) := by
  have hcouple := isingLeapfrogStoppedKernel_reflectionCoupling_l1_le R
    (rho * rho) p p' (level : Int)
  have hbad := stoppedCouplingBad_diffusive_weight_le R level rho p p'
    hstart hmirror hρ hleft hright hbottom htop
  calc
    _ ≤ 2 * (Nat.card (IsingLeapfrogStoppedCouplingBadFamily R
        (rho * rho) p p' (level : Int)) : Real) /
          (4 : Real) ^ (rho * rho) := hcouple
    _ = 2 * ((Nat.card (IsingLeapfrogStoppedCouplingBadFamily R
        (rho * rho) p p' (level : Int)) : Real) /
          (4 : Real) ^ (rho * rho)) := by ring
    _ ≤ 2 * (38 / (rho : Real)) := mul_le_mul_of_nonneg_left hbad
      (show (0 : Real) ≤ 2 by norm_num)
    _ = 76 / (rho : Real) := by ring

end

end StatMech.Universality
