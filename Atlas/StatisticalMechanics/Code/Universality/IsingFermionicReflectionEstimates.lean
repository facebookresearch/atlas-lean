/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicLineGambler








namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

private def encodeStep (d : Int × Int) : Bool × Bool :=
  (decide (d.1 = 1), decide (d.2 = 1))

private def encodePath (path : List (Int × Int)) : List (Bool × Bool) :=
  path.map encodeStep



private def horizontalRightCode (path : List (Int × Int)) : List Bool :=
  path.map (fun d => decide (d.1 = -1))

private def horizontalLeftCode (path : List (Int × Int)) : List Bool :=
  path.map (fun d => decide (d.1 = 1))

private def verticalCode (path : List (Int × Int)) : List Bool :=
  path.map (fun d => decide (d.2 = 1))

def lineFreeEndpoint (start : Int) : List Bool → Int
  | [] => start
  | b :: bs => lineFreeEndpoint (start + if b then 1 else -1) bs

private noncomputable def intLineChoiceNext (n : Nat) (x : Int)
    (b : Bool) : Int :=
  if x = 0 ∨ x = n then x else x + if b then 1 else -1

private noncomputable def intLineChoiceRun (n : Nat) : Int → List Bool → Int
  | x, [] => x
  | x, b :: bs => intLineChoiceRun n (intLineChoiceNext n x b) bs

private theorem lineFreeEndpoint_horizontalRightCode
    (path : List (Int × Int)) (start : Int × Int) (right : Int)
    (hvalid : IsingDiagonalWalkStepsValid path) :
    lineFreeEndpoint (right - start.1) (horizontalRightCode path) =
      right - (isingDiagonalWalkEndpoint start path).1 := by
  induction path generalizing start with
  | nil => simp [lineFreeEndpoint, horizontalRightCode,
      isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement]
  | cons d path ih =>
      have hd := hvalid d (by simp)
      have htail : IsingDiagonalWalkStepsValid path := by
        intro e he
        exact hvalid e (by simp [he])
      have hih := ih (isingDiagonalWalkNext start d) htail
      have hstep :
          right - start.1 + (if decide (d.1 = -1) then 1 else -1) =
            right - (isingDiagonalWalkNext start d).1 := by
        rcases hd.1 with hd | hd <;>
          simp [hd, isingDiagonalWalkNext] <;> omega
      rw [horizontalRightCode, List.map_cons, lineFreeEndpoint, hstep]
      simpa [isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement,
        isingDiagonalWalkNext, add_assoc] using hih

private theorem lineFreeEndpoint_horizontalLeftCode
    (path : List (Int × Int)) (start : Int × Int)
    (hvalid : IsingDiagonalWalkStepsValid path) :
    lineFreeEndpoint start.1 (horizontalLeftCode path) =
      (isingDiagonalWalkEndpoint start path).1 := by
  induction path generalizing start with
  | nil => simp [lineFreeEndpoint, horizontalLeftCode,
      isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement]
  | cons d path ih =>
      have hd := hvalid d (by simp)
      have htail : IsingDiagonalWalkStepsValid path := by
        intro e he
        exact hvalid e (by simp [he])
      have hih := ih (isingDiagonalWalkNext start d) htail
      have hstep :
          start.1 + (if decide (d.1 = 1) then 1 else -1) =
            (isingDiagonalWalkNext start d).1 := by
        rcases hd.1 with hd | hd <;>
          simp [hd, isingDiagonalWalkNext] <;> omega
      rw [horizontalLeftCode, List.map_cons, lineFreeEndpoint, hstep]
      simpa [isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement,
        isingDiagonalWalkNext, add_assoc] using hih

private theorem lineFreeEndpoint_verticalCode
    (path : List (Int × Int)) (start : Int × Int)
    (hvalid : IsingDiagonalWalkStepsValid path) :
    lineFreeEndpoint start.2 (verticalCode path) =
      (isingDiagonalWalkEndpoint start path).2 := by
  induction path generalizing start with
  | nil => simp [lineFreeEndpoint, verticalCode,
      isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement]
  | cons d path ih =>
      have hd := hvalid d (by simp)
      have htail : IsingDiagonalWalkStepsValid path := by
        intro e he
        exact hvalid e (by simp [he])
      have hih := ih (isingDiagonalWalkNext start d) htail
      have hstep :
          start.2 + (if decide (d.2 = 1) then 1 else -1) =
            (isingDiagonalWalkNext start d).2 := by
        rcases hd.2 with hd | hd <;>
          simp [hd, isingDiagonalWalkNext] <;> omega
      rw [verticalCode, List.map_cons, lineFreeEndpoint, hstep]
      simpa [isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement,
        isingDiagonalWalkNext, add_assoc] using hih

def VerticalChoicePathFamily (t : Nat) (x y : Int) :=
  {bs : List Bool // bs.length = t ∧ lineFreeEndpoint x bs = y}

noncomputable instance verticalChoicePathFamily_finite
    (t : Nat) (x y : Int) : Finite (VerticalChoicePathFamily t x y) := by
  letI : Fintype {bs : List Bool // bs.length = t} :=
    (List.finite_length_eq Bool t).fintype
  exact Finite.of_injective
    (fun w : VerticalChoicePathFamily t x y =>
      (⟨w.1, w.2.1⟩ : {bs : List Bool // bs.length = t}))
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun z : {bs : List Bool // bs.length = t} => z.1) h)

private def verticalChoicePathFamilySuccEquiv (t : Nat) (x y : Int) :
    VerticalChoicePathFamily (t + 1) x y ≃
      Σ b : Bool, VerticalChoicePathFamily t
        (x + if b then 1 else -1) y where
  toFun w := by
    rcases w with ⟨bs, hlen, hend⟩
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
        exact ⟨b, ⟨bs, by simpa using hlen, by
          simpa [lineFreeEndpoint] using hend⟩⟩
  invFun w := ⟨w.1 :: w.2.1, by simp [w.2.2.1], by
    simpa [lineFreeEndpoint] using w.2.2.2⟩
  left_inv w := by
    rcases w with ⟨bs, hlen, hend⟩
    cases bs with
    | nil => simp at hlen
    | cons b bs => rfl
  right_inv w := by
    rcases w with ⟨b, bs, hlen, hend⟩
    rfl

private def verticalChoicePathFamilyZeroSelfEquiv (x : Int) :
    VerticalChoicePathFamily 0 x x ≃ ULift.{1, 0} Unit where
  toFun _ := ⟨Unit.unit⟩
  invFun _ := ⟨[], rfl, rfl⟩
  left_inv w := by
    apply Subtype.ext
    exact (List.eq_nil_of_length_eq_zero w.2.1).symm
  right_inv _ := rfl

private def verticalChoicePathFamilyZeroNeEquiv (x y : Int) (hxy : x ≠ y) :
    VerticalChoicePathFamily 0 x y ≃ Empty where
  toFun w := by
    have hnil : w.1 = [] := List.eq_nil_of_length_eq_zero w.2.1
    have : x = y := by simpa [hnil, lineFreeEndpoint] using w.2.2
    exact (hxy this).elim
  invFun e := e.elim
  left_inv w := (hxy (by
    have hnil : w.1 = [] := List.eq_nil_of_length_eq_zero w.2.1
    simpa [hnil, lineFreeEndpoint] using w.2.2)).elim
  right_inv e := e.elim



theorem isingLineBinomialKernel_eq_natCard_verticalChoicePath_div
    (t : Nat) (x y : Int) :
    isingLineBinomialKernel t x y =
      Nat.card (VerticalChoicePathFamily t x y) / (2 : Real) ^ t := by
  induction t generalizing x with
  | zero =>
      by_cases hxy : x = y
      · subst y
        rw [Nat.card_congr (verticalChoicePathFamilyZeroSelfEquiv x)]
        simp [isingLineBinomialKernel, isingBinomialWeight]
      · rw [Nat.card_congr
          (verticalChoicePathFamilyZeroNeEquiv x y hxy)]
        simp [isingLineBinomialKernel, isingBinomialWeight, hxy,
          Ne.symm hxy]
  | succ t ih =>
      rw [isingLineBinomialKernel_succ]
      rw [Nat.card_congr (verticalChoicePathFamilySuccEquiv t x y),
        Nat.card_sigma]
      rw [ih, ih]
      simp
      push_cast
      rw [pow_succ]
      ring

private theorem intLineChoiceRun_of_zero (n : Nat) (bs : List Bool) :
    intLineChoiceRun n 0 bs = 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp [intLineChoiceRun, intLineChoiceNext, ih]

private theorem intLineChoiceRun_eq_zero_of_free_hit
    (n : Nat) (start : Int) (bs : List Bool) (k : Nat)
    (hstart0 : 0 ≤ start) (hstartn : start < n)
    (hk : k ≤ bs.length)
    (hhit : lineFreeEndpoint start (bs.take k) = 0)
    (hnoRight : ∀ j, j < k →
      lineFreeEndpoint start (bs.take j) ≠ n) :
    intLineChoiceRun n start bs = 0 := by
  induction k generalizing start bs with
  | zero =>
      simp [lineFreeEndpoint] at hhit
      subst start
      exact intLineChoiceRun_of_zero n bs
  | succ k ih =>
      cases bs with
      | nil => simp at hk
      | cons b bs =>
          have hstartNeN : start ≠ n := hnoRight 0 (by omega)
          by_cases hstartZero : start = 0
          · subst start
            exact intLineChoiceRun_of_zero n (b :: bs)
          · have hstartPos : 0 < start := by omega
            let next := start + if b then 1 else -1
            have hrun : intLineChoiceRun n start (b :: bs) =
                intLineChoiceRun n next bs := by
              simp [intLineChoiceRun, intLineChoiceNext, hstartZero,
                hstartNeN, next]
            by_cases hnextZero : next = 0
            · rw [hrun, hnextZero]
              exact intLineChoiceRun_of_zero n bs
            · have hhitTail : lineFreeEndpoint next (bs.take k) = 0 := by
                simpa [lineFreeEndpoint, next] using hhit
              have hkTail : k ≤ bs.length := by simpa using hk
              have hnextNonneg : 0 ≤ next := by
                unfold next
                cases b <;> simp_all <;> omega
              have hnextLt : next < n := by
                by_contra hnot
                have hnle : n ≤ next := by omega
                have hnextLe : next ≤ n := by
                  unfold next
                  cases b <;> simp_all <;> omega
                have hnextEq : next = n := by omega
                by_cases hk0 : k = 0
                · subst k
                  simp [lineFreeEndpoint] at hhitTail
                  exact hnextZero hhitTail
                · have hbad := hnoRight 1 (by omega)
                  apply hbad
                  simpa [lineFreeEndpoint, next, hnextEq]
              have hnoTail : ∀ j, j < k →
                  lineFreeEndpoint next (bs.take j) ≠ n := by
                intro j hj
                have hbad := hnoRight (j + 1) (by omega)
                simpa [lineFreeEndpoint, next, List.take_succ_cons] using hbad
              rw [hrun]
              exact ih next bs hnextNonneg hnextLt hkTail hhitTail hnoTail

private theorem intLineChoiceRun_eq_lineChoiceRun_val
    (n : Nat) (p : IsingLineBox n) (bs : List Bool) :
    intLineChoiceRun n p.1 bs = (isingLineChoiceRun n p bs).1 := by
  induction bs generalizing p with
  | nil => rfl
  | cons b bs ih =>
      simp only [intLineChoiceRun, isingLineChoiceRun]
      by_cases hp : isingLineBoxBoundary n p
      · have hp' : (p.1 : Int) = 0 ∨ (p.1 : Int) = n := by
          unfold isingLineBoxBoundary at hp
          rcases hp with hp | hp <;> simp [hp]
        simp only [intLineChoiceNext, hp', if_pos,
          isingLineChoiceNext, dif_pos hp]
        exact ih p
      · have hp' : ¬((p.1 : Int) = 0 ∨ (p.1 : Int) = n) := by
          unfold isingLineBoxBoundary at hp
          push Not at hp ⊢
          exact ⟨by exact_mod_cast hp.1, by exact_mod_cast hp.2⟩
        simp only [intLineChoiceNext, hp', if_false,
          isingLineChoiceNext, dif_neg hp]
        cases b
        · have hnext := ih (isingLineWest n p)
          have hp0 : 0 < p.1 := by
            unfold isingLineBoxBoundary at hp
            omega
          have hcast : ((isingLineWest n p).1 : Int) = (p.1 : Int) - 1 := by
            change ((p.1 - 1 : Nat) : Int) = _
            rw [Int.ofNat_sub hp0]
            norm_num
          change intLineChoiceRun n ((p.1 : Int) - 1) bs = _
          rw [← hcast]
          exact hnext
        · have hnext := ih (isingLineEast n p hp)
          simpa [isingLineEast] using hnext

private theorem encodeStep_injective_of_valid {d e : Int × Int}
    (hd : (d.1 = 1 ∨ d.1 = -1) ∧ (d.2 = 1 ∨ d.2 = -1))
    (he : (e.1 = 1 ∨ e.1 = -1) ∧ (e.2 = 1 ∨ e.2 = -1))
    (h : encodeStep d = encodeStep e) : d = e := by
  rcases hd with ⟨hdx | hdx, hdy | hdy⟩ <;>
    rcases he with ⟨hex | hex, hey | hey⟩ <;>
    simp [encodeStep, hdx, hdy, hex, hey] at h
  all_goals apply Prod.ext <;> simp_all

private theorem encodePath_injective_of_valid
    {a b : List (Int × Int)}
    (ha : IsingDiagonalWalkStepsValid a)
    (hb : IsingDiagonalWalkStepsValid b)
    (h : encodePath a = encodePath b) : a = b := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => rfl
      | cons e b => simp [encodePath] at h
  | cons d a ih =>
      cases b with
      | nil => simp [encodePath] at h
      | cons e b =>
          simp only [encodePath, List.map_cons, List.cons.injEq] at h
          have hd := ha d (by simp)
          have he := hb e (by simp)
          have hde := encodeStep_injective_of_valid hd he h.1
          subst e
          congr 1
          apply ih
          · intro z hz
            exact ha z (by simp [hz])
          · intro z hz
            exact hb z (by simp [hz])
          · exact h.2

private def firstHitFamilyCode
    {start : Int × Int} {level : Int} {walkLength : Nat}
    {target : Int × Int}
    (w : FirstHitFamily start level walkLength target) :
    {bits : List (Bool × Bool) // bits.length = walkLength} :=
  ⟨encodePath w.1.steps, by
    simp [encodePath, w.2.2.2.1]⟩

private theorem firstHitFamilyCode_injective
    {start : Int × Int} {level : Int} {walkLength : Nat}
    {target : Int × Int} :
    Function.Injective (@firstHitFamilyCode start level walkLength target) := by
  intro w v h
  have hcode : encodePath w.1.steps = encodePath v.1.steps :=
    congrArg Subtype.val h
  have hsteps := encodePath_injective_of_valid w.2.2.1 v.2.2.1 hcode
  have hw := firstHitSplit_eq_some w.1 w.2.1
  have hv := firstHitSplit_eq_some v.1 v.2.1
  have hwv : w.1 = v.1 := by
    apply Option.some.inj
    rw [← hw, ← hv, hsteps]
  exact Subtype.ext hwv

noncomputable instance firstHitFamily_finite
    (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    Finite (FirstHitFamily start level walkLength target) := by
  letI : Fintype
      {bits : List (Bool × Bool) // bits.length = walkLength} :=
    (List.finite_length_eq (Bool × Bool) walkLength).fintype
  exact Finite.of_injective firstHitFamilyCode firstHitFamilyCode_injective

noncomputable instance survivingFirstHitFamily_finite
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    Finite (SurvivingFirstHitFamily R start level walkLength target) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance survivalExceptionalFirstHitFamily_finite
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    Finite (SurvivalExceptionalFirstHitFamily R start level walkLength target) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance survivalExceptionalMirrorFamily_finite
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    Finite (SurvivalExceptionalMirrorFamily R start level walkLength target) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance survivalMatchedFirstHitFamily_finite
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    Finite (SurvivalMatchedFirstHitFamily R start level walkLength target) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance survivalMatchedMirrorFamily_finite
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    Finite (SurvivalMatchedMirrorFamily R start level walkLength target) :=
  Finite.of_injective Subtype.val Subtype.val_injective



theorem survivalExceptionalFirstHitFamily_code_injective
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    ∃ f : SurvivalExceptionalFirstHitFamily R start level walkLength target →
        {bits : List (Bool × Bool) // bits.length = walkLength},
      Function.Injective f := by
  exact ⟨fun w => firstHitFamilyCode w.1.1,
    fun a b h => by
      apply Subtype.ext
      apply Subtype.ext
      exact firstHitFamilyCode_injective h⟩



theorem natDist_survivingFirstHitFamily_le_exceptions
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    Nat.dist
        (Nat.card (SurvivingFirstHitFamily R start level walkLength target))
        (Nat.card (SurvivingFirstHitFamily R
          (reflectedEndpoint level start) level walkLength target)) ≤
      Nat.card (SurvivalExceptionalFirstHitFamily R start level
          walkLength target) +
        Nat.card (SurvivalExceptionalMirrorFamily R start level
          walkLength target) := by
  have hs := Nat.card_congr
    (survivingFirstHitFamilyPartitionEquiv R start level walkLength target)
  have hm := Nat.card_congr
    (survivingMirrorFamilyPartitionEquiv R start level walkLength target)
  rw [Nat.card_sum] at hs hm
  have hmatch := natCard_survivalMatchedFirstHitFamily_eq
    R start level walkLength target
  unfold Nat.dist
  omega



theorem survivalExceptional_reflected_exists_hit_right
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R)
    (w : SurvivalExceptionalFirstHitFamily R start level walkLength target) :
    ∃ k, k < w.1.1.1.before.length ∧
      (isingDiagonalWalkEndpoint (reflectedEndpoint level start)
        (w.1.1.1.reflectPrefix.steps.take k)).1 = R := by
  let split := w.1.1.1
  have hfirst := w.1.1.2.1
  have hvalid := w.1.1.2.2.1
  have hsurvive := w.1.2
  have hexception := w.2
  rcases survivalException_before_firstHit split hsurvive hexception with
    ⟨k, hkbefore, hklength, hout⟩
  have hsourceSide :
      (isingDiagonalWalkEndpoint start (split.before.take k)).1 < level :=
    hfirst.endpoint_take_fst_lt split hvalid (by omega) k hkbefore
  have hsourceAtK := hsurvive k (by
    rw [← reflectPrefix_length split]
    exact hklength)
  have hrefx := reflectPrefix_endpoint_take_fst_of_le_before
    split k hkbefore.le
  have hrefy := reflectPrefix_endpoint_take_snd_of_le_before
    split k hkbefore.le
  have hsourceSteps : split.steps.take k = split.before.take k := by
    unfold steps
    exact List.take_append_of_le_length hkbefore.le
  rw [hsourceSteps] at hsourceAtK hrefx hrefy
  have hrefRight : (R : Int) ≤
      (isingDiagonalWalkEndpoint (reflectedEndpoint level start)
        (split.reflectPrefix.steps.take k)).1 := by
    unfold InOpenBox at hsourceAtK hout
    rcases hsourceAtK with ⟨hsx0, hsxR, hsy0, hsyR⟩
    have hrefPositive : 0 <
        (isingDiagonalWalkEndpoint (reflectedEndpoint level start)
          (split.reflectPrefix.steps.take k)).1 := by
      rw [hrefx]
      omega
    have hrefY :
        0 < (isingDiagonalWalkEndpoint (reflectedEndpoint level start)
              (split.reflectPrefix.steps.take k)).2 ∧
          (isingDiagonalWalkEndpoint (reflectedEndpoint level start)
              (split.reflectPrefix.steps.take k)).2 < R := by
      rw [hrefy]
      exact ⟨hsy0, hsyR⟩
    omega
  have hrefValid := reflectPrefix_valid split hvalid
  have htakeValid : IsingDiagonalWalkStepsValid
      (split.reflectPrefix.steps.take k) := by
    intro d hd
    exact hrefValid d (List.mem_of_mem_take hd)
  have hrefStart : (reflectedEndpoint level start).1 < R := by
    unfold reflectedEndpoint
    dsimp
    omega
  rcases exists_prefix_fst_eq_of_lt_of_le
      (split.reflectPrefix.steps.take k) (reflectedEndpoint level start) R
      htakeValid hrefStart hrefRight with ⟨j, hj, heq⟩
  refine ⟨j, ?_, ?_⟩
  · have hjk : j ≤ k := by
      rw [List.length_take] at hj
      omega
    change j < split.before.length
    omega
  · have hjk : j ≤ k := by
      rw [List.length_take] at hj
      omega
    simpa [List.take_take, Nat.min_eq_left hjk] using heq



theorem survivalExceptionalMirror_reflected_exists_hit_left
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (w : SurvivalExceptionalMirrorFamily R start level walkLength target) :
    ∃ k, k < w.1.1.1.before.length ∧
      (isingDiagonalWalkEndpoint start
        (w.1.1.1.reflectPrefix.steps.take k)).1 = 0 := by
  let split := w.1.1.1
  have hfirst := w.1.1.2.1
  have hvalid := w.1.1.2.2.1
  have hsurvive := w.1.2
  have hexception :
      ¬ StaysInOpenBox R start split.reflectPrefix.steps := by
    simpa [SurvivalExceptionalMirrorFamily, reflectPrefix, steps] using w.2
  have hexception' :
      ¬ StaysInOpenBox R (reflectedEndpoint level
        (reflectedEndpoint level start)) split.reflectPrefix.steps := by
    simpa using hexception
  rcases survivalException_before_firstHit split hsurvive hexception' with
    ⟨k, hkbefore, hklength, hout⟩
  have hmirrorStart : level < (reflectedEndpoint level start).1 := by
    unfold reflectedEndpoint
    dsimp
    omega
  have hsourceSide : level <
      (isingDiagonalWalkEndpoint (reflectedEndpoint level start)
        (split.before.take k)).1 :=
    hfirst.endpoint_take_fst_gt split hvalid hmirrorStart k hkbefore
  have hsourceAtK := hsurvive k (by
    rw [← reflectPrefix_length split]
    exact hklength)
  have hrefx := reflectPrefix_endpoint_take_fst_of_le_before
    split k hkbefore.le
  have hrefy := reflectPrefix_endpoint_take_snd_of_le_before
    split k hkbefore.le
  have hsourceSteps : split.steps.take k = split.before.take k := by
    unfold steps
    exact List.take_append_of_le_length hkbefore.le
  rw [hsourceSteps] at hsourceAtK hrefx hrefy
  have hrefLeftCanonical :
      (isingDiagonalWalkEndpoint (reflectedEndpoint level
          (reflectedEndpoint level start))
        (split.reflectPrefix.steps.take k)).1 ≤ 0 := by
    unfold InOpenBox at hsourceAtK hout
    rcases hsourceAtK with ⟨hsx0, hsxR, hsy0, hsyR⟩
    have hrefBelowR :
        (isingDiagonalWalkEndpoint (reflectedEndpoint level
          (reflectedEndpoint level start))
          (split.reflectPrefix.steps.take k)).1 < R := by
      rw [hrefx]
      omega
    have hrefY :
        0 < (isingDiagonalWalkEndpoint (reflectedEndpoint level
              (reflectedEndpoint level start))
              (split.reflectPrefix.steps.take k)).2 ∧
          (isingDiagonalWalkEndpoint (reflectedEndpoint level
              (reflectedEndpoint level start))
              (split.reflectPrefix.steps.take k)).2 < R := by
      rw [hrefy]
      exact ⟨hsy0, hsyR⟩
    omega
  have hrefLeft :
      (isingDiagonalWalkEndpoint start
        (split.reflectPrefix.steps.take k)).1 ≤ 0 := by
    simpa using hrefLeftCanonical
  have hrefValid := reflectPrefix_valid split hvalid
  have htakeValid : IsingDiagonalWalkStepsValid
      (split.reflectPrefix.steps.take k) := by
    intro d hd
    exact hrefValid d (List.mem_of_mem_take hd)
  by_cases hstartZero : start.1 = 0
  · refine ⟨0, ?_, ?_⟩
    · change 0 < split.before.length
      exact lt_of_le_of_lt (Nat.zero_le k) hkbefore
    simp [isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement,
      hstartZero]
  · have hrefStart : 0 < start.1 := by omega
    rcases exists_prefix_fst_eq_of_ge_of_gt
        (split.reflectPrefix.steps.take k) start 0 htakeValid hrefStart
        hrefLeft with ⟨j, hj, heq⟩
    refine ⟨j, ?_, ?_⟩
    · have hjk : j ≤ k := by
        rw [List.length_take] at hj
        omega
      change j < split.before.length
      omega
    · have hjk : j ≤ k := by
        rw [List.length_take] at hj
        omega
      simpa [List.take_take, Nat.min_eq_left hjk] using heq

private def rightGapNeighbor (R level : Nat)
    (hgap : level + 1 < R) : IsingLineBox (R - level) :=
  ⟨R - level - 1, by omega⟩

private def rightGapLeft (R level : Nat) : IsingLineBox (R - level) :=
  ⟨0, by omega⟩

private theorem survivalExceptional_horizontal_run_left
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R)
    (w : SurvivalExceptionalFirstHitFamily R start (level : Int)
      walkLength target) :
    isingLineChoiceRun (R - level) (rightGapNeighbor R level hgap)
        (horizontalRightCode w.1.1.1.reflectPrefix.steps) =
      rightGapLeft R level := by
  let split := w.1.1.1
  let path := split.reflectPrefix.steps
  let n := R - level
  have hrefValid : IsingDiagonalWalkStepsValid path :=
    reflectPrefix_valid split w.1.1.2.2.1
  rcases survivalExceptional_reflected_exists_hit_right R start (level : Int)
      walkLength target hstart (by exact_mod_cast hlevel)
      (by exact_mod_cast hgap) w with ⟨k, hkbefore, hhit⟩
  change k < split.before.length at hkbefore
  change (isingDiagonalWalkEndpoint (reflectedEndpoint (level : Int) start)
    (path.take k)).1 = R at hhit
  have hkpath : k ≤ path.length := by
    dsimp [path]
    rw [reflectPrefix_length]
    unfold steps
    simp only [List.length_append]
    exact le_trans hkbefore.le (Nat.le_add_right _ _)
  have hfreeHit :
      lineFreeEndpoint ((R - level - 1 : Nat) : Int)
          ((horizontalRightCode path).take k) = 0 := by
    have htakeValid : IsingDiagonalWalkStepsValid (path.take k) := by
      intro d hd
      exact hrefValid d (List.mem_of_mem_take hd)
    have hline := lineFreeEndpoint_horizontalRightCode
      (path.take k) (reflectedEndpoint (level : Int) start) (R : Int)
      htakeValid
    have hinitial :
        ((R - level - 1 : Nat) : Int) =
          (R : Int) - (reflectedEndpoint (level : Int) start).1 := by
      unfold reflectedEndpoint
      dsimp
      push_cast
      omega
    have hline' : lineFreeEndpoint ((R : Int) -
        (reflectedEndpoint (level : Int) start).1)
        ((horizontalRightCode path).take k) =
          (R : Int) - (isingDiagonalWalkEndpoint
            (reflectedEndpoint (level : Int) start) (path.take k)).1 := by
      simpa only [horizontalRightCode, List.map_take] using hline
    rw [← hinitial, hhit] at hline'
    simpa using hline'
  have hnoRight : ∀ j, j < k →
      lineFreeEndpoint ((R - level - 1 : Nat) : Int)
        ((horizontalRightCode path).take j) ≠ (R - level : Nat) := by
    intro j hj hright
    have hjbefore : j < split.before.length := by omega
    have htakeValid : IsingDiagonalWalkStepsValid (path.take j) := by
      intro d hd
      exact hrefValid d (List.mem_of_mem_take hd)
    have hline := lineFreeEndpoint_horizontalRightCode
      (path.take j) (reflectedEndpoint (level : Int) start) (R : Int)
      htakeValid
    have hinitial :
        ((R - level - 1 : Nat) : Int) =
          (R : Int) - (reflectedEndpoint (level : Int) start).1 := by
      unfold reflectedEndpoint
      dsimp
      push_cast
      omega
    have hline' : lineFreeEndpoint ((R : Int) -
        (reflectedEndpoint (level : Int) start).1)
        ((horizontalRightCode path).take j) =
          (R : Int) - (isingDiagonalWalkEndpoint
            (reflectedEndpoint (level : Int) start) (path.take j)).1 := by
      simpa only [horizontalRightCode, List.map_take] using hline
    rw [← hinitial] at hline'
    have hendpoint :
        (isingDiagonalWalkEndpoint (reflectedEndpoint (level : Int) start)
          (path.take j)).1 = level := by
      push_cast at hright
      omega
    have hfirst := reflectPrefix_firstHit split w.1.1.2.1 j (by simpa)
    apply hfirst
    dsimp [path] at hendpoint
    unfold steps at hendpoint
    have hjref : j ≤ split.reflectPrefix.before.length := by
      simpa [reflectPrefix] using hjbefore.le
    rw [List.take_append_of_le_length hjref] at hendpoint
    exact hendpoint
  have hstartNonneg : 0 ≤ ((R - level - 1 : Nat) : Int) := by omega
  have hstartLt : ((R - level - 1 : Nat) : Int) < (R - level : Nat) := by
    push_cast
    omega
  have hrun := intLineChoiceRun_eq_zero_of_free_hit (R - level)
    ((R - level - 1 : Nat) : Int) (horizontalRightCode path) k
    hstartNonneg hstartLt (by simpa [horizontalRightCode] using hkpath)
    hfreeHit hnoRight
  have hagree := intLineChoiceRun_eq_lineChoiceRun_val (R - level)
    (rightGapNeighbor R level hgap) (horizontalRightCode path)
  apply Fin.ext
  have hvalInt : ((isingLineChoiceRun (R - level)
      (rightGapNeighbor R level hgap) (horizontalRightCode path)).1 : Int) =
      0 := by
    rw [← hagree]
    simpa [rightGapNeighbor] using hrun
  change (isingLineChoiceRun (R - level) (rightGapNeighbor R level hgap)
    (horizontalRightCode path)).1 = 0
  exact_mod_cast hvalInt

private theorem horizontalRightCode_verticalCode_injective_of_valid
    {a b : List (Int × Int)}
    (ha : IsingDiagonalWalkStepsValid a)
    (hb : IsingDiagonalWalkStepsValid b)
    (hh : horizontalRightCode a = horizontalRightCode b)
    (hv : verticalCode a = verticalCode b) : a = b := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => rfl
      | cons e b => simp [horizontalRightCode] at hh
  | cons d a ih =>
      cases b with
      | nil => simp [horizontalRightCode] at hh
      | cons e b =>
          simp only [horizontalRightCode, verticalCode, List.map_cons,
            List.cons.injEq] at hh hv
          have hd := ha d (by simp)
          have he := hb e (by simp)
          have hde : d = e := by
            rcases hd with ⟨hdx | hdx, hdy | hdy⟩ <;>
              rcases he with ⟨hex | hex, hey | hey⟩ <;>
              simp [hdx, hdy, hex, hey] at hh hv
            all_goals apply Prod.ext <;> simp_all
          subst e
          congr 1
          apply ih
          · intro z hz
            exact ha z (by simp [hz])
          · intro z hz
            exact hb z (by simp [hz])
          · exact hh.2
          · exact hv.2

private theorem reflectPrefix_verticalCode_endpoint
    {start : Int × Int} {level : Int} {walkLength : Nat}
    {target : Int × Int}
    (w : FirstHitFamily start level walkLength target) :
    lineFreeEndpoint start.2 (verticalCode w.1.reflectPrefix.steps) =
      target.2 := by
  have hvalid := reflectPrefix_valid w.1 w.2.2.1
  have hline := lineFreeEndpoint_verticalCode w.1.reflectPrefix.steps
    (reflectedEndpoint level start) hvalid
  calc
    lineFreeEndpoint start.2 (verticalCode w.1.reflectPrefix.steps) =
        (isingDiagonalWalkEndpoint (reflectedEndpoint level start)
          w.1.reflectPrefix.steps).2 := hline
    _ = w.1.reflectPrefix.endpoint.2 := rfl
    _ = w.1.endpoint.2 := congrArg Prod.snd (reflectPrefix_endpoint w.1)
    _ = target.2 := congrArg Prod.snd w.2.2.2.2

def survivalExceptionalProjection
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R) :
    SurvivalExceptionalFirstHitFamily R start (level : Int)
        walkLength target →
      IsingLineChoicePathFamily (R - level) walkLength
          (rightGapNeighbor R level hgap) (rightGapLeft R level) ×
        {v : List Bool // v.length = walkLength} := fun w =>
  let path := w.1.1.1.reflectPrefix.steps
  ⟨⟨horizontalRightCode path, by
      simpa [horizontalRightCode, path, reflectPrefix_length] using
        w.1.1.2.2.2.1,
      survivalExceptional_horizontal_run_left R level walkLength start target
        hstart hlevel hgap w⟩,
    ⟨verticalCode path, by
      simpa [verticalCode, path, reflectPrefix_length] using
        w.1.1.2.2.2.1⟩⟩



theorem survivalExceptionalFirstHitFamily_projection_injective
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R) :
    Function.Injective
      (survivalExceptionalProjection R level walkLength start target
        hstart hlevel hgap) := by
  intro a b hab
  have hh : horizontalRightCode a.1.1.1.reflectPrefix.steps =
      horizontalRightCode b.1.1.1.reflectPrefix.steps := by
    exact congrArg (fun z => z.1.1) hab
  have hv : verticalCode a.1.1.1.reflectPrefix.steps =
      verticalCode b.1.1.1.reflectPrefix.steps := by
    exact congrArg (fun z => z.2.1) hab
  have hsteps : a.1.1.1.reflectPrefix.steps =
      b.1.1.1.reflectPrefix.steps :=
    horizontalRightCode_verticalCode_injective_of_valid
      (reflectPrefix_valid a.1.1.1 a.1.1.2.2.1)
      (reflectPrefix_valid b.1.1.1 b.1.1.2.2.1) hh hv
  have haSome := firstHitSplit_eq_some a.1.1.1.reflectPrefix
    (reflectPrefix_firstHit a.1.1.1 a.1.1.2.1)
  have hbSome := firstHitSplit_eq_some b.1.1.1.reflectPrefix
    (reflectPrefix_firstHit b.1.1.1 b.1.1.2.1)
  have hsplits : a.1.1.1.reflectPrefix = b.1.1.1.reflectPrefix := by
    apply Option.some.inj
    rw [← haSome, ← hbSome, hsteps]
  have hfamilies :
      (reflectPrefixFirstHitFamilyEquiv start (level : Int) walkLength target)
          a.1.1 =
        (reflectPrefixFirstHitFamilyEquiv start (level : Int) walkLength target)
          b.1.1 := by
    apply Subtype.ext
    exact hsplits
  have habFamily : a.1.1 = b.1.1 :=
    (reflectPrefixFirstHitFamilyEquiv start (level : Int) walkLength target).injective
      hfamilies
  apply Subtype.ext
  apply Subtype.ext
  exact habFamily


def SurvivalExceptionalFirstHitFamilyAll
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat) :=
  Σ target : Int × Int,
    SurvivalExceptionalFirstHitFamily R start level walkLength target

def survivalExceptionalProjectionAll
    (R level walkLength : Nat) (start : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R) :
    SurvivalExceptionalFirstHitFamilyAll R start (level : Int) walkLength →
      IsingLineChoicePathFamily (R - level) walkLength
          (rightGapNeighbor R level hgap) (rightGapLeft R level) ×
        {v : List Bool // v.length = walkLength} := fun w =>
  survivalExceptionalProjection R level walkLength start w.1
    hstart hlevel hgap w.2

theorem survivalExceptionalProjectionAll_injective
    (R level walkLength : Nat) (start : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R) :
    Function.Injective
      (survivalExceptionalProjectionAll R level walkLength start
        hstart hlevel hgap) := by
  intro a b hab
  have hh : horizontalRightCode a.2.1.1.1.reflectPrefix.steps =
      horizontalRightCode b.2.1.1.1.reflectPrefix.steps :=
    congrArg (fun z => z.1.1) hab
  have hv : verticalCode a.2.1.1.1.reflectPrefix.steps =
      verticalCode b.2.1.1.1.reflectPrefix.steps :=
    congrArg (fun z => z.2.1) hab
  have hsteps : a.2.1.1.1.reflectPrefix.steps =
      b.2.1.1.1.reflectPrefix.steps :=
    horizontalRightCode_verticalCode_injective_of_valid
      (reflectPrefix_valid a.2.1.1.1 a.2.1.1.2.2.1)
      (reflectPrefix_valid b.2.1.1.1 b.2.1.1.2.2.1) hh hv
  have haSome := firstHitSplit_eq_some a.2.1.1.1.reflectPrefix
    (reflectPrefix_firstHit a.2.1.1.1 a.2.1.1.2.1)
  have hbSome := firstHitSplit_eq_some b.2.1.1.1.reflectPrefix
    (reflectPrefix_firstHit b.2.1.1.1 b.2.1.1.2.1)
  have hsplits : a.2.1.1.1.reflectPrefix =
      b.2.1.1.1.reflectPrefix := by
    apply Option.some.inj
    rw [← haSome, ← hbSome, hsteps]
  have horiginal : a.2.1.1.1 = b.2.1.1.1 := by
    cases ha : a.2.1.1.1 with
    | mk ab aa ahit =>
      cases hb : b.2.1.1.1 with
      | mk bb ba bhit =>
        have hreflect : Function.Injective reflectIncrement := by
          intro x y hxy
          apply Prod.ext
          · have hx := congrArg Prod.fst hxy
            simp [reflectIncrement] at hx
            linarith
          · simpa [reflectIncrement] using congrArg Prod.snd hxy
        have hbeforeMap := congrArg
          (fun w : IsingDiagonalWalkHitSplit
            (reflectedEndpoint (level : Int) start) (level : Int) => w.before)
          hsplits
        simp only [ha, hb, reflectPrefix_before] at hbeforeMap
        have hbefore : ab = bb :=
          (Function.Injective.list_map hreflect) hbeforeMap
        have hafterRaw := congrArg
          (fun w : IsingDiagonalWalkHitSplit
            (reflectedEndpoint (level : Int) start) (level : Int) => w.after)
          hsplits
        simp only [ha, hb, reflectPrefix_after] at hafterRaw
        have hafter : aa = ba := hafterRaw
        subst bb
        subst ba
        rfl
  have htarget : a.1 = b.1 := by
    have haend := a.2.1.1.2.2.2.2
    have hbend := b.2.1.1.2.2.2.2
    rw [← haend, ← hbend, horiginal]
  cases a with
  | mk atarget aw =>
    cases b with
    | mk btarget bw =>
      dsimp at htarget horiginal
      subst btarget
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        exact horiginal

noncomputable instance survivalExceptionalFirstHitFamilyAll_finite
    (R walkLength : Nat) (start : Int × Int) (level : Int) :
    Finite (SurvivalExceptionalFirstHitFamilyAll R start level
      walkLength) := by
  letI : Fintype
      {bits : List (Bool × Bool) // bits.length = walkLength} :=
    (List.finite_length_eq (Bool × Bool) walkLength).fintype
  exact Finite.of_injective
    (fun w : SurvivalExceptionalFirstHitFamilyAll R start level
      walkLength => firstHitFamilyCode w.2.1.1)
    (by
      intro a b h
      have hsteps := encodePath_injective_of_valid
        a.2.1.1.2.2.1 b.2.1.1.2.2.1 (congrArg Subtype.val h)
      have haSome := firstHitSplit_eq_some a.2.1.1.1 a.2.1.1.2.1
      have hbSome := firstHitSplit_eq_some b.2.1.1.1 b.2.1.1.2.1
      have horiginal : a.2.1.1.1 = b.2.1.1.1 := by
        apply Option.some.inj
        rw [← haSome, ← hbSome, hsteps]
      have htarget : a.1 = b.1 := by
        have haend := a.2.1.1.2.2.2.2
        have hbend := b.2.1.1.2.2.2.2
        rw [← haend, ← hbend, horiginal]
      cases a with
      | mk atarget aw =>
        cases b with
        | mk btarget bw =>
          dsimp at htarget horiginal
          subst btarget
          apply Sigma.ext
          · rfl
          · apply heq_of_eq
            apply Subtype.ext
            apply Subtype.ext
            apply Subtype.ext
            exact horiginal)

private def survivalExceptionalPointwiseProjection
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R) :
    SurvivalExceptionalFirstHitFamily R start (level : Int)
        walkLength target →
      IsingLineChoicePathFamily (R - level) walkLength
          (rightGapNeighbor R level hgap) (rightGapLeft R level) ×
        VerticalChoicePathFamily walkLength start.2 target.2 := fun w =>
  let path := w.1.1.1.reflectPrefix.steps
  ⟨⟨horizontalRightCode path, by
      simpa [horizontalRightCode, path, reflectPrefix_length] using
        w.1.1.2.2.2.1,
      survivalExceptional_horizontal_run_left R level walkLength start target
        hstart hlevel hgap w⟩,
    ⟨verticalCode path, by
      simpa [verticalCode, path, reflectPrefix_length] using
        w.1.1.2.2.2.1,
      reflectPrefix_verticalCode_endpoint w.1.1⟩⟩

private theorem survivalExceptionalPointwiseProjection_injective
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R) :
    Function.Injective
      (survivalExceptionalPointwiseProjection R level walkLength start target
        hstart hlevel hgap) := by
  intro a b hab
  apply survivalExceptionalFirstHitFamily_projection_injective R level
    walkLength start target hstart hlevel hgap
  apply Prod.ext
  · simpa [survivalExceptionalPointwiseProjection,
        survivalExceptionalProjection] using
      congrArg (fun z => z.1) hab
  · apply Subtype.ext
    simpa [survivalExceptionalPointwiseProjection,
        survivalExceptionalProjection] using
      congrArg (fun z => z.2.1) hab

private theorem
    natCard_survivalExceptionalFirstHitFamily_le_line_mul_vertical
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R) :
    Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
        walkLength target) ≤
      Nat.card (IsingLineChoicePathFamily (R - level) walkLength
        (rightGapNeighbor R level hgap) (rightGapLeft R level)) *
      Nat.card (VerticalChoicePathFamily walkLength start.2 target.2) := by
  calc
    Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
        walkLength target) ≤
        Nat.card (IsingLineChoicePathFamily (R - level) walkLength
            (rightGapNeighbor R level hgap) (rightGapLeft R level) ×
          VerticalChoicePathFamily walkLength start.2 target.2) :=
      Nat.card_le_card_of_injective
        (survivalExceptionalPointwiseProjection R level walkLength start target
          hstart hlevel hgap)
        (survivalExceptionalPointwiseProjection_injective R level walkLength
          start target hstart hlevel hgap)
    _ = _ := by rw [Nat.card_prod]

private noncomputable instance boolListLength_finite (t : Nat) :
    Finite {v : List Bool // v.length = t} :=
  List.finite_length_eq Bool t

private theorem natCard_boolListLength (t : Nat) :
    Nat.card {v : List Bool // v.length = t} = 2 ^ t := by
  change Nat.card (List.Vector Bool t) = 2 ^ t
  rw [Nat.card_congr (Equiv.vectorEquivFin Bool t)]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun]
  simp



theorem natCard_survivalExceptionalFirstHitFamily_le_line_mul_pow
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R) :
    Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
        walkLength target) ≤
      Nat.card (IsingLineChoicePathFamily (R - level) walkLength
        (rightGapNeighbor R level hgap) (rightGapLeft R level)) *
          2 ^ walkLength := by
  calc
    Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
        walkLength target) ≤
        Nat.card (IsingLineChoicePathFamily (R - level) walkLength
            (rightGapNeighbor R level hgap) (rightGapLeft R level) ×
          {v : List Bool // v.length = walkLength}) :=
      Nat.card_le_card_of_injective
        (survivalExceptionalProjection R level walkLength start target
          hstart hlevel hgap)
        (survivalExceptionalFirstHitFamily_projection_injective R level
          walkLength start target hstart hlevel hgap)
    _ = Nat.card (IsingLineChoicePathFamily (R - level) walkLength
          (rightGapNeighbor R level hgap) (rightGapLeft R level)) *
        Nat.card {v : List Bool // v.length = walkLength} := by
      rw [Nat.card_prod]
    _ = _ := by rw [natCard_boolListLength]




theorem survivalExceptionalFirstHitFamily_weight_le_inv_rightGap
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R) :
    (Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
        walkLength target) : Real) / 4 ^ walkLength ≤
      1 / ((R - level : Nat) : Real) := by
  let p := rightGapNeighbor R level hgap
  let q := rightGapLeft R level
  have hcountNat :=
    natCard_survivalExceptionalFirstHitFamily_le_line_mul_pow R level
      walkLength start target hstart hlevel hgap
  have hcountReal :
      (Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
          walkLength target) : Real) ≤
        (Nat.card (IsingLineChoicePathFamily (R - level) walkLength p q) :
          Real) * (2 : Real) ^ walkLength := by
    dsimp [p, q]
    exact_mod_cast hcountNat
  have hgapPos : 0 < R - level := by omega
  have hline :
      (Nat.card (IsingLineChoicePathFamily (R - level) walkLength p q) :
          Real) / (2 : Real) ^ walkLength ≤
        1 / ((R - level : Nat) : Real) := by
    rw [← isingLineStoppedKernel_eq_natCard_choicePath_div]
    dsimp [p, q]
    simpa [rightGapNeighbor, rightGapLeft] using
      (isingLineStoppedKernel_left_of_rightNeighbor
        (R - level) walkLength hgapPos)
  calc
    (Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
        walkLength target) : Real) / 4 ^ walkLength ≤
        ((Nat.card (IsingLineChoicePathFamily (R - level) walkLength p q) :
          Real) * (2 : Real) ^ walkLength) / 4 ^ walkLength :=
      div_le_div_of_nonneg_right hcountReal (by positivity)
    _ = (Nat.card (IsingLineChoicePathFamily (R - level) walkLength p q) :
          Real) / (2 : Real) ^ walkLength := by
      rw [show (4 : Real) ^ walkLength =
          (2 : Real) ^ walkLength * (2 : Real) ^ walkLength by
        rw [← mul_pow]
        norm_num]
      field_simp
    _ ≤ 1 / ((R - level : Nat) : Real) := hline



theorem survivalExceptionalFirstHitFamilyAll_weight_le_inv_rightGap
    (R level walkLength : Nat) (start : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R) :
    (Nat.card (SurvivalExceptionalFirstHitFamilyAll R start (level : Int)
        walkLength) : Real) / 4 ^ walkLength ≤
      1 / ((R - level : Nat) : Real) := by
  let p := rightGapNeighbor R level hgap
  let q := rightGapLeft R level
  have hcountNat :
      Nat.card (SurvivalExceptionalFirstHitFamilyAll R start (level : Int)
        walkLength) ≤
        Nat.card (IsingLineChoicePathFamily (R - level) walkLength p q) *
          2 ^ walkLength := by
    calc
      _ ≤ Nat.card (IsingLineChoicePathFamily (R - level) walkLength p q ×
          {v : List Bool // v.length = walkLength}) :=
        Nat.card_le_card_of_injective
          (survivalExceptionalProjectionAll R level walkLength start
            hstart hlevel hgap)
          (survivalExceptionalProjectionAll_injective R level walkLength start
            hstart hlevel hgap)
      _ = Nat.card (IsingLineChoicePathFamily (R - level) walkLength p q) *
          Nat.card {v : List Bool // v.length = walkLength} := by
        rw [Nat.card_prod]
      _ = _ := by rw [natCard_boolListLength]
  have hcountReal :
      (Nat.card (SurvivalExceptionalFirstHitFamilyAll R start (level : Int)
          walkLength) : Real) ≤
        (Nat.card (IsingLineChoicePathFamily (R - level) walkLength p q) :
          Real) * (2 : Real) ^ walkLength := by
    exact_mod_cast hcountNat
  have hline :
      (Nat.card (IsingLineChoicePathFamily (R - level) walkLength p q) :
          Real) / (2 : Real) ^ walkLength ≤
        1 / ((R - level : Nat) : Real) := by
    rw [← isingLineStoppedKernel_eq_natCard_choicePath_div]
    dsimp [p, q]
    simpa [rightGapNeighbor, rightGapLeft] using
      (isingLineStoppedKernel_left_of_rightNeighbor (R - level) walkLength
        (show 0 < R - level by omega))
  calc
    _ ≤ ((Nat.card (IsingLineChoicePathFamily (R - level) walkLength p q) :
          Real) * (2 : Real) ^ walkLength) / 4 ^ walkLength :=
      div_le_div_of_nonneg_right hcountReal (by positivity)
    _ = (Nat.card (IsingLineChoicePathFamily (R - level) walkLength p q) :
          Real) / (2 : Real) ^ walkLength := by
      rw [show (4 : Real) ^ walkLength =
          (2 : Real) ^ walkLength * (2 : Real) ^ walkLength by
        rw [← mul_pow]
        norm_num]
      field_simp
    _ ≤ 1 / ((R - level : Nat) : Real) := hline



theorem survivalExceptionalFirstHitFamily_weight_le_inv_rightGap_mul_binomial
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R) :
    (Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
        walkLength target) : Real) / 4 ^ walkLength ≤
      (1 / ((R - level : Nat) : Real)) *
        isingLineBinomialKernel walkLength start.2 target.2 := by
  let p := rightGapNeighbor R level hgap
  let q := rightGapLeft R level
  let H := IsingLineChoicePathFamily (R - level) walkLength p q
  let V := VerticalChoicePathFamily walkLength start.2 target.2
  have hcountNat :=
    natCard_survivalExceptionalFirstHitFamily_le_line_mul_vertical R level
      walkLength start target hstart hlevel hgap
  have hcountReal :
      (Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
          walkLength target) : Real) ≤
        (Nat.card H : Real) * (Nat.card V : Real) := by
    dsimp [H, V, p, q]
    exact_mod_cast hcountNat
  have hgapPos : 0 < R - level := by omega
  have hline : (Nat.card H : Real) / (2 : Real) ^ walkLength ≤
      1 / ((R - level : Nat) : Real) := by
    dsimp [H]
    rw [← isingLineStoppedKernel_eq_natCard_choicePath_div]
    dsimp [p, q]
    simpa [rightGapNeighbor, rightGapLeft] using
      (isingLineStoppedKernel_left_of_rightNeighbor
        (R - level) walkLength hgapPos)
  have hvertical : (Nat.card V : Real) / (2 : Real) ^ walkLength =
      isingLineBinomialKernel walkLength start.2 target.2 := by
    dsimp [V]
    symm
    exact isingLineBinomialKernel_eq_natCard_verticalChoicePath_div
      walkLength start.2 target.2
  calc
    (Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
        walkLength target) : Real) / 4 ^ walkLength ≤
        ((Nat.card H : Real) * (Nat.card V : Real)) / 4 ^ walkLength :=
      div_le_div_of_nonneg_right hcountReal (by positivity)
    _ = ((Nat.card H : Real) / (2 : Real) ^ walkLength) *
        ((Nat.card V : Real) / (2 : Real) ^ walkLength) := by
      rw [show (4 : Real) ^ walkLength =
          (2 : Real) ^ walkLength * (2 : Real) ^ walkLength by
        rw [← mul_pow]
        norm_num]
      field_simp
    _ = ((Nat.card H : Real) / (2 : Real) ^ walkLength) *
        isingLineBinomialKernel walkLength start.2 target.2 := by
      rw [hvertical]
    _ ≤ (1 / ((R - level : Nat) : Real)) *
        isingLineBinomialKernel walkLength start.2 target.2 :=
      mul_le_mul_of_nonneg_right hline
        (isingLineBinomialKernel_nonneg walkLength start.2 target.2)

private def leftGapNeighbor (level : Nat)
    (hlevel : 0 < level) : IsingLineBox level :=
  ⟨level - 1, by omega⟩

private def leftGapLeft (level : Nat) : IsingLineBox level :=
  ⟨0, by omega⟩

private theorem survivalExceptionalMirror_horizontal_run_left
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (w : SurvivalExceptionalMirrorFamily R start (level : Int)
      walkLength target) :
    isingLineChoiceRun level (leftGapNeighbor level hlevel)
        (horizontalLeftCode w.1.1.1.reflectPrefix.steps) =
      leftGapLeft level := by
  let split := w.1.1.1
  let path := split.reflectPrefix.steps
  have hrefValid : IsingDiagonalWalkStepsValid path :=
    reflectPrefix_valid split w.1.1.2.2.1
  rcases survivalExceptionalMirror_reflected_exists_hit_left R start
      (level : Int) walkLength target hstart (by exact_mod_cast hlevel) w with
    ⟨k, hkbefore, hhit⟩
  change k < split.before.length at hkbefore
  change (isingDiagonalWalkEndpoint start (path.take k)).1 = 0 at hhit
  have hkpath : k ≤ path.length := by
    dsimp [path]
    rw [reflectPrefix_length]
    unfold steps
    simp only [List.length_append]
    exact le_trans hkbefore.le (Nat.le_add_right _ _)
  have hfreeHit :
      lineFreeEndpoint ((level - 1 : Nat) : Int)
          ((horizontalLeftCode path).take k) = 0 := by
    have htakeValid : IsingDiagonalWalkStepsValid (path.take k) := by
      intro d hd
      exact hrefValid d (List.mem_of_mem_take hd)
    have hline := lineFreeEndpoint_horizontalLeftCode (path.take k) start
      htakeValid
    have hinitial : ((level - 1 : Nat) : Int) = start.1 := by
      push_cast
      omega
    have hline' : lineFreeEndpoint start.1
        ((horizontalLeftCode path).take k) =
          (isingDiagonalWalkEndpoint start (path.take k)).1 := by
      simpa only [horizontalLeftCode, List.map_take] using hline
    rw [← hinitial, hhit] at hline'
    exact hline'
  have hnoRight : ∀ j, j < k →
      lineFreeEndpoint ((level - 1 : Nat) : Int)
        ((horizontalLeftCode path).take j) ≠ (level : Nat) := by
    intro j hj hright
    have hjbefore : j < split.before.length := by omega
    have htakeValid : IsingDiagonalWalkStepsValid (path.take j) := by
      intro d hd
      exact hrefValid d (List.mem_of_mem_take hd)
    have hline := lineFreeEndpoint_horizontalLeftCode (path.take j) start
      htakeValid
    have hinitial : ((level - 1 : Nat) : Int) = start.1 := by
      push_cast
      omega
    have hline' : lineFreeEndpoint start.1
        ((horizontalLeftCode path).take j) =
          (isingDiagonalWalkEndpoint start (path.take j)).1 := by
      simpa only [horizontalLeftCode, List.map_take] using hline
    rw [← hinitial] at hline'
    have hendpoint :
        (isingDiagonalWalkEndpoint start (path.take j)).1 = level := by
      exact_mod_cast hline'.symm.trans hright
    have hfirst := reflectPrefix_firstHit split w.1.1.2.1 j (by simpa)
    apply hfirst
    have hstartEq : reflectedEndpoint (level : Int)
        (reflectedEndpoint (level : Int) start) = start :=
      reflectedEndpoint_reflectedEndpoint (level : Int) start
    have hendpoint' :
        (isingDiagonalWalkEndpoint
          (reflectedEndpoint (level : Int)
            (reflectedEndpoint (level : Int) start)) (path.take j)).1 =
          level := by simpa using hendpoint
    dsimp [path] at hendpoint'
    unfold steps at hendpoint'
    have hjref : j ≤ split.reflectPrefix.before.length := by
      simpa [reflectPrefix] using hjbefore.le
    rw [List.take_append_of_le_length hjref] at hendpoint'
    exact hendpoint'
  have hstartNonneg : 0 ≤ ((level - 1 : Nat) : Int) := by omega
  have hstartLt : ((level - 1 : Nat) : Int) < (level : Nat) := by
    push_cast
    omega
  have hrun := intLineChoiceRun_eq_zero_of_free_hit level
    ((level - 1 : Nat) : Int) (horizontalLeftCode path) k
    hstartNonneg hstartLt (by simpa [horizontalLeftCode] using hkpath)
    hfreeHit hnoRight
  have hagree := intLineChoiceRun_eq_lineChoiceRun_val level
    (leftGapNeighbor level hlevel) (horizontalLeftCode path)
  apply Fin.ext
  have hvalInt : ((isingLineChoiceRun level
      (leftGapNeighbor level hlevel) (horizontalLeftCode path)).1 : Int) =
      0 := by
    rw [← hagree]
    simpa [leftGapNeighbor] using hrun
  change (isingLineChoiceRun level (leftGapNeighbor level hlevel)
    (horizontalLeftCode path)).1 = 0
  exact_mod_cast hvalInt

private theorem horizontalLeftCode_verticalCode_injective_of_valid
    {a b : List (Int × Int)}
    (ha : IsingDiagonalWalkStepsValid a)
    (hb : IsingDiagonalWalkStepsValid b)
    (hh : horizontalLeftCode a = horizontalLeftCode b)
    (hv : verticalCode a = verticalCode b) : a = b := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => rfl
      | cons e b => simp [horizontalLeftCode] at hh
  | cons d a ih =>
      cases b with
      | nil => simp [horizontalLeftCode] at hh
      | cons e b =>
          simp only [horizontalLeftCode, verticalCode, List.map_cons,
            List.cons.injEq] at hh hv
          have hd := ha d (by simp)
          have he := hb e (by simp)
          have hde : d = e := by
            rcases hd with ⟨hdx | hdx, hdy | hdy⟩ <;>
              rcases he with ⟨hex | hex, hey | hey⟩ <;>
              simp [hdx, hdy, hex, hey] at hh hv
            all_goals apply Prod.ext <;> simp_all
          subst e
          congr 1
          apply ih
          · intro z hz
            exact ha z (by simp [hz])
          · intro z hz
            exact hb z (by simp [hz])
          · exact hh.2
          · exact hv.2

def survivalExceptionalMirrorProjection
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level) :
    SurvivalExceptionalMirrorFamily R start (level : Int) walkLength target →
      IsingLineChoicePathFamily level walkLength
          (leftGapNeighbor level hlevel) (leftGapLeft level) ×
        {v : List Bool // v.length = walkLength} := fun w =>
  let path := w.1.1.1.reflectPrefix.steps
  ⟨⟨horizontalLeftCode path, by
      simpa [horizontalLeftCode, path, reflectPrefix_length] using
        w.1.1.2.2.2.1,
      survivalExceptionalMirror_horizontal_run_left R level walkLength
        start target hstart hlevel w⟩,
    ⟨verticalCode path, by
      simpa [verticalCode, path, reflectPrefix_length] using
        w.1.1.2.2.2.1⟩⟩

theorem survivalExceptionalMirrorProjection_injective
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level) :
    Function.Injective
      (survivalExceptionalMirrorProjection R level walkLength start target
        hstart hlevel) := by
  intro a b hab
  have hh : horizontalLeftCode a.1.1.1.reflectPrefix.steps =
      horizontalLeftCode b.1.1.1.reflectPrefix.steps :=
    congrArg (fun z => z.1.1) hab
  have hv : verticalCode a.1.1.1.reflectPrefix.steps =
      verticalCode b.1.1.1.reflectPrefix.steps :=
    congrArg (fun z => z.2.1) hab
  have hsteps : a.1.1.1.reflectPrefix.steps =
      b.1.1.1.reflectPrefix.steps :=
    horizontalLeftCode_verticalCode_injective_of_valid
      (reflectPrefix_valid a.1.1.1 a.1.1.2.2.1)
      (reflectPrefix_valid b.1.1.1 b.1.1.2.2.1) hh hv
  have haSome := firstHitSplit_eq_some a.1.1.1.reflectPrefix
    (reflectPrefix_firstHit a.1.1.1 a.1.1.2.1)
  have hbSome := firstHitSplit_eq_some b.1.1.1.reflectPrefix
    (reflectPrefix_firstHit b.1.1.1 b.1.1.2.1)
  have hsplits : a.1.1.1.reflectPrefix = b.1.1.1.reflectPrefix := by
    apply Option.some.inj
    rw [← haSome, ← hbSome, hsteps]
  have hfamilies :
      (reflectPrefixFirstHitFamilyEquiv (reflectedEndpoint (level : Int) start)
          (level : Int) walkLength target) a.1.1 =
        (reflectPrefixFirstHitFamilyEquiv
          (reflectedEndpoint (level : Int) start)
          (level : Int) walkLength target) b.1.1 := by
    apply Subtype.ext
    exact hsplits
  have habFamily : a.1.1 = b.1.1 :=
    (reflectPrefixFirstHitFamilyEquiv (reflectedEndpoint (level : Int) start)
      (level : Int) walkLength target).injective hfamilies
  apply Subtype.ext
  apply Subtype.ext
  exact habFamily


def SurvivalExceptionalMirrorFamilyAll
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat) :=
  Σ target : Int × Int,
    SurvivalExceptionalMirrorFamily R start level walkLength target

def survivalExceptionalMirrorProjectionAll
    (R level walkLength : Nat) (start : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level) :
    SurvivalExceptionalMirrorFamilyAll R start (level : Int) walkLength →
      IsingLineChoicePathFamily level walkLength
          (leftGapNeighbor level hlevel) (leftGapLeft level) ×
        {v : List Bool // v.length = walkLength} := fun w =>
  survivalExceptionalMirrorProjection R level walkLength start w.1
    hstart hlevel w.2

theorem survivalExceptionalMirrorProjectionAll_injective
    (R level walkLength : Nat) (start : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level) :
    Function.Injective
      (survivalExceptionalMirrorProjectionAll R level walkLength start
        hstart hlevel) := by
  intro a b hab
  have hh : horizontalLeftCode a.2.1.1.1.reflectPrefix.steps =
      horizontalLeftCode b.2.1.1.1.reflectPrefix.steps :=
    congrArg (fun z => z.1.1) hab
  have hv : verticalCode a.2.1.1.1.reflectPrefix.steps =
      verticalCode b.2.1.1.1.reflectPrefix.steps :=
    congrArg (fun z => z.2.1) hab
  have hsteps : a.2.1.1.1.reflectPrefix.steps =
      b.2.1.1.1.reflectPrefix.steps :=
    horizontalLeftCode_verticalCode_injective_of_valid
      (reflectPrefix_valid a.2.1.1.1 a.2.1.1.2.2.1)
      (reflectPrefix_valid b.2.1.1.1 b.2.1.1.2.2.1) hh hv
  have haSome := firstHitSplit_eq_some a.2.1.1.1.reflectPrefix
    (reflectPrefix_firstHit a.2.1.1.1 a.2.1.1.2.1)
  have hbSome := firstHitSplit_eq_some b.2.1.1.1.reflectPrefix
    (reflectPrefix_firstHit b.2.1.1.1 b.2.1.1.2.1)
  have hsplits : a.2.1.1.1.reflectPrefix =
      b.2.1.1.1.reflectPrefix := by
    apply Option.some.inj
    rw [← haSome, ← hbSome, hsteps]
  have horiginal : a.2.1.1.1 = b.2.1.1.1 := by
    cases ha : a.2.1.1.1 with
    | mk ab aa ahit =>
      cases hb : b.2.1.1.1 with
      | mk bb ba bhit =>
        have hreflect : Function.Injective reflectIncrement := by
          intro x y hxy
          apply Prod.ext
          · have hx := congrArg Prod.fst hxy
            simp [reflectIncrement] at hx
            linarith
          · simpa [reflectIncrement] using congrArg Prod.snd hxy
        have hbeforeMap := congrArg
          (fun w => w.before) hsplits
        simp only [ha, hb, reflectPrefix_before] at hbeforeMap
        have hbefore : ab = bb :=
          (Function.Injective.list_map hreflect) hbeforeMap
        have hafterRaw := congrArg (fun w => w.after) hsplits
        simp only [ha, hb, reflectPrefix_after] at hafterRaw
        have hafter : aa = ba := hafterRaw
        subst bb
        subst ba
        rfl
  have htarget : a.1 = b.1 := by
    have haend := a.2.1.1.2.2.2.2
    have hbend := b.2.1.1.2.2.2.2
    rw [← haend, ← hbend, horiginal]
  cases a with
  | mk atarget aw =>
    cases b with
    | mk btarget bw =>
      dsimp at htarget horiginal
      subst btarget
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        exact horiginal

noncomputable instance survivalExceptionalMirrorFamilyAll_finite
    (R walkLength : Nat) (start : Int × Int) (level : Int) :
    Finite (SurvivalExceptionalMirrorFamilyAll R start level
      walkLength) := by
  letI : Fintype
      {bits : List (Bool × Bool) // bits.length = walkLength} :=
    (List.finite_length_eq (Bool × Bool) walkLength).fintype
  exact Finite.of_injective
    (fun w : SurvivalExceptionalMirrorFamilyAll R start level
      walkLength => firstHitFamilyCode w.2.1.1)
    (by
      intro a b h
      have hsteps := encodePath_injective_of_valid
        a.2.1.1.2.2.1 b.2.1.1.2.2.1 (congrArg Subtype.val h)
      have haSome := firstHitSplit_eq_some a.2.1.1.1 a.2.1.1.2.1
      have hbSome := firstHitSplit_eq_some b.2.1.1.1 b.2.1.1.2.1
      have horiginal : a.2.1.1.1 = b.2.1.1.1 := by
        apply Option.some.inj
        rw [← haSome, ← hbSome, hsteps]
      have htarget : a.1 = b.1 := by
        have haend := a.2.1.1.2.2.2.2
        have hbend := b.2.1.1.2.2.2.2
        rw [← haend, ← hbend, horiginal]
      cases a with
      | mk atarget aw =>
        cases b with
        | mk btarget bw =>
          dsimp at htarget horiginal
          subst btarget
          apply Sigma.ext
          · rfl
          · apply heq_of_eq
            apply Subtype.ext
            apply Subtype.ext
            apply Subtype.ext
            exact horiginal)

private def survivalExceptionalMirrorPointwiseProjection
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level) :
    SurvivalExceptionalMirrorFamily R start (level : Int) walkLength target →
      IsingLineChoicePathFamily level walkLength
          (leftGapNeighbor level hlevel) (leftGapLeft level) ×
        VerticalChoicePathFamily walkLength start.2 target.2 := fun w =>
  let path := w.1.1.1.reflectPrefix.steps
  ⟨⟨horizontalLeftCode path, by
      simpa [horizontalLeftCode, path, reflectPrefix_length] using
        w.1.1.2.2.2.1,
      survivalExceptionalMirror_horizontal_run_left R level walkLength
        start target hstart hlevel w⟩,
    ⟨verticalCode path, by
      simpa [verticalCode, path, reflectPrefix_length] using
        w.1.1.2.2.2.1,
      by simpa using reflectPrefix_verticalCode_endpoint w.1.1⟩⟩

private theorem survivalExceptionalMirrorPointwiseProjection_injective
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level) :
    Function.Injective
      (survivalExceptionalMirrorPointwiseProjection R level walkLength
        start target hstart hlevel) := by
  intro a b hab
  apply survivalExceptionalMirrorProjection_injective R level walkLength
    start target hstart hlevel
  apply Prod.ext
  · simpa [survivalExceptionalMirrorPointwiseProjection,
        survivalExceptionalMirrorProjection] using
      congrArg (fun z => z.1) hab
  · apply Subtype.ext
    simpa [survivalExceptionalMirrorPointwiseProjection,
        survivalExceptionalMirrorProjection] using
      congrArg (fun z => z.2.1) hab



theorem survivalExceptionalMirrorFamily_weight_le_inv_leftGap
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level) :
    (Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
        walkLength target) : Real) / 4 ^ walkLength ≤
      1 / (level : Real) := by
  let p := leftGapNeighbor level hlevel
  let q := leftGapLeft level
  have hcountNat :
      Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
        walkLength target) ≤
        Nat.card (IsingLineChoicePathFamily level walkLength p q) *
          2 ^ walkLength := by
    calc
      Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
          walkLength target) ≤
          Nat.card (IsingLineChoicePathFamily level walkLength p q ×
            {v : List Bool // v.length = walkLength}) :=
        Nat.card_le_card_of_injective
          (survivalExceptionalMirrorProjection R level walkLength start target
            hstart hlevel)
          (survivalExceptionalMirrorProjection_injective R level walkLength
            start target hstart hlevel)
      _ = Nat.card (IsingLineChoicePathFamily level walkLength p q) *
          Nat.card {v : List Bool // v.length = walkLength} := by
        rw [Nat.card_prod]
      _ = _ := by rw [natCard_boolListLength]
  have hcountReal :
      (Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
          walkLength target) : Real) ≤
        (Nat.card (IsingLineChoicePathFamily level walkLength p q) : Real) *
          (2 : Real) ^ walkLength := by
    exact_mod_cast hcountNat
  have hline :
      (Nat.card (IsingLineChoicePathFamily level walkLength p q) : Real) /
          (2 : Real) ^ walkLength ≤ 1 / (level : Real) := by
    rw [← isingLineStoppedKernel_eq_natCard_choicePath_div]
    dsimp [p, q]
    simpa [leftGapNeighbor, leftGapLeft] using
      (isingLineStoppedKernel_left_of_rightNeighbor level walkLength hlevel)
  calc
    (Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
        walkLength target) : Real) / 4 ^ walkLength ≤
        ((Nat.card (IsingLineChoicePathFamily level walkLength p q) : Real) *
          (2 : Real) ^ walkLength) / 4 ^ walkLength :=
      div_le_div_of_nonneg_right hcountReal (by positivity)
    _ = (Nat.card (IsingLineChoicePathFamily level walkLength p q) : Real) /
          (2 : Real) ^ walkLength := by
      rw [show (4 : Real) ^ walkLength =
          (2 : Real) ^ walkLength * (2 : Real) ^ walkLength by
        rw [← mul_pow]
        norm_num]
      field_simp
    _ ≤ 1 / (level : Real) := hline



theorem survivalExceptionalMirrorFamilyAll_weight_le_inv_leftGap
    (R level walkLength : Nat) (start : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level) :
    (Nat.card (SurvivalExceptionalMirrorFamilyAll R start (level : Int)
        walkLength) : Real) / 4 ^ walkLength ≤
      1 / (level : Real) := by
  let p := leftGapNeighbor level hlevel
  let q := leftGapLeft level
  have hcountNat :
      Nat.card (SurvivalExceptionalMirrorFamilyAll R start (level : Int)
        walkLength) ≤
        Nat.card (IsingLineChoicePathFamily level walkLength p q) *
          2 ^ walkLength := by
    calc
      _ ≤ Nat.card (IsingLineChoicePathFamily level walkLength p q ×
          {v : List Bool // v.length = walkLength}) :=
        Nat.card_le_card_of_injective
          (survivalExceptionalMirrorProjectionAll R level walkLength start
            hstart hlevel)
          (survivalExceptionalMirrorProjectionAll_injective R level walkLength
            start hstart hlevel)
      _ = Nat.card (IsingLineChoicePathFamily level walkLength p q) *
          Nat.card {v : List Bool // v.length = walkLength} := by
        rw [Nat.card_prod]
      _ = _ := by rw [natCard_boolListLength]
  have hcountReal :
      (Nat.card (SurvivalExceptionalMirrorFamilyAll R start (level : Int)
          walkLength) : Real) ≤
        (Nat.card (IsingLineChoicePathFamily level walkLength p q) : Real) *
          (2 : Real) ^ walkLength := by
    exact_mod_cast hcountNat
  have hline :
      (Nat.card (IsingLineChoicePathFamily level walkLength p q) : Real) /
          (2 : Real) ^ walkLength ≤ 1 / (level : Real) := by
    rw [← isingLineStoppedKernel_eq_natCard_choicePath_div]
    dsimp [p, q]
    simpa [leftGapNeighbor, leftGapLeft] using
      (isingLineStoppedKernel_left_of_rightNeighbor level walkLength hlevel)
  calc
    _ ≤ ((Nat.card (IsingLineChoicePathFamily level walkLength p q) : Real) *
          (2 : Real) ^ walkLength) / 4 ^ walkLength :=
      div_le_div_of_nonneg_right hcountReal (by positivity)
    _ = (Nat.card (IsingLineChoicePathFamily level walkLength p q) : Real) /
          (2 : Real) ^ walkLength := by
      rw [show (4 : Real) ^ walkLength =
          (2 : Real) ^ walkLength * (2 : Real) ^ walkLength by
        rw [← mul_pow]
        norm_num]
      field_simp
    _ ≤ 1 / (level : Real) := hline



theorem survivalExceptionalMirrorFamily_weight_le_inv_leftGap_mul_binomial
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level) :
    (Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
        walkLength target) : Real) / 4 ^ walkLength ≤
      (1 / (level : Real)) *
        isingLineBinomialKernel walkLength start.2 target.2 := by
  let p := leftGapNeighbor level hlevel
  let q := leftGapLeft level
  let H := IsingLineChoicePathFamily level walkLength p q
  let V := VerticalChoicePathFamily walkLength start.2 target.2
  have hcountNat :
      Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
        walkLength target) ≤ Nat.card H * Nat.card V := by
    calc
      Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
          walkLength target) ≤ Nat.card (H × V) :=
        Nat.card_le_card_of_injective
          (survivalExceptionalMirrorPointwiseProjection R level walkLength
            start target hstart hlevel)
          (survivalExceptionalMirrorPointwiseProjection_injective R level
            walkLength start target hstart hlevel)
      _ = _ := by rw [Nat.card_prod]
  have hcountReal :
      (Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
          walkLength target) : Real) ≤
        (Nat.card H : Real) * (Nat.card V : Real) := by
    exact_mod_cast hcountNat
  have hline : (Nat.card H : Real) / (2 : Real) ^ walkLength ≤
      1 / (level : Real) := by
    dsimp [H]
    rw [← isingLineStoppedKernel_eq_natCard_choicePath_div]
    dsimp [p, q]
    simpa [leftGapNeighbor, leftGapLeft] using
      (isingLineStoppedKernel_left_of_rightNeighbor level walkLength hlevel)
  have hvertical : (Nat.card V : Real) / (2 : Real) ^ walkLength =
      isingLineBinomialKernel walkLength start.2 target.2 := by
    dsimp [V]
    symm
    exact isingLineBinomialKernel_eq_natCard_verticalChoicePath_div
      walkLength start.2 target.2
  calc
    (Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
        walkLength target) : Real) / 4 ^ walkLength ≤
        ((Nat.card H : Real) * (Nat.card V : Real)) / 4 ^ walkLength :=
      div_le_div_of_nonneg_right hcountReal (by positivity)
    _ = ((Nat.card H : Real) / (2 : Real) ^ walkLength) *
        ((Nat.card V : Real) / (2 : Real) ^ walkLength) := by
      rw [show (4 : Real) ^ walkLength =
          (2 : Real) ^ walkLength * (2 : Real) ^ walkLength by
        rw [← mul_pow]
        norm_num]
      field_simp
    _ = ((Nat.card H : Real) / (2 : Real) ^ walkLength) *
        isingLineBinomialKernel walkLength start.2 target.2 := by
      rw [hvertical]
    _ ≤ (1 / (level : Real)) *
        isingLineBinomialKernel walkLength start.2 target.2 :=
      mul_le_mul_of_nonneg_right hline
        (isingLineBinomialKernel_nonneg walkLength start.2 target.2)



theorem survivingFirstHitFamily_weight_dist_le_inv_gaps
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R) :
    (Nat.dist
        (Nat.card (SurvivingFirstHitFamily R start (level : Int)
          walkLength target))
        (Nat.card (SurvivingFirstHitFamily R
          (reflectedEndpoint (level : Int) start) (level : Int)
          walkLength target)) : Real) / 4 ^ walkLength ≤
      1 / ((R - level : Nat) : Real) + 1 / (level : Real) := by
  have hdistNat := natDist_survivingFirstHitFamily_le_exceptions R start
    (level : Int) walkLength target
  have hdistReal :
      (Nat.dist
          (Nat.card (SurvivingFirstHitFamily R start (level : Int)
            walkLength target))
          (Nat.card (SurvivingFirstHitFamily R
            (reflectedEndpoint (level : Int) start) (level : Int)
            walkLength target)) : Real) ≤
        (Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
          walkLength target) : Real) +
        (Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
          walkLength target) : Real) := by
    exact_mod_cast hdistNat
  calc
    _ ≤ ((Nat.card (SurvivalExceptionalFirstHitFamily R start
          (level : Int) walkLength target) : Real) +
        (Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
          walkLength target) : Real)) / 4 ^ walkLength :=
      div_le_div_of_nonneg_right hdistReal (by positivity)
    _ = (Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
          walkLength target) : Real) / 4 ^ walkLength +
        (Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
          walkLength target) : Real) / 4 ^ walkLength := by ring
    _ ≤ 1 / ((R - level : Nat) : Real) + 1 / (level : Real) :=
      add_le_add
        (survivalExceptionalFirstHitFamily_weight_le_inv_rightGap R level
          walkLength start target hstart hlevel hgap)
        (survivalExceptionalMirrorFamily_weight_le_inv_leftGap R level
          walkLength start target hstart hlevel)



theorem survivingFirstHitFamily_weight_dist_le_inv_gaps_mul_binomial
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R) :
    (Nat.dist
        (Nat.card (SurvivingFirstHitFamily R start (level : Int)
          walkLength target))
        (Nat.card (SurvivingFirstHitFamily R
          (reflectedEndpoint (level : Int) start) (level : Int)
          walkLength target)) : Real) / 4 ^ walkLength ≤
      (1 / ((R - level : Nat) : Real) + 1 / (level : Real)) *
        isingLineBinomialKernel walkLength start.2 target.2 := by
  have hdistNat := natDist_survivingFirstHitFamily_le_exceptions R start
    (level : Int) walkLength target
  have hdistReal :
      (Nat.dist
          (Nat.card (SurvivingFirstHitFamily R start (level : Int)
            walkLength target))
          (Nat.card (SurvivingFirstHitFamily R
            (reflectedEndpoint (level : Int) start) (level : Int)
            walkLength target)) : Real) ≤
        (Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
          walkLength target) : Real) +
        (Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
          walkLength target) : Real) := by
    exact_mod_cast hdistNat
  calc
    _ ≤ ((Nat.card (SurvivalExceptionalFirstHitFamily R start
          (level : Int) walkLength target) : Real) +
        (Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
          walkLength target) : Real)) / 4 ^ walkLength :=
      div_le_div_of_nonneg_right hdistReal (by positivity)
    _ = (Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
          walkLength target) : Real) / 4 ^ walkLength +
        (Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
          walkLength target) : Real) / 4 ^ walkLength := by ring
    _ ≤ (1 / ((R - level : Nat) : Real)) *
          isingLineBinomialKernel walkLength start.2 target.2 +
        (1 / (level : Real)) *
          isingLineBinomialKernel walkLength start.2 target.2 :=
      add_le_add
        (survivalExceptionalFirstHitFamily_weight_le_inv_rightGap_mul_binomial
          R level walkLength start target hstart hlevel hgap)
        (survivalExceptionalMirrorFamily_weight_le_inv_leftGap_mul_binomial
          R level walkLength start target hstart hlevel)
    _ = _ := by ring



theorem survivingFirstHitFamily_diffusive_weight_dist_le
    (R level ρ : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hρ : 0 < ρ)
    (hleft : ρ + 1 ≤ level) (hright : level + 1 + ρ ≤ R) :
    (Nat.dist
        (Nat.card (SurvivingFirstHitFamily R start (level : Int)
          (ρ * ρ) target))
        (Nat.card (SurvivingFirstHitFamily R
          (reflectedEndpoint (level : Int) start) (level : Int)
          (ρ * ρ) target)) : Real) / 4 ^ (ρ * ρ) ≤
      4 / (ρ : Real) ^ 2 := by
  have hbase :=
    survivingFirstHitFamily_weight_dist_le_inv_gaps_mul_binomial R level
      (ρ * ρ) start target hstart (by omega) (by omega)
  let K := isingLineBinomialKernel (ρ * ρ) start.2 target.2
  have hK0 : 0 ≤ K := isingLineBinomialKernel_nonneg _ _ _
  have hKsq := isingLineBinomialKernel_sq_le (ρ * ρ) start.2 target.2
  norm_num [Nat.cast_add, Nat.cast_mul] at hKsq
  have hden : 0 < (ρ : Real) ^ 2 + 1 := by positivity
  have hKsq' : K ^ 2 * ((ρ : Real) ^ 2 + 1) ≤ 2 := by
    apply (le_div_iff₀ hden).mp
    dsimp [K]
    convert hKsq using 1 <;> ring
  have hρReal : 0 < (ρ : Real) := by positivity
  have hK : K ≤ 2 / (ρ : Real) := by
    apply (le_div_iff₀ hρReal).2
    have hprod0 : 0 ≤ (ρ : Real) * K := mul_nonneg hρReal.le hK0
    have hprodSq : ((ρ : Real) * K) ^ 2 ≤ 2 := by
      nlinarith [sq_nonneg K]
    nlinarith
  have hrightGap : (ρ : Real) ≤ (R - level : Nat) := by
    exact_mod_cast (show ρ ≤ R - level by omega)
  have hleftGap : (ρ : Real) ≤ level := by
    exact_mod_cast (show ρ ≤ level by omega)
  have hinvRight : 1 / ((R - level : Nat) : Real) ≤
      1 / (ρ : Real) := one_div_le_one_div_of_le hρReal hrightGap
  have hinvLeft : 1 / (level : Real) ≤ 1 / (ρ : Real) :=
    one_div_le_one_div_of_le hρReal hleftGap
  have hgap : 1 / ((R - level : Nat) : Real) + 1 / (level : Real) ≤
      2 / (ρ : Real) := by
    calc
      _ ≤ 1 / (ρ : Real) + 1 / (ρ : Real) :=
        add_le_add hinvRight hinvLeft
      _ = _ := by ring
  calc
    _ ≤ (1 / ((R - level : Nat) : Real) + 1 / (level : Real)) * K :=
      hbase
    _ ≤ (2 / (ρ : Real)) * K :=
      mul_le_mul_of_nonneg_right hgap hK0
    _ ≤ (2 / (ρ : Real)) * (2 / (ρ : Real)) :=
      mul_le_mul_of_nonneg_left hK (by positivity)
    _ = 4 / (ρ : Real) ^ 2 := by ring

end IsingDiagonalWalkHitSplit

end StatMech.Universality
