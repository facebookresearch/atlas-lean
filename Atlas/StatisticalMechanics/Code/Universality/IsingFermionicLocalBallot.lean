/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicStoppedPointwise





namespace StatMech.Universality

open Finset
open IsingDiagonalWalkHitSplit

noncomputable section

private theorem choose_right_mono_to_middle (n : Nat) :
    ∀ {k i : Nat}, k ≤ i → i ≤ n / 2 → n.choose k ≤ n.choose i := by
  intro k i hki him
  induction i, hki using Nat.le_induction with
  | base => exact le_rfl
  | succ i hki ih =>
      have hi : i < n / 2 := by omega
      have hfactor : i + 1 ≤ n - i := by omega
      have hmul : n.choose i * (i + 1) ≤ n.choose i * (n - i) :=
        Nat.mul_le_mul_left _ hfactor
      rw [← Nat.choose_succ_right_eq] at hmul
      exact le_trans (ih (by omega))
        (Nat.le_of_mul_le_mul_right hmul (by omega))

private theorem choose_mul_middle_block_le_two_pow
    (n k : Nat) (hk : k ≤ n / 2) :
    (n / 2 - k + 1) * n.choose k ≤ 2 ^ n := by
  let block := Finset.Icc k (n / 2)
  have hterm : ∀ i ∈ block, n.choose k ≤ n.choose i := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    exact choose_right_mono_to_middle n hi.1 hi.2
  have hsum : (∑ i ∈ block, n.choose k) ≤
      ∑ i ∈ block, n.choose i :=
    Finset.sum_le_sum hterm
  have hsubset : block ⊆ Finset.range (n + 1) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    simp
    omega
  have hfull : (∑ i ∈ block, n.choose i) ≤
      ∑ i ∈ Finset.range (n + 1), n.choose i := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => by omega)
  have hcard : block.card = n / 2 - k + 1 := by
    dsimp [block]
    rw [Nat.card_Icc]
    omega
  calc
    (n / 2 - k + 1) * n.choose k =
        ∑ i ∈ block, n.choose k := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
      norm_num
    _ ≤ ∑ i ∈ block, n.choose i := hsum
    _ ≤ ∑ i ∈ Finset.range (n + 1), n.choose i := hfull
    _ = 2 ^ n := Nat.sum_range_choose n

private theorem choose_adjacent_sub_mul_le (n k : Nat) (hk : k ≤ n / 2) :
    (n + 1) * (n.choose k - n.choose (k - 1)) ≤ 4 * 2 ^ n := by
  by_cases hk0 : k = 0
  · subst k
    simp only [Nat.choose_zero_right, Nat.zero_sub, Nat.choose_zero_succ,
      Nat.sub_zero, mul_one]
    have hpow : n + 1 ≤ 2 ^ n := by
      simpa using Nat.choose_succ_le_two_pow n 1
    omega
  let A := n.choose k
  let B := n.choose (k - 1)
  let den := n - k + 1
  let d := n + 1 - 2 * k
  let s := n / 2 - k + 1
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  have hpred : k - 1 ≤ n / 2 := by omega
  have hBA : B ≤ A := by
    dsimp [A, B]
    exact choose_right_mono_to_middle n (by omega) hk
  have hchoose : A * k = B * den := by
    have h := Nat.choose_succ_right_eq n (k - 1)
    rw [show n - (k - 1) = n - k + 1 by omega] at h
    dsimp [A, B, den]
    simpa [Nat.sub_add_cancel hkpos] using h
  have hdiff : (A - B) * den = A * d := by
    calc
      (A - B) * den = A * den - B * den := Nat.sub_mul A B den
      _ = A * den - A * k := by rw [← hchoose]
      _ = A * (den - k) := (Nat.mul_sub_left_distrib A den k).symm
      _ = A * d := by
        congr 1
        dsimp [den, d]
        omega
  have hblock : s * A ≤ 2 ^ n := by
    dsimp [s, A]
    exact choose_mul_middle_block_le_two_pow n k hk
  have hnum : (n + 1) * d ≤ 4 * den * s := by
    have h1 : n + 1 ≤ 2 * den := by
      dsimp [den]
      omega
    have h2 : d ≤ 2 * s := by
      dsimp [d, s]
      omega
    calc
      (n + 1) * d ≤ (2 * den) * (2 * s) := Nat.mul_le_mul h1 h2
      _ = 4 * den * s := by ring
  have hden : 0 < den := by
    dsimp [den]
    omega
  apply Nat.le_of_mul_le_mul_right _ hden
  calc
    (n + 1) * (n.choose k - n.choose (k - 1)) * den =
        A * ((n + 1) * d) := by
      dsimp [A, B] at hdiff ⊢
      rw [mul_assoc, hdiff]
      ring
    _ ≤ A * (4 * den * s) := Nat.mul_le_mul_left A hnum
    _ = 4 * den * (s * A) := by ring
    _ ≤ 4 * den * 2 ^ n := Nat.mul_le_mul_left (4 * den) hblock
    _ = 4 * 2 ^ n * den := by ring

theorem isingBinomialWeight_sub_pred_le
    (n k : Nat) (hk : k ≤ n / 2) :
    isingBinomialWeight n k - isingBinomialWeightPrev n k ≤
      4 / (n + 1 : Real) := by
  by_cases hk0 : k = 0
  · subst k
    simp only [isingBinomialWeightPrev, if_pos, sub_zero]
    have hpowNat : n + 1 ≤ 2 ^ n := by
      simpa using Nat.choose_succ_le_two_pow n 1
    have hpowReal : (n + 1 : Real) ≤ (2 : Real) ^ n := by exact_mod_cast hpowNat
    unfold isingBinomialWeight
    simp only [Nat.choose_zero_right, Nat.cast_one]
    have hn : (0 : Real) < n + 1 := by positivity
    have hp : (0 : Real) < (2 : Real) ^ n := by positivity
    apply (div_le_div_iff₀ hp hn).2
    nlinarith
  have hBA : n.choose (k - 1) ≤ n.choose k :=
    choose_right_mono_to_middle n (by omega) hk
  have hnat := choose_adjacent_sub_mul_le n k hk
  have hreal : (n + 1 : Real) *
      ((n.choose k : Real) - n.choose (k - 1)) ≤
        4 * (2 : Real) ^ n := by
    exact_mod_cast hnat
  have hn : (0 : Real) < n + 1 := by positivity
  have hpow : (0 : Real) < (2 : Real) ^ n := by positivity
  rw [isingBinomialWeightPrev, if_neg hk0]
  unfold isingBinomialWeight
  apply (le_div_iff₀ hn).2
  calc
    ((n.choose k : Real) / 2 ^ n -
          (n.choose (k - 1) : Real) / 2 ^ n) * (n + 1 : Real) =
      ((n + 1 : Real) *
        ((n.choose k : Real) - n.choose (k - 1))) / 2 ^ n := by ring
    _ ≤ (4 * (2 : Real) ^ n) / 2 ^ n :=
      div_le_div_of_nonneg_right hreal hpow.le
    _ = 4 := by field_simp



theorem isingLineBinomialKernel_adjacentStart_sub_le
    (t : Nat) (x y : Int) (hy : y < x + 1) :
    isingLineBinomialKernel t x y -
        isingLineBinomialKernel t (x + 2) y ≤
      4 / (t + 1 : Real) := by
  by_cases hex : ∃ k ∈ Finset.range (t + 1),
      y = x + 2 * (k : Int) - (t : Int)
  · rcases hex with ⟨k, hkRange, hkEnd⟩
    have hkt : k ≤ t / 2 := by
      push_cast at hkEnd
      omega
    have hlower : isingLineBinomialKernel t x y =
        isingBinomialWeight t k := by
      unfold isingLineBinomialKernel
      rw [Finset.sum_eq_single k]
      · simp [hkEnd]
      · intro b hb hbk
        have hbne : ¬ y = x + 2 * (b : Int) - (t : Int) := by
          intro hbe
          have : b = k := by
            push_cast at hbe hkEnd
            omega
          exact hbk this
        simp [hbne]
      · exact fun hknot => (hknot hkRange).elim
    have hupper : isingLineBinomialKernel t (x + 2) y =
        isingBinomialWeightPrev t k := by
      by_cases hk0 : k = 0
      · subst k
        have hzero : isingLineBinomialKernel t (x + 2) y = 0 := by
          unfold isingLineBinomialKernel
          apply Finset.sum_eq_zero
          intro b hb
          have hbne : ¬ y = x + 2 + 2 * (b : Int) - (t : Int) := by
            intro hbe
            push_cast at hbe hkEnd
            omega
          simp [hbne]
        rw [hzero]
        simp [isingBinomialWeightPrev]
      · have hkPredRange : k - 1 ∈ Finset.range (t + 1) := by
          simp
          omega
        rw [isingBinomialWeightPrev, if_neg hk0]
        unfold isingLineBinomialKernel
        rw [Finset.sum_eq_single (k - 1)]
        · have heq : y = x + 2 + 2 * ((k - 1 : Nat) : Int) - (t : Int) := by
            push_cast at hkEnd ⊢
            omega
          simp [heq]
        · intro b hb hbk
          have hbne : ¬ y = x + 2 + 2 * (b : Int) - (t : Int) := by
            intro hbe
            have : b = k - 1 := by
              push_cast at hbe hkEnd
              omega
            exact hbk this
          simp [hbne]
        · exact fun hknot => (hknot hkPredRange).elim
    rw [hlower, hupper]
    exact isingBinomialWeight_sub_pred_le t k hkt
  · have hlower : isingLineBinomialKernel t x y = 0 := by
      unfold isingLineBinomialKernel
      apply Finset.sum_eq_zero
      intro k hk
      have hkne : ¬ y = x + 2 * (k : Int) - (t : Int) := by
        intro heq
        exact hex ⟨k, hk, heq⟩
      simp [hkne]
    rw [hlower]
    have hupper := isingLineBinomialKernel_nonneg t (x + 2) y
    have hbound : (0 : Real) ≤ 4 / (t + 1 : Real) := by positivity
    linarith

private def localHorizontalStep (b : Bool) : Int × Int :=
  (if b then 1 else -1, 1)

private def localHorizontalSteps (bs : List Bool) : List (Int × Int) :=
  bs.map localHorizontalStep

private def localHorizontalCode (d : Int × Int) : Bool :=
  decide (d.1 = 1)

private theorem localHorizontalSteps_length (bs : List Bool) :
    (localHorizontalSteps bs).length = bs.length := by
  simp [localHorizontalSteps]

private theorem localHorizontalSteps_valid (bs : List Bool) :
    IsingDiagonalWalkStepsValid (localHorizontalSteps bs) := by
  intro d hd
  rcases List.mem_map.mp hd with ⟨b, hb, rfl⟩
  cases b <;> simp [localHorizontalStep]

private theorem localHorizontalSteps_vertical (bs : List Bool) :
    ∀ d ∈ localHorizontalSteps bs, d.2 = 1 := by
  intro d hd
  rcases List.mem_map.mp hd with ⟨b, hb, rfl⟩
  simp [localHorizontalStep]

private theorem localHorizontalCode_step (b : Bool) :
    localHorizontalCode (localHorizontalStep b) = b := by
  cases b <;> simp [localHorizontalCode, localHorizontalStep]

private theorem localHorizontalCodes_steps (bs : List Bool) :
    (localHorizontalSteps bs).map localHorizontalCode = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      change localHorizontalCode (localHorizontalStep b) ::
        (localHorizontalSteps bs).map localHorizontalCode = b :: bs
      rw [localHorizontalCode_step, ih]

private theorem localHorizontalSteps_codes
    (path : List (Int × Int))
    (hvalid : IsingDiagonalWalkStepsValid path)
    (hvertical : ∀ d ∈ path, d.2 = 1) :
    localHorizontalSteps (path.map localHorizontalCode) = path := by
  induction path with
  | nil => rfl
  | cons d path ih =>
      have hd := hvalid d (by simp)
      have hdv := hvertical d (by simp)
      have htail : IsingDiagonalWalkStepsValid path := by
        intro e he
        exact hvalid e (by simp [he])
      have htailv : ∀ e ∈ path, e.2 = 1 := by
        intro e he
        exact hvertical e (by simp [he])
      have hstep : localHorizontalStep (localHorizontalCode d) = d := by
        rcases hd.1 with hdx | hdx <;> apply Prod.ext <;>
          simp [localHorizontalStep, localHorizontalCode, hdx, hdv]
      change localHorizontalStep (localHorizontalCode d) ::
        localHorizontalSteps (path.map localHorizontalCode) = d :: path
      rw [hstep, ih htail htailv]

private theorem lineFreeEndpoint_localHorizontalSteps
    (bs : List Bool) (start : Int) :
    lineFreeEndpoint start bs =
      (isingDiagonalWalkEndpoint (start, 0) (localHorizontalSteps bs)).1 := by
  induction bs generalizing start with
  | nil => simp [lineFreeEndpoint, localHorizontalSteps,
      isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement]
  | cons b bs ih =>
      cases b with
      | false =>
          convert ih (start - 1) using 1 <;>
            simp [lineFreeEndpoint, localHorizontalSteps, localHorizontalStep,
              isingDiagonalWalkEndpoint, isingDiagonalWalkNext,
              isingDiagonalWalkDisplacement, add_assoc] <;> ring
      | true =>
          convert ih (start + 1) using 1 <;>
            simp [lineFreeEndpoint, localHorizontalSteps, localHorizontalStep,
              isingDiagonalWalkEndpoint, isingDiagonalWalkNext,
              isingDiagonalWalkDisplacement, add_assoc] <;> ring

private abbrev LocalHorizontalFreeFiber
    (t : Nat) (start target : Int) :=
  VerticalChoicePathFamily t start target

private def LocalHorizontalHitFiber
    (t : Nat) (start level target : Int) :=
  {w : LocalHorizontalFreeFiber t start target //
    isingDiagonalWalkFirstHitSplit? (start, 0) level
      (localHorizontalSteps w.1) ≠ none}

private def LocalHorizontalNoHitFiber
    (t : Nat) (start level target : Int) :=
  {w : LocalHorizontalFreeFiber t start target //
    ¬ isingDiagonalWalkFirstHitSplit? (start, 0) level
      (localHorizontalSteps w.1) ≠ none}

noncomputable instance localHorizontalHitFiber_finite
    (t : Nat) (start level target : Int) :
    Finite (LocalHorizontalHitFiber t start level target) := by
  exact Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance localHorizontalNoHitFiber_finite
    (t : Nat) (start level target : Int) :
    Finite (LocalHorizontalNoHitFiber t start level target) := by
  exact Finite.of_injective Subtype.val Subtype.val_injective

private theorem natCard_localHorizontalFree_eq_hit_add_noHit
    (t : Nat) (start level target : Int) :
    Nat.card (LocalHorizontalFreeFiber t start target) =
      Nat.card (LocalHorizontalHitFiber t start level target) +
        Nat.card (LocalHorizontalNoHitFiber t start level target) := by
  rw [← Nat.card_sum]
  exact Nat.card_congr
    (Equiv.sumCompl (fun w : LocalHorizontalFreeFiber t start target =>
      isingDiagonalWalkFirstHitSplit? (start, 0) level
        (localHorizontalSteps w.1) ≠ none)).symm

private theorem reflectPrefix_steps_vertical
    {start : Int × Int} {level : Int}
    (split : IsingDiagonalWalkHitSplit start level)
    (hvertical : ∀ d ∈ split.steps, d.2 = 1) :
    ∀ d ∈ split.reflectPrefix.steps, d.2 = 1 := by
  intro d hd
  change d ∈ split.before.map reflectIncrement ++ split.after at hd
  rcases List.mem_append.mp hd with hd | hd
  · rcases List.mem_map.mp hd with ⟨e, he, rfl⟩
    simpa [reflectIncrement] using hvertical e
      (List.mem_append.mpr (Or.inl he))
  · exact hvertical d (List.mem_append.mpr (Or.inr hd))

private theorem reflectPrefix_injective
    {start : Int × Int} {level : Int} :
    Function.Injective
      (IsingDiagonalWalkHitSplit.reflectPrefix (start := start) (level := level)) := by
  intro a b h
  cases a with
  | mk ab aa ahit =>
      cases b with
      | mk bb ba bhit =>
          simp only [IsingDiagonalWalkHitSplit.reflectPrefix] at h
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
                (reflectedEndpoint level start) level => w.before) h
            exact (Function.Injective.list_map hreflect) hmap
          have hafter : aa = ba := congrArg
            (fun w : IsingDiagonalWalkHitSplit
              (reflectedEndpoint level start) level => w.after) h
          subst bb
          subst ba
          rfl

private noncomputable def localHorizontalHitReflect
    (t : Nat) (start level target : Int) :
    LocalHorizontalHitFiber t start level target →
      LocalHorizontalHitFiber t (2 * level - start) level target := fun w => by
  let split := (isingDiagonalWalkFirstHitSplit? (start, 0) level
    (localHorizontalSteps w.1.1)).get (Option.ne_none_iff_isSome.mp w.2)
  have hsplit : isingDiagonalWalkFirstHitSplit? (start, 0) level
      (localHorizontalSteps w.1.1) = some split :=
    (Option.some_get (Option.ne_none_iff_isSome.mp w.2)).symm
  let split' := split.reflectPrefix
  let bs' := split'.steps.map localHorizontalCode
  have hvalid : split.Valid := by
    unfold IsingDiagonalWalkHitSplit.Valid
    rw [firstHitSplit_steps hsplit]
    exact localHorizontalSteps_valid w.1.1
  have hdecode : localHorizontalSteps bs' = split'.steps :=
    localHorizontalSteps_codes split'.steps (reflectPrefix_valid split hvalid) (by
      intro d hd
      change d ∈ split.before.map reflectIncrement ++ split.after at hd
      rcases List.mem_append.mp hd with hd | hd
      · rcases List.mem_map.mp hd with ⟨e, he, rfl⟩
        simpa [reflectIncrement] using localHorizontalSteps_vertical w.1.1 e
          (by rw [← firstHitSplit_steps hsplit]; exact List.mem_append.mpr (Or.inl he))
      · exact localHorizontalSteps_vertical w.1.1 d
          (by rw [← firstHitSplit_steps hsplit]; exact List.mem_append.mpr (Or.inr hd)))
  refine ⟨⟨bs', ?_, ?_⟩, ?_⟩
  · rw [← localHorizontalSteps_length, hdecode, reflectPrefix_length,
      firstHitSplit_steps hsplit, localHorizontalSteps_length]
    exact w.1.2.1
  · rw [lineFreeEndpoint_localHorizontalSteps, hdecode]
    have horig : split.endpoint.1 = target := by
      unfold IsingDiagonalWalkHitSplit.endpoint
      rw [firstHitSplit_steps hsplit]
      exact (lineFreeEndpoint_localHorizontalSteps w.1.1 start).symm.trans
        w.1.2.2
    exact (reflectPrefix_endpoint_fst split).trans horig
  · change isingDiagonalWalkFirstHitSplit?
      (reflectedEndpoint level (start, 0)) level
        (localHorizontalSteps bs') ≠ none
    rw [hdecode, firstHitSplit_eq_some split'
      (reflectPrefix_firstHit split (firstHitSplit_firstHit hsplit))]
    exact Option.some_ne_none split'

private theorem localHorizontalHitReflect_injective
    (t : Nat) (start level target : Int) :
    Function.Injective (localHorizontalHitReflect t start level target) := by
  intro a b h
  have hbits := congrArg
    (fun z : LocalHorizontalHitFiber t (2 * level - start) level target => z.1.1) h
  let sa := (isingDiagonalWalkFirstHitSplit? (start, 0) level
    (localHorizontalSteps a.1.1)).get (Option.ne_none_iff_isSome.mp a.2)
  let sb := (isingDiagonalWalkFirstHitSplit? (start, 0) level
    (localHorizontalSteps b.1.1)).get (Option.ne_none_iff_isSome.mp b.2)
  have hsa : isingDiagonalWalkFirstHitSplit? (start, 0) level
      (localHorizontalSteps a.1.1) = some sa :=
    (Option.some_get (Option.ne_none_iff_isSome.mp a.2)).symm
  have hsb : isingDiagonalWalkFirstHitSplit? (start, 0) level
      (localHorizontalSteps b.1.1) = some sb :=
    (Option.some_get (Option.ne_none_iff_isSome.mp b.2)).symm
  change sa.reflectPrefix.steps.map localHorizontalCode =
    sb.reflectPrefix.steps.map localHorizontalCode at hbits
  have hsaValid : sa.Valid := by
    unfold IsingDiagonalWalkHitSplit.Valid
    rw [firstHitSplit_steps hsa]
    exact localHorizontalSteps_valid a.1.1
  have hsbValid : sb.Valid := by
    unfold IsingDiagonalWalkHitSplit.Valid
    rw [firstHitSplit_steps hsb]
    exact localHorizontalSteps_valid b.1.1
  have hsaVertical : ∀ d ∈ sa.steps, d.2 = 1 := by
    rw [firstHitSplit_steps hsa]
    exact localHorizontalSteps_vertical a.1.1
  have hsbVertical : ∀ d ∈ sb.steps, d.2 = 1 := by
    rw [firstHitSplit_steps hsb]
    exact localHorizontalSteps_vertical b.1.1
  have hrefSteps : sa.reflectPrefix.steps = sb.reflectPrefix.steps := by
    rw [← localHorizontalSteps_codes _ (reflectPrefix_valid sa hsaValid)
      (reflectPrefix_steps_vertical sa hsaVertical),
      ← localHorizontalSteps_codes _ (reflectPrefix_valid sb hsbValid)
      (reflectPrefix_steps_vertical sb hsbVertical)]
    exact congrArg localHorizontalSteps hbits
  have hrefSplits : sa.reflectPrefix = sb.reflectPrefix := by
    apply Option.some.inj
    rw [← firstHitSplit_eq_some sa.reflectPrefix
        (reflectPrefix_firstHit sa (firstHitSplit_firstHit hsa)),
      ← firstHitSplit_eq_some sb.reflectPrefix
        (reflectPrefix_firstHit sb (firstHitSplit_firstHit hsb)), hrefSteps]
  have hsplits : sa = sb := reflectPrefix_injective hrefSplits
  have hpaths : localHorizontalSteps a.1.1 = localHorizontalSteps b.1.1 := by
    rw [← firstHitSplit_steps hsa, ← firstHitSplit_steps hsb, hsplits]
  have horigBits := congrArg (List.map localHorizontalCode) hpaths
  rw [localHorizontalCodes_steps, localHorizontalCodes_steps] at horigBits
  exact Subtype.ext (Subtype.ext horigBits)

private theorem natCard_localHorizontalHit_reflect
    (t : Nat) (start level target : Int) :
    Nat.card (LocalHorizontalHitFiber t start level target) =
      Nat.card (LocalHorizontalHitFiber t (2 * level - start) level target) := by
  apply le_antisymm
  · exact Nat.card_le_card_of_injective
      (localHorizontalHitReflect t start level target)
      (localHorizontalHitReflect_injective t start level target)
  · have h := Nat.card_le_card_of_injective
      (localHorizontalHitReflect t (2 * level - start) level target)
      (localHorizontalHitReflect_injective t (2 * level - start) level target)
    simpa only [show 2 * level - (2 * level - start) = start by ring] using h

private theorem localHorizontalFreeUpper_all_hit
    (t : Nat) (level target : Int) (htarget : target < level) :
    Nat.card (LocalHorizontalHitFiber t (level + 1) level target) =
      Nat.card (LocalHorizontalFreeFiber t (level + 1) target) := by
  apply le_antisymm
  · exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  · let f : LocalHorizontalFreeFiber t (level + 1) target →
        LocalHorizontalHitFiber t (level + 1) level target := fun w => ⟨w, by
      intro hnone
      rcases exists_prefix_fst_eq_of_ge_of_gt (localHorizontalSteps w.1)
        (level + 1, 0) level (localHorizontalSteps_valid w.1) (by omega) (by
          calc
            (isingDiagonalWalkEndpoint (level + 1, 0)
                (localHorizontalSteps w.1)).1 = target := by
              rw [← lineFreeEndpoint_localHorizontalSteps]
              exact w.2.2
            _ ≤ level := htarget.le) with ⟨k, hk, heq⟩
      exact (firstHitSplit_none_endpoint_fst_ne hnone k hk) heq⟩
    exact Nat.card_le_card_of_injective f (by
      intro a b h
      exact congrArg Subtype.val h)


def IsingHorizontalNoHitEndpointFamily
    (t : Nat) (level target : Int) :=
  {w : IsingHorizontalNoHitFamily t (level - 1) level //
    lineFreeEndpoint (level - 1) w.1 = target}

noncomputable instance isingHorizontalNoHitEndpointFamily_finite
    (t : Nat) (level target : Int) :
    Finite (IsingHorizontalNoHitEndpointFamily t level target) := by
  exact Finite.of_injective Subtype.val Subtype.val_injective

private def noHitEndpointToLocalNoHit
    (t : Nat) (level target : Int) :
    IsingHorizontalNoHitEndpointFamily t level target →
      LocalHorizontalNoHitFiber t (level - 1) level target := fun w => by
  refine ⟨⟨w.1.1, w.1.2.1, w.2⟩, ?_⟩
  change ¬ isingDiagonalWalkFirstHitSplit? (level - 1, 0) level
    (localHorizontalSteps w.1.1) ≠ none
  intro hne
  let split := (isingDiagonalWalkFirstHitSplit? (level - 1, 0) level
    (localHorizontalSteps w.1.1)).get (Option.ne_none_iff_isSome.mp hne)
  have hsplit : isingDiagonalWalkFirstHitSplit? (level - 1, 0) level
      (localHorizontalSteps w.1.1) = some split :=
    (Option.some_get (Option.ne_none_iff_isSome.mp hne)).symm
  have hk : split.before.length ≤ t := by
    have hlen := congrArg List.length (firstHitSplit_steps hsplit)
    simp [IsingDiagonalWalkHitSplit.steps, localHorizontalSteps, w.1.2.1] at hlen
    omega
  apply w.1.2.2 split.before.length hk
  calc
    lineFreeEndpoint (level - 1) (w.1.1.take split.before.length) =
        (isingDiagonalWalkEndpoint (level - 1, 0)
          (localHorizontalSteps (w.1.1.take split.before.length))).1 :=
      lineFreeEndpoint_localHorizontalSteps _ _
    _ = (isingDiagonalWalkEndpoint (level - 1, 0)
          ((localHorizontalSteps w.1.1).take split.before.length)).1 := by
      simp [localHorizontalSteps, List.map_take]
    _ = (isingDiagonalWalkEndpoint (level - 1, 0) split.before).1 := by
      rw [← firstHitSplit_steps hsplit]
      simp [IsingDiagonalWalkHitSplit.steps]
    _ = level := split.hit

private theorem noHitEndpointToLocalNoHit_injective
    (t : Nat) (level target : Int) :
    Function.Injective (noHitEndpointToLocalNoHit t level target) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z => z.1.1) h

theorem horizontalNoHitEndpoint_weight_le
    (t : Nat) (level target : Int) :
    Nat.card (IsingHorizontalNoHitEndpointFamily t level target) /
        (2 : Real) ^ t ≤
      4 / (t + 1 : Real) := by
  by_cases htarget : target < level
  · have hnohitCard : Nat.card
        (IsingHorizontalNoHitEndpointFamily t level target) ≤
      Nat.card (LocalHorizontalNoHitFiber t (level - 1) level target) :=
      Nat.card_le_card_of_injective (noHitEndpointToLocalNoHit t level target)
        (noHitEndpointToLocalNoHit_injective t level target)
    have hpartition := natCard_localHorizontalFree_eq_hit_add_noHit
      t (level - 1) level target
    have hreflect := natCard_localHorizontalHit_reflect
      t (level - 1) level target
    have hupper := localHorizontalFreeUpper_all_hit t level target htarget
    have hrefStart : 2 * level - (level - 1) = level + 1 := by ring
    rw [hrefStart, hupper] at hreflect
    have hcardDiff : Nat.card
        (LocalHorizontalNoHitFiber t (level - 1) level target) =
      Nat.card (VerticalChoicePathFamily t (level - 1) target) -
        Nat.card (VerticalChoicePathFamily t (level + 1) target) := by
      dsimp [LocalHorizontalFreeFiber] at hpartition hreflect ⊢
      omega
    have hupperLe : Nat.card (VerticalChoicePathFamily t (level + 1) target) ≤
        Nat.card (VerticalChoicePathFamily t (level - 1) target) := by
      dsimp [LocalHorizontalFreeFiber] at hpartition hreflect
      omega
    have hden : 0 < (2 : Real) ^ t := by positivity
    calc
      _ ≤ Nat.card (LocalHorizontalNoHitFiber t (level - 1) level target) /
          (2 : Real) ^ t := by
        apply div_le_div_of_nonneg_right _ hden.le
        exact_mod_cast hnohitCard
      _ = isingLineBinomialKernel t (level - 1) target -
          isingLineBinomialKernel t (level + 1) target := by
        rw [hcardDiff, Nat.cast_sub]
        · rw [sub_div, ← isingLineBinomialKernel_eq_natCard_verticalChoicePath_div,
            ← isingLineBinomialKernel_eq_natCard_verticalChoicePath_div]
        · exact hupperLe
      _ ≤ 4 / (t + 1 : Real) := by
        convert isingLineBinomialKernel_adjacentStart_sub_le
          t (level - 1) target (by omega) using 1 <;> ring
  · have hempty : IsEmpty (IsingHorizontalNoHitEndpointFamily t level target) :=
      ⟨fun w => by
        have hbelow : lineFreeEndpoint (level - 1) w.1.1 < level := by
          by_contra hn
          have hvalid := localHorizontalSteps_valid w.1.1
          have hend : level ≤ (isingDiagonalWalkEndpoint (level - 1, 0)
              (localHorizontalSteps w.1.1)).1 := by
            rw [← lineFreeEndpoint_localHorizontalSteps]
            omega
          rcases exists_prefix_fst_eq_of_lt_of_le (localHorizontalSteps w.1.1)
            (level - 1, 0) level hvalid (by omega) hend with ⟨k, hk, heq⟩
          apply w.1.2.2 k (by simpa [localHorizontalSteps, w.1.2.1] using hk)
          rw [lineFreeEndpoint_localHorizontalSteps]
          simpa [localHorizontalSteps, List.map_take] using heq
        exact htarget (by simpa [w.2] using hbelow)⟩
    letI := hempty
    simp only [Nat.card_of_isEmpty, Nat.cast_zero, zero_div]
    exact div_nonneg (by norm_num) (by positivity)

end

end StatMech.Universality
