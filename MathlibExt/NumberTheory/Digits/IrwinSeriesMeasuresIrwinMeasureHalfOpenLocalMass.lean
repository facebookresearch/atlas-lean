/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.IrwinSeriesMeasures
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Local structure of the Irwin measures on cylinders

This module proves that, on the half-open cylinder above a point of base-$b$
depth $l$, an Irwin measure of index below the digit count of the point's
prefix restricts to zero, and an Irwin measure of index at least that count
scales to the Irwin measure of the affinely rescaled set.

Source: Jean-François Burnol, *Measures for the Summation of Irwin Series*,
INTEGERS 26 (2026), Article A11, Proposition 8.
-/

namespace MetaMathlibExt

open scoped BigOperators ENNReal
open Filter MeasureTheory Set

namespace irwinMeasure_halfOpen_local_mass

/-- The fold defining `stringValue` distributes over the initial accumulator. -/
private theorem foldl_stringValue (b : ℕ) :
    ∀ (Z : List (Fin b)) (m : ℕ),
      Z.foldl (fun n a => b * n + a.val) m =
        m * b ^ Z.length + Z.foldl (fun n a => b * n + a.val) 0 := by
  intro Z
  induction Z with
  | nil => intro m; simp
  | cons a Z ih =>
    intro m
    simp only [List.length_cons, List.foldl_cons, pow_succ', mul_zero, zero_add]
    rw [ih (b * m + a.val), ih a.val]
    ring

/-- The value of a concatenated digit string splits into a shifted prefix value
plus the suffix value. -/
private theorem stringValue_append (b : ℕ) (A Z : List (Fin b)) :
    stringValue b (A ++ Z) = stringValue b A * b ^ Z.length + stringValue b Z := by
  unfold stringValue
  rw [List.foldl_append, foldl_stringValue]

/-- The value of a digit string with a given first digit splits into the first
digit's contribution plus the value of the remaining string. -/
private theorem stringValue_cons (b : ℕ) (a : Fin b) (X : List (Fin b)) :
    stringValue b (a :: X) = a.val * b ^ X.length + stringValue b X := by
  unfold stringValue
  simp only [List.foldl_cons]
  rw [foldl_stringValue]
  simp

/-- The value of a digit string is strictly below the place value of its
length. -/
private theorem stringValue_lt (b : ℕ) (X : List (Fin b)) :
    stringValue b X < b ^ X.length := by
  induction X with
  | nil => simp [stringValue]
  | cons a X ih =>
    rw [stringValue_cons]
    have ha : a.val < b := a.isLt
    have h1 : a.val * b ^ X.length + stringValue b X < (a.val + 1) * b ^ X.length := by
      have e : (a.val + 1) * b ^ X.length = a.val * b ^ X.length + b ^ X.length := by
        rw [add_mul, one_mul]
      omega
    have h2 : (a.val + 1) * b ^ X.length ≤ b * b ^ X.length :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt ha)
    calc a.val * b ^ X.length + stringValue b X
        < (a.val + 1) * b ^ X.length := h1
      _ ≤ b * b ^ X.length := h2
      _ = b ^ (X.length + 1) := by rw [pow_succ']
      _ = b ^ (a :: X).length := rfl

/-- Two digit strings of the same length with the same value are equal. -/
private theorem eq_of_stringValue_eq (b : ℕ) (hb : 1 < b) :
    ∀ (A A' : List (Fin b)), A.length = A'.length →
      stringValue b A = stringValue b A' → A = A' := by
  intro A
  induction A with
  | nil =>
    intro A' hlen _
    cases A' with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons a A ih =>
    intro A' hlen hval
    cases A' with
    | nil => simp at hlen
    | cons a' A' =>
      simp only [List.length_cons] at hlen
      have hlen' : A.length = A'.length := Nat.succ.inj hlen
      rw [stringValue_cons, stringValue_cons] at hval
      rw [← hlen'] at hval
      have hB : 0 < b ^ A.length := pow_pos (Nat.zero_lt_of_lt hb) _
      have hlt : stringValue b A < b ^ A.length := stringValue_lt b A
      have hlt' : stringValue b A' < b ^ A.length := hlen' ▸ stringValue_lt b A'
      have hdiv : a.val = a'.val := by
        have e1 : (a.val * b ^ A.length + stringValue b A) / b ^ A.length = a.val := by
          apply Nat.div_eq_of_lt_le
          · omega
          · have e : (a.val + 1) * b ^ A.length = a.val * b ^ A.length + b ^ A.length := by
              rw [add_mul, one_mul]
            omega
        have e2 : (a'.val * b ^ A.length + stringValue b A') / b ^ A.length = a'.val := by
          apply Nat.div_eq_of_lt_le
          · omega
          · have e : (a'.val + 1) * b ^ A.length = a'.val * b ^ A.length + b ^ A.length := by
              rw [add_mul, one_mul]
            omega
        rw [hval] at e1
        exact e1.symm.trans e2
      have htail : stringValue b A = stringValue b A' := by
        have e1 : (a.val * b ^ A.length + stringValue b A) % b ^ A.length = stringValue b A :=
          Nat.mul_add_mod_of_lt hlt
        have e2 : (a'.val * b ^ A.length + stringValue b A') % b ^ A.length = stringValue b A' :=
          Nat.mul_add_mod_of_lt hlt'
        rw [hval] at e1
        exact e1.symm.trans e2
      have hA : A = A' := ih A' hlen' htail
      have haa : a = a' := Fin.ext hdiv
      rw [haa, hA]

/-- A digit string whose normalized value lies in the half-open cylinder above
`x` is at least as long as the depth, and begins with the prefix representing
`x`. Shorter strings would contradict the minimality of the depth. -/
private theorem take_eq_of_mem_Ico (b : ℕ) (hb : 1 < b) (x : ℝ) (l : ℕ)
    (hdepth : HasBaseDepth b x l)
    (X : List (Fin b)) (hXlen : X.length = l)
    (hXval : normalizedStringValue b X = x)
    (Y : List (Fin b))
    (hY : normalizedStringValue b Y ∈ Set.Ico x (x + (b : ℝ) ^ (-(l : ℤ)))) :
    l ≤ Y.length ∧ Y.take l = X := by
  obtain ⟨hxy, hyx⟩ := hY
  have hbR : (0 : ℝ) < b := by exact_mod_cast Nat.zero_lt_of_lt hb
  have hBpos : (0 : ℝ) < (b : ℝ) ^ l := pow_pos hbR _
  have hBne : (b : ℝ) ^ l ≠ 0 := pow_ne_zero _ (ne_of_gt hbR)
  have hBx : (b : ℝ) ^ l * x = (stringValue b X : ℝ) := by
    rw [← hXval, normalizedStringValue, hXlen]
    field_simp
  have hz : (b : ℝ) ^ l * (b : ℝ) ^ (-(l : ℤ)) = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ (ne_of_gt hbR)]
    simp
  have hlo : (stringValue b X : ℝ) ≤ (b : ℝ) ^ l * normalizedStringValue b Y := by
    rw [← hBx]
    exact mul_le_mul_of_nonneg_left hxy hBpos.le
  have hhi : (b : ℝ) ^ l * normalizedStringValue b Y < (stringValue b X : ℝ) + 1 := by
    have h := mul_lt_mul_of_pos_left hyx hBpos
    rw [mul_add, hz, hBx] at h
    exact h
  have hlen : l ≤ Y.length := by
    by_contra hle
    have hlt : Y.length < l := by omega
    have hpow : (b : ℝ) ^ l = (b : ℝ) ^ Y.length * (b : ℝ) ^ (l - Y.length) := by
      rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hlt)]
    have hBm : (b : ℝ) ^ Y.length ≠ 0 := pow_ne_zero _ (ne_of_gt hbR)
    have hBy : (b : ℝ) ^ l * normalizedStringValue b Y =
        ((stringValue b Y * b ^ (l - Y.length) : ℕ) : ℝ) := by
      unfold normalizedStringValue
      rw [hpow]
      field_simp
      push_cast
      ring
    have hN : stringValue b Y * b ^ (l - Y.length) = stringValue b X := by
      have e1 : (stringValue b X : ℝ) ≤ ((stringValue b Y * b ^ (l - Y.length) : ℕ) : ℝ) := by
        rw [← hBy]
        exact hlo
      have e2 : ((stringValue b Y * b ^ (l - Y.length) : ℕ) : ℝ) < (stringValue b X : ℝ) + 1 := by
        rw [← hBy]
        exact hhi
      have g1 : stringValue b X ≤ stringValue b Y * b ^ (l - Y.length) := by
        exact_mod_cast e1
      have g2 : stringValue b Y * b ^ (l - Y.length) < stringValue b X + 1 := by
        exact_mod_cast e2
      omega
    have hYx : normalizedStringValue b Y = x := by
      have e : (b : ℝ) ^ l * normalizedStringValue b Y = (b : ℝ) ^ l * x := by
        rw [hBy, hBx]
        exact_mod_cast hN
      exact mul_left_cancel₀ hBne e
    obtain ⟨-, hdepth2⟩ := hdepth
    apply hdepth2 Y.length hlt
    refine ⟨(stringValue b Y : ℤ), ?_⟩
    rw [← hYx]
    unfold normalizedStringValue
    push_cast
    ring
  have htake_len : (Y.take l).length = l := by
    rw [List.length_take]
    omega
  have hYeq : Y.take l ++ Y.drop l = Y := List.take_append_drop _ _
  have hvalY : stringValue b Y =
      stringValue b (Y.take l) * b ^ (Y.drop l).length + stringValue b (Y.drop l) := by
    conv_lhs => rw [← hYeq]
    exact stringValue_append b _ _
  have hylen : Y.length = l + (Y.drop l).length := by
    have h := congrArg List.length hYeq
    simp only [List.length_append, htake_len] at h
    omega
  have hBs : (b : ℝ) ^ (Y.drop l).length ≠ 0 := pow_ne_zero _ (ne_of_gt hbR)
  have hBpY : (b : ℝ) ^ l * normalizedStringValue b Y =
      (stringValue b (Y.take l) : ℝ) +
        (stringValue b (Y.drop l) : ℝ) / (b : ℝ) ^ (Y.drop l).length := by
    unfold normalizedStringValue
    rw [hylen, hvalY, pow_add]
    push_cast
    field_simp
  have hltZ : stringValue b (Y.drop l) < b ^ (Y.drop l).length :=
    stringValue_lt b _
  have hr0 : (0 : ℝ) ≤ (stringValue b (Y.drop l) : ℝ) / (b : ℝ) ^ (Y.drop l).length :=
    div_nonneg (by positivity) (by positivity)
  have hr1 : (stringValue b (Y.drop l) : ℝ) / (b : ℝ) ^ (Y.drop l).length < 1 := by
    rw [div_lt_one (pow_pos hbR _)]
    exact_mod_cast hltZ
  have h1 : (stringValue b X : ℝ) ≤
      (stringValue b (Y.take l) : ℝ) +
        (stringValue b (Y.drop l) : ℝ) / (b : ℝ) ^ (Y.drop l).length := by
    rw [← hBx, ← hBpY]
    exact mul_le_mul_of_nonneg_left hxy hBpos.le
  have h2 : (stringValue b (Y.take l) : ℝ) +
        (stringValue b (Y.drop l) : ℝ) / (b : ℝ) ^ (Y.drop l).length <
      (stringValue b X : ℝ) + 1 := by
    have h := mul_lt_mul_of_pos_left hyx hBpos
    rw [mul_add, hz, hBx, hBpY] at h
    exact h
  have hp : stringValue b (Y.take l) = stringValue b X := by
    have hp1 : (stringValue b (Y.take l) : ℝ) < (stringValue b X : ℝ) + 1 := by linarith
    have hp2 : (stringValue b X : ℝ) < (stringValue b (Y.take l) : ℝ) + 1 := by linarith
    have h1n : stringValue b (Y.take l) < stringValue b X + 1 := by exact_mod_cast hp1
    have h2n : stringValue b X < stringValue b (Y.take l) + 1 := by exact_mod_cast hp2
    omega
  exact ⟨hlen, eq_of_stringValue_eq b hb _ _ (by rw [htake_len, hXlen]) hp⟩

/-- Rescaling a digit string obtained by prepending the endpoint prefix. -/
private theorem affine_eq_of_append (b : ℕ) (hb : 1 < b) (x : ℝ) (l : ℕ)
    (X : List (Fin b)) (hXlen : X.length = l) (hXval : normalizedStringValue b X = x)
    (Z : List (Fin b)) :
    (b : ℝ) ^ l * normalizedStringValue b (X ++ Z) - (b : ℝ) ^ l * x =
      normalizedStringValue b Z := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast Nat.zero_lt_of_lt hb
  have hBx : (b : ℝ) ^ l * x = (stringValue b X : ℝ) := by
    rw [← hXval, normalizedStringValue, hXlen]
    field_simp
  have hval : stringValue b (X ++ Z) =
      stringValue b X * b ^ Z.length + stringValue b Z := stringValue_append b X Z
  unfold normalizedStringValue
  rw [List.length_append, hXlen, hval, pow_add]
  push_cast
  rw [← hBx]
  field_simp
  ring

/-- The weight of a digit string obtained by prepending the endpoint prefix
factors as the prefix weight times the suffix weight. -/
private theorem stringWeight_append (b : ℕ) (hb : 1 < b) (l : ℕ) (X : List (Fin b))
    (hXlen : X.length = l) (Z : List (Fin b)) :
    stringWeight b (X ++ Z) =
      ENNReal.ofReal ((b : ℝ) ^ (-(l : ℤ))) * stringWeight b Z := by
  unfold stringWeight
  rw [List.length_append, hXlen]
  have hcast : (-((l + Z.length : ℕ) : ℤ)) = (-(l : ℤ)) + (-(Z.length : ℤ)) := by
    push_cast
    ring
  have hbRne : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  rw [hcast, zpow_add₀ hbRne]
  rw [ENNReal.ofReal_mul (zpow_nonneg (Nat.cast_nonneg b) _)]

/-- The Irwin measure of a set inside the half-open cylinder, at index at
least the prefix count, is the prefix weight times the Irwin measure of the
rescaled set. -/
private theorem irwinMeasure_eq_smul_of_le (b d : ℕ) (hb : 1 < b) (hd : d < b) (x : ℝ)
    (l : ℕ) (hdepth : HasBaseDepth b x l)
    (X : List (Fin b)) (hXlen : X.length = l)
    (hXval : normalizedStringValue b X = x) (j : ℕ) (hj : j = X.count ⟨d, hd⟩)
    (k : ℕ) (hjk : j ≤ k) (U : Set ℝ)
    (hU : U ⊆ Set.Ico x (x + (b : ℝ) ^ (-(l : ℤ)))) :
    irwinMeasure b d k hd U =
      ENNReal.ofReal ((b : ℝ) ^ (-(l : ℤ))) *
        irwinMeasure b d (k - j) hd (affineScaleSet b l x U) := by
  classical
  have hbR : (0 : ℝ) < b := by exact_mod_cast Nat.zero_lt_of_lt hb
  have hBne : (b : ℝ) ^ l ≠ 0 := pow_ne_zero _ (ne_of_gt hbR)
  have hatom : ∀ (Y : List (Fin b)) (W : Set ℝ),
      stringAtom b Y W = W.indicator (fun _ => stringWeight b Y) (normalizedStringValue b Y) := by
    intro Y W
    unfold stringAtom
    rw [smul_apply]
    simp [Set.indicator]
  set S : Type := {Y : List (Fin b) // Y.count ⟨d, hd⟩ = k} with hS
  set T : Type := {Z : List (Fin b) // Z.count ⟨d, hd⟩ = k - j} with hT
  set V : Set ℝ := affineScaleSet b l x U with hV
  have hchar : ∀ Y : S, normalizedStringValue b Y.1 ∈ U →
      l ≤ Y.1.length ∧ Y.1.take l = X := fun Y hY =>
    take_eq_of_mem_Ico b hb x l hdepth X hXlen hXval Y.1 (hU hY)
  have hYeq : ∀ Y : S, normalizedStringValue b Y.1 ∈ U →
      Y.1 = X ++ Y.1.drop l := by
    intro Y hY
    obtain ⟨-, htake⟩ := hchar Y hY
    calc Y.1 = Y.1.take l ++ Y.1.drop l := (List.take_append_drop _ _).symm
      _ = X ++ Y.1.drop l := by rw [htake]
  have haffine : ∀ (Z : List (Fin b)),
      (b : ℝ) ^ l * normalizedStringValue b (X ++ Z) - (b : ℝ) ^ l * x =
        normalizedStringValue b Z :=
    fun Z => affine_eq_of_append b hb x l X hXlen hXval Z
  let e : {Y : S // normalizedStringValue b Y.1 ∈ U} ≃
      {Z : T // normalizedStringValue b Z.1 ∈ V} :=
    { toFun := fun Y =>
        ⟨⟨Y.1.1.drop l, by
          have h1 : Y.1.1.count ⟨d, hd⟩ =
              (Y.1.1.take l).count ⟨d, hd⟩ + (Y.1.1.drop l).count ⟨d, hd⟩ := by
            conv_lhs => rw [← List.take_append_drop l Y.1.1]
            rw [List.count_append]
          obtain ⟨-, htake⟩ := hchar Y.1 Y.2
          rw [htake] at h1
          have hk : Y.1.1.count ⟨d, hd⟩ = k := Y.1.2
          omega⟩,
         by
          rw [hV, affineScaleSet]
          refine ⟨normalizedStringValue b Y.1.1, Y.2, ?_⟩
          have h := haffine (Y.1.1.drop l)
          rw [← hYeq Y.1 Y.2] at h
          exact h⟩
      invFun := fun Z =>
        ⟨⟨X ++ Z.1.1, by
          rw [List.count_append]
          have hjX : X.count ⟨d, hd⟩ = j := hj.symm
          have hk : Z.1.1.count ⟨d, hd⟩ = k - j := Z.1.2
          omega⟩,
         by
          obtain ⟨y, hyU, hy⟩ := Z.2
          have h := haffine Z.1.1
          have hyeq : y = normalizedStringValue b (X ++ Z.1.1) := by
            have h2 : (b : ℝ) ^ l * y - (b : ℝ) ^ l * x =
                (b : ℝ) ^ l * normalizedStringValue b (X ++ Z.1.1) - (b : ℝ) ^ l * x := by
              rw [h]; exact hy
            have := mul_left_cancel₀ hBne
              (by linarith : (b : ℝ) ^ l * y =
                (b : ℝ) ^ l * normalizedStringValue b (X ++ Z.1.1))
            exact this
          rw [← hyeq]; exact hyU⟩
      left_inv := fun Y => by
        apply Subtype.ext
        apply Subtype.ext
        exact (hYeq Y.1 Y.2).symm
      right_inv := fun Z => by
        apply Subtype.ext
        apply Subtype.ext
        simp [hXlen] }
  have hL : irwinMeasure b d k hd U =
      ∑' Y : {Y : S // normalizedStringValue b Y.1 ∈ U}, stringWeight b Y.1.1 := by
    have hLf : (fun Y : S => stringAtom b Y.1 U) =
        fun Y => ({Y : S | normalizedStringValue b Y.1 ∈ U} : Set S).indicator
          (fun Y => stringWeight b Y.1) Y := by
      funext Y
      rw [hatom]
      by_cases h : normalizedStringValue b Y.1 ∈ U <;>
        simp [Set.indicator, h]
    rw [irwinMeasure, Measure.sum_apply_of_countable, hLf]
    exact (tsum_subtype _ _).symm
  have hR : irwinMeasure b d (k - j) hd V =
      ∑' Z : {Z : T // normalizedStringValue b Z.1 ∈ V}, stringWeight b Z.1.1 := by
    have hRf : (fun Z : T => stringAtom b Z.1 V) =
        fun Z => ({Z : T | normalizedStringValue b Z.1 ∈ V} : Set T).indicator
          (fun Z => stringWeight b Z.1) Z := by
      funext Z
      rw [hatom]
      by_cases h : normalizedStringValue b Z.1 ∈ V <;>
        simp [Set.indicator, h]
    rw [irwinMeasure, Measure.sum_apply_of_countable, hRf]
    exact (tsum_subtype _ _).symm
  have hmain : (∑' Y : {Y : S // normalizedStringValue b Y.1 ∈ U}, stringWeight b Y.1.1) =
      ∑' Z : {Z : T // normalizedStringValue b Z.1 ∈ V},
        ENNReal.ofReal ((b : ℝ) ^ (-(l : ℤ))) * stringWeight b Z.1.1 := by
    rw [← tsum_comp_eq_tsum_of_equiv e
      (fun Z => ENNReal.ofReal ((b : ℝ) ^ (-(l : ℤ))) * stringWeight b Z.1.1)]
    apply tsum_congr
    intro Y
    have h := stringWeight_append b hb l X hXlen (Y.1.1.drop l)
    rw [hYeq Y.1 Y.2]
    exact h
  rw [hL, hR, hmain, ENNReal.tsum_mul_left]

/-- The Irwin measure of a set inside the half-open cylinder vanishes at index
below the prefix count. -/
private theorem irwinMeasure_eq_zero_of_lt (b d : ℕ) (hb : 1 < b) (hd : d < b) (x : ℝ)
    (l : ℕ) (hdepth : HasBaseDepth b x l)
    (X : List (Fin b)) (hXlen : X.length = l)
    (hXval : normalizedStringValue b X = x) (j : ℕ) (hj : j = X.count ⟨d, hd⟩)
    (k : ℕ) (hk : k < j) (U : Set ℝ)
    (hU : U ⊆ Set.Ico x (x + (b : ℝ) ^ (-(l : ℤ)))) :
    irwinMeasure b d k hd U = 0 := by
  classical
  have hatom : ∀ (Y : List (Fin b)) (W : Set ℝ),
      stringAtom b Y W = W.indicator (fun _ => stringWeight b Y) (normalizedStringValue b Y) := by
    intro Y W
    unfold stringAtom
    rw [smul_apply]
    simp [Set.indicator]
  unfold irwinMeasure
  rw [Measure.sum_apply_eq_zero]
  intro Y
  rw [hatom]
  apply Set.indicator_of_notMem
  intro hmem
  obtain ⟨-, htake⟩ :=
    take_eq_of_mem_Ico b hb x l hdepth X hXlen hXval Y.1 (hU hmem)
  have hcount : Y.1.count ⟨d, hd⟩ =
      (Y.1.take l).count ⟨d, hd⟩ + (Y.1.drop l).count ⟨d, hd⟩ := by
    conv_lhs => rw [← List.take_append_drop l Y.1]
    rw [List.count_append]
  rw [htake] at hcount
  have hkY : Y.1.count ⟨d, hd⟩ = k := Y.2
  omega

end irwinMeasure_halfOpen_local_mass

set_option linter.unusedVariables false in
/-- **Local structure of the Irwin measures on cylinders.** Let $b > 1$ and $d < b$ be natural
numbers, and for each natural number $k$ let $\mu_k$ be the Irwin measure of base $b$ and digit
$d$ with index $k$. Let $x \in [0, 1)$ have base-$b$ depth $l$, that is, $l$ is the least natural
number such that $b^l x$ is an integer; let $X$ be a string of $l$ base-$b$ digits, read most
significant digit first, whose value $n(X)$ satisfies $n(X)/b^l = x$; and let $j$ be the number
of occurrences of $d$ in $X$. Then for every $k < j$ the restriction of $\mu_k$ to
$[x, x + b^{-l})$ is the zero measure, and for every $k \ge j$ and every subset
$U \subseteq [x, x + b^{-l})$, as real numbers $\mu_k(U) = b^{-l} \mu_{k-j}(b^l U - b^l x)$,
where $b^l U - b^l x$ is the image of $U$ under $y \mapsto b^l y - b^l x$.

Source: Jean-François Burnol, *Measures for the
Summation of Irwin Series*, INTEGERS 26 (2026), Article A11, Proposition 8. -/
public theorem irwinMeasure_halfOpen_local_mass
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (x : ℝ) (l : ℕ)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (hdepth : HasBaseDepth b x l)
    (X : List (Fin b)) (hXlen : X.length = l)
    (hXval : normalizedStringValue b X = x) (j : ℕ)
    (hj : j = X.count ⟨d, hd⟩) :
    (∀ k, k < j →
      (irwinMeasure b d k hd).restrict
        (Set.Ico x (x + (b : ℝ) ^ (-(l : ℤ)))) = 0) ∧
    (∀ k, j ≤ k → ∀ U : Set ℝ,
      U ⊆ Set.Ico x (x + (b : ℝ) ^ (-(l : ℤ))) →
      (irwinMeasure b d k hd U).toReal =
        (b : ℝ) ^ (-(l : ℤ)) *
          (irwinMeasure b d (k - j) hd
            (affineScaleSet b l x U)).toReal) := by
  refine ⟨?_, ?_⟩
  · intro k hk
    apply Measure.ext
    intro S hS
    rw [Measure.restrict_apply hS,
      irwinMeasure_halfOpen_local_mass.irwinMeasure_eq_zero_of_lt b d hb hd x l
        hdepth X hXlen hXval j hj k hk _ Set.inter_subset_right]
    simp
  · intro k hk U hU
    rw [irwinMeasure_halfOpen_local_mass.irwinMeasure_eq_smul_of_le b d hb hd x l
      hdepth X hXlen hXval j hj k hk U hU, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (zpow_nonneg (Nat.cast_nonneg b) _)]

end MetaMathlibExt
