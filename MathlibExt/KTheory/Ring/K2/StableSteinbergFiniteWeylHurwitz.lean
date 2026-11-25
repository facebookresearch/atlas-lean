/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Logic.Relation

/-! # Pure permutation labeled right-Hurwitz shortening

For `n : ℕ`, an ordered distinct endpoint label `SwapLabel n` denotes the
`Equiv.swap` of its endpoints, `wordProd` is the head-left ordered product
(`[] ↦ 1`, `(l :: ws) ↦ swapDenote l * wordProd ws`), `conjLabel b a` applies
the conjugator denotation `swapDenote b` to both victim endpoints, one directed
right step sends `pre ++ [a, b] ++ suf` to `pre ++ [b, conjLabel b a] ++ suf`,
and `HurwitzReach` is its reflexive-transitive closure. The right move alone
bubbles a point-mover right past a point-fixer while preserving mover status,
which drives the selected point-elimination proof: choose a point moved by the
first label, group the first two movers by pushing the first right, stop when
their denotations agree, otherwise squeeze two distinct movers so the fixed-point
mover count drops; a single mover contradicts product one. Termination is strong
induction on that mover count. The empty word has product one but no pair, so
the main theorem requires a nonempty hypothesis. Purpose: coefficient-free
permutation prerequisite driving the finite-Weyl boundary lift. Nonclaims: no
Weyl-group, torus, cocycle, finite containment, kernel generation, global TWT,
or Matsumoto claim.
-/

@[expose] public section

namespace AlgebraicKTheory

/-- Ordered distinct endpoint label: a pair of `Fin n` endpoints with
`p.1 ≠ p.2`. Order is retained so `(a, b)` and `(b, a)` are distinct labels
with equal denotations. Purpose: labeled transposition input. Nonclaims: no
Weyl, torus, or Matsumoto content. -/
public def SwapLabel (n : ℕ) : Type :=
  { p : Fin n × Fin n // p.1 ≠ p.2 }

/-- Swap denotation of a label: `Equiv.swap` of its two endpoints. Purpose:
permutation meaning of a label. Nonclaims: no Weyl or torus meaning. -/
public def swapDenote {n : ℕ} (l : SwapLabel n) : Equiv.Perm (Fin n) :=
  Equiv.swap l.val.1 l.val.2

/-- Head-left labeled word product: `[] ↦ 1`, `(l :: ws) ↦ swapDenote l *
wordProd ws`. Orientation is head-left throughout, matching the accepted
`List.ofFn`/`List.prod` word order. The empty word gives `1`. Purpose:
permutation product input. Nonclaims: no Weyl evaluation or Matsumoto claim. -/
public def wordProd {n : ℕ} : List (SwapLabel n) → Equiv.Perm (Fin n)
  | [] => 1
  | l :: ws => swapDenote l * wordProd ws

/-- Conjugated label: apply the conjugator denotation to both victim endpoints.
Distinctness is preserved by injectivity of the conjugator. Purpose: right-move
output label. Nonclaims: no Weyl conjugation claim. -/
public def conjLabel {n : ℕ} (b a : SwapLabel n) : SwapLabel n :=
  ⟨(swapDenote b a.val.1, swapDenote b a.val.2),
    fun h => a.property ((swapDenote b).injective h)⟩

/-- One directed right-Hurwitz step with explicit context: `pre ++ [a, b] ++ suf`
rewrites to `pre ++ [b, conjLabel b a] ++ suf`. Only the right move is exposed
because it alone bubbles a mover past a fixer in the point-elimination proof.
Purpose: atomic product-preserving move. Nonclaims: no reverse, left, symmetric
closure, or Coxeter abstraction. -/
public inductive HurwitzStep {n : ℕ} :
    List (SwapLabel n) → List (SwapLabel n) → Prop
  | step (pre suf : List (SwapLabel n)) (a b : SwapLabel n) :
      HurwitzStep (pre ++ [a, b] ++ suf) (pre ++ [b, conjLabel b a] ++ suf)

/-- Hurwitz reachability: reflexive-transitive closure of `HurwitzStep`, with no
symmetric closure. Purpose: multi-step trace. Nonclaims: no symmetric or
generate-equivalence closure. -/
public def HurwitzReach {n : ℕ} (w w' : List (SwapLabel n)) : Prop :=
  Relation.ReflTransGen (@HurwitzStep n) w w'

/-- A label denotation is an involution. -/
private theorem swapDenote_mul_self {n : ℕ} (l : SwapLabel n) :
    swapDenote l * swapDenote l = 1 :=
  Equiv.swap_mul_self _ _

/-- A label denotation is self-inverse. -/
private theorem swapDenote_inv_self {n : ℕ} (l : SwapLabel n) :
    (swapDenote l)⁻¹ = swapDenote l :=
  Equiv.swap_inv _ _

/-- Denotation of a conjugated label is conjugation. -/
private theorem conjDenote {n : ℕ} (b a : SwapLabel n) :
    swapDenote (conjLabel b a) =
      swapDenote b * swapDenote a * (swapDenote b)⁻¹ :=
  Equiv.swap_apply_apply (swapDenote b) a.val.1 a.val.2

/-- Conjugation unfolds with the involution. -/
private theorem conjDenote_mul {n : ℕ} (b a : SwapLabel n) :
    swapDenote (conjLabel b a) =
      swapDenote b * swapDenote a * swapDenote b := by
  rw [conjDenote, swapDenote_inv_self]

/-- Appending words multiplies products head-left. -/
private theorem wordProd_append {n : ℕ} (l₁ l₂ : List (SwapLabel n)) :
    wordProd (l₁ ++ l₂) = wordProd l₁ * wordProd l₂ := by
  induction l₁ with
  | nil => simp [wordProd]
  | cons x xs ih => simp [wordProd, ih, mul_assoc]

/-- The right pair preserves its product: `b * (b * a * b) = a * b` since
`b` is an involution. -/
private theorem pair_prod {n : ℕ} (a b : SwapLabel n) :
    swapDenote a * swapDenote b =
      swapDenote b * swapDenote (conjLabel b a) := by
  have hc : swapDenote (conjLabel b a) =
      swapDenote b * swapDenote a * swapDenote b :=
    conjDenote_mul b a
  rw [hc, ← mul_assoc, ← mul_assoc, swapDenote_mul_self, one_mul]

/-- A Hurwitz step preserves the word product. -/
private theorem step_prod {n : ℕ} (pre suf : List (SwapLabel n))
    (a b : SwapLabel n) :
    wordProd (pre ++ [a, b] ++ suf) =
      wordProd (pre ++ [b, conjLabel b a] ++ suf) := by
  have hpair : swapDenote a * swapDenote b =
      swapDenote b * swapDenote (conjLabel b a) :=
    pair_prod a b
  have h1 : wordProd (pre ++ [a, b] ++ suf) =
      wordProd pre * (swapDenote a * (swapDenote b * wordProd suf)) := by
    simp [wordProd_append, wordProd]
  have h2 : wordProd (pre ++ [b, conjLabel b a] ++ suf) =
      wordProd pre *
        (swapDenote b * (swapDenote (conjLabel b a) * wordProd suf)) := by
    simp [wordProd_append, wordProd]
  have he : (swapDenote a * (swapDenote b * wordProd suf)) =
      (swapDenote b * (swapDenote (conjLabel b a) * wordProd suf)) := by
    rw [← mul_assoc, ← mul_assoc, hpair]
  rw [h1, h2, he]

/-- Reachability preserves the word product. -/
private theorem reach_prod {n : ℕ} {w w' : List (SwapLabel n)}
    (h : HurwitzReach w w') : wordProd w = wordProd w' := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    cases hstep with
    | step pre suf a b =>
      exact ih.trans (step_prod pre suf a b)

/-- A Hurwitz step preserves length. -/
private theorem step_length {n : ℕ} (pre suf : List (SwapLabel n))
    (a b : SwapLabel n) :
    (pre ++ [a, b] ++ suf).length = (pre ++ [b, conjLabel b a] ++ suf).length := by
  simp

/-- Reachability preserves length. -/
private theorem reach_length {n : ℕ} {w w' : List (SwapLabel n)}
    (h : HurwitzReach w w') : w.length = w'.length := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    cases hstep with
    | step pre suf a b =>
      exact ih.trans (step_length pre suf a b)

/-- A single step is reachable. -/
private theorem reach_single {n : ℕ} {w w' : List (SwapLabel n)}
    (h : HurwitzStep w w') : HurwitzReach w w' :=
  Relation.ReflTransGen.single h

/-- Reachability composes. -/
private theorem reach_trans {n : ℕ} {w w₁ w' : List (SwapLabel n)}
    (h : HurwitzReach w w₁) (h' : HurwitzReach w₁ w') : HurwitzReach w w' :=
  Relation.ReflTransGen.trans h h'

/-- A label moves exactly its two endpoints. -/
private theorem swap_moves_iff {n : ℕ} (l : SwapLabel n) (p : Fin n) :
    swapDenote l p ≠ p ↔ p = l.val.1 ∨ p = l.val.2 := by
  simp [swapDenote, Equiv.swap_apply_ne_self_iff, l.property]

/-- Fixed-point mover count for one point. -/
private def moverCount {n : ℕ} (p : Fin n) : List (SwapLabel n) → ℕ
  | [] => 0
  | l :: ws =>
    if swapDenote l p = p then moverCount p ws else moverCount p ws + 1

/-- Mover count unfolds on a fixing head. -/
private theorem moverCount_cons_fix {n : ℕ} (p : Fin n) (l : SwapLabel n)
    (ws : List (SwapLabel n)) (h : swapDenote l p = p) :
    moverCount p (l :: ws) = moverCount p ws := by
  simp [moverCount, h]

/-- Mover count unfolds on a moving head. -/
private theorem moverCount_cons_move {n : ℕ} (p : Fin n) (l : SwapLabel n)
    (ws : List (SwapLabel n)) (h : swapDenote l p ≠ p) :
    moverCount p (l :: ws) = moverCount p ws + 1 := by
  simp [moverCount, h]

/-- Mover count adds over append. -/
private theorem moverCount_append {n : ℕ} (p : Fin n)
    (l₁ l₂ : List (SwapLabel n)) :
    moverCount p (l₁ ++ l₂) = moverCount p l₁ + moverCount p l₂ := by
  induction l₁ with
  | nil => simp [moverCount]
  | cons x xs ih =>
    by_cases h : swapDenote x p = p
    · simp [moverCount, h, ih]
    · simp [moverCount, h, ih]
      omega

/-- All-fixing words have zero movers. -/
private theorem moverCount_all_fix_zero {n : ℕ} (p : Fin n)
    (w : List (SwapLabel n)) (h : ∀ x ∈ w, swapDenote x p = p) :
    moverCount p w = 0 := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    have hx : swapDenote x p = p := h x List.mem_cons_self
    have hs : ∀ y ∈ xs, swapDenote y p = p := fun y hy =>
      h y (List.mem_cons_of_mem x hy)
    rw [moverCount_cons_fix p x xs hx, ih hs]

/-- Zero movers means every label fixes the point. -/
private theorem moverCount_zero_all_fix {n : ℕ} (p : Fin n)
    (w : List (SwapLabel n)) (h : moverCount p w = 0) :
    ∀ x ∈ w, swapDenote x p = p := by
  induction w with
  | nil => exact fun x hx => absurd hx (by simp)
  | cons x xs ih =>
    intro y hy
    by_cases hx : swapDenote x p = p
    · have h' : y = x ∨ y ∈ xs := List.mem_cons.mp hy
      cases h' with
      | inl heq =>
        cases heq
        exact hx
      | inr hmem =>
        have hxs : moverCount p xs = 0 := by
          have : moverCount p (x :: xs) = moverCount p xs := moverCount_cons_fix p x xs hx
          omega
        exact ih hxs y hmem
    · have : moverCount p (x :: xs) = moverCount p xs + 1 :=
        moverCount_cons_move p x xs hx
      omega

/-- Inverses preserve fixed points. -/
private theorem inv_fixes {n : ℕ} (f : Equiv.Perm (Fin n)) (p : Fin n)
    (h : f p = p) : f⁻¹ p = p := by
  have h2 : f⁻¹ (f p) = p := Equiv.symm_apply_apply f p
  have h3 : f⁻¹ p = f⁻¹ (f p) := congrArg (⇑f⁻¹) h.symm
  exact h3.trans h2

/-- Products of fixers fix the point. -/
private theorem product_all_fix_fixes {n : ℕ} (p : Fin n)
    (w : List (SwapLabel n)) (h : ∀ x ∈ w, swapDenote x p = p) :
    wordProd w p = p := by
  induction w with
  | nil => simp [wordProd]
  | cons x xs ih =>
    have hx : swapDenote x p = p := h x List.mem_cons_self
    have hs : ∀ y ∈ xs, swapDenote y p = p := fun y hy =>
      h y (List.mem_cons_of_mem x hy)
    have ih' : wordProd xs p = p := ih hs
    change (swapDenote x * wordProd xs) p = p
    rw [Equiv.Perm.mul_apply, ih', hx]

/-- A word with exactly one mover splits around it. -/
private theorem singleton_split {n : ℕ} (p : Fin n) (w : List (SwapLabel n))
    (h : moverCount p w = 1) :
    ∃ pre m suf, w = pre ++ [m] ++ suf ∧ swapDenote m p ≠ p ∧
      (∀ x ∈ pre, swapDenote x p = p) ∧ ∀ x ∈ suf, swapDenote x p = p := by
  induction w with
  | nil => simp [moverCount] at h
  | cons x xs ih =>
    by_cases hx : swapDenote x p = p
    · have hxs : moverCount p xs = 1 := by
        have : moverCount p (x :: xs) = moverCount p xs :=
          moverCount_cons_fix p x xs hx
        omega
      obtain ⟨pre, m, suf, heq, hm, hpre, hsuf⟩ := ih hxs
      exact ⟨x :: pre, m, suf, by simp [heq],
        hm, fun y hy => by
          have h' : y = x ∨ y ∈ pre := List.mem_cons.mp hy
          cases h' with
          | inl heq2 =>
            cases heq2
            exact hx
          | inr hmem => exact hpre y hmem, hsuf⟩
    · have hxs : moverCount p xs = 0 := by
        have : moverCount p (x :: xs) = moverCount p xs + 1 :=
          moverCount_cons_move p x xs hx
        omega
      have hsuf : ∀ y ∈ xs, swapDenote y p = p :=
        moverCount_zero_all_fix p xs hxs
      exact ⟨[], x, xs, by simp, hx,
        fun y hy => absurd hy (by simp), hsuf⟩

/-- Exactly one mover contradicts product one. -/
private theorem exactly_one_false {n : ℕ} (p : Fin n) (w : List (SwapLabel n))
    (hcount : moverCount p w = 1) (hprod : wordProd w = 1) : False := by
  obtain ⟨pre, m, suf, heq, hm, hpre, hsuf⟩ := singleton_split p w hcount
  have hA : wordProd pre p = p := product_all_fix_fixes p pre hpre
  have hB : wordProd suf p = p := product_all_fix_fixes p suf hsuf
  have hAi : (wordProd pre)⁻¹ p = p := inv_fixes _ p hA
  have hBi : (wordProd suf)⁻¹ p = p := inv_fixes _ p hB
  have hprodW : wordProd pre * (swapDenote m * wordProd suf) = 1 := by
    have : wordProd (pre ++ [m] ++ suf) =
        wordProd pre * (swapDenote m * wordProd suf) := by
      simp [wordProd_append, wordProd]
    rw [← heq] at this
    rw [this] at hprod
    exact hprod
  have hmul : swapDenote m * wordProd suf = (wordProd pre)⁻¹ := by
    have h1 : (wordProd pre)⁻¹ * (wordProd pre * (swapDenote m * wordProd suf)) =
        (wordProd pre)⁻¹ * 1 := by rw [hprodW]
    simp only [← mul_assoc, inv_mul_cancel, one_mul, mul_one] at h1
    exact h1
  have hmEq : swapDenote m = (wordProd pre)⁻¹ * (wordProd suf)⁻¹ := by
    have h2 : (swapDenote m * wordProd suf) * (wordProd suf)⁻¹ =
        (wordProd pre)⁻¹ * (wordProd suf)⁻¹ := by rw [hmul]
    simp only [mul_assoc, mul_inv_cancel, mul_one] at h2
    exact h2
  have hfix : swapDenote m p = p := by
    rw [hmEq, Equiv.Perm.mul_apply, hBi, hAi]
  exact hm hfix

/-- A word with a mover splits off its first mover. -/
private theorem first_mover_split {n : ℕ} (p : Fin n) (w : List (SwapLabel n))
    (h : 1 ≤ moverCount p w) :
    ∃ pre m suf, w = pre ++ [m] ++ suf ∧ (∀ x ∈ pre, swapDenote x p = p) ∧
      swapDenote m p ≠ p := by
  induction w with
  | nil => simp [moverCount] at h
  | cons x xs ih =>
    by_cases hx : swapDenote x p = p
    · have hxs : 1 ≤ moverCount p xs := by
        have : moverCount p (x :: xs) = moverCount p xs :=
          moverCount_cons_fix p x xs hx
        omega
      obtain ⟨pre, m, suf, heq, hpre, hm⟩ := ih hxs
      exact ⟨x :: pre, m, suf, by simp [heq],
        fun y hy => by
          have h' : y = x ∨ y ∈ pre := List.mem_cons.mp hy
          cases h' with
          | inl heq2 =>
            cases heq2
            exact hx
          | inr hmem => exact hpre y hmem, hm⟩
    · exact ⟨[], x, xs, by simp, fun y hy => absurd hy (by simp), hx⟩

/-- A word with two movers splits off its first two movers. -/
private theorem first_two_movers_split {n : ℕ} (p : Fin n)
    (w : List (SwapLabel n)) (h : 2 ≤ moverCount p w) :
    ∃ pre m mid m₂ suf, w = pre ++ [m] ++ mid ++ [m₂] ++ suf ∧
      (∀ x ∈ pre, swapDenote x p = p) ∧ swapDenote m p ≠ p ∧
      (∀ x ∈ mid, swapDenote x p = p) ∧ swapDenote m₂ p ≠ p := by
  have h1 : 1 ≤ moverCount p w := by omega
  obtain ⟨pre, m, rest, heq, hpre, hm⟩ := first_mover_split p w h1
  have hcount : moverCount p w = moverCount p pre + (moverCount p rest + 1) := by
    have e1 : w = pre ++ ([m] ++ rest) := by
      simp [heq, List.append_assoc]
    have e2 : moverCount p ([m] ++ rest) = moverCount p rest + 1 := by
      have : moverCount p ([m] ++ rest) = moverCount p (m :: rest) := by simp
      rw [this]
      have : moverCount p (m :: rest) = moverCount p rest + 1 :=
        moverCount_cons_move p m rest hm
      exact this
    rw [e1, moverCount_append, e2]
  have hzero : moverCount p pre = 0 := moverCount_all_fix_zero p pre hpre
  have hrest : 1 ≤ moverCount p rest := by omega
  obtain ⟨mid, m₂, suf, heq2, hmid, hm₂⟩ := first_mover_split p rest hrest
  exact ⟨pre, m, mid, m₂, suf,
    by simp [heq, heq2, List.append_assoc],
    hpre, hm, hmid, hm₂⟩

/-- Pushing a mover right past a fixer preserves mover status: the right move
`(m, f) ↦ (f, f * m * f)` sends a fixer left and keeps a mover on the right,
since the conjugator fixes `p`. -/
private theorem conj_fix_move {n : ℕ} (p : Fin n) (f m : SwapLabel n)
    (hf : swapDenote f p = p) (hm : swapDenote m p ≠ p) :
    swapDenote (conjLabel f m) p ≠ p := by
  have hfinj : Function.Injective (swapDenote f) := (swapDenote f).injective
  have hd : swapDenote (conjLabel f m) =
      swapDenote f * swapDenote m * swapDenote f :=
    conjDenote_mul f m
  have e : (swapDenote f * swapDenote m * swapDenote f) p =
      swapDenote f (swapDenote m p) := by
    show ((swapDenote f * swapDenote m) * swapDenote f) p = _
    rw [Equiv.Perm.mul_apply, hf, Equiv.Perm.mul_apply]
  have hne : swapDenote f (swapDenote m p) ≠ p := by
    intro hcon
    have h2 : swapDenote f (swapDenote m p) = swapDenote f p := by
      rw [hcon, hf]
    exact hm (hfinj h2)
  rw [hd, e]
  exact hne

/-- Squeezing two distinct movers fixes the point: for `q = b(p)`, distinctness
forces `a` to fix `q`, so `(b * a * b)(p) = p` by group calculation. -/
private theorem conj_distinct_fix {n : ℕ} (p : Fin n) (a b : SwapLabel n)
    (ha : swapDenote a p ≠ p) (hb : swapDenote b p ≠ p)
    (hne : swapDenote a ≠ swapDenote b) :
    swapDenote (conjLabel b a) p = p := by
  have hpq : p ≠ swapDenote b p := Ne.symm hb
  have hbOr : p = b.val.1 ∨ p = b.val.2 := (swap_moves_iff b p).mp hb
  have hb_swap : swapDenote b = Equiv.swap p (swapDenote b p) := by
    cases hbOr with
    | inl hb1 =>
      have e : swapDenote b p = b.val.2 := by
        change Equiv.swap b.val.1 b.val.2 p = _
        rw [hb1]
        exact Equiv.swap_apply_left _ _
      change Equiv.swap b.val.1 b.val.2 = _
      rw [e, hb1]
    | inr hb2 =>
      have e : swapDenote b p = b.val.1 := by
        change Equiv.swap b.val.1 b.val.2 p = _
        rw [hb2]
        exact Equiv.swap_apply_right _ _
      change Equiv.swap b.val.1 b.val.2 = _
      rw [e, hb2, Equiv.swap_comm]
  have haq : swapDenote a (swapDenote b p) = swapDenote b p := by
    by_contra hcon
    have hmove_q : swapDenote a (swapDenote b p) ≠ swapDenote b p := hcon
    have hqOr : swapDenote b p = a.val.1 ∨ swapDenote b p = a.val.2 :=
      (swap_moves_iff a (swapDenote b p)).mp hmove_q
    have haOr : p = a.val.1 ∨ p = a.val.2 := (swap_moves_iff a p).mp ha
    have ha_swap : swapDenote a = Equiv.swap p (swapDenote b p) := by
      cases haOr with
      | inl ha1 =>
        cases hqOr with
        | inl hq1 =>
          have : p = swapDenote b p := ha1.trans hq1.symm
          exact absurd this hpq
        | inr hq2 =>
          change Equiv.swap a.val.1 a.val.2 = _
          rw [← ha1, ← hq2]
      | inr ha2 =>
        cases hqOr with
        | inl hq1 =>
          change Equiv.swap a.val.1 a.val.2 = _
          rw [← hq1, ← ha2, Equiv.swap_comm]
        | inr hq2 =>
          have : p = swapDenote b p := ha2.trans hq2.symm
          exact absurd this hpq
    exact hne (ha_swap.trans hb_swap.symm)
  have hbb : swapDenote b (swapDenote b p) = p := by
    have h1 : (swapDenote b * swapDenote b) p = (1 : Equiv.Perm (Fin n)) p := by
      rw [swapDenote_mul_self]
    rw [Equiv.Perm.mul_apply] at h1
    simpa using h1
  have hc : swapDenote (conjLabel b a) =
      swapDenote b * swapDenote a * swapDenote b :=
    conjDenote_mul b a
  calc swapDenote (conjLabel b a) p
      = (swapDenote b * swapDenote a * swapDenote b) p := by rw [hc]
    _ = swapDenote b (swapDenote a (swapDenote b p)) := by
        show ((swapDenote b * swapDenote a) * swapDenote b) p = _
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    _ = swapDenote b (swapDenote b p) := by rw [haq]
    _ = p := hbb

/-- Push the first mover right past intervening fixers, grouping it with the
second mover. Only right `(mover, fixer)` steps are used, so mover status is
preserved by `conj_fix_move`. -/
private theorem bubble_push {n : ℕ} (p : Fin n) (pre mid : List (SwapLabel n))
    (m : SwapLabel n) (rest : List (SwapLabel n))
    (hm : swapDenote m p ≠ p)
    (hmid : ∀ x ∈ mid, swapDenote x p = p) :
    ∃ m', HurwitzReach (pre ++ [m] ++ mid ++ rest)
      (pre ++ mid ++ [m'] ++ rest) ∧ swapDenote m' p ≠ p := by
  induction mid generalizing pre m with
  | nil =>
    have e : pre ++ [m] ++ ([] : List (SwapLabel n)) ++ rest =
        pre ++ [] ++ [m] ++ rest := by
      simp [List.append_assoc]
    exact ⟨m, by rw [e]; exact Relation.ReflTransGen.refl, hm⟩
  | cons f fs ih =>
    have hf : swapDenote f p = p := hmid f List.mem_cons_self
    have hfs : ∀ x ∈ fs, swapDenote x p = p := fun x hx =>
      hmid x (List.mem_cons_of_mem f hx)
    have hm1 : swapDenote (conjLabel f m) p ≠ p := conj_fix_move p f m hf hm
    have hform : pre ++ [m] ++ (f :: fs) ++ rest =
        pre ++ [m, f] ++ (fs ++ rest) := by
      simp [List.append_assoc]
    have hstep : HurwitzStep (pre ++ [m] ++ (f :: fs) ++ rest)
        (pre ++ [f, conjLabel f m] ++ (fs ++ rest)) := by
      rw [hform]
      exact HurwitzStep.step pre (fs ++ rest) m f
    have hreach1 : HurwitzReach (pre ++ [m] ++ (f :: fs) ++ rest)
        (pre ++ [f, conjLabel f m] ++ (fs ++ rest)) :=
      reach_single hstep
    have hnorm : pre ++ [f, conjLabel f m] ++ (fs ++ rest) =
        (pre ++ [f]) ++ [conjLabel f m] ++ fs ++ rest := by
      simp [List.append_assoc]
    rw [hnorm] at hreach1
    obtain ⟨m', hreach2, hm'⟩ := ih (pre ++ [f]) (conjLabel f m) hm1 hfs
    have htarget : pre ++ [f] ++ fs ++ [m'] ++ rest =
        pre ++ (f :: fs) ++ [m'] ++ rest := by
      simp [List.append_assoc]
    rw [htarget] at hreach2
    exact ⟨m', reach_trans hreach1 hreach2, hm'⟩

/-- Deleted adjacent equal denotations preserve product one. -/
private theorem deleted_prod_one {n : ℕ} (pre : List (SwapLabel n))
    (t₁ t₂ : SwapLabel n) (suf : List (SwapLabel n))
    (hprod : wordProd (pre ++ [t₁, t₂] ++ suf) = 1)
    (heq : swapDenote t₁ = swapDenote t₂) :
    wordProd (pre ++ suf) = 1 := by
  have h1 : wordProd (pre ++ [t₁, t₂] ++ suf) =
      wordProd pre * ((swapDenote t₁ * swapDenote t₂) * wordProd suf) := by
    simp [wordProd_append, wordProd, mul_assoc]
  have hpair : swapDenote t₁ * swapDenote t₂ = 1 := by
    rw [heq, swapDenote_mul_self]
  rw [h1, hpair, one_mul] at hprod
  have h2 : wordProd (pre ++ suf) = wordProd pre * wordProd suf :=
    wordProd_append pre suf
  rw [h2]
  exact hprod

/-- Inner point-elimination: for a fixed point, strong induction on mover count
finds a reachable adjacent equal-denotation pair with deleted product one. -/
private theorem aux_exists {n : ℕ} (p : Fin n) :
    ∀ (k : ℕ) (w : List (SwapLabel n)), moverCount p w = k → 2 ≤ k →
      wordProd w = 1 → w ≠ [] →
      ∃ pre t₁ t₂ suf, HurwitzReach w (pre ++ [t₁, t₂] ++ suf) ∧
        swapDenote t₁ = swapDenote t₂ ∧ wordProd (pre ++ suf) = 1 ∧
        w.length = (pre ++ suf).length + 2 := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro w hk h2 hprod hne
    obtain ⟨pre, m, mid, m₂, suf, heq, hpre, hm, hmid, hm₂⟩ :=
      first_two_movers_split p w (by omega)
    obtain ⟨mstar, hreachB, hmstar⟩ := bubble_push p pre mid m ([m₂] ++ suf) hm
      (fun x hx => hmid x hx)
    have hgroup : HurwitzReach w (pre ++ mid ++ [mstar, m₂] ++ suf) := by
      have eW : w = pre ++ [m] ++ mid ++ ([m₂] ++ suf) := by
        simp [heq, List.append_assoc]
      have eT : pre ++ mid ++ [mstar] ++ ([m₂] ++ suf) =
          pre ++ mid ++ [mstar, m₂] ++ suf := by
        simp [List.append_assoc]
      rw [← eW, eT] at hreachB
      exact hreachB
    have hprodG : wordProd (pre ++ mid ++ [mstar, m₂] ++ suf) = 1 := by
      have hpg : wordProd w = wordProd (pre ++ mid ++ [mstar, m₂] ++ suf) :=
        reach_prod hgroup
      rw [← hpg]
      exact hprod
    by_cases heqD : swapDenote mstar = swapDenote m₂
    · have hlen : w.length = (pre ++ mid ++ suf).length + 2 := by
        have h1 : (pre ++ mid ++ [mstar, m₂] ++ suf).length =
            (pre ++ mid ++ suf).length + 2 := by
          simp
          omega
        have hlenW : w.length = (pre ++ mid ++ [mstar, m₂] ++ suf).length :=
          reach_length hgroup
        omega
      exact ⟨pre ++ mid, mstar, m₂, suf, hgroup, heqD,
        deleted_prod_one _ _ _ _ hprodG heqD, hlen⟩
    · have hcfix : swapDenote (conjLabel m₂ mstar) p = p :=
        conj_distinct_fix p mstar m₂ hmstar hm₂ heqD
      have hstep : HurwitzStep (pre ++ mid ++ [mstar, m₂] ++ suf)
          (pre ++ mid ++ [m₂, conjLabel m₂ mstar] ++ suf) :=
        HurwitzStep.step (pre ++ mid) suf mstar m₂
      have hreachS : HurwitzReach (pre ++ mid ++ [mstar, m₂] ++ suf)
          (pre ++ mid ++ [m₂, conjLabel m₂ mstar] ++ suf) :=
        reach_single hstep
      have hreachW : HurwitzReach w
          (pre ++ mid ++ [m₂, conjLabel m₂ mstar] ++ suf) :=
        reach_trans hgroup hreachS
      have hprodS : wordProd (pre ++ mid ++ [m₂, conjLabel m₂ mstar] ++ suf) = 1 := by
        have hps : wordProd w =
            wordProd (pre ++ mid ++ [m₂, conjLabel m₂ mstar] ++ suf) :=
          reach_prod hreachW
        rw [← hps]
        exact hprod
      have hcountS : moverCount p (pre ++ mid ++ [m₂, conjLabel m₂ mstar] ++ suf) =
          moverCount p w - 1 := by
        have eW : moverCount p w =
            moverCount p pre + 1 + (moverCount p mid + (1 + moverCount p suf)) := by
          have e0 : w = pre ++ ([m] ++ (mid ++ ([m₂] ++ suf))) := by
            simp [heq, List.append_assoc]
          rw [e0, moverCount_append, moverCount_append, moverCount_append,
            moverCount_append]
          have h0 : moverCount p pre = 0 := moverCount_all_fix_zero p pre hpre
          have h1 : moverCount p mid = 0 := moverCount_all_fix_zero p mid hmid
          have hm1 : moverCount p [m] = 1 := by
            have h1 : ¬ swapDenote m p = p := hm
            have e : moverCount p [m] = moverCount p (m :: []) := by simp
            rw [e]
            simp [moverCount, h1]
          have hm2 : moverCount p [m₂] = 1 := by
            have h1 : ¬ swapDenote m₂ p = p := hm₂
            have e : moverCount p [m₂] = moverCount p (m₂ :: []) := by simp
            rw [e]
            simp [moverCount, h1]
          have eM : moverCount p [m] = 1 := hm1
          have eM2 : moverCount p [m₂] = 1 := hm2
          omega
        have eS : moverCount p (pre ++ mid ++ [m₂, conjLabel m₂ mstar] ++ suf) =
            moverCount p pre + (moverCount p mid + (1 + moverCount p suf)) := by
          have e0 : pre ++ mid ++ [m₂, conjLabel m₂ mstar] ++ suf =
              pre ++ (mid ++ ([m₂] ++ ([conjLabel m₂ mstar] ++ suf))) := by
            simp [List.append_assoc]
          rw [e0, moverCount_append, moverCount_append, moverCount_append,
            moverCount_append]
          have h0 : moverCount p pre = 0 := moverCount_all_fix_zero p pre hpre
          have h1 : moverCount p mid = 0 := moverCount_all_fix_zero p mid hmid
          have hc0 : moverCount p [conjLabel m₂ mstar] = 0 := by
            have : moverCount p [conjLabel m₂ mstar] =
                moverCount p ((conjLabel m₂ mstar) :: []) := by simp
            rw [this]
            simp [moverCount, hcfix]
          have hm2 : moverCount p [m₂] = 1 := by
            have : moverCount p [m₂] = moverCount p (m₂ :: []) := by simp
            rw [this]
            have h1 : ¬ swapDenote m₂ p = p := hm₂
            simp [moverCount, h1]
          omega
        omega
      have hlt : moverCount p (pre ++ mid ++ [m₂, conjLabel m₂ mstar] ++ suf) < k := by
        omega
      have hneS : pre ++ mid ++ [m₂, conjLabel m₂ mstar] ++ suf ≠ [] := by
        intro hcon
        have hlen0 : (pre ++ mid ++ [m₂, conjLabel m₂ mstar] ++ suf).length = 0 :=
          congrArg List.length hcon
        have hlenW : w.length =
            (pre ++ mid ++ [m₂, conjLabel m₂ mstar] ++ suf).length :=
          reach_length hreachW
        rw [hlen0] at hlenW
        exact hne (List.length_eq_zero_iff.mp hlenW)
      by_cases h2S : 2 ≤ moverCount p (pre ++ mid ++ [m₂, conjLabel m₂ mstar] ++ suf)
      · obtain ⟨pre0, t₁, t₂, suf0, hreach0, heq0, hprod0, hlen0⟩ :=
          ih _ hlt _ rfl h2S hprodS hneS
        have hlenW : w.length =
            (pre ++ mid ++ [m₂, conjLabel m₂ mstar] ++ suf).length :=
          reach_length hreachW
        have hlen : w.length = (pre0 ++ suf0).length + 2 := by omega
        exact ⟨pre0, t₁, t₂, suf0, reach_trans hreachW hreach0, heq0, hprod0, hlen⟩
      · exfalso
        have hone : moverCount p (pre ++ mid ++ [m₂, conjLabel m₂ mstar] ++ suf) = 1 := by
          omega
        exact exactly_one_false _ _ hone hprodS

/-- Main shortening step: a nonempty product-one labeled word reaches an
adjacent equal-denotation pair whose deletion stays product-one with exact
two-letter length drop. Equality is of denotations, not labels, so `(a, b)`
and `(b, a)` count as equal. The empty word has product one but no pair, hence
the nonempty hypothesis. Purpose: one-step Hurwitz shortening input for the
finite-Weyl boundary lift. Nonclaims: no Weyl, torus, cocycle, finite
containment, kernel generation, global TWT, or Matsumoto claim. -/
public theorem exists_hurwitz_adjacent_equal {n : ℕ} (w : List (SwapLabel n))
    (hne : w ≠ []) (hprod : wordProd w = 1) :
    ∃ pre t₁ t₂ suf, HurwitzReach w (pre ++ [t₁, t₂] ++ suf) ∧
      swapDenote t₁ = swapDenote t₂ ∧ wordProd (pre ++ suf) = 1 ∧
      w.length = (pre ++ suf).length + 2 := by
  cases w with
  | nil => exact (hne rfl).elim
  | cons a rest =>
    have hm : swapDenote a (a.val.1) ≠ a.val.1 := by
      have h1 : swapDenote a a.val.1 = a.val.2 := by
        change Equiv.swap a.val.1 a.val.2 a.val.1 = _
        exact Equiv.swap_apply_left _ _
      intro hcon
      rw [h1] at hcon
      exact a.property hcon.symm
    have hcount1 : 1 ≤ moverCount a.val.1 (a :: rest) := by
      have e : moverCount a.val.1 (a :: rest) = moverCount a.val.1 rest + 1 :=
        moverCount_cons_move _ a rest hm
      omega
    have hcountNe : moverCount a.val.1 (a :: rest) ≠ 1 := by
      intro hcon
      exact exactly_one_false _ _ hcon hprod
    have hcount2 : 2 ≤ moverCount a.val.1 (a :: rest) := by omega
    exact aux_exists a.val.1 _ _ rfl hcount2 hprod hne

end AlgebraicKTheory

end
