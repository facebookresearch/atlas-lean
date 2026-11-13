/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-- Expand a block list for the forward map: each part `a` becomes `1`
followed by `(a - 1) / k` copies of `k`. -/
private def expandA (k : ℕ) : List ℕ → List ℕ
  | [] => []
  | a :: as => 1 :: (List.replicate ((a - 1) / k) k ++ expandA k as)

/-- Expand a block list for the backward map: each part `b` becomes `k`
followed by `b - k` copies of `1`. -/
private def expandB (k : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: bs => k :: (List.replicate (b - k) 1 ++ expandB k bs)

/-- Parse a sequence by cutting before every occurrence of `X`, accumulating
the other elements into the current open part. -/
private def parseAux (X cur : ℕ) : List ℕ → List ℕ
  | [] => [cur]
  | y :: ys => if y = X then cur :: parseAux X y ys else parseAux X (cur + y) ys

/-- Parse a nonempty sequence with `parseAux`, and `[]` to `[]`. -/
private def parseBefore (X : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: xs => parseAux X x xs

/-- Forward block map: expand, replace the leading `1` by `k`, re-parse. -/
private def fwd (k : ℕ) : List ℕ → List ℕ
  | [] => []
  | a :: as => parseBefore k (k :: (List.replicate ((a - 1) / k) k ++ expandA k as))

/-- Backward block map: expand, replace the leading `k` by `1`, re-parse. -/
private def bwd (k : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: bs => parseBefore 1 (1 :: (List.replicate (b - k) 1 ++ expandB k bs))

private theorem expandA_nil (k : ℕ) : expandA k [] = [] := rfl

private theorem expandA_cons (k a : ℕ) (as : List ℕ) :
    expandA k (a :: as) = 1 :: (List.replicate ((a - 1) / k) k ++ expandA k as) :=
  rfl

private theorem expandB_nil (k : ℕ) : expandB k [] = [] := rfl

private theorem expandB_cons (k b : ℕ) (bs : List ℕ) :
    expandB k (b :: bs) = k :: (List.replicate (b - k) 1 ++ expandB k bs) :=
  rfl

private theorem parseAux_nil (X cur : ℕ) : parseAux X cur [] = [cur] := rfl

private theorem parseAux_cons (X cur y : ℕ) (ys : List ℕ) :
    parseAux X cur (y :: ys) =
      (if y = X then cur :: parseAux X y ys else parseAux X (cur + y) ys) :=
  rfl

private theorem parseBefore_nil (X : ℕ) : parseBefore X [] = [] := rfl

private theorem parseBefore_cons (X x : ℕ) (xs : List ℕ) :
    parseBefore X (x :: xs) = parseAux X x xs :=
  rfl

private theorem fwd_cons (k a : ℕ) (as : List ℕ) :
    fwd k (a :: as) =
      parseBefore k (k :: (List.replicate ((a - 1) / k) k ++ expandA k as)) :=
  rfl

private theorem bwd_cons (k b : ℕ) (bs : List ℕ) :
    bwd k (b :: bs) =
      parseBefore 1 (1 :: (List.replicate (b - k) 1 ++ expandB k bs)) :=
  rfl

private theorem fwd_of_ne (k : ℕ) (L : List ℕ) :
    L ≠ [] → fwd k L = parseBefore k (k :: (expandA k L).tail) := by
  intro hL
  obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil hL
  rfl

private theorem bwd_of_ne (k : ℕ) (L : List ℕ) :
    L ≠ [] → bwd k L = parseBefore 1 (1 :: (expandB k L).tail) := by
  intro hL
  obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hL
  rfl

private theorem sum_rep_nat (n a : ℕ) : (List.replicate n a).sum = n * a := by
  induction n with
  | zero => simp
  | succ t ih => rw [List.replicate_succ, List.sum_cons, ih]; ring

private theorem mem_expandA (k y : ℕ) (l : List ℕ) :
    y ∈ expandA k l → y = 1 ∨ y = k := by
  induction l with
  | nil => simp [expandA]
  | cons a as ih =>
    intro hy
    rw [expandA_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact Or.inl rfl
    · rw [List.mem_append] at hy
      rcases hy with hy | hy
      · rw [List.mem_replicate] at hy
        exact Or.inr hy.2
      · exact ih hy

private theorem mem_expandB (k y : ℕ) (l : List ℕ) :
    y ∈ expandB k l → y = k ∨ y = 1 := by
  induction l with
  | nil => simp [expandB]
  | cons b bs ih =>
    intro hy
    rw [expandB_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact Or.inl rfl
    · rw [List.mem_append] at hy
      rcases hy with hy | hy
      · rw [List.mem_replicate] at hy
        exact Or.inr hy.2
      · exact ih hy

private theorem sum_expandA (k : ℕ) (l : List ℕ) :
    (∀ a ∈ l, a % k = 1 % k) → (∀ a ∈ l, 0 < a) → (expandA k l).sum = l.sum := by
  induction l with
  | nil => intro _ _; rfl
  | cons a as ih =>
    intro hmem hpos
    have ha : a % k = 1 % k := hmem a List.mem_cons_self
    have hapos : 0 < a := hpos a List.mem_cons_self
    have hmem' : ∀ x ∈ as, x % k = 1 % k :=
      fun x hx => hmem x (List.mem_cons_of_mem a hx)
    have hpos' : ∀ x ∈ as, 0 < x :=
      fun x hx => hpos x (List.mem_cons_of_mem a hx)
    have hdvd : k ∣ a - 1 :=
      Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq ha)
    have e : (a - 1) / k * k = a - 1 := Nat.div_mul_cancel hdvd
    rw [expandA_cons, List.sum_cons, List.sum_append, sum_rep_nat, ih hmem' hpos',
      List.sum_cons]
    omega

private theorem sum_expandB (k : ℕ) (l : List ℕ) :
    (∀ b ∈ l, k ≤ b) → (expandB k l).sum = l.sum := by
  induction l with
  | nil => intro _; rfl
  | cons b bs ih =>
    intro hmem
    have hb : k ≤ b := hmem b List.mem_cons_self
    have hmem' : ∀ x ∈ bs, k ≤ x :=
      fun x hx => hmem x (List.mem_cons_of_mem b hx)
    have e : k + (b - k) = b := by omega
    have e2 : (b - k) * 1 = b - k := by ring
    rw [expandB_cons, List.sum_cons, List.sum_append, sum_rep_nat, ih hmem',
      List.sum_cons]
    omega

private theorem sum_parseAux (X cur : ℕ) (s : List ℕ) :
    (parseAux X cur s).sum = cur + s.sum := by
  induction s generalizing cur with
  | nil => simp [parseAux]
  | cons y ys ih =>
    rw [parseAux_cons]
    by_cases hy : y = X
    · rw [ite_eq_left hy, List.sum_cons, ih, List.sum_cons]
    · rw [ite_eq_right hy, ih, List.sum_cons, Nat.add_assoc]

private theorem all_ge_parseAux (X cur : ℕ) (s : List ℕ) :
    X ≤ cur → ∀ p ∈ parseAux X cur s, X ≤ p := by
  induction s generalizing cur with
  | nil =>
    intro hle p hp
    rw [parseAux_nil] at hp
    simp at hp
    omega
  | cons y ys ih =>
    intro hle p hp
    rw [parseAux_cons] at hp
    by_cases hy : y = X
    · rw [ite_eq_left hy, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hle
      · exact ih y (by omega) p hp
    · rw [ite_eq_right hy] at hp
      exact ih (cur + y) (by omega) p hp

private theorem mod_parseAux (k cur : ℕ) (s : List ℕ) :
    cur % k = 1 % k → (∀ y ∈ s, y = 1 ∨ y = k) →
      ∀ p ∈ parseAux 1 cur s, p % k = 1 % k := by
  induction s generalizing cur with
  | nil =>
    intro hcur _ p hp
    rw [parseAux_nil, List.mem_singleton] at hp
    rw [hp]
    exact hcur
  | cons y ys ih =>
    intro hcur hmem p hp
    have hy : y = 1 ∨ y = k := hmem y List.mem_cons_self
    have hmem' : ∀ z ∈ ys, z = 1 ∨ z = k :=
      fun z hz => hmem z (List.mem_cons_of_mem y hz)
    rw [parseAux_cons] at hp
    by_cases h1 : y = 1
    · subst h1
      rw [ite_eq_left rfl, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hcur
      · exact ih 1 rfl hmem' p hp
    · rw [ite_eq_right h1] at hp
      have hyk : y = k := hy.resolve_left h1
      have hcur' : (cur + y) % k = 1 % k := by
        rw [hyk, Nat.add_mod_right]
        exact hcur
      exact ih (cur + y) hcur' hmem' p hp

/-- Consuming a run of `k`s into the open part of a cut-before-`1` parse. -/
private theorem parseAux_leadK (k : ℕ) (hk : 2 ≤ k) (cur t : ℕ) (s : List ℕ) :
    parseAux 1 cur (List.replicate t k ++ s) = parseAux 1 (cur + t * k) s := by
  induction t generalizing cur with
  | zero => simp
  | succ t ih =>
    have hkk : k ≠ 1 := by omega
    simp only [List.replicate_succ, List.cons_append, parseAux, ite_eq_right hkk]
    rw [ih]
    have h : (cur + k) + t * k = cur + (t + 1) * k := by ring
    rw [h]

/-- Consuming a run of `1`s into the open part of a cut-before-`k` parse. -/
private theorem parseAux_lead1 (k : ℕ) (hk : 2 ≤ k) (cur t : ℕ) (s : List ℕ) :
    parseAux k cur (List.replicate t 1 ++ s) = parseAux k (cur + t) s := by
  induction t generalizing cur with
  | zero => simp
  | succ t ih =>
    have h11 : (1 : ℕ) ≠ k := by omega
    simp only [List.replicate_succ, List.cons_append, parseAux, ite_eq_right h11]
    rw [ih]
    have h : (cur + 1) + t = cur + (t + 1) := by ring
    rw [h]

/-- A replicate block followed by a single element collapses. -/
private theorem rep_append_cons (m a : ℕ) (l : List ℕ) :
    List.replicate m a ++ (a :: l) = a :: (List.replicate m a ++ l) := by
  induction m with
  | zero => rfl
  | succ t ih => simp only [List.replicate_succ, List.cons_append, ih]

/-- Expanding after a cut-before-`k` parse recovers a `{1, k}`-sequence. -/
private theorem expandB_parseAux (k cur : ℕ) (s : List ℕ) :
    k ≤ cur → (∀ y ∈ s, y = 1 ∨ y = k) →
      expandB k (parseAux k cur s) = (k :: List.replicate (cur - k) 1) ++ s := by
  induction s generalizing cur with
  | nil =>
    intro _ _
    simp [parseAux, expandB]
  | cons y ys ih =>
    intro hle hmem
    have hy : y = 1 ∨ y = k := hmem y List.mem_cons_self
    have hmem' : ∀ z ∈ ys, z = 1 ∨ z = k :=
      fun z hz => hmem z (List.mem_cons_of_mem y hz)
    rw [parseAux_cons]
    by_cases hkk : y = k
    · rw [ite_eq_left hkk, hkk, expandB_cons, ih k (le_refl k) hmem']
      have hrep0 : (k :: List.replicate (k - k) 1) ++ ys = k :: ys := by
        have e0 : k - k = 0 := by omega
        rw [e0, List.replicate_zero]
        simp
      rw [hrep0, List.cons_append]
    · have hy1 : y = 1 := hy.resolve_right hkk
      have hle' : k ≤ cur + 1 := by omega
      rw [ite_eq_right hkk, hy1, ih (cur + 1) hle' hmem']
      have hdiv : cur + 1 - k = (cur - k) + 1 := by omega
      simp only [hdiv, List.replicate_succ, List.cons_append, rep_append_cons]

/-- Expanding after a cut-before-`1` parse recovers a `{1, k}`-sequence. -/
private theorem expandA_parseAux (k : ℕ) (hk : 2 ≤ k) (cur : ℕ) (s : List ℕ) :
    cur % k = 1 % k → 1 ≤ cur → (∀ y ∈ s, y = 1 ∨ y = k) →
      expandA k (parseAux 1 cur s) =
        (1 :: List.replicate ((cur - 1) / k) k) ++ s := by
  induction s generalizing cur with
  | nil =>
    intro _ _ _
    rw [parseAux_nil, expandA_cons, expandA_nil, List.append_nil, List.append_nil]
  | cons y ys ih =>
    intro hcur hge hmem
    have hy : y = 1 ∨ y = k := hmem y List.mem_cons_self
    have hmem' : ∀ z ∈ ys, z = 1 ∨ z = k :=
      fun z hz => hmem z (List.mem_cons_of_mem y hz)
    rw [parseAux_cons]
    by_cases h1 : y = 1
    · subst h1
      rw [ite_eq_left rfl, expandA_cons, ih 1 rfl (le_refl 1) hmem']
      have hrep0 : (1 :: List.replicate ((1 - 1) / k) k) ++ ys = 1 :: ys := by
        have e0 : (1 - 1) / k = 0 := by simp
        rw [e0, List.replicate_zero]
        simp
      rw [hrep0, List.cons_append]
    · rw [ite_eq_right h1]
      have hyk : y = k := hy.resolve_left h1
      have hcur' : (cur + y) % k = 1 % k := by
        rw [hyk, Nat.add_mod_right]
        exact hcur
      have hge' : 1 ≤ cur + y := by omega
      rw [ih (cur + y) hcur' hge' hmem', hyk]
      have hdiv : (cur + k - 1) / k = (cur - 1) / k + 1 := by
        have e : cur + k - 1 = (cur - 1) + 1 * k := by omega
        have hk0 : 0 < k := by omega
        rw [e, Nat.add_mul_div_right _ _ hk0]
      simp only [hdiv, List.replicate_succ, List.cons_append, rep_append_cons]

/-- Parsing inverts `expandB`: blocks starting with `k` followed by `1`s. -/
private theorem parseAux_expandB (k : ℕ) (hk : 2 ≤ k) (l : List ℕ) :
    (∀ b ∈ l, k ≤ b) → parseBefore k (expandB k l) = l := by
  induction l with
  | nil => intro _; rfl
  | cons b bs ih =>
    intro hmem
    have hb : k ≤ b := hmem b List.mem_cons_self
    have hmem' : ∀ x ∈ bs, k ≤ x :=
      fun x hx => hmem x (List.mem_cons_of_mem b hx)
    have hX : expandB k (b :: bs) =
        k :: (List.replicate (b - k) 1 ++ expandB k bs) := rfl
    have hP : parseBefore k (expandB k (b :: bs)) =
        parseAux k k (List.replicate (b - k) 1 ++ expandB k bs) := by
      rw [hX]; rfl
    rw [hP, parseAux_lead1 k hk k (b - k) (expandB k bs)]
    have e2 : k + (b - k) = b := by omega
    rw [e2]
    cases bs with
    | nil => rfl
    | cons b' bs' =>
      have hIH := ih hmem'
      have hX2 : expandB k (b' :: bs') =
          k :: (List.replicate (b' - k) 1 ++ expandB k bs') := rfl
      have hP2 : parseBefore k (expandB k (b' :: bs')) =
          parseAux k k (List.replicate (b' - k) 1 ++ expandB k bs') := by
        rw [hX2]; rfl
      rw [hX2, parseAux_cons, ite_eq_left rfl]
      have hgoal : parseAux k k (List.replicate (b' - k) 1 ++ expandB k bs') =
          b' :: bs' := by
        rw [← hP2]
        exact hIH
      exact congrArg (b :: ·) hgoal

/-- Parsing inverts `expandA`: blocks starting with `1` followed by `k`s. -/
private theorem parseAux_expandA (k : ℕ) (hk : 2 ≤ k) (l : List ℕ) :
    (∀ a ∈ l, a % k = 1 % k) → (∀ a ∈ l, 0 < a) →
      parseBefore 1 (expandA k l) = l := by
  induction l with
  | nil => intro _ _; rfl
  | cons a as ih =>
    intro hmem hpos
    have ha : a % k = 1 % k := hmem a List.mem_cons_self
    have hapos : 0 < a := hpos a List.mem_cons_self
    have hmem' : ∀ x ∈ as, x % k = 1 % k :=
      fun x hx => hmem x (List.mem_cons_of_mem a hx)
    have hpos' : ∀ x ∈ as, 0 < x :=
      fun x hx => hpos x (List.mem_cons_of_mem a hx)
    have hdvd : k ∣ a - 1 :=
      Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq ha)
    have e : (a - 1) / k * k = a - 1 := Nat.div_mul_cancel hdvd
    have hX : expandA k (a :: as) =
        1 :: (List.replicate ((a - 1) / k) k ++ expandA k as) := rfl
    have hP : parseBefore 1 (expandA k (a :: as)) =
        parseAux 1 1 (List.replicate ((a - 1) / k) k ++ expandA k as) := by
      rw [hX]; rfl
    rw [hP, parseAux_leadK k hk 1 ((a - 1) / k) (expandA k as)]
    have e2 : 1 + (a - 1) / k * k = a := by omega
    rw [e2]
    cases as with
    | nil => rfl
    | cons a' as' =>
      have hIH := ih hmem' hpos'
      have hX2 : expandA k (a' :: as') =
          1 :: (List.replicate ((a' - 1) / k) k ++ expandA k as') := rfl
      have hP2 : parseBefore 1 (expandA k (a' :: as')) =
          parseAux 1 1 (List.replicate ((a' - 1) / k) k ++ expandA k as') := by
        rw [hX2]; rfl
      rw [hX2, parseAux_cons, ite_eq_left rfl]
      have hgoal : parseAux 1 1 (List.replicate ((a' - 1) / k) k ++ expandA k as') =
          a' :: as' := by
        rw [← hP2]
        exact hIH
      exact congrArg (a :: ·) hgoal

private theorem expandA_parseBefore (k : ℕ) (hk : 2 ≤ k) (s : List ℕ) :
    (∀ y ∈ s, y = 1 ∨ y = k) → expandA k (parseBefore 1 (1 :: s)) = 1 :: s := by
  intro hmem
  rw [parseBefore_cons]
  have h := expandA_parseAux k hk 1 s rfl (le_refl 1) hmem
  have hrep0 : (1 :: List.replicate ((1 - 1) / k) k) ++ s = 1 :: s := by
    have e0 : (1 - 1) / k = 0 := by simp
    rw [e0, List.replicate_zero]
    simp
  rwa [hrep0] at h

private theorem expandB_parseBefore (k : ℕ) (s : List ℕ) :
    (∀ y ∈ s, y = 1 ∨ y = k) → expandB k (parseBefore k (k :: s)) = k :: s := by
  intro hmem
  rw [parseBefore_cons]
  have h := expandB_parseAux k k s (le_refl k) hmem
  have hrep0 : (k :: List.replicate (k - k) 1) ++ s = k :: s := by
    have e0 : k - k = 0 := by omega
    rw [e0, List.replicate_zero]
    simp
  rwa [hrep0] at h

private theorem bwd_fwd (k : ℕ) (hk : 2 ≤ k) (a : ℕ) (as : List ℕ) :
    (∀ x ∈ a :: as, x % k = 1 % k) → (∀ x ∈ a :: as, 0 < x) →
      bwd k (fwd k (a :: as)) = a :: as := by
  intro hmem hpos
  have hmemA : ∀ y ∈ List.replicate ((a - 1) / k) k ++ expandA k as,
      y = 1 ∨ y = k := by
    intro y hy
    rw [List.mem_append] at hy
    rcases hy with hy | hy
    · rw [List.mem_replicate] at hy
      exact Or.inr hy.2
    · exact mem_expandA k y as hy
  have h1 : expandB k (fwd k (a :: as)) =
      k :: (List.replicate ((a - 1) / k) k ++ expandA k as) := by
    rw [fwd_cons]
    exact expandB_parseBefore k _ hmemA
  have hX : expandA k (a :: as) =
      1 :: (List.replicate ((a - 1) / k) k ++ expandA k as) := rfl
  have h2 : 1 :: (expandB k (fwd k (a :: as))).tail = expandA k (a :: as) := by
    rw [h1, List.tail_cons, hX]
  have h3 : bwd k (fwd k (a :: as)) = parseBefore 1 (expandA k (a :: as)) := by
    have hne : fwd k (a :: as) ≠ [] := by
      intro h
      rw [h, expandB_nil] at h1
      simp at h1
    rw [bwd_of_ne k _ hne, h2]
  rw [h3]
  exact parseAux_expandA k hk (a :: as) hmem hpos

private theorem fwd_bwd (k : ℕ) (hk : 2 ≤ k) (b : ℕ) (bs : List ℕ) :
    (∀ x ∈ b :: bs, k ≤ x) → fwd k (bwd k (b :: bs)) = b :: bs := by
  intro hmem
  have hmemB : ∀ y ∈ List.replicate (b - k) 1 ++ expandB k bs, y = k ∨ y = 1 := by
    intro y hy
    rw [List.mem_append] at hy
    rcases hy with hy | hy
    · rw [List.mem_replicate] at hy
      exact Or.inr hy.2
    · exact mem_expandB k y bs hy
  have h1 : expandA k (bwd k (b :: bs)) =
      1 :: (List.replicate (b - k) 1 ++ expandB k bs) := by
    rw [bwd_cons]
    exact expandA_parseBefore k hk _ (fun y hy => (hmemB y hy).symm)
  have hX : expandB k (b :: bs) =
      k :: (List.replicate (b - k) 1 ++ expandB k bs) := rfl
  have h2 : k :: (expandA k (bwd k (b :: bs))).tail = expandB k (b :: bs) := by
    rw [h1, List.tail_cons, hX]
  have h3 : fwd k (bwd k (b :: bs)) = parseBefore k (expandB k (b :: bs)) := by
    have hne : bwd k (b :: bs) ≠ [] := by
      intro h
      rw [h, expandA_nil] at h1
      simp at h1
    rw [fwd_of_ne k _ hne, h2]
  rw [h3]
  exact parseAux_expandB k hk (b :: bs) hmem

private theorem bwd_fwd_general (k : ℕ) (hk : 2 ≤ k) (bl : List ℕ) :
    (∀ x ∈ bl, x % k = 1 % k) → (∀ x ∈ bl, 0 < x) → bwd k (fwd k bl) = bl := by
  intro hmem hpos
  by_cases hne : bl = []
  · subst hne
    rfl
  · obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil hne
    exact bwd_fwd k hk a as hmem hpos

private theorem fwd_bwd_general (k : ℕ) (hk : 2 ≤ k) (bl : List ℕ) :
    (∀ x ∈ bl, k ≤ x) → fwd k (bwd k bl) = bl := by
  intro hmem
  by_cases hne : bl = []
  · subst hne
    rfl
  · obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil hne
    exact fwd_bwd k hk a as hmem

private theorem sum_fwd_gen (k n : ℕ) (bl : List ℕ) :
    bl ≠ [] → (expandA k bl).sum = bl.sum → bl.sum = n → 0 < n →
      (fwd k bl).sum = n + k - 1 := by
  intro hne hsumA hsum hn
  obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [fwd_cons, parseBefore_cons, sum_parseAux]
  have hA : (expandA k (a :: as)).sum = n := hsumA.trans hsum
  have hX : expandA k (a :: as) =
      1 :: (List.replicate ((a - 1) / k) k ++ expandA k as) := rfl
  have h2 : (expandA k (a :: as)).sum =
      1 + (List.replicate ((a - 1) / k) k ++ expandA k as).sum := by
    rw [hX, List.sum_cons]
  omega

private theorem sum_bwd_gen (k n : ℕ) (bl : List ℕ) :
    0 < k → bl ≠ [] → (expandB k bl).sum = bl.sum → bl.sum = n →
      (bwd k bl).sum = n - k + 1 := by
  intro hk hne hsumB hsum
  obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [bwd_cons, parseBefore_cons, sum_parseAux]
  have hB : (expandB k (b :: bs)).sum = n := hsumB.trans hsum
  have hX : expandB k (b :: bs) =
      k :: (List.replicate (b - k) 1 ++ expandB k bs) := rfl
  have h2 : (expandB k (b :: bs)).sum =
      k + (List.replicate (b - k) 1 ++ expandB k bs).sum := by
    rw [hX, List.sum_cons]
  omega

private theorem fwd_ge (k : ℕ) (al : List ℕ) (p : ℕ) :
    p ∈ fwd k al → k ≤ p := by
  intro hp
  by_cases hne : al = []
  · subst hne
    simp [fwd] at hp
  · obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil hne
    rw [fwd_cons, parseBefore_cons] at hp
    exact all_ge_parseAux k k _ (le_refl k) p hp

private theorem bwd_mod (k : ℕ) (bl : List ℕ) :
    (∀ y ∈ expandB k bl, y = 1 ∨ y = k) → ∀ p ∈ bwd k bl, p % k = 1 % k := by
  intro hmemB p hp
  by_cases hne : bl = []
  · subst hne
    simp [bwd] at hp
  · obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hne
    rw [bwd_cons, parseBefore_cons] at hp
    exact mod_parseAux k 1 _ rfl
      (fun y hy => hmemB y (List.mem_cons_of_mem k hy)) p hp

private theorem pos_fwd (k : ℕ) (bl : List ℕ) :
    0 < k → ∀ p ∈ fwd k bl, 0 < p := by
  intro hk p hp
  have h := fwd_ge k bl p hp
  omega

private theorem pos_bwd (k : ℕ) (hk : 2 ≤ k) (bl : List ℕ) :
    (∀ p ∈ bwd k bl, p % k = 1 % k) → ∀ p ∈ bwd k bl, 0 < p := by
  intro hmod p hp
  by_contra h
  have hp0 : p = 0 := by omega
  have h1k : (1 : ℕ) % k = 1 := Nat.mod_eq_of_lt (by omega)
  have hm := hmod p hp
  rw [hp0, Nat.zero_mod, h1k] at hm
  exact zero_ne_one hm

/--
**Munagi's theorem on restricted compositions.** For positive integers $n$ and $k$, the number
of compositions of $n$ all of whose parts are congruent to $1$ modulo $k$ equals the number of
compositions of $n + k - 1$ all of whose parts are at least $k$.

Proves `Wanted` entry `munagi_restricted_compositions`.

Source: Jia Huang, "Even and Odd Compositions with Restricted Parts", Journal of Integer Sequences 27 (2024), Article 24.6.5, Theorem `thm:comp2` (Munagi), lines 160-162, <https://cs.uwaterloo.ca/journals/JIS/VOL27/Huang/huang9.tex>.
-/
theorem munagi_restricted_compositions
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    Fintype.card {c : Composition n // ∀ a ∈ c.blocks, a % k = 1 % k} =
      Fintype.card {c : Composition (n + k - 1) // ∀ a ∈ c.blocks, k ≤ a} := by
  by_cases hk1 : k = 1
  · subst hk1
    have hnn : n + 1 - 1 = n := by omega
    rw [hnn]
    exact Fintype.card_congr
      ((Equiv.subtypeUnivEquiv (fun c _ _ => by omega)).trans
        (Equiv.subtypeUnivEquiv (fun c a ha => c.blocks_pos ha)).symm)
  · have hk2 : 2 ≤ k := by omega
    refine Fintype.card_congr
      { toFun := fun c =>
          ⟨⟨fwd k c.val.blocks,
            fun {p} hp => pos_fwd k c.val.blocks (by omega) p hp,
            by
              have hne : c.val.blocks ≠ [] := by
                intro h
                have hs := c.val.blocks_sum
                rw [h, List.sum_nil] at hs
                omega
              have hsumA :=
                sum_expandA k c.val.blocks (fun x hx => c.2 x hx)
                  (fun x hx => c.val.blocks_pos hx)
              exact sum_fwd_gen k n c.val.blocks hne hsumA c.val.blocks_sum hn⟩,
            fun p hp => fwd_ge k c.val.blocks p hp⟩,
        invFun := fun c =>
          ⟨⟨bwd k c.val.blocks,
            fun {p} hp =>
              pos_bwd k hk2 c.val.blocks
                (fun q hq =>
                  bwd_mod k c.val.blocks
                    (fun y hy => (mem_expandB k y c.val.blocks hy).symm) q hq)
                p hp,
            by
              have hne : c.val.blocks ≠ [] := by
                intro h
                have hs := c.val.blocks_sum
                rw [h, List.sum_nil] at hs
                omega
              have hsumB :=
                sum_expandB k c.val.blocks (fun x hx => c.2 x hx)
              have h :=
                sum_bwd_gen k (n + k - 1) c.val.blocks (by omega) hne hsumB
                  c.val.blocks_sum
              omega⟩,
            fun p hp =>
              bwd_mod k c.val.blocks
                (fun y hy => (mem_expandB k y c.val.blocks hy).symm) p hp⟩,
        left_inv := ?_, right_inv := ?_ }
    · intro c
      obtain ⟨⟨bl, hpos, _hsum⟩, hmem⟩ := c
      apply Subtype.ext
      apply Composition.ext
      change bwd k (fwd k bl) = bl
      exact bwd_fwd_general k hk2 bl hmem (fun x hx => hpos hx)
    · intro c
      obtain ⟨⟨bl, _hpos, _hsum⟩, hmem⟩ := c
      apply Subtype.ext
      apply Composition.ext
      change fwd k (bwd k bl) = bl
      exact fwd_bwd_general k hk2 bl hmem

end MetaMathlibExt
