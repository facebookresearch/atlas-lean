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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergUpperUnipotent

/-! # Upper-unipotent collection steps

For `a < b < n` over `[Ring R]`, the out-of-order adjacent product
`x b n v * x a b u` collects to head-left order
`x a n (-(u * v)) * (x a b u * x b n v)`, with correction coefficient
`-(u * v)` in ordinary noncommutative `u * v` order. For `i ≠ j`, `k ≠ l`,
`i ≠ l`, `j ≠ k`, the disjoint product `x k l b * x i j a` equals
`x i j a * x k l b` with no correction factor. For `i ≠ j`, the same-pair
product `x i j a * x i j b` equals `x i j (a + b)` with additive coefficient
update. For `i < j < n`, right multiplication of `upperUnipotentProd n c` by
`x i j a` recollects to another `upperUnipotentProd`, with coefficients
unchanged off `orderedPositiveRoots n`, via later-column Chevalley corrections
and same-column merging. The ordered evaluator is closed under multiplication:
`upperUnipotentProd n c₁ * upperUnipotentProd n c₂` recollects to another
`upperUnipotentProd`, with coefficients unchanged off `orderedPositiveRoots n`.
The inverse `(upperUnipotentProd n c)⁻¹` recollects to another
`upperUnipotentProd`, with coefficients unchanged off `orderedPositiveRoots n`,
by absorbing the reversed negated word head-first.
Every element of `upperUnipotentSubgroup n` equals `upperUnipotentProd n c`
for a coefficient assignment vanishing off `orderedPositiveRoots n`.
Purpose: first executable mixed column/rank Chevalley collection step
plus disjoint-generator commuting step plus same-pair merge step plus
multiplication closure plus inverse re-collection plus subgroup representation
toward ordered upper-unipotent words. Nonclaims: no collection termination, ordered normal
form, coefficient or evaluator uniqueness beyond the stated off-root
preservation, `toStableE` injectivity, TWT/Bruhat statement, kernel generation,
or Matsumoto claim.
-/

namespace AlgebraicKTheory

namespace StableSteinberg

universe u

variable {R : Type u} [Ring R]

open scoped commutatorElement

/-- Mixed adjacent swap: for `a < b < n`, `x b n v * x a b u` equals
`x a n (-(u * v)) * (x a b u * x b n v)` in head-left collected order, with
correction coefficient `-(u * v)` in ordinary `u * v` order. Proved from
accepted `x_chev` via the repository commutator convention
`⁅x, y⁆ = x * y * x⁻¹ * y⁻¹` plus ordinary group algebra, then accepted
`x_neg` for the sign. Purpose: atomic mixed collection step. Nonclaims: no
evaluator multiplication/inversion closure, ordered normal form, uniqueness,
`toStableE` injectivity, TWT, kernel generation, or Matsumoto theorem. -/
public theorem upperUnipotent_mixedSwap_chev {n a b : ℕ} (ha : a < b)
    (hb : b < n) (u v : R) :
    x b n (Nat.ne_of_lt hb) v * x a b (ne_of_lt ha) u =
      x a n (Nat.ne_of_lt (Nat.lt_trans ha hb)) (-(u * v)) *
        (x a b (ne_of_lt ha) u * x b n (Nat.ne_of_lt hb) v) := by
  have hab : a ≠ b := ne_of_lt ha
  have hbn : b ≠ n := Nat.ne_of_lt hb
  have han : a ≠ n := Nat.ne_of_lt (Nat.lt_trans ha hb)
  have h_chev : ⁅x (R := R) a b hab u, x b n hbn v⁆ =
      x a n han (u * v) :=
    x_chev a b n hab hbn han u v
  have h_swap : ⁅x (R := R) b n hbn v, x a b hab u⁆ =
      (⁅x (R := R) a b hab u, x b n hbn v⁆)⁻¹ := by
    simp only [commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc]
  have h_rc : ⁅x (R := R) b n hbn v, x a b hab u⁆ =
      x a n han (-(u * v)) := by
    calc
      ⁅x (R := R) b n hbn v, x a b hab u⁆
          = (⁅x (R := R) a b hab u, x b n hbn v⁆)⁻¹ := h_swap
      _ = (x a n han (u * v))⁻¹ := by rw [h_chev]
      _ = x a n han (-(u * v)) := by rw [← x_neg]
  have h_exp : x (R := R) b n hbn v * x a b hab u *
      (x (R := R) b n hbn v)⁻¹ * (x (R := R) a b hab u)⁻¹ =
      x a n han (-(u * v)) := by
    simpa [commutatorElement_def] using h_rc
  calc
    x (R := R) b n hbn v * x a b hab u
        = (x (R := R) b n hbn v * x a b hab u *
          (x (R := R) b n hbn v)⁻¹ * (x (R := R) a b hab u)⁻¹) *
          x a b hab u * x (R := R) b n hbn v := by
        simp [mul_assoc]
    _ = x a n han (-(u * v)) *
        (x a b hab u * x (R := R) b n hbn v) := by
      rw [h_exp, mul_assoc]

/-- Disjoint swap: for `i ≠ j`, `k ≠ l`, `i ≠ l`, `j ≠ k`,
`x k l b * x i j a` equals `x i j a * x k l b`, with no correction
factor. Proved from accepted `x_comm` via the repository commutator
convention `⁅x, y⁆ = x * y * x⁻¹ * y⁻¹` plus ordinary group algebra.
Purpose: atomic disjoint-generator commuting step. Nonclaims: no
coefficient updates, collection termination, multiplication/inversion
closure, ordered normal form, uniqueness, `toStableE` injectivity, TWT,
kernel generation, or Matsumoto theorem. -/
public theorem upperUnipotent_disjointSwap_comm {i j k l : ℕ}
    (hij : i ≠ j) (hkl : k ≠ l) (hil : i ≠ l) (hjk : j ≠ k)
    (a b : R) :
    x k l hkl b * x i j hij a = x i j hij a * x k l hkl b := by
  have h_comm : ⁅x (R := R) i j hij a, x k l hkl b⁆ = 1 :=
    x_comm i j k l hij hkl hil hjk a b
  have h_exp : x (R := R) i j hij a * x k l hkl b *
      (x (R := R) i j hij a)⁻¹ * (x (R := R) k l hkl b)⁻¹ = 1 := by
    simpa [commutatorElement_def] using h_comm
  have h_eq : x (R := R) i j hij a * x k l hkl b =
      x (R := R) k l hkl b * x i j hij a := by
    calc
      x (R := R) i j hij a * x k l hkl b
          = (x (R := R) i j hij a * x k l hkl b *
            (x (R := R) i j hij a)⁻¹ * (x (R := R) k l hkl b)⁻¹) *
            x k l hkl b * x i j hij a := by
          simp [mul_assoc]
      _ = x (R := R) k l hkl b * x i j hij a := by
        rw [h_exp, one_mul]
  exact h_eq.symm

/-- Same-pair addition: for `i ≠ j`, `x i j a * x i j b` equals
`x i j (a + b)` in this exact left-to-right factor order, with additive
coefficient update `a + b`. Holds over `[Ring R]` with no import change,
proved directly from accepted `x_add`. Purpose: atomic same-pair merge step
needed by the right-insertion driver. Nonclaims: no collection termination,
evaluator multiplication/inversion closure, ordered normal-form existence,
coefficient/evaluator uniqueness, `toStableE` injectivity, TWT, kernel
generation, or Matsumoto theorem. -/
public theorem upperUnipotent_samePair_add {i j : ℕ} (hij : i ≠ j) (a b : R) :
    x (R := R) i j hij a * x i j hij b = x i j hij (a + b) :=
  x_add i j hij a b

/-- Column word over an explicit index list: head-left product of the
`x k m` generators with coefficient function `d`; indices with `k = m`
contribute `1`. Purpose: concrete word manipulated by the column
insertion and bubble lemmas below. Nonclaims: no normal form,
uniqueness, or closure claim. -/
private def colWord (m : ℕ) (L : List ℕ) (d : ℕ → R) : StableSteinberg R :=
  (L.map (fun k => if h : k ≠ m then x (R := R) k m h (d k) else 1)).prod

private theorem colWord_cons (m : ℕ) (k : ℕ) (L : List ℕ) (d : ℕ → R) :
    colWord m (k :: L) d =
      (if h : k ≠ m then x (R := R) k m h (d k) else 1) *
        colWord m L d := by
  simp [colWord, List.map_cons, List.prod_cons]

private theorem colWord_congr (L : List ℕ) (m : ℕ) {d₁ d₂ : ℕ → R} :
    (∀ k ∈ L, d₁ k = d₂ k) →
    colWord m L d₁ = colWord m L d₂ := by
  intro h
  revert h
  induction L with
  | nil =>
    intro _h
    simp [colWord]
  | cons k L ih =>
    intro h
    have hk : d₁ k = d₂ k := h k (List.mem_cons.mpr (Or.inl rfl))
    have ht : ∀ k' ∈ L, d₁ k' = d₂ k' :=
      fun k' hk' => h k' (List.mem_cons.mpr (Or.inr hk'))
    rw [colWord_cons, colWord_cons, hk, ih ht]

/-- Right coefficient update at one column slot. -/
private def colUpdR (d : ℕ → R) (i : ℕ) (a : R) : ℕ → R :=
  fun k => if k = i then d k + a else d k

/-- Left coefficient update at one column slot. -/
private def colUpdL (d : ℕ → R) (i : ℕ) (t : R) : ℕ → R :=
  fun k => if k = i then t + d k else d k

private theorem colUpdR_self (d : ℕ → R) (i : ℕ) (a : R) :
    colUpdR d i a i = d i + a := by
  simp [colUpdR]

private theorem colUpdR_of_ne (d : ℕ → R) (i : ℕ) (a : R) (k : ℕ)
    (h : k ≠ i) : colUpdR d i a k = d k := by
  simp [colUpdR, ite_eq_right h]

private theorem colUpdL_self (d : ℕ → R) (i : ℕ) (t : R) :
    colUpdL d i t i = t + d i := by
  simp [colUpdL]

private theorem colUpdL_of_ne (d : ℕ → R) (i : ℕ) (t : R) (k : ℕ)
    (h : k ≠ i) : colUpdL d i t k = d k := by
  simp [colUpdL, ite_eq_right h]

/-- A same-column generator commutes past a column word avoiding its slot,
by one disjoint swap per factor. -/
private theorem colWord_commute_through (L : List ℕ) (m : ℕ) (d : ℕ → R)
    (i : ℕ) (him : i ≠ m) (a : R) :
    (∀ k ∈ L, k < m) → (∀ k ∈ L, k ≠ i) →
    colWord m L d * x (R := R) i m him a =
      x (R := R) i m him a * colWord m L d := by
  intro hb hne
  revert hb hne
  induction L with
  | nil =>
    intro _hb _hne
    simp [colWord]
  | cons k L ih =>
    intro hb hne
    have hkm : k < m := hb k (List.mem_cons.mpr (Or.inl rfl))
    have hkb : ∀ k' ∈ L, k' < m :=
      fun k' hk' => hb k' (List.mem_cons.mpr (Or.inr hk'))
    have hkn : ∀ k' ∈ L, k' ≠ i :=
      fun k' hk' => hne k' (List.mem_cons.mpr (Or.inr hk'))
    have hkm' : k ≠ m := Nat.ne_of_lt hkm
    have h0eq :
        (if h : k ≠ m then x (R := R) k m h (d k) else 1) =
          x (R := R) k m hkm' (d k) :=
      dite_eq_left hkm'
    have hsw :
        x (R := R) k m hkm' (d k) * x (R := R) i m him a =
          x (R := R) i m him a * x (R := R) k m hkm' (d k) :=
      upperUnipotent_disjointSwap_comm him hkm' him (Ne.symm hkm') a (d k)
    rw [colWord_cons]
    have e0 :
        ((if h : k ≠ m then x (R := R) k m h (d k) else 1) *
          colWord m L d) * x (R := R) i m him a =
        (if h : k ≠ m then x (R := R) k m h (d k) else 1) *
          (colWord m L d * x (R := R) i m him a) :=
      mul_assoc _ _ _
    rw [e0, ih hkb hkn, h0eq]
    calc x (R := R) k m hkm' (d k) *
            (x (R := R) i m him a * colWord m L d)
        = (x (R := R) k m hkm' (d k) * x (R := R) i m him a) *
            colWord m L d := (mul_assoc _ _ _).symm
      _ = (x (R := R) i m him a * x (R := R) k m hkm' (d k)) *
            colWord m L d := by rw [hsw]
      _ = x (R := R) i m him a *
            (x (R := R) k m hkm' (d k) * colWord m L d) :=
        mul_assoc _ _ _

/-- Right insertion into a same-column word: merging `x i m a` on the
right adds `a` to the `(i, m)` coefficient and leaves every other slot
unchanged. Uses only disjoint swaps and same-pair addition. -/
private theorem col_right_insert (L : List ℕ) (m : ℕ) (d : ℕ → R)
    (i : ℕ) (him : i ≠ m) (a : R) :
    (∀ k ∈ L, k < m) → L.Nodup → i ∈ L →
    colWord m L d * x (R := R) i m him a =
      colWord m L (colUpdR d i a) := by
  intro hb hnod hmem
  revert hb hnod hmem
  induction L with
  | nil =>
    intro _hb _hnod hmem
    simp at hmem
  | cons k L ih =>
    intro hb hnod hmem
    have hkm : k < m := hb k (List.mem_cons.mpr (Or.inl rfl))
    have hkb : ∀ k' ∈ L, k' < m :=
      fun k' hk' => hb k' (List.mem_cons.mpr (Or.inr hk'))
    have hkm' : k ≠ m := Nat.ne_of_lt hkm
    by_cases hki : k = i
    · subst k
      have hni : i ∉ L := (List.nodup_cons.mp hnod).1
      have hne : ∀ k' ∈ L, k' ≠ i := by
        intro k' hk' hcon
        subst k'
        exact hni hk'
      have hcomm :
          colWord m L d * x (R := R) i m him a =
            x (R := R) i m him a * colWord m L d :=
        colWord_commute_through L m d i him a hkb hne
      have hupd : ∀ k' ∈ L, colUpdR d i a k' = d k' :=
        fun k' hk' => colUpdR_of_ne d i a k' (hne k' hk')
      have hR : colWord m L (colUpdR d i a) = colWord m L d :=
        colWord_congr L m hupd
      have hadd :
          x (R := R) i m him (d i) * x (R := R) i m him a =
            x (R := R) i m him (d i + a) :=
        upperUnipotent_samePair_add him (d i) a
      have h0eqi :
          (if h : i ≠ m then x (R := R) i m h (d i) else 1) =
            x (R := R) i m him (d i) :=
        dite_eq_left him
      have h0eq' :
          (if h : i ≠ m then x (R := R) i m h (colUpdR d i a i) else 1) =
            x (R := R) i m him (d i + a) := by
        rw [colUpdR_self]
        exact dite_eq_left him
      rw [colWord_cons, colWord_cons]
      have e0 :
          ((if h : i ≠ m then x (R := R) i m h (d i) else 1) *
            colWord m L d) * x (R := R) i m him a =
          (if h : i ≠ m then x (R := R) i m h (d i) else 1) *
            (colWord m L d * x (R := R) i m him a) :=
        mul_assoc _ _ _
      rw [e0, hcomm, h0eqi]
      have e1 :
          x (R := R) i m him (d i) *
              (x (R := R) i m him a * colWord m L d) =
            (x (R := R) i m him (d i) * x (R := R) i m him a) *
              colWord m L d := (mul_assoc _ _ _).symm
      rw [e1, hadd, h0eq', hR]
    · have hnodT : L.Nodup := (List.nodup_cons.mp hnod).2
      have hmemT : i ∈ L := by
        obtain hcon | h := List.mem_cons.mp hmem
        · exact False.elim (hki hcon.symm)
        · exact h
      have ih' := ih hkb hnodT hmemT
      have hdkeq : colUpdR d i a k = d k :=
        colUpdR_of_ne d i a k hki
      rw [colWord_cons, colWord_cons]
      have e0 :
          ((if h : k ≠ m then x (R := R) k m h (d k) else 1) *
            colWord m L d) * x (R := R) i m him a =
          (if h : k ≠ m then x (R := R) k m h (d k) else 1) *
            (colWord m L d * x (R := R) i m him a) :=
        mul_assoc _ _ _
      rw [e0, ih', hdkeq]

/-- Left insertion into a same-column word: merging `x i m t` on the
left adds `t` on the left of the `(i, m)` coefficient. -/
private theorem col_left_insert (L : List ℕ) (m : ℕ) (d : ℕ → R)
    (i : ℕ) (him : i ≠ m) (t : R) :
    (∀ k ∈ L, k < m) → L.Nodup → i ∈ L →
    x (R := R) i m him t * colWord m L d =
      colWord m L (colUpdL d i t) := by
  intro hb hnod hmem
  revert hb hnod hmem
  induction L with
  | nil =>
    intro _hb _hnod hmem
    simp at hmem
  | cons k L ih =>
    intro hb hnod hmem
    have hkm : k < m := hb k (List.mem_cons.mpr (Or.inl rfl))
    have hkb : ∀ k' ∈ L, k' < m :=
      fun k' hk' => hb k' (List.mem_cons.mpr (Or.inr hk'))
    have hkm' : k ≠ m := Nat.ne_of_lt hkm
    by_cases hki : k = i
    · subst k
      have hni : i ∉ L := (List.nodup_cons.mp hnod).1
      have hne : ∀ k' ∈ L, k' ≠ i := by
        intro k' hk' hcon
        subst k'
        exact hni hk'
      have hcomm :
          x (R := R) i m him t * colWord m L d =
            colWord m L d * x (R := R) i m him t :=
        (colWord_commute_through L m d i him t hkb hne).symm
      have hupd : ∀ k' ∈ L, colUpdL d i t k' = d k' :=
        fun k' hk' => colUpdL_of_ne d i t k' (hne k' hk')
      have hR : colWord m L (colUpdL d i t) = colWord m L d :=
        colWord_congr L m hupd
      have hadd :
          x (R := R) i m him t * x (R := R) i m him (d i) =
            x (R := R) i m him (t + d i) :=
        upperUnipotent_samePair_add him t (d i)
      have h0eqi :
          (if h : i ≠ m then x (R := R) i m h (d i) else 1) =
            x (R := R) i m him (d i) :=
        dite_eq_left him
      have h0eq' :
          (if h : i ≠ m then x (R := R) i m h (colUpdL d i t i) else 1) =
            x (R := R) i m him (t + d i) := by
        rw [colUpdL_self]
        exact dite_eq_left him
      rw [colWord_cons, colWord_cons]
      have e0 :
          x (R := R) i m him t *
              ((if h : i ≠ m then x (R := R) i m h (d i) else 1) *
                colWord m L d) =
            (x (R := R) i m him t *
              (if h : i ≠ m then x (R := R) i m h (d i) else 1)) *
              colWord m L d := (mul_assoc _ _ _).symm
      rw [e0, h0eqi, hadd, h0eq', hR]
    · have hnodT : L.Nodup := (List.nodup_cons.mp hnod).2
      have hmemT : i ∈ L := by
        obtain hcon | h := List.mem_cons.mp hmem
        · exact False.elim (hki hcon.symm)
        · exact h
      have ih' := ih hkb hnodT hmemT
      have hdkeq : colUpdL d i t k = d k :=
        colUpdL_of_ne d i t k hki
      have h0eq :
          (if h : k ≠ m then x (R := R) k m h (d k) else 1) =
            x (R := R) k m hkm' (d k) :=
        dite_eq_left hkm'
      have hsw :
          x (R := R) i m him t * x (R := R) k m hkm' (d k) =
            x (R := R) k m hkm' (d k) * x (R := R) i m him t :=
        (upperUnipotent_disjointSwap_comm him hkm' him (Ne.symm hkm') t
          (d k)).symm
      rw [colWord_cons, colWord_cons]
      have e0 :
          x (R := R) i m him t *
              ((if h : k ≠ m then x (R := R) k m h (d k) else 1) *
                colWord m L d) =
            (x (R := R) i m him t *
              (if h : k ≠ m then x (R := R) k m h (d k) else 1)) *
              colWord m L d := (mul_assoc _ _ _).symm
      rw [e0, h0eq, hsw]
      have e1 :
          (x (R := R) k m hkm' (d k) * x (R := R) i m him t) *
              colWord m L d =
            x (R := R) k m hkm' (d k) *
              (x (R := R) i m him t * colWord m L d) :=
        mul_assoc _ _ _
      rw [e1, ih']
      have h0eq'' :
          (if h : k ≠ m then x (R := R) k m h (colUpdL d i t k) else 1) =
            x (R := R) k m hkm' (d k) := by
        rw [hdkeq]
        exact dite_eq_left hkm'
      rw [h0eq'']

/-- Bubbling a generator left through a later column: every factor either
commutes past (disjoint) or contributes one Chevalley correction, and all
corrections lie in the same column, hence merge into a single correction
generator on the left. -/
private theorem bubble_later (L : List ℕ) (l : ℕ) (i j : ℕ) (d : ℕ → R)
    (hij : i ≠ j) (hlt : i < j) (hjl : j < l) (a : R) :
    (∀ k ∈ L, k < l) →
    ∃ t : R, colWord l L d * x (R := R) i j hij a =
      x (R := R) i l (Nat.ne_of_lt (Nat.lt_trans hlt hjl)) t *
        (x (R := R) i j hij a * colWord l L d) := by
  intro hb
  revert hb
  induction L with
  | nil =>
    intro _hb
    refine ⟨0, ?_⟩
    simp [colWord]
  | cons k0 L ih =>
    intro hb
    have hk0 : k0 < l := hb k0 (List.mem_cons.mpr (Or.inl rfl))
    have hbt : ∀ k ∈ L, k < l :=
      fun k hk => hb k (List.mem_cons.mpr (Or.inr hk))
    obtain ⟨tR, ihR⟩ := ih hbt
    have hk0' : k0 ≠ l := Nat.ne_of_lt hk0
    have hil : i ≠ l := Nat.ne_of_lt (Nat.lt_trans hlt hjl)
    have h0eq :
        (if h : k0 ≠ l then x (R := R) k0 l h (d k0) else 1) =
          x (R := R) k0 l hk0' (d k0) :=
      dite_eq_left hk0'
    rw [colWord_cons]
    have e0 :
        ((if h : k0 ≠ l then x (R := R) k0 l h (d k0) else 1) *
          colWord l L d) * x (R := R) i j hij a =
        (if h : k0 ≠ l then x (R := R) k0 l h (d k0) else 1) *
          (colWord l L d * x (R := R) i j hij a) :=
      mul_assoc _ _ _
    rw [e0, h0eq, ihR]
    by_cases hk0j : k0 = j
    · subst k0
      have h1 :
          x (R := R) j l hk0' (d j) * x (R := R) i l hil tR =
            x (R := R) i l hil tR * x (R := R) j l hk0' (d j) :=
        upperUnipotent_disjointSwap_comm hil hk0' hil (Ne.symm hk0') tR
          (d j)
      have hchev :
          x (R := R) j l hk0' (d j) * x (R := R) i j hij a =
            x (R := R) i l hil (-(a * d j)) *
              (x (R := R) i j hij a * x (R := R) j l hk0' (d j)) :=
        upperUnipotent_mixedSwap_chev hlt hjl a (d j)
      refine ⟨tR + -(a * d j), ?_⟩
      calc x (R := R) j l hk0' (d j) *
              (x (R := R) i l hil tR *
                (x (R := R) i j hij a * colWord l L d))
          = (x (R := R) j l hk0' (d j) * x (R := R) i l hil tR) *
              (x (R := R) i j hij a * colWord l L d) :=
            (mul_assoc _ _ _).symm
        _ = (x (R := R) i l hil tR * x (R := R) j l hk0' (d j)) *
              (x (R := R) i j hij a * colWord l L d) := by rw [h1]
        _ = x (R := R) i l hil tR *
              (x (R := R) j l hk0' (d j) *
                (x (R := R) i j hij a * colWord l L d)) :=
            mul_assoc _ _ _
        _ = x (R := R) i l hil tR *
              ((x (R := R) j l hk0' (d j) * x (R := R) i j hij a) *
                colWord l L d) := by
            exact congrArg _ (mul_assoc _ _ _).symm
        _ = x (R := R) i l hil tR *
              ((x (R := R) i l hil (-(a * d j)) *
                (x (R := R) i j hij a * x (R := R) j l hk0' (d j))) *
                colWord l L d) := by rw [hchev]
        _ = x (R := R) i l hil tR *
              (x (R := R) i l hil (-(a * d j)) *
                ((x (R := R) i j hij a * x (R := R) j l hk0' (d j)) *
                  colWord l L d)) := by
            exact congrArg _ (mul_assoc _ _ _)
        _ = x (R := R) i l hil tR *
              (x (R := R) i l hil (-(a * d j)) *
                (x (R := R) i j hij a *
                  (x (R := R) j l hk0' (d j) * colWord l L d))) := by
            rw [mul_assoc (x (R := R) i j hij a)
              (x (R := R) j l hk0' (d j)) (colWord l L d)]
        _ = (x (R := R) i l hil tR *
              x (R := R) i l hil (-(a * d j))) *
              (x (R := R) i j hij a *
                (x (R := R) j l hk0' (d j) * colWord l L d)) :=
            (mul_assoc _ _ _).symm
        _ = x (R := R) i l hil (tR + -(a * d j)) *
              (x (R := R) i j hij a *
                (x (R := R) j l hk0' (d j) * colWord l L d)) := by
            rw [upperUnipotent_samePair_add hil tR (-(a * d j))]
    · have h1 :
          x (R := R) k0 l hk0' (d k0) * x (R := R) i l hil tR =
            x (R := R) i l hil tR * x (R := R) k0 l hk0' (d k0) :=
        upperUnipotent_disjointSwap_comm hil hk0' hil (Ne.symm hk0') tR
          (d k0)
      have hdis :
          x (R := R) k0 l hk0' (d k0) * x (R := R) i j hij a =
            x (R := R) i j hij a * x (R := R) k0 l hk0' (d k0) :=
        upperUnipotent_disjointSwap_comm hij hk0' hil (Ne.symm hk0j) a
          (d k0)
      refine ⟨tR, ?_⟩
      calc x (R := R) k0 l hk0' (d k0) *
              (x (R := R) i l hil tR *
                (x (R := R) i j hij a * colWord l L d))
          = (x (R := R) k0 l hk0' (d k0) * x (R := R) i l hil tR) *
              (x (R := R) i j hij a * colWord l L d) :=
            (mul_assoc _ _ _).symm
        _ = (x (R := R) i l hil tR * x (R := R) k0 l hk0' (d k0)) *
              (x (R := R) i j hij a * colWord l L d) := by rw [h1]
        _ = x (R := R) i l hil tR *
              (x (R := R) k0 l hk0' (d k0) *
                (x (R := R) i j hij a * colWord l L d)) :=
            mul_assoc _ _ _
        _ = x (R := R) i l hil tR *
              ((x (R := R) k0 l hk0' (d k0) * x (R := R) i j hij a) *
                colWord l L d) := by
            exact congrArg _ (mul_assoc _ _ _).symm
        _ = x (R := R) i l hil tR *
              ((x (R := R) i j hij a * x (R := R) k0 l hk0' (d k0)) *
                colWord l L d) := by rw [hdis]
        _ = x (R := R) i l hil tR *
              (x (R := R) i j hij a *
                (x (R := R) k0 l hk0' (d k0) * colWord l L d)) := by
            exact congrArg _ (mul_assoc _ _ _)

/-- Prefix glue for the `j < m` rank step: column `m` takes the
left-inserted correction, the prefix keeps `c₁`. -/
private def gluePre (c₁ : ℕ × ℕ → R) (m : ℕ) (i : ℕ) (t : R)
    (c : ℕ × ℕ → R) : ℕ × ℕ → R :=
  fun p => if p.2 = m then (if p.1 = i then t + c p else c p) else c₁ p

private theorem gluePre_col (c₁ : ℕ × ℕ → R) (m : ℕ) (i : ℕ) (t : R)
    (c : ℕ × ℕ → R) (k : ℕ) :
    gluePre c₁ m i t c (k, m) =
      (if k = i then t + c (k, m) else c (k, m)) := by
  change (if (k, m).2 = m then
      (if (k, m).1 = i then t + c (k, m) else c (k, m)) else
      c₁ (k, m)) = (if k = i then t + c (k, m) else c (k, m))
  rw [ite_eq_left rfl]

private theorem gluePre_pre (c₁ : ℕ × ℕ → R) (m : ℕ) (i : ℕ) (t : R)
    (c : ℕ × ℕ → R) (p : ℕ × ℕ) (h : p.2 ≠ m) :
    gluePre c₁ m i t c p = c₁ p := by
  change (if p.2 = m then (if p.1 = i then t + c p else c p) else c₁ p) =
    c₁ p
  exact ite_eq_right h

/-- Last-column glue for the `j = m` rank step: column `m` takes the
right-inserted generator, every other pair keeps `c`. -/
private def glueLast (m : ℕ) (i : ℕ) (a : R)
    (c : ℕ × ℕ → R) : ℕ × ℕ → R :=
  fun p => if p.2 = m then (if p.1 = i then c p + a else c p) else c p

private theorem glueLast_col (m : ℕ) (i : ℕ) (a : R)
    (c : ℕ × ℕ → R) (k : ℕ) :
    glueLast m i a c (k, m) =
      (if k = i then c (k, m) + a else c (k, m)) := by
  change (if (k, m).2 = m then
      (if (k, m).1 = i then c (k, m) + a else c (k, m)) else
      c (k, m)) = (if k = i then c (k, m) + a else c (k, m))
  rw [ite_eq_left rfl]

private theorem glueLast_pre (m : ℕ) (i : ℕ) (a : R)
    (c : ℕ × ℕ → R) (p : ℕ × ℕ) (h : p.2 ≠ m) :
    glueLast m i a c p = c p := by
  change (if p.2 = m then (if p.1 = i then c p + a else c p) else c p) =
    c p
  exact ite_eq_right h

/-- Every rank-`m` root is a rank-`m + 1` root. -/
private theorem roots_mono_entry (m : ℕ) (p : ℕ × ℕ)
    (h : p ∈ orderedPositiveRoots m) : p ∈ orderedPositiveRoots (m + 1) := by
  obtain ⟨a, b⟩ := p
  have hmem := orderedPositiveRoots_mem.mp h
  exact orderedPositiveRoots_mem.mpr ⟨hmem.1, Nat.lt_succ_of_lt hmem.2⟩

/-- The ordered evaluator depends only on coefficients on the root list. -/
private theorem prod_congr_on_roots :
    ∀ (n : ℕ) (d₁ d₂ : ℕ × ℕ → R),
    (∀ p ∈ orderedPositiveRoots n, d₁ p = d₂ p) →
    upperUnipotentProd (R := R) n d₁ = upperUnipotentProd n d₂ := by
  intro n
  induction n with
  | zero =>
    intro d₁ d₂ _h
    simp
  | succ m ih =>
    intro d₁ d₂ h
    have hsucc1 := upperUnipotentProd_succ m d₁
    have hsucc2 := upperUnipotentProd_succ m d₂
    rw [hsucc1, hsucc2]
    have hpre : ∀ p ∈ orderedPositiveRoots m, d₁ p = d₂ p :=
      fun p hp => h p (roots_mono_entry m p hp)
    have hcol :
        ∀ k ∈ List.range m,
          (fun k => d₁ (k, m)) k = (fun k => d₂ (k, m)) k := by
      intro k hk
      change d₁ (k, m) = d₂ (k, m)
      exact h (k, m)
        (orderedPositiveRoots_mem.mpr
          ⟨List.mem_range.mp hk, Nat.lt_succ_self m⟩)
    have epre := ih d₁ d₂ hpre
    have bcol :
        ((List.range m).map (fun i =>
          if h : i ≠ m then x (R := R) i m h (d₁ (i, m)) else 1)).prod =
        colWord m (List.range m) (fun k => d₁ (k, m)) := rfl
    have bcol2 :
        ((List.range m).map (fun i =>
          if h : i ≠ m then x (R := R) i m h (d₂ (i, m)) else 1)).prod =
        colWord m (List.range m) (fun k => d₂ (k, m)) := rfl
    have hcolEq := colWord_congr (List.range m) m hcol
    rw [bcol, bcol2, hcolEq, epre]

/-- Rank induction for right insertion: the suffix columns to the right of
`(i, j)` contribute at most a same-column correction each, absorbed
locally, while the prefix is handled by the induction hypothesis. -/
private theorem insert_right_aux :
    ∀ (n : ℕ) (c : ℕ × ℕ → R) (i j : ℕ) (a : R) (hij : i ≠ j)
      (_hlt : i < j) (_hj : j < n),
    ∃ c' : ℕ × ℕ → R,
      upperUnipotentProd (R := R) n c * x (R := R) i j hij a =
        upperUnipotentProd n c' ∧
      ∀ p ∉ orderedPositiveRoots n, c' p = c p := by
  intro n
  induction n with
  | zero =>
    intro c i j a hij _ hj
    exact absurd hj (by omega)
  | succ m ih =>
    intro c i j a hij hlt hj
    have hsplit : j < m ∨ j = m := by omega
    obtain hjm | hjeq := hsplit
    · have him : i ≠ m := Nat.ne_of_lt (Nat.lt_trans hlt hjm)
      have him_lt : i < m := Nat.lt_trans hlt hjm
      have hbnd : ∀ k ∈ List.range m, k < m :=
        fun k hk => List.mem_range.mp hk
      have hnodR : (List.range m).Nodup := List.nodup_range
      have hmem_i : i ∈ List.range m := List.mem_range.mpr him_lt
      obtain ⟨t, hbub⟩ :=
        bubble_later (List.range m) m i j (fun k => c (k, m)) hij hlt
          hjm a hbnd
      obtain ⟨c₁, hc1eq, hc1sup⟩ := ih c i j a hij hlt hjm
      have hyc :
          x (R := R) i m him t * x (R := R) i j hij a =
            x (R := R) i j hij a * x (R := R) i m him t :=
        upperUnipotent_disjointSwap_comm hij him him (Ne.symm hij) a t
      have hleft :=
        col_left_insert (List.range m) m (fun k => c (k, m)) i him t
          hbnd hnodR hmem_i
      refine ⟨gluePre c₁ m i t c, ?_, ?_⟩
      · have hsucc := upperUnipotentProd_succ m c
        have hsucc' := upperUnipotentProd_succ m (gluePre c₁ m i t c)
        rw [hsucc, hsucc']
        have bcol :
            ((List.range m).map (fun i =>
              if h : i ≠ m then x (R := R) i m h (c (i, m)) else 1)).prod =
            colWord m (List.range m) (fun k => c (k, m)) := rfl
        have bcol' :
            ((List.range m).map (fun k =>
              if h : k ≠ m then
                x (R := R) k m h (gluePre c₁ m i t c (k, m)) else 1)).prod =
            colWord m (List.range m)
              (fun k => gluePre c₁ m i t c (k, m)) := rfl
        rw [bcol, bcol']
        have hcolEq :
            colWord m (List.range m)
                (fun k => gluePre c₁ m i t c (k, m)) =
              colWord m (List.range m)
                (colUpdL (fun k => c (k, m)) i t) := by
          apply colWord_congr
          intro k _hk
          rw [gluePre_col]
          rfl
        have hpre : upperUnipotentProd m (gluePre c₁ m i t c) =
            upperUnipotentProd m c₁ := by
          apply prod_congr_on_roots
          intro p hp
          obtain ⟨a', b⟩ := p
          have hbm : b < m := (orderedPositiveRoots_mem.mp hp).2
          have h2 : (a', b).2 ≠ m := by
            intro hcon
            have hbe : (a', b).2 = b := rfl
            omega
          exact gluePre_pre c₁ m i t c (a', b) h2
        have step1 :
            (upperUnipotentProd m c *
              colWord m (List.range m) (fun k => c (k, m))) *
              x (R := R) i j hij a =
            upperUnipotentProd m c *
              (x (R := R) i m him t *
                (x (R := R) i j hij a *
                  colWord m (List.range m) (fun k => c (k, m)))) :=
          calc (upperUnipotentProd m c *
                  colWord m (List.range m) (fun k => c (k, m))) *
                  x (R := R) i j hij a
              = upperUnipotentProd m c *
                  (colWord m (List.range m) (fun k => c (k, m)) *
                    x (R := R) i j hij a) :=
                mul_assoc _ _ _
            _ = upperUnipotentProd m c *
                  (x (R := R) i m him t *
                    (x (R := R) i j hij a *
                      colWord m (List.range m) (fun k => c (k, m)))) := by
                exact congrArg _ hbub
        have step2 :
            upperUnipotentProd m c *
                (x (R := R) i m him t *
                  (x (R := R) i j hij a *
                    colWord m (List.range m) (fun k => c (k, m)))) =
              (upperUnipotentProd m c * x (R := R) i j hij a) *
                (x (R := R) i m him t *
                  colWord m (List.range m) (fun k => c (k, m))) := by
          have e :
              x (R := R) i m him t *
                  (x (R := R) i j hij a *
                    colWord m (List.range m) (fun k => c (k, m))) =
                x (R := R) i j hij a *
                  (x (R := R) i m him t *
                    colWord m (List.range m) (fun k => c (k, m))) := by
            calc x (R := R) i m him t *
                    (x (R := R) i j hij a *
                      colWord m (List.range m) (fun k => c (k, m)))
                = (x (R := R) i m him t * x (R := R) i j hij a) *
                    colWord m (List.range m) (fun k => c (k, m)) :=
                  (mul_assoc _ _ _).symm
              _ = (x (R := R) i j hij a * x (R := R) i m him t) *
                    colWord m (List.range m) (fun k => c (k, m)) := by
                  rw [hyc]
              _ = x (R := R) i j hij a *
                    (x (R := R) i m him t *
                      colWord m (List.range m) (fun k => c (k, m))) :=
                  mul_assoc _ _ _
          calc upperUnipotentProd m c *
                  (x (R := R) i m him t *
                    (x (R := R) i j hij a *
                      colWord m (List.range m) (fun k => c (k, m))))
              = upperUnipotentProd m c *
                  (x (R := R) i j hij a *
                    (x (R := R) i m him t *
                      colWord m (List.range m) (fun k => c (k, m)))) := by
                exact congrArg _ e
            _ = (upperUnipotentProd m c * x (R := R) i j hij a) *
                  (x (R := R) i m him t *
                    colWord m (List.range m) (fun k => c (k, m))) :=
                (mul_assoc _ _ _).symm
        rw [step1, step2, hc1eq, hleft, hcolEq, hpre]
      · intro p hp
        obtain ⟨a', b⟩ := p
        by_cases h2 : b = m
        · subst b
          have hai : a' ≠ i := by
            intro hcon
            subst a'
            exact hp (orderedPositiveRoots_mem.mpr
              ⟨him_lt, Nat.lt_succ_self m⟩)
          change (if (a', m).2 = m then
              (if (a', m).1 = i then t + c (a', m) else c (a', m)) else
              c₁ (a', m)) = c (a', m)
          rw [ite_eq_left rfl, ite_eq_right hai]
        · have h2' : (a', b).2 ≠ m := by
            intro hcon
            have hbe : (a', b).2 = b := rfl
            omega
          have e := gluePre_pre c₁ m i t c (a', b) h2'
          rw [e]
          exact hc1sup (a', b)
            (fun hcon => hp (roots_mono_entry m (a', b) hcon))
    · subst j
      have hbnd : ∀ k ∈ List.range m, k < m :=
        fun k hk => List.mem_range.mp hk
      have hnodR : (List.range m).Nodup := List.nodup_range
      have himem : i ∈ List.range m := List.mem_range.mpr hlt
      have hins :=
        col_right_insert (List.range m) m (fun k => c (k, m)) i hij a
          hbnd hnodR himem
      refine ⟨glueLast m i a c, ?_, ?_⟩
      · have hsucc := upperUnipotentProd_succ m c
        have hsucc' := upperUnipotentProd_succ m (glueLast m i a c)
        rw [hsucc, hsucc']
        have bcol :
            ((List.range m).map (fun i =>
              if h : i ≠ m then x (R := R) i m h (c (i, m)) else 1)).prod =
            colWord m (List.range m) (fun k => c (k, m)) := rfl
        have bcol' :
            ((List.range m).map (fun k =>
              if h : k ≠ m then
                x (R := R) k m h (glueLast m i a c (k, m)) else 1)).prod =
            colWord m (List.range m)
              (fun k => glueLast m i a c (k, m)) := rfl
        rw [bcol, bcol']
        have hcolEq :
            colWord m (List.range m)
                (fun k => glueLast m i a c (k, m)) =
              colWord m (List.range m)
                (colUpdR (fun k => c (k, m)) i a) := by
          apply colWord_congr
          intro k _hk
          rw [glueLast_col]
          rfl
        have hpre : upperUnipotentProd m (glueLast m i a c) =
            upperUnipotentProd m c := by
          apply prod_congr_on_roots
          intro p hp
          obtain ⟨a', b⟩ := p
          have hbm : b < m := (orderedPositiveRoots_mem.mp hp).2
          have h2 : (a', b).2 ≠ m := by
            intro hcon
            have hbe : (a', b).2 = b := rfl
            omega
          exact glueLast_pre m i a c (a', b) h2
        have step1 :
            (upperUnipotentProd m c *
              colWord m (List.range m) (fun k => c (k, m))) *
              x (R := R) i m hij a =
            upperUnipotentProd m c *
              colWord m (List.range m)
                (colUpdR (fun k => c (k, m)) i a) :=
          calc (upperUnipotentProd m c *
                  colWord m (List.range m) (fun k => c (k, m))) *
                  x (R := R) i m hij a
              = upperUnipotentProd m c *
                  (colWord m (List.range m) (fun k => c (k, m)) *
                    x (R := R) i m hij a) :=
                mul_assoc _ _ _
            _ = upperUnipotentProd m c *
                  colWord m (List.range m)
                    (colUpdR (fun k => c (k, m)) i a) := by
                exact congrArg _ hins
        rw [step1, hcolEq, hpre]
      · intro p hp
        obtain ⟨a', b⟩ := p
        by_cases h2 : b = m
        · subst b
          have hai : a' ≠ i := by
            intro hcon
            subst a'
            exact hp (orderedPositiveRoots_mem.mpr
              ⟨hlt, Nat.lt_succ_self m⟩)
          change (if (a', m).2 = m then
              (if (a', m).1 = i then c (a', m) + a else c (a', m)) else
              c (a', m)) = c (a', m)
          rw [ite_eq_left rfl, ite_eq_right hai]
        · have h2' : (a', b).2 ≠ m := by
            intro hcon
            have hbe : (a', b).2 = b := rfl
            omega
          exact glueLast_pre m i a c (a', b) h2'

/-- Right insertion for ordered upper-unipotent products: for `i ≠ j`,
`i < j`, `j < n`, right-multiplying `upperUnipotentProd n c` by
`x i j hij a` recollects to `upperUnipotentProd n c'` for an updated
coefficient assignment `c'` that agrees with `c` off
`orderedPositiveRoots n`. The Chevalley correction at each later column
lands in that same column and is absorbed locally; earlier columns are
handled by rank induction. Purpose: atomic right-insertion collection
step toward ordered upper-unipotent words. Nonclaims: no collection
termination, multiplication/inversion closure, ordered normal form,
coefficient or evaluator uniqueness, `toStableE` injectivity, TWT/Bruhat
statement, kernel generation, or Matsumoto claim. -/
public theorem upperUnipotentProd_insert_right {n i j : ℕ} (hij : i ≠ j)
    (hlt : i < j) (hj : j < n) (c : ℕ × ℕ → R) (a : R) :
    ∃ c' : ℕ × ℕ → R,
      upperUnipotentProd (R := R) n c * x i j hij a =
        upperUnipotentProd n c' ∧
      ∀ p ∉ orderedPositiveRoots n, c' p = c p :=
  insert_right_aux n c i j a hij hlt hj

/-- Absorb one successor column word on the right: for `m < n` and every
`k ∈ L` with `k < m`, `upperUnipotentProd n c * colWord m L e` recollects
to another `upperUnipotentProd`, preserving `c` off `orderedPositiveRoots n`.
Proved by induction on `L` with accepted `upperUnipotentProd_insert_right`. -/
private theorem mul_col_absorb (n m : ℕ) (hm : m < n) (L : List ℕ)
    (hL : ∀ k ∈ L, k < m) (c : ℕ × ℕ → R) (e : ℕ → R) :
    ∃ c' : ℕ × ℕ → R,
      upperUnipotentProd (R := R) n c * colWord m L e =
        upperUnipotentProd n c' ∧
      ∀ p ∉ orderedPositiveRoots n, c' p = c p := by
  revert hL c
  induction L with
  | nil =>
    intro hL c
    refine ⟨c, ?_, fun p _ => rfl⟩
    simp [colWord]
  | cons k L ih =>
    intro hL c
    have hkm : k < m := hL k (List.mem_cons.mpr (Or.inl rfl))
    have hL' : ∀ k' ∈ L, k' < m :=
      fun k' hk' => hL k' (List.mem_cons.mpr (Or.inr hk'))
    have hkm' : k ≠ m := Nat.ne_of_lt hkm
    obtain ⟨c₁, hc₁eq, hc₁sup⟩ :=
      upperUnipotentProd_insert_right hkm' hkm hm c (e k)
    obtain ⟨c', hc'eq, hc'sup⟩ := ih hL' c₁
    refine ⟨c', ?_, fun p hp => (hc'sup p hp).trans (hc₁sup p hp)⟩
    have hhead :
        (if h : k ≠ m then x (R := R) k m h (e k) else 1) =
          x (R := R) k m hkm' (e k) :=
      dite_eq_left hkm'
    have hcol : colWord m (k :: L) e =
        x (R := R) k m hkm' (e k) * colWord m L e := by
      rw [colWord_cons, hhead]
    rw [hcol, ← mul_assoc, hc₁eq, hc'eq]

/-- Absorb a right prefix of rank `m ≤ n`: `upperUnipotentProd n c₁ *
upperUnipotentProd m c₂` recollects to another `upperUnipotentProd n`,
preserving `c₁` off `orderedPositiveRoots n`. Proved by induction on `m`
with `upperUnipotentProd_succ`, the induction hypothesis for the prefix,
and `mul_col_absorb` for `List.range m`. -/
private theorem mul_prefix_absorb (n : ℕ) (c₁ c₂ : ℕ × ℕ → R) (m : ℕ)
    (hmn : m ≤ n) :
    ∃ c' : ℕ × ℕ → R,
      upperUnipotentProd (R := R) n c₁ * upperUnipotentProd (R := R) m c₂ =
        upperUnipotentProd n c' ∧
      ∀ p ∉ orderedPositiveRoots n, c' p = c₁ p := by
  revert hmn
  induction m with
  | zero =>
    intro _hmn
    refine ⟨c₁, ?_, fun p _ => rfl⟩
    simp
  | succ m ih =>
    intro hmn
    have hmn' : m ≤ n := by omega
    have hmlt : m < n := by omega
    obtain ⟨cMid, hcMideq, hcMidsup⟩ := ih hmn'
    have hsucc : upperUnipotentProd (R := R) (m + 1) c₂ =
        upperUnipotentProd m c₂ *
          colWord m (List.range m) (fun k => c₂ (k, m)) := by
      rw [upperUnipotentProd_succ]
      rfl
    have hbnd : ∀ k ∈ List.range m, k < m :=
      fun k hk => List.mem_range.mp hk
    obtain ⟨c', hc'eq, hc'sup⟩ :=
      mul_col_absorb n m hmlt (List.range m) hbnd cMid
        (fun k => c₂ (k, m))
    refine ⟨c', ?_, fun p hp => (hc'sup p hp).trans (hcMidsup p hp)⟩
    rw [hsucc, ← mul_assoc, hcMideq, hc'eq]

/-- Multiplication closure for ordered upper-unipotent products: the
head-left product `upperUnipotentProd n c₁ * upperUnipotentProd n c₂`
recollects to `upperUnipotentProd n c'` for an updated coefficient
assignment `c'` that agrees with the left assignment `c₁` off
`orderedPositiveRoots n`. The `m = n` specialization of `mul_prefix_absorb`,
which inducts on the right rank with `upperUnipotentProd_succ` and absorbs
each successor column by `mul_col_absorb`. Purpose: ordered-evaluator
multiplication closure step toward ordered upper-unipotent words.
Nonclaims: no inversion closure, collection termination, ordered
normal-form existence/uniqueness, coefficient/evaluator uniqueness beyond
the stated preservation, `toStableE` injectivity, TWT/Bruhat statement,
kernel generation, or Matsumoto claim. -/
public theorem upperUnipotentProd_mul_closed (n : ℕ) (c₁ c₂ : ℕ × ℕ → R) :
    ∃ c' : ℕ × ℕ → R,
      upperUnipotentProd (R := R) n c₁ * upperUnipotentProd (R := R) n c₂ =
        upperUnipotentProd n c' ∧
      ∀ p ∉ orderedPositiveRoots n, c' p = c₁ p :=
  mul_prefix_absorb n c₁ c₂ n (Nat.le_refl n)

/-- Vanishing coefficients give the identity: if `d` is zero on
`orderedPositiveRoots n`, then `upperUnipotentProd n d = 1`, by rank induction
through `upperUnipotentProd_zero`/`upperUnipotentProd_succ` with each
successor-column zero factor simplified by `x_zero`. -/
private theorem prod_one_of_zero_on_roots :
    ∀ (n : ℕ) (d : ℕ × ℕ → R),
    (∀ p ∈ orderedPositiveRoots n, d p = 0) →
    upperUnipotentProd (R := R) n d = 1 := by
  intro n
  induction n with
  | zero =>
    intro d _h
    exact upperUnipotentProd_zero d
  | succ m ih =>
    intro d h
    have hpre : ∀ p ∈ orderedPositiveRoots m, d p = 0 :=
      fun p hp => h p (roots_mono_entry m p hp)
    have hfactor : ∀ k : ℕ, k < m →
        (if h : k ≠ m then x (R := R) k m h (d (k, m)) else 1) = 1 := by
      intro k hk
      have hmem : (k, m) ∈ orderedPositiveRoots (m + 1) :=
        orderedPositiveRoots_mem.mpr ⟨hk, Nat.lt_succ_self m⟩
      have hd0 : d (k, m) = 0 := h (k, m) hmem
      rw [hd0, dite_eq_left (Nat.ne_of_lt hk), x_zero]
    have hprod : ∀ (L : List ℕ), (∀ i ∈ L, i < m) →
        ((L.map (fun i =>
          if h : i ≠ m then x (R := R) i m h (d (i, m)) else 1))).prod
          = 1 := by
      intro L hb
      induction L with
      | nil => simp
      | cons k L ihL =>
        have hk : k < m := hb k (List.mem_cons.mpr (Or.inl rfl))
        have hb' : ∀ i ∈ L, i < m :=
          fun i hi => hb i (List.mem_cons.mpr (Or.inr hi))
        rw [List.map_cons, List.prod_cons, hfactor k hk, ihL hb', mul_one]
    have hsucc := upperUnipotentProd_succ m d
    have hbnd : ∀ i ∈ List.range m, i < m :=
      fun i hi => List.mem_range.mp hi
    rw [hsucc, ih d hpre, hprod (List.range m) hbnd, mul_one]

/-- Head-first absorption of a reversed negated word: if every pair of `L`
lies in `orderedPositiveRoots n`, then `upperUnipotentProd n c` times the
explicit factor word recollects to another `upperUnipotentProd`, preserving `c`
off `orderedPositiveRoots n`. Each head pair is a positive root by
`orderedPositiveRoots_mem`, hence absorbed by
`upperUnipotentProd_insert_right`; recurse on the tail. -/
private theorem inv_reverse_absorb (n : ℕ) :
    ∀ (L : List (ℕ × ℕ)) (c : ℕ × ℕ → R) (cSrc : ℕ × ℕ → R),
    (∀ p ∈ L, p ∈ orderedPositiveRoots n) →
    ∃ c' : ℕ × ℕ → R,
      upperUnipotentProd (R := R) n c *
          (L.map (fun p =>
            if h : p.1 ≠ p.2 then x (R := R) p.1 p.2 h (-(cSrc p))
            else 1)).prod =
        upperUnipotentProd n c' ∧
      ∀ p ∉ orderedPositiveRoots n, c' p = c p := by
  intro L
  induction L with
  | nil =>
    intro c _cSrc _hL
    refine ⟨c, ?_, fun p _ => rfl⟩
    simp
  | cons hd tl ih =>
    intro c cSrc hL
    have hmem : hd ∈ orderedPositiveRoots n :=
      hL hd (List.mem_cons.mpr (Or.inl rfl))
    have htl : ∀ p ∈ tl, p ∈ orderedPositiveRoots n :=
      fun p hp => hL p (List.mem_cons.mpr (Or.inr hp))
    obtain ⟨i, j⟩ := hd
    have hmem' := orderedPositiveRoots_mem.mp hmem
    have hlt : i < j := hmem'.1
    have hjn : j < n := hmem'.2
    have hij : i ≠ j := ne_of_lt hlt
    have ehead : (if h : (i, j).1 ≠ (i, j).2 then
        x (R := R) (i, j).1 (i, j).2 h (-(cSrc (i, j))) else 1) =
        x (R := R) i j hij (-(cSrc (i, j))) :=
      dite_eq_left hij
    obtain ⟨c₁, hc₁eq, hc₁sup⟩ :=
      upperUnipotentProd_insert_right hij hlt hjn c (-(cSrc (i, j)))
    obtain ⟨c', hc'eq, hc'sup⟩ := ih c₁ cSrc htl
    refine ⟨c', ?_, fun p hp => (hc'sup p hp).trans (hc₁sup p hp)⟩
    rw [List.map_cons, List.prod_cons, ehead, ← mul_assoc, hc₁eq, hc'eq]

/-- Inverse re-collection for ordered upper-unipotent products:
`(upperUnipotentProd n c)⁻¹` equals `upperUnipotentProd n c'` for an updated
coefficient assignment `c'` that agrees with `c` off `orderedPositiveRoots n`.
The accepted inverse word is absorbed head-first: base coefficients vanishing
on the roots evaluate to `1`, and each reversed negated factor is a positive
root reinserted by `upperUnipotentProd_insert_right`. Holds over `[Ring R]`
with no import change. Purpose: ordered-evaluator inversion-closure step toward
ordered upper-unipotent words. Nonclaims: no collection termination, ordered
normal-form existence/uniqueness, coefficient/evaluator uniqueness beyond the
stated off-root preservation, `toStableE` injectivity, TWT/Bruhat statement,
kernel generation, or Matsumoto claim. -/
public theorem upperUnipotentProd_inv_closed (n : ℕ) (c : ℕ × ℕ → R) :
    ∃ c' : ℕ × ℕ → R,
      (upperUnipotentProd (R := R) n c)⁻¹ = upperUnipotentProd n c' ∧
      ∀ p ∉ orderedPositiveRoots n, c' p = c p := by
  have hinv := upperUnipotentProd_inv_eq_reverse_neg_prod n c
  set c₀ : ℕ × ℕ → R :=
    fun p => if p ∈ orderedPositiveRoots n then 0 else c p
  have hbase : upperUnipotentProd (R := R) n c₀ = 1 := by
    apply prod_one_of_zero_on_roots
    intro p hp
    exact ite_eq_left hp
  have hL : ∀ p ∈ (orderedPositiveRoots n).reverse,
      p ∈ orderedPositiveRoots n :=
    fun p hp => List.mem_reverse.mp hp
  obtain ⟨c', hc'eq, hc'sup⟩ := inv_reverse_absorb n _ c₀ c hL
  refine ⟨c', ?_, fun p hp => (hc'sup p hp).trans ?_⟩
  · rw [hbase, one_mul] at hc'eq
    exact hinv.trans hc'eq
  · exact ite_eq_right hp

/-- Subgroup representation: every `g ∈ upperUnipotentSubgroup n` equals
`upperUnipotentProd n c` for a coefficient assignment vanishing off
`orderedPositiveRoots n`. Proved by `Subgroup.closure_induction`: generator via
the zero-coefficient identity plus `upperUnipotentProd_insert_right`, one via
the zero function and `prod_one_of_zero_on_roots`, multiplication via
`upperUnipotentProd_mul_closed`, inversion via `upperUnipotentProd_inv_closed`,
normalizing each witness to zero off the roots. Purpose: ordered-evaluator
subgroup representation toward ordered upper-unipotent words. Nonclaims: no
range/subgroup equality, coefficient/evaluator uniqueness, injectivity,
normal-form uniqueness, TWT/Bruhat statement, kernel generation, or Matsumoto
claim. -/
public theorem upperUnipotentSubgroup_exists_prod_repr {n : ℕ}
    {g : StableSteinberg R} (hg : g ∈ upperUnipotentSubgroup (R := R) n) :
    ∃ c : ℕ × ℕ → R,
      g = upperUnipotentProd n c ∧
      ∀ p ∉ orderedPositiveRoots n, c p = 0 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, j, hij, a, rfl, hlt, _hi, hj⟩ := hx
    have hbase : upperUnipotentProd (R := R) n (fun _ => 0) = 1 :=
      prod_one_of_zero_on_roots n _ (fun p _ => rfl)
    obtain ⟨c', hc'eq, hc'sup⟩ :=
      upperUnipotentProd_insert_right hij hlt hj (fun _ => 0) a
    refine ⟨c', ?_, fun p hp => (hc'sup p hp).trans rfl⟩
    calc x (R := R) i j hij a
        = 1 * x (R := R) i j hij a := by rw [one_mul]
      _ = upperUnipotentProd (R := R) n (fun _ => 0) *
          x (R := R) i j hij a := by rw [hbase]
      _ = upperUnipotentProd n c' := hc'eq
  | one =>
    refine ⟨fun _ => 0, ?_, fun p _ => rfl⟩
    exact (prod_one_of_zero_on_roots n _ (fun p _ => rfl)).symm
  | mul x y _ _ ihx ihy =>
    obtain ⟨c₁, rfl, hc₁norm⟩ := ihx
    obtain ⟨c₂, rfl, _⟩ := ihy
    obtain ⟨c', hc'eq, hc'sup⟩ := upperUnipotentProd_mul_closed n c₁ c₂
    exact ⟨c', hc'eq, fun p hp => (hc'sup p hp).trans (hc₁norm p hp)⟩
  | inv x _ ih =>
    obtain ⟨c₁, rfl, hc₁norm⟩ := ih
    obtain ⟨c', hc'eq, hc'sup⟩ := upperUnipotentProd_inv_closed n c₁
    exact ⟨c', hc'eq, fun p hp => (hc'sup p hp).trans (hc₁norm p hp)⟩

end StableSteinberg

end AlgebraicKTheory
