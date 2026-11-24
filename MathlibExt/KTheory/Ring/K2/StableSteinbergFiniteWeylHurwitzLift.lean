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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergWeylRelations
public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylHurwitz

/-! # Atomic Weyl lift of the labeled right-Hurwitz step

For `n : ℕ` and `[Ring R]`, `weylOfSwapLabel a u` is the stable Steinberg Weyl
element `w_{a.1,a.2}(u)` at the ordered endpoints of the swap label `a`, and
`exists_weylOfSwapLabel_mul_eq_rightHurwitz` lifts one directed right-Hurwitz
step `[a, b] ↦ [b, conjLabel b a]` to an exact product equality
`Wₐ(u) * W_b(v) = W_b(v) * W_{conjLabel b a}(q)` for an exhibited unit `q`.

Orientation is head-left throughout, matching `wordProd` and the accepted
right move: the conjugator `W_b` travels left past the victim `Wₐ`, and the
conjugated label appears on the right with transported coefficient `q`. Every
case goes through the inverse-conjugation invariant
`W_b⁻¹ * Wₐ * W_b = W_{conj}(q)` (never conjugation by `W_b` itself), with
`W_b⁻¹ = W_b(-v)` by `weyl_neg_eq_inv`.

Nonclaims: no `ReflTransGen` trace recursion, no terminal-pair deletion, no
torus/cocycle landing, no strict descent, no kernel generation, no TWT, and no
Matsumoto theorem.
-/

@[expose] public section

namespace AlgebraicKTheory

universe u

variable {R : Type u} [Ring R]

/-- Ordered-label Weyl element `Wₐ(u) = w_{a.1,a.2}(u)` in `St(R)`.

Purpose: coefficient-carrying Weyl meaning of an ordered endpoint label,
preserving the `(a, b)` versus `(b, a)` orientation needed by `weyl_swap`.
The `Fin n` endpoints are coerced by `val` to the `ℕ` indices of
`StableSteinberg.weyl`, with distinctness transported by `Fin.ext`.
Hypotheses: `a.1 ≠ a.2` carried by the label; `[Ring R]` only, no field or
commutativity assumption. Nonclaims: no torus, cocycle, kernel, or Matsumoto
content. -/
public def weylOfSwapLabel {n : ℕ} (a : SwapLabel n) (u : Rˣ) : StableSteinberg R :=
  StableSteinberg.weyl a.val.1.val a.val.2.val (fun h => a.property (Fin.ext h)) u

/-- Coercion of a negated unit. -/
private theorem coe_neg_units (u : Rˣ) : (↑(-u) : R) = -(↑u : R) := rfl

/-- `Fin` inequality transports to `ℕ` through `val`. -/
private theorem fin_val_ne {n : ℕ} {x y : Fin n} (h : x ≠ y) : x.val ≠ y.val :=
  fun he => h (Fin.ext he)

/-- Negation distributes over unit multiplication on both sides. -/
private theorem units_neg_mul_neg (a b : Rˣ) : -a * -b = a * b := by
  apply Units.ext
  simp only [Units.val_mul, neg_mul_neg]

/-- Inverse of a negated unit. -/
private theorem units_inv_neg (v : Rˣ) : (-v)⁻¹ = -(v⁻¹) := by
  have h : -(v⁻¹) * -v = 1 := by rw [units_neg_mul_neg, inv_mul_cancel]
  exact inv_eq_of_mul_eq_one_left h

/-- Double negation of a unit. -/
private theorem units_neg_neg (w : Rˣ) : - -w = w := by
  apply Units.ext
  simp only [neg_neg]

/-- Negated inverse of a negated unit. -/
private theorem units_neg_inv_neg (v : Rˣ) : -(-v)⁻¹ = v⁻¹ := by
  rw [units_inv_neg, units_neg_neg]

/-- Negation of a negated-left product. -/
private theorem units_neg_neg_mul (a b : Rˣ) : -(-a * b) = a * b := by
  apply Units.ext
  simp only [Units.val_mul, neg_mul, neg_neg]

/-- Negation of a product as right-negated product. -/
private theorem units_neg_eq_mul_neg (a b : Rˣ) : -(a * b) = a * -b := by
  apply Units.ext
  simp only [Units.val_mul, coe_neg_units, mul_neg]

/-- Negation of a negated-left factor. -/
private theorem units_neg_mul (a b : Rˣ) : -a * b = -(a * b) := by
  apply Units.ext
  simp only [Units.val_mul, coe_neg_units, neg_mul]

/-- Negation cancels on both sides of a triple product. -/
private theorem units_neg_mul_mul_neg (a b c : Rˣ) : -a * b * -c = a * b * c := by
  have h1 : -a * b = -(a * b) := units_neg_mul a b
  rw [h1]
  exact units_neg_mul_neg (a * b) c

/-- From the inverse-conjugation identity to the forward product form. -/
private theorem mul_eq_of_inv_conj {G : Type*} [Group G] {a b c : G}
    (h : b⁻¹ * a * b = c) : a * b = b * c := by
  have e : b * (b⁻¹ * a * b) = a * b := by
    rw [← mul_assoc b (b⁻¹ * a) b, ← mul_assoc b b⁻¹ a, mul_inv_cancel, one_mul]
  rw [← e, h]

/-- Assemble one right-Hurwitz step from the negated-conjugator computation. -/
private theorem assemble_rightHurwitz {G : Type*} [Group G] {a b m c : G}
    (hbinv : b⁻¹ = m) (hb : m⁻¹ = b) (hcore : m * a * m⁻¹ = c) :
    a * b = b * c := by
  have h : b⁻¹ * a * b = c := by
    have e := hcore
    rwa [hb, ← hbinv] at e
  exact mul_eq_of_inv_conj h

/-- Weyl words at propositionally equal indices agree. -/
private theorem weyl_congr {x x' y y' : ℕ} {hx : x ≠ y} {hx' : x' ≠ y'}
    (w : Rˣ) (h1 : x = x') (h2 : y = y') :
    StableSteinberg.weyl x y hx w = StableSteinberg.weyl x' y' hx' w := by
  subst h1
  subst h2
  rfl

/-- Same-pair Weyl conjugation by the inverse-conjugator form.

Conjugating `W_{ij}(u)` by `W_{ij}(w)` moves both `x_{ij}` factors to the
opposite root via `weyl_conj_x_ij` and the middle `x_{ji}` factor back via
`weyl_conj_x_ji`, reassembling to `W_{ji}(-(w⁻¹ * u * w⁻¹))`. This covers the
equal-label and reversed-label cases with `w := -v` and `w := v⁻¹`. -/
private theorem weyl_samePair_conj {i j : ℕ} (hij : i ≠ j) (w u : Rˣ) :
    StableSteinberg.weyl i j hij w * StableSteinberg.weyl i j hij u *
      (StableSteinberg.weyl i j hij w)⁻¹ =
      StableSteinberg.weyl j i hij.symm (-((w⁻¹) * u * (w⁻¹))) := by
  have hW : StableSteinberg.weyl i j hij u =
      StableSteinberg.x i j hij (↑u : R) *
        StableSteinberg.x j i hij.symm (-(↑(u⁻¹) : R)) *
        StableSteinberg.x i j hij (↑u : R) := by
    simp only [StableSteinberg.weyl]
  have f1 := StableSteinberg.weyl_conj_x_ij i j hij w (↑u : R)
  have f2 := StableSteinberg.weyl_conj_x_ji i j hij w (-(↑(u⁻¹) : R))
  have eA : -((↑(w⁻¹) : R) * (↑u : R) * (↑(w⁻¹) : R)) =
      (↑(-((w⁻¹) * u * (w⁻¹))) : R) := by
    simp only [coe_neg_units, Units.val_mul, mul_assoc]
  have uq1 : ((w⁻¹) * u * (w⁻¹))⁻¹ = w * ((u⁻¹) * w) := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv]
  have uq : (-((w⁻¹) * u * (w⁻¹)))⁻¹ = -(w * ((u⁻¹) * w)) := by
    rw [units_inv_neg, uq1]
  have eB : -((↑w : R) * (-(↑(u⁻¹) : R)) * (↑w : R)) =
      -((↑((-( (w⁻¹) * u * (w⁻¹)))⁻¹) : R)) := by
    rw [uq]
    simp only [Units.val_mul, coe_neg_units, mul_neg, neg_mul, neg_neg, mul_assoc]
  rw [hW, ← conj_mul, ← conj_mul, f1, f2, eA, eB]
  simp only [StableSteinberg.weyl]

/-- Disjoint endpoint sets: `q = u`. The conjugator fixes both victim endpoints,
so the conjugated label is the victim label and the Weyl words commute by
`weyl_comm_of_disjoint`. -/
private theorem hurwitzLift_disjoint {n : ℕ} {i j k l : Fin n}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (u v : Rˣ) :
    ∃ q : Rˣ, weylOfSwapLabel (⟨⟨i, j⟩, hij⟩ : SwapLabel n) u *
        weylOfSwapLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) v =
      weylOfSwapLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) v *
        weylOfSwapLabel
          (conjLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n)
            (⟨⟨i, j⟩, hij⟩ : SwapLabel n)) q := by
  have hWbinv : (StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v)⁻¹ =
      StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v) :=
    (StableSteinberg.weyl_neg_eq_inv k.val l.val (fin_val_ne hkl) v).symm
  have hWb : (StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v))⁻¹ =
      StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v := by
    rw [← hWbinv, inv_inv]
  have hcomm := StableSteinberg.weyl_comm_of_disjoint i.val j.val k.val l.val
    (fin_val_ne hij) (fin_val_ne hkl) (fin_val_ne hik) (fin_val_ne hil)
    (fin_val_ne hjk) (fin_val_ne hjl) u (-v)
  have hcore : StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v) *
      StableSteinberg.weyl i.val j.val (fin_val_ne hij) u *
      (StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v))⁻¹ =
      StableSteinberg.weyl i.val j.val (fin_val_ne hij) u := by
    have e : StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v) *
        StableSteinberg.weyl i.val j.val (fin_val_ne hij) u =
        StableSteinberg.weyl i.val j.val (fin_val_ne hij) u *
        StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v) :=
      (Commute.symm hcomm).eq
    rw [e, mul_assoc, mul_inv_cancel, mul_one]
  have e1 : swapDenote (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) i = i := by
    apply Fin.ext
    change (Equiv.swap k l i).val = i.val
    rw [Equiv.swap_apply_of_ne_of_ne hik hil]
  have e2 : swapDenote (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) j = j := by
    apply Fin.ext
    change (Equiv.swap k l j).val = j.val
    rw [Equiv.swap_apply_of_ne_of_ne hjk hjl]
  have hconj : conjLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n)
      (⟨⟨i, j⟩, hij⟩ : SwapLabel n) = (⟨(i, j), hij⟩ : SwapLabel n) := by
    apply Subtype.ext
    change (swapDenote _ _, swapDenote _ _) = (i, j)
    exact Prod.ext e1 e2
  refine ⟨u, ?_⟩
  rw [hconj]
  change StableSteinberg.weyl i.val j.val (fin_val_ne hij) u *
      StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v =
    StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v *
      StableSteinberg.weyl i.val j.val (fin_val_ne hij) u
  exact assemble_rightHurwitz hWbinv hWb hcore

/-- `a.1 = b.2` with the other three endpoints distinct: `q = (-v) * u`.
Direct `weyl_conj_weyl_mixed` with conjugator `W_{kl}(-v)` and victim `W_{ij}(u)`
sharing the middle index `l = i`; the conjugated label is `(k, j)`. -/
private theorem hurwitzLift_a1b2 {n : ℕ} {i j k l : Fin n}
    (hij : i ≠ j) (hkl : k ≠ l)
    (h_il : i = l) (h_n7 : ¬(i = l ∧ j = k)) (u v : Rˣ) :
    ∃ q : Rˣ, weylOfSwapLabel (⟨⟨i, j⟩, hij⟩ : SwapLabel n) u *
        weylOfSwapLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) v =
      weylOfSwapLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) v *
        weylOfSwapLabel
          (conjLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n)
            (⟨⟨i, j⟩, hij⟩ : SwapLabel n)) q := by
  have h_jk : j ≠ k := fun hjk => h_n7 ⟨h_il, hjk⟩
  have h_kj : k ≠ j := Ne.symm h_jk
  have h_lj : l ≠ j := fun h => hij (h_il.trans h)
  have h_jl : j ≠ l := fun h => (Ne.symm hij) (h.trans h_il.symm)
  have hmix := StableSteinberg.weyl_conj_weyl_mixed k.val j.val l.val
    (fin_val_ne h_kj) (fin_val_ne hkl) (fin_val_ne h_lj) (-v) u
  have hvic : StableSteinberg.weyl i.val j.val (fin_val_ne hij) u =
      StableSteinberg.weyl l.val j.val (fin_val_ne h_lj) u :=
    weyl_congr u (congrArg Fin.val h_il) rfl
  have hWbinv : (StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v)⁻¹ =
      StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v) :=
    (StableSteinberg.weyl_neg_eq_inv k.val l.val (fin_val_ne hkl) v).symm
  have hWb : (StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v))⁻¹ =
      StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v := by
    rw [← hWbinv, inv_inv]
  have hcore : StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v) *
      StableSteinberg.weyl i.val j.val (fin_val_ne hij) u *
      (StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v))⁻¹ =
      StableSteinberg.weyl k.val j.val (fin_val_ne h_kj) ((-v) * u) := by
    rw [hvic]
    exact hmix
  have e1 : swapDenote (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) i = k := by
    apply Fin.ext
    change (Equiv.swap k l i).val = k.val
    rw [h_il, Equiv.swap_apply_right]
  have e2 : swapDenote (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) j = j := by
    apply Fin.ext
    change (Equiv.swap k l j).val = j.val
    rw [Equiv.swap_apply_of_ne_of_ne h_jk h_jl]
  have hconj : conjLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n)
      (⟨⟨i, j⟩, hij⟩ : SwapLabel n) = (⟨(k, j), h_kj⟩ : SwapLabel n) := by
    apply Subtype.ext
    change (swapDenote _ _, swapDenote _ _) = (k, j)
    exact Prod.ext e1 e2
  refine ⟨(-v) * u, ?_⟩
  rw [hconj]
  change StableSteinberg.weyl i.val j.val (fin_val_ne hij) u *
      StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v =
    StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v *
      StableSteinberg.weyl k.val j.val (fin_val_ne h_kj) ((-v) * u)
  exact assemble_rightHurwitz hWbinv hWb hcore

/-- `a.1 = b.1` with the other endpoints distinct: `q = v⁻¹ * u`.
Swap the conjugator `W_{kl}(-v) = W_{li}(v⁻¹)` by `weyl_swap`, then
`weyl_conj_weyl_mixed`; the conjugated label is `(l, j)`. -/
private theorem hurwitzLift_a1b1 {n : ℕ} {i j k l : Fin n}
    (hij : i ≠ j) (hkl : k ≠ l)
    (h_ik : i = k) (h_n6 : ¬(i = k ∧ j = l)) (h_nil : i ≠ l) (u v : Rˣ) :
    ∃ q : Rˣ, weylOfSwapLabel (⟨⟨i, j⟩, hij⟩ : SwapLabel n) u *
        weylOfSwapLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) v =
      weylOfSwapLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) v *
        weylOfSwapLabel
          (conjLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n)
            (⟨⟨i, j⟩, hij⟩ : SwapLabel n)) q := by
  have h_jl : j ≠ l := fun hjl => h_n6 ⟨h_ik, hjl⟩
  have h_li : l ≠ i := Ne.symm h_nil
  have h_lj : l ≠ j := fun h => h_jl h.symm
  have h_jk : j ≠ k := fun h => (Ne.symm hij) (h.trans h_ik.symm)
  have hWm : StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v) =
      StableSteinberg.weyl i.val l.val (fin_val_ne h_nil) (-v) :=
    weyl_congr (-v) (congrArg Fin.val h_ik.symm) rfl
  have hswap0 := StableSteinberg.weyl_swap i.val l.val (fin_val_ne h_nil) (-v)
  rw [units_neg_inv_neg] at hswap0
  have hmix := StableSteinberg.weyl_conj_weyl_mixed l.val j.val i.val
    (fin_val_ne h_lj) (fin_val_ne h_li) (fin_val_ne hij) (v⁻¹) u
  have hWbinv : (StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v)⁻¹ =
      StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v) :=
    (StableSteinberg.weyl_neg_eq_inv k.val l.val (fin_val_ne hkl) v).symm
  have hWb : (StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v))⁻¹ =
      StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v := by
    rw [← hWbinv, inv_inv]
  have hcore : StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v) *
      StableSteinberg.weyl i.val j.val (fin_val_ne hij) u *
      (StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v))⁻¹ =
      StableSteinberg.weyl l.val j.val (fin_val_ne h_lj) ((v⁻¹) * u) := by
    rw [hWm, hswap0]
    exact hmix
  have e1 : swapDenote (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) i = l := by
    apply Fin.ext
    change (Equiv.swap k l i).val = l.val
    rw [h_ik, Equiv.swap_apply_left]
  have e2 : swapDenote (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) j = j := by
    apply Fin.ext
    change (Equiv.swap k l j).val = j.val
    rw [Equiv.swap_apply_of_ne_of_ne h_jk h_jl]
  have hconj : conjLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n)
      (⟨⟨i, j⟩, hij⟩ : SwapLabel n) = (⟨(l, j), h_lj⟩ : SwapLabel n) := by
    apply Subtype.ext
    change (swapDenote _ _, swapDenote _ _) = (l, j)
    exact Prod.ext e1 e2
  refine ⟨(v⁻¹) * u, ?_⟩
  rw [hconj]
  change StableSteinberg.weyl i.val j.val (fin_val_ne hij) u *
      StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v =
    StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v *
      StableSteinberg.weyl l.val j.val (fin_val_ne h_lj) ((v⁻¹) * u)
  exact assemble_rightHurwitz hWbinv hWb hcore

/-- `a.2 = b.1` with the other endpoints distinct: `q = u * v`.
Swap both the conjugator `W_{kl}(-v) = W_{lj}(v⁻¹)` and the victim
`W_{ij}(u) = W_{ji}(-u⁻¹)` by `weyl_swap`, apply `weyl_conj_weyl_mixed`, then
swap the result back; the conjugated label is `(i, l)`. -/
private theorem hurwitzLift_a2b1 {n : ℕ} {i j k l : Fin n}
    (hij : i ≠ j) (hkl : k ≠ l)
    (h_jk : j = k) (h_nil : i ≠ l) (h_nik : i ≠ k) (u v : Rˣ) :
    ∃ q : Rˣ, weylOfSwapLabel (⟨⟨i, j⟩, hij⟩ : SwapLabel n) u *
        weylOfSwapLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) v =
      weylOfSwapLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) v *
        weylOfSwapLabel
          (conjLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n)
            (⟨⟨i, j⟩, hij⟩ : SwapLabel n)) q := by
  have h_jl : j ≠ l := fun h => hkl (h_jk.symm.trans h)
  have h_lj : l ≠ j := Ne.symm h_jl
  have h_li : l ≠ i := Ne.symm h_nil
  have hWm : StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v) =
      StableSteinberg.weyl j.val l.val (fin_val_ne h_jl) (-v) :=
    weyl_congr (-v) (congrArg Fin.val h_jk.symm) rfl
  have hswap0 := StableSteinberg.weyl_swap j.val l.val (fin_val_ne h_jl) (-v)
  rw [units_neg_inv_neg] at hswap0
  have hvic := StableSteinberg.weyl_swap i.val j.val (fin_val_ne hij) u
  have hmix := StableSteinberg.weyl_conj_weyl_mixed l.val i.val j.val
    (fin_val_ne h_li) (fin_val_ne h_lj) (fin_val_ne (Ne.symm hij)) (v⁻¹) (-u⁻¹)
  have hw : -((v⁻¹ * (-u⁻¹))⁻¹) = u * v := by
    rw [mul_inv_rev, units_inv_neg, inv_inv, inv_inv, units_neg_neg_mul]
  have hswap2 := StableSteinberg.weyl_swap l.val i.val (fin_val_ne h_li)
    (v⁻¹ * (-u⁻¹))
  rw [hw] at hswap2
  have hres : StableSteinberg.weyl l.val i.val (fin_val_ne h_li) (v⁻¹ * (-u⁻¹)) =
      StableSteinberg.weyl i.val l.val (fin_val_ne h_nil) (u * v) := hswap2
  have hWbinv : (StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v)⁻¹ =
      StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v) :=
    (StableSteinberg.weyl_neg_eq_inv k.val l.val (fin_val_ne hkl) v).symm
  have hWb : (StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v))⁻¹ =
      StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v := by
    rw [← hWbinv, inv_inv]
  have hcore : StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v) *
      StableSteinberg.weyl i.val j.val (fin_val_ne hij) u *
      (StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v))⁻¹ =
      StableSteinberg.weyl i.val l.val (fin_val_ne h_nil) (u * v) := by
    rw [hWm, hswap0, hvic]
    exact hmix.trans hres
  have e1 : swapDenote (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) i = i := by
    apply Fin.ext
    change (Equiv.swap k l i).val = i.val
    rw [Equiv.swap_apply_of_ne_of_ne h_nik h_nil]
  have e2 : swapDenote (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) j = l := by
    apply Fin.ext
    change (Equiv.swap k l j).val = l.val
    rw [h_jk, Equiv.swap_apply_left]
  have hconj : conjLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n)
      (⟨⟨i, j⟩, hij⟩ : SwapLabel n) = (⟨(i, l), h_nil⟩ : SwapLabel n) := by
    apply Subtype.ext
    change (swapDenote _ _, swapDenote _ _) = (i, l)
    exact Prod.ext e1 e2
  refine ⟨u * v, ?_⟩
  rw [hconj]
  change StableSteinberg.weyl i.val j.val (fin_val_ne hij) u *
      StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v =
    StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v *
      StableSteinberg.weyl i.val l.val (fin_val_ne h_nil) (u * v)
  exact assemble_rightHurwitz hWbinv hWb hcore

/-- `a.2 = b.2` with the other endpoints distinct: `q = u * (-v⁻¹)`.
Bridge the conjugator to `(k, j)`, swap the victim by `weyl_swap`, apply
`weyl_conj_weyl_mixed`, then swap the result back; the conjugated label is
`(i, k)`. -/
private theorem hurwitzLift_a2b2 {n : ℕ} {i j k l : Fin n}
    (hij : i ≠ j) (hkl : k ≠ l)
    (h_jl : j = l) (h_nik : i ≠ k) (h_njk : j ≠ k) (u v : Rˣ) :
    ∃ q : Rˣ, weylOfSwapLabel (⟨⟨i, j⟩, hij⟩ : SwapLabel n) u *
        weylOfSwapLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) v =
      weylOfSwapLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) v *
        weylOfSwapLabel
          (conjLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n)
            (⟨⟨i, j⟩, hij⟩ : SwapLabel n)) q := by
  have h_kj : k ≠ j := Ne.symm h_njk
  have h_ki : k ≠ i := Ne.symm h_nik
  have hWm : StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v) =
      StableSteinberg.weyl k.val j.val (fin_val_ne h_kj) (-v) :=
    weyl_congr (-v) rfl (congrArg Fin.val h_jl.symm)
  have hvic := StableSteinberg.weyl_swap i.val j.val (fin_val_ne hij) u
  have hmix := StableSteinberg.weyl_conj_weyl_mixed k.val i.val j.val
    (fin_val_ne h_ki) (fin_val_ne h_kj) (fin_val_ne (Ne.symm hij)) (-v) (-u⁻¹)
  have g1 : (-v) * (-u⁻¹) = v * u⁻¹ := units_neg_mul_neg v (u⁻¹)
  have g2 : -((v * u⁻¹)⁻¹) = u * (-v⁻¹) := by
    rw [mul_inv_rev, inv_inv, units_neg_eq_mul_neg]
  have hswap2 := StableSteinberg.weyl_swap k.val i.val (fin_val_ne h_ki) (v * u⁻¹)
  rw [g2] at hswap2
  have hres : StableSteinberg.weyl k.val i.val (fin_val_ne h_ki) (v * u⁻¹) =
      StableSteinberg.weyl i.val k.val (fin_val_ne h_nik) (u * (-v⁻¹)) := hswap2
  have hWbinv : (StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v)⁻¹ =
      StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v) :=
    (StableSteinberg.weyl_neg_eq_inv k.val l.val (fin_val_ne hkl) v).symm
  have hWb : (StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v))⁻¹ =
      StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v := by
    rw [← hWbinv, inv_inv]
  have hcore : StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v) *
      StableSteinberg.weyl i.val j.val (fin_val_ne hij) u *
      (StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v))⁻¹ =
      StableSteinberg.weyl i.val k.val (fin_val_ne h_nik) (u * (-v⁻¹)) := by
    rw [hWm, hvic]
    have e1 := hmix
    rw [g1] at e1
    exact e1.trans hres
  have h_il : i ≠ l := fun h => hij (h.trans h_jl.symm)
  have e1 : swapDenote (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) i = i := by
    apply Fin.ext
    change (Equiv.swap k l i).val = i.val
    rw [Equiv.swap_apply_of_ne_of_ne h_nik h_il]
  have e2 : swapDenote (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) j = k := by
    apply Fin.ext
    change (Equiv.swap k l j).val = k.val
    rw [h_jl, Equiv.swap_apply_right]
  have hconj : conjLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n)
      (⟨⟨i, j⟩, hij⟩ : SwapLabel n) = (⟨(i, k), h_nik⟩ : SwapLabel n) := by
    apply Subtype.ext
    change (swapDenote _ _, swapDenote _ _) = (i, k)
    exact Prod.ext e1 e2
  refine ⟨u * (-v⁻¹), ?_⟩
  rw [hconj]
  change StableSteinberg.weyl i.val j.val (fin_val_ne hij) u *
      StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v =
    StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v *
      StableSteinberg.weyl i.val k.val (fin_val_ne h_nik) (u * (-v⁻¹))
  exact assemble_rightHurwitz hWbinv hWb hcore

/-- `a = b` as ordered labels: `q = -(v⁻¹ * u * v⁻¹)`.
Bridge the conjugator to the victim pair and apply `weyl_samePair_conj` with
`w := -v`; conjugation swaps both victim endpoints, so the conjugated label is
the reversed pair `(j, i)`. -/
private theorem hurwitzLift_eq {n : ℕ} {i j k l : Fin n}
    (hij : i ≠ j) (hkl : k ≠ l)
    (h_ik : i = k) (h_jl : j = l) (u v : Rˣ) :
    ∃ q : Rˣ, weylOfSwapLabel (⟨⟨i, j⟩, hij⟩ : SwapLabel n) u *
        weylOfSwapLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) v =
      weylOfSwapLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) v *
        weylOfSwapLabel
          (conjLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n)
            (⟨⟨i, j⟩, hij⟩ : SwapLabel n)) q := by
  have h_ji : j ≠ i := Ne.symm hij
  have hWm : StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v) =
      StableSteinberg.weyl i.val j.val (fin_val_ne hij) (-v) :=
    weyl_congr (-v) (congrArg Fin.val h_ik.symm) (congrArg Fin.val h_jl.symm)
  have hsp := weyl_samePair_conj (fin_val_ne hij) (-v) u
  have g6 : -(((-v)⁻¹) * u * ((-v)⁻¹)) = -(v⁻¹ * u * v⁻¹) := by
    rw [units_inv_neg, units_neg_mul_mul_neg]
  have hres : StableSteinberg.weyl j.val i.val (fin_val_ne h_ji)
      (-(((-v)⁻¹) * u * ((-v)⁻¹))) =
      StableSteinberg.weyl j.val i.val (fin_val_ne h_ji) (-(v⁻¹ * u * v⁻¹)) := by
    rw [g6]
  have hWbinv : (StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v)⁻¹ =
      StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v) :=
    (StableSteinberg.weyl_neg_eq_inv k.val l.val (fin_val_ne hkl) v).symm
  have hWb : (StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v))⁻¹ =
      StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v := by
    rw [← hWbinv, inv_inv]
  have hcore : StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v) *
      StableSteinberg.weyl i.val j.val (fin_val_ne hij) u *
      (StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v))⁻¹ =
      StableSteinberg.weyl j.val i.val (fin_val_ne h_ji) (-(v⁻¹ * u * v⁻¹)) := by
    rw [hWm]
    exact hsp.trans hres
  have e1 : swapDenote (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) i = j := by
    apply Fin.ext
    change (Equiv.swap k l i).val = j.val
    rw [h_ik, Equiv.swap_apply_left]
    exact congrArg Fin.val h_jl.symm
  have e2 : swapDenote (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) j = i := by
    apply Fin.ext
    change (Equiv.swap k l j).val = i.val
    rw [h_jl, Equiv.swap_apply_right]
    exact congrArg Fin.val h_ik.symm
  have hconj : conjLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n)
      (⟨⟨i, j⟩, hij⟩ : SwapLabel n) = (⟨(j, i), h_ji⟩ : SwapLabel n) := by
    apply Subtype.ext
    change (swapDenote _ _, swapDenote _ _) = (j, i)
    exact Prod.ext e1 e2
  refine ⟨-(v⁻¹ * u * v⁻¹), ?_⟩
  rw [hconj]
  change StableSteinberg.weyl i.val j.val (fin_val_ne hij) u *
      StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v =
    StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v *
      StableSteinberg.weyl j.val i.val (fin_val_ne h_ji) (-(v⁻¹ * u * v⁻¹))
  exact assemble_rightHurwitz hWbinv hWb hcore

/-- `a` is the reversed ordered label of `b`: `q = -(v * u * v)`.
Swap the conjugator to the victim pair with `weyl_swap`, bridge indices, and
apply `weyl_samePair_conj` with `w := v⁻¹`; conjugation fixes the ordered pair
here, so the conjugated label is `(k, l)`. -/
private theorem hurwitzLift_rev {n : ℕ} {i j k l : Fin n}
    (hij : i ≠ j) (hkl : k ≠ l)
    (h_il : i = l) (h_jk : j = k) (u v : Rˣ) :
    ∃ q : Rˣ, weylOfSwapLabel (⟨⟨i, j⟩, hij⟩ : SwapLabel n) u *
        weylOfSwapLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) v =
      weylOfSwapLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) v *
        weylOfSwapLabel
          (conjLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n)
            (⟨⟨i, j⟩, hij⟩ : SwapLabel n)) q := by
  have hswap0 := StableSteinberg.weyl_swap k.val l.val (fin_val_ne hkl) (-v)
  rw [units_neg_inv_neg] at hswap0
  have hWm' : StableSteinberg.weyl l.val k.val (fin_val_ne (Ne.symm hkl)) (v⁻¹) =
      StableSteinberg.weyl i.val j.val (fin_val_ne hij) (v⁻¹) :=
    weyl_congr (v⁻¹) (congrArg Fin.val h_il.symm) (congrArg Fin.val h_jk.symm)
  have hsp := weyl_samePair_conj (fin_val_ne hij) (v⁻¹) u
  have g7 : -((((v⁻¹))⁻¹) * u * (((v⁻¹))⁻¹)) = -(v * u * v) := by
    rw [inv_inv]
  have hres : StableSteinberg.weyl j.val i.val (fin_val_ne (Ne.symm hij))
      (-((((v⁻¹))⁻¹) * u * (((v⁻¹))⁻¹))) =
      StableSteinberg.weyl j.val i.val (fin_val_ne (Ne.symm hij)) (-(v * u * v)) := by
    rw [g7]
  have hWm2 : StableSteinberg.weyl j.val i.val (fin_val_ne (Ne.symm hij))
      (-(v * u * v)) =
      StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-(v * u * v)) :=
    weyl_congr (-(v * u * v)) (congrArg Fin.val h_jk) (congrArg Fin.val h_il)
  have hWbinv : (StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v)⁻¹ =
      StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v) :=
    (StableSteinberg.weyl_neg_eq_inv k.val l.val (fin_val_ne hkl) v).symm
  have hWb : (StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v))⁻¹ =
      StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v := by
    rw [← hWbinv, inv_inv]
  have hcore : StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v) *
      StableSteinberg.weyl i.val j.val (fin_val_ne hij) u *
      (StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v))⁻¹ =
      StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-(v * u * v)) := by
    have hswap0' : StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-v) =
        StableSteinberg.weyl l.val k.val (fin_val_ne (Ne.symm hkl)) (v⁻¹) := hswap0
    rw [hswap0', hWm']
    exact (hsp.trans hres).trans hWm2
  have e1 : swapDenote (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) i = k := by
    apply Fin.ext
    change (Equiv.swap k l i).val = k.val
    rw [h_il, Equiv.swap_apply_right]
  have e2 : swapDenote (⟨⟨k, l⟩, hkl⟩ : SwapLabel n) j = l := by
    apply Fin.ext
    change (Equiv.swap k l j).val = l.val
    rw [h_jk, Equiv.swap_apply_left]
  have hconj : conjLabel (⟨⟨k, l⟩, hkl⟩ : SwapLabel n)
      (⟨⟨i, j⟩, hij⟩ : SwapLabel n) = (⟨(k, l), hkl⟩ : SwapLabel n) := by
    apply Subtype.ext
    change (swapDenote _ _, swapDenote _ _) = (k, l)
    exact Prod.ext e1 e2
  refine ⟨-(v * u * v), ?_⟩
  rw [hconj]
  change StableSteinberg.weyl i.val j.val (fin_val_ne hij) u *
      StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v =
    StableSteinberg.weyl k.val l.val (fin_val_ne hkl) v *
      StableSteinberg.weyl k.val l.val (fin_val_ne hkl) (-(v * u * v))
  exact assemble_rightHurwitz hWbinv hWb hcore

/-- Atomic Weyl lift of one directed right-Hurwitz step.

Purpose: transport a single forward move `[a, b] ↦ [b, conjLabel b a]` from
permutations to stable Steinberg Weyl words with an exact exhibited
coefficient. Orientation is head-left: `Wₐ(u) * W_b(v) = W_b(v) * W_conj(q)`.
Hypotheses: ordered endpoint labels `a b`, units `u v`, `[Ring R]` only; no
commutativity, field, or finiteness hypothesis beyond the labels. The witness
`q` is the exhaustive endpoint-incidence table: disjoint gives `u`;
`a.1 = b.2` gives `(-v) * u`; `a.1 = b.1` gives `v⁻¹ * u`; `a.2 = b.1` gives
`u * v`; `a.2 = b.2` gives `u * (-v⁻¹)`; `a = b` gives `-(v⁻¹ * u * v⁻¹)`;
`a` reversed from `b` gives `-(v * u * v)`. Nonclaims: no `ReflTransGen`
trace recursion, no terminal-pair deletion, no torus/cocycle landing, no
strict descent, no kernel generation, no TWT, and no Matsumoto theorem. -/
public theorem exists_weylOfSwapLabel_mul_eq_rightHurwitz {n : ℕ} (a b : SwapLabel n)
    (u v : Rˣ) :
    ∃ q : Rˣ, weylOfSwapLabel a u * weylOfSwapLabel b v =
      weylOfSwapLabel b v * weylOfSwapLabel (conjLabel b a) q := by
  obtain ⟨⟨i, j⟩, hij⟩ := a
  obtain ⟨⟨k, l⟩, hkl⟩ := b
  by_cases h6 : i = k ∧ j = l
  · obtain ⟨h_ik, h_jl⟩ := h6
    exact hurwitzLift_eq hij hkl h_ik h_jl u v
  · by_cases h7 : i = l ∧ j = k
    · obtain ⟨h_il, h_jk⟩ := h7
      exact hurwitzLift_rev hij hkl h_il h_jk u v
    · by_cases h2 : i = l
      · exact hurwitzLift_a1b2 hij hkl h2 h7 u v
      · by_cases h3 : i = k
        · exact hurwitzLift_a1b1 hij hkl h3 h6 h2 u v
        · by_cases h4 : j = k
          · exact hurwitzLift_a2b1 hij hkl h4 h2 h3 u v
          · by_cases h5 : j = l
            · exact hurwitzLift_a2b2 hij hkl h5 h3 h4 u v
            · exact hurwitzLift_disjoint hij hkl h3 h2 h4 h5 u v

end AlgebraicKTheory

end
