/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Finset.Insert
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.AssociatedStirlingEulerian
public import MathlibExt.NumberTheory.Recurrences.HonsbergerFibonacciP
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Sum
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Logic.Equiv.Fin.Basic
import Lean.Elab.Tactic.Omega

/-!
# Counting strongly restricted permutations

For natural numbers `m`, `j`, `i`, `r`, and `k` with `1 ≤ j` and `r < m`, permutations of
`Fin (i * m + r)` with displacements in `{-m, 0, j * m}` act independently on each residue
class modulo `m`. In a nonempty class, the first position is either fixed or starts a cycle
of length `j + 1` with exactly one excedance. Removing the first block gives the Fibonacci
recurrence for the total count and the `(1, j + 1)`-bonacci polynomial recurrence for the
count by number of excedances. The count with exactly `k` excedances is the coefficient of
`X ^ k` in the product of the residue-class polynomials. Both counts use the same
`fixedEquiv`, `jumpEquiv`, and `multiplePermEquiv` decompositions in this module.

## References

* Michael A. Allen, *Connections Between Combinations Without Specified Separations and
  Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
  Sequences 28 (2025), Article 25.3.7, Section 3.2, Corollary 14, equations (7) and (8).
* Michael A. Allen, *On a Two-Parameter Family of Generalizations of Pascal's Triangle*,
  Journal of Integer Sequences 25 (2022), Article 22.9.8, Corollaries 10 and 11 (the
  residue-class enumeration of restricted combinations used in the published proof).
* Kenneth Edwards and Michael A. Allen, *Strongly restricted permutations and tiling with
  fences*, Discrete Applied Mathematics 187 (2015), 82–90 (the fence bijection recalled as
  Lemma 12 in Allen's 2025 paper).
-/

namespace MetaMathlibExt

private def LineStep (j x y : ℕ) : Prop := y + 1 = x ∨ y = x ∨ y = x + j

private abbrev LinePerm (j n : ℕ) :=
  {p : Equiv.Perm (Fin n) // ∀ x : Fin n, LineStep j x (p x)}

private theorem lineStep_add_iff (j k x y : ℕ) :
    LineStep j (k + x) (k + y) ↔ LineStep j x y := by
  unfold LineStep
  omega

private theorem first_fixed_or_jump {j n : ℕ} (p : LinePerm j n) (hn : 0 < n) :
    (p.val ⟨0, hn⟩).val = 0 ∨ (p.val ⟨0, hn⟩).val = j := by
  have h := p.property ⟨0, hn⟩
  simp only [LineStep, Nat.zero_add] at h
  omega

-- For a nonfixed first point, surjectivity forces each downward step in order:
-- the preimage of `t < j` is neither `t` (whose image is known) nor `t - j`.
private theorem first_cycle {j n : ℕ} (p : LinePerm j n) (hn : 0 < n)
    (h0 : (p.val ⟨0, hn⟩).val = j) (t : ℕ) (ht : t < j) :
    (p.val ⟨t + 1, by have := (p.val ⟨0, hn⟩).isLt; omega⟩).val = t := by
  have hjn : j < n := h0 ▸ (p.val ⟨0, hn⟩).isLt
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    obtain ⟨y, hy⟩ := p.val.surjective ⟨t, by omega⟩
    have hy' : (p.val y).val = t := congrArg Fin.val hy
    have h := p.property y
    unfold LineStep at h
    have hyval : y.val = t + 1 := by
      rcases h with h | h | h
      · omega
      · have hyt : y.val = t := by omega
        by_cases ht0 : t = 0
        · have : y = ⟨0, hn⟩ := Fin.ext (show y.val = 0 by omega)
          rw [this, h0] at hy'
          omega
        · have ht' : t - 1 < j := by omega
          have hh := ih (t - 1) (by omega) ht'
          have he : y = ⟨t - 1 + 1, by omega⟩ := Fin.ext (show y.val = t - 1 + 1 by omega)
          rw [he, hh] at hy'
          omega
      · omega
    exact (congrArg (fun x => (p.val x).val) (Fin.ext hyval : y = ⟨t + 1, by omega⟩)).symm.trans
      hy'

private def identityLine (j n : ℕ) : LinePerm j n :=
  ⟨Equiv.refl _, fun _ => Or.inr (Or.inl rfl)⟩

-- The cycle sends 0 to j and every successor to its predecessor.
private def cycleLine (j : ℕ) : LinePerm j (j + 1) where
  val :=
    { toFun := fun x => ⟨if x.val = 0 then j else x.val - 1, by split <;> omega⟩
      invFun := fun x => ⟨if x.val = j then 0 else x.val + 1, by split <;> omega⟩
      left_inv := fun x => Fin.ext (by dsimp; split <;> split <;> omega)
      right_inv := fun x => Fin.ext (by dsimp; split <;> split <;> omega) }
  property x := by
    unfold LineStep
    change (if x.val = 0 then j else x.val - 1) + 1 = x.val ∨
      (if x.val = 0 then j else x.val - 1) = x.val ∨
      (if x.val = 0 then j else x.val - 1) = x.val + j
    split <;> omega

private def splitLine {k l n : ℕ} (h : k + l = n) : Fin k ⊕ Fin l ≃ Fin n :=
  finSumFinEquiv.trans (finCongr h)

@[simp] private theorem splitLine_left_val {k l n : ℕ} (h : k + l = n) (x : Fin k) :
    (splitLine h (.inl x)).val = x.val := rfl

@[simp] private theorem splitLine_right_val {k l n : ℕ} (h : k + l = n) (x : Fin l) :
    (splitLine h (.inr x)).val = k + x.val := rfl

-- Gluing a prescribed prefix to a tail is a bijection onto the permutations
-- that agree with the prefix. Surjectivity of the prefix keeps the tail invariant.
private noncomputable def appendLine {j k l n : ℕ} (h : k + l = n) (p : LinePerm j k) :
    LinePerm j l ≃ {q : LinePerm j n // ∀ x : Fin k,
      q.val (splitLine h (.inl x)) = splitLine h (.inl (p.val x))} := by
  let e := splitLine h
  let glue (q : LinePerm j l) : LinePerm j n :=
    ⟨e.permCongr (Equiv.sumCongr p.val q.val), by
      intro x
      obtain ⟨y | y, rfl⟩ := e.surjective x
      · simpa [e, Equiv.sumCongr_apply] using p.property y
      · simpa [e, Equiv.sumCongr_apply, lineStep_add_iff] using q.property y⟩
  let f (q : LinePerm j l) : {q : LinePerm j n // ∀ x : Fin k,
      q.val (e (.inl x)) = e (.inl (p.val x))} :=
    ⟨glue q, fun x => by simp [glue, Equiv.sumCongr_apply]⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro q₁ q₂ hq
    apply Subtype.ext
    apply Equiv.ext
    intro x
    have hx := congrArg (fun q => q.val.val (e (.inr x))) hq
    apply Sum.inr.inj
    apply e.injective
    simpa [f, glue, Equiv.sumCongr_apply] using hx
  · intro q
    have htail (x : Fin l) : ∃ y : Fin l, q.val.val (e (.inr x)) = e (.inr y) := by
      obtain ⟨y | y, hy⟩ := e.surjective (q.val.val (e (.inr x)))
      · obtain ⟨z, rfl⟩ := p.val.surjective y
        have hz := q.val.val.injective (hy.symm.trans (q.property z).symm)
        cases e.injective hz
      · exact ⟨y, hy.symm⟩
    let tail (x : Fin l) := (htail x).choose
    have htail' (x : Fin l) : q.val.val (e (.inr x)) = e (.inr (tail x)) :=
      (htail x).choose_spec
    have htailInj : Function.Injective tail := by
      intro a b hab
      apply Sum.inr.inj
      apply e.injective
      apply q.val.val.injective
      rw [htail', htail', hab]
    let tailPerm := Equiv.ofBijective tail ⟨htailInj, Finite.surjective_of_injective htailInj⟩
    have hstep (x : Fin l) : LineStep j x (tailPerm x) := by
      have hx := q.val.property (e (.inr x))
      rw [htail' x] at hx
      change LineStep j x (tail x)
      simpa [e, lineStep_add_iff] using hx
    refine ⟨⟨tailPerm, hstep⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro x
    obtain ⟨y | y, rfl⟩ := e.surjective x
    · simpa [f, glue, Equiv.sumCongr_apply] using (q.property y).symm
    · change e.permCongr (Equiv.sumCongr p.val tailPerm) (e (.inr y)) = q.val.val (e (.inr y))
      rw [Equiv.permCongr_apply, e.symm_apply_apply, Equiv.sumCongr_apply, Sum.map_inr]
      exact (htail' y).symm

private def FixesFirst {j n : ℕ} (hn : 0 < n) (p : LinePerm j n) : Prop :=
  (p.val ⟨0, hn⟩).val = 0

private noncomputable def fixedEquiv (j n : ℕ) (hn : 0 < n) :
    LinePerm j (n - 1) ≃ {p : LinePerm j n // FixesFirst hn p} :=
  (appendLine (show 1 + (n - 1) = n by omega) (identityLine j 1)).trans <|
    Equiv.subtypeEquivRight fun p => by
      constructor
      · intro h
        exact congrArg Fin.val (h 0)
      · intro h x
        apply Fin.ext
        have hx : x = 0 := Subsingleton.elim _ _
        subst x
        exact h

private noncomputable def jumpEquiv {j n : ℕ} (hj : 1 ≤ j) (hjn : j < n) :
    LinePerm j (n - (j + 1)) ≃ {p : LinePerm j n // ¬ FixesFirst (by omega) p} :=
  (appendLine (show j + 1 + (n - (j + 1)) = n by omega) (cycleLine j)).trans <|
    Equiv.subtypeEquivRight fun p => by
      let hn : 0 < n := by omega
      change _ ↔ ¬ FixesFirst hn p
      constructor
      · intro h hf
        have hz := congrArg Fin.val (h (⟨0, by omega⟩ : Fin (j + 1)))
        change (p.val ⟨0, hn⟩).val = j at hz
        exact (Nat.ne_of_gt hj) (hz.symm.trans hf)
      · intro h x
        have h0 := (first_fixed_or_jump p hn).resolve_left h
        apply Fin.ext
        change (p.val ⟨x.val, by omega⟩).val = if x.val = 0 then j else x.val - 1
        split
        · next hx => simpa only [hx] using h0
        · next hx =>
          have hstep := first_cycle p hn h0 (x.val - 1) (by have := x.isLt; omega)
          have he : (⟨x.val - 1 + 1, by have := x.isLt; omega⟩ : Fin n) =
              ⟨x.val, by have := x.isLt; omega⟩ := Fin.ext (show x.val - 1 + 1 = x.val by omega)
          simpa only [he] using hstep

private theorem card_linePerm (j n : ℕ) (hj : 1 ≤ j) :
    Nat.card (LinePerm j n) = fibonacciP j (n + 1) := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n = 0
    · subst n
      have : Unique (LinePerm j 0) :=
        ⟨⟨identityLine j 0⟩, fun p => Subtype.ext (Equiv.ext fun x => Fin.elim0 x)⟩
      rw [Nat.card_unique, fibonacciP_eq_one j 1 le_rfl hj]
    · have hn' : 0 < n := by omega
      have hfixed := Nat.card_congr (fixedEquiv j n hn')
      by_cases hjn : j < n
      · calc
          Nat.card (LinePerm j n) =
              Nat.card (LinePerm j (n - 1) ⊕ LinePerm j (n - (j + 1))) :=
            Nat.card_congr (((fixedEquiv j n hn').sumCongr (jumpEquiv hj hjn)).trans
              (Equiv.sumCompl (FixesFirst hn'))).symm
          _ = fibonacciP j (n + 1) := by
            rw [Nat.card_sum, ih (n - 1) (by omega), ih (n - (j + 1)) (by omega),
              fibonacciP_rec j (n + 1) (by omega)]
            congr 2 <;> omega
      · have hfix (p : LinePerm j n) : FixesFirst hn' p := by
          rcases first_fixed_or_jump p hn' with h | h
          · exact h
          · have := (p.val ⟨0, hn'⟩).isLt
            omega
        rw [← Nat.card_congr (Equiv.subtypeUnivEquiv hfix), ← hfixed,
          ih (n - 1) (by omega), show n - 1 + 1 = n by omega]
        by_cases he : n = j
        · subst n
          rw [fibonacciP_rec j (j + 1) (by omega)]
          simp
        · rw [fibonacciP_eq_one j n hn' (by omega),
            fibonacciP_eq_one j (n + 1) (by omega) (by omega)]

private def residueSize {m : ℕ} (i r : ℕ) (a : Fin m) := i + if a.val < r then 1 else 0

private theorem residue_bound {m i r q a : ℕ} (hr : r < m) (ha : a < m) :
    q * m + a < i * m + r ↔ q < residueSize i r (⟨a, ha⟩ : Fin m) := by
  change _ ↔ q < i + if a < r then 1 else 0
  rcases lt_trichotomy q i with h | rfl | h
  · have hm := Nat.mul_le_mul_right m (show q + 1 ≤ i by omega)
    rw [Nat.add_mul, Nat.one_mul] at hm
    split <;> omega
  · split <;> omega
  · have hm := Nat.mul_le_mul_right m (show i + 1 ≤ q by omega)
    rw [Nat.add_mul, Nat.one_mul] at hm
    split <;> omega

private theorem quotient_residue_inj {m x y a b : ℕ} (hm : 0 < m) (ha : a < m) (hb : b < m)
    (h : x * m + a = y * m + b) : x = y ∧ a = b := by
  have hab : a = b := by
    simpa only [Nat.mul_add_mod_of_lt ha, Nat.mul_add_mod_of_lt hb] using
      congrArg (fun z => z % m) h
  refine ⟨?_, hab⟩
  subst b
  have hmul : x * m = y * m := Nat.add_right_cancel h
  exact Nat.eq_of_mul_eq_mul_right hm hmul

private noncomputable def residueEquiv {m i r : ℕ} (hr : r < m) :
    (Σ a : Fin m, Fin (residueSize i r a)) ≃ Fin (i * m + r) := by
  let f : (Σ a : Fin m, Fin (residueSize i r a)) → Fin (i * m + r) :=
    fun ⟨a, q⟩ => ⟨q.val * m + a.val, (residue_bound hr a.isLt).mpr q.isLt⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro ⟨a, x⟩ ⟨b, y⟩ h
    have ⟨hxy, hab⟩ := quotient_residue_inj (by omega) a.isLt b.isLt (congrArg Fin.val h)
    obtain rfl : a = b := Fin.ext hab
    obtain rfl : x = y := Fin.ext hxy
    rfl
  · intro z
    have hm : 0 < m := by omega
    have ha := Nat.mod_lt z.val hm
    have hz := Nat.div_add_mod' z.val m
    have hq : z.val / m < residueSize i r (⟨z.val % m, ha⟩ : Fin m) :=
      (residue_bound hr ha).mp (by rw [hz]; exact z.isLt)
    exact ⟨⟨⟨z.val % m, ha⟩, ⟨z.val / m, hq⟩⟩, Fin.ext hz⟩

private theorem residueEquiv_val {m i r : ℕ} (hr : r < m) (a : Fin m)
    (x : Fin (residueSize i r a)) : (residueEquiv hr ⟨a, x⟩).val = x.val * m + a.val := rfl

private def Allowed (m j x y : ℕ) : Prop :=
  (y : ℤ) - (x : ℤ) ∈ ({-(m : ℤ), 0, ((j * m : ℕ) : ℤ)} : Finset ℤ)

private theorem allowed_mul_add_iff {m j a b x y : ℕ} (hm : 0 < m) (ha : a < m) (hb : b < m) :
    Allowed m j (x * m + a) (y * m + b) ↔ a = b ∧ LineStep j x y := by
  have hcases : Allowed m j (x * m + a) (y * m + b) ↔
      (y + 1) * m + b = x * m + a ∨ y * m + b = x * m + a ∨
        y * m + b = (x + j) * m + a := by
    simp only [Allowed, Finset.mem_insert, Finset.mem_singleton, Nat.add_mul, Nat.one_mul]
    push_cast
    omega
  rw [hcases]
  constructor
  · rintro (h | h | h)
    · obtain ⟨hy, hab⟩ := quotient_residue_inj hm hb ha h
      exact ⟨hab.symm, Or.inl hy⟩
    · obtain ⟨hy, hab⟩ := quotient_residue_inj hm hb ha h
      exact ⟨hab.symm, Or.inr (Or.inl hy)⟩
    · obtain ⟨hy, hab⟩ := quotient_residue_inj hm hb ha h
      exact ⟨hab.symm, Or.inr (Or.inr hy)⟩
  · rintro ⟨rfl, h | h | h⟩
    · exact Or.inl (by rw [h])
    · exact Or.inr (Or.inl (by rw [h]))
    · exact Or.inr (Or.inr (by rw [h]))

private def FiberStep {m i r : ℕ} (j : ℕ) :
    (Σ a : Fin m, Fin (residueSize i r a)) → (Σ a : Fin m, Fin (residueSize i r a)) → Prop
  | ⟨a, x⟩, y => ∃ z : Fin (residueSize i r a), y = ⟨a, z⟩ ∧ LineStep j x z

private theorem fiberStep_iff {m i r j : ℕ} (hr : r < m)
    (x y : Σ a : Fin m, Fin (residueSize i r a)) :
    Allowed m j (residueEquiv hr x) (residueEquiv hr y) ↔ FiberStep j x y := by
  obtain ⟨a, x⟩ := x
  obtain ⟨b, y⟩ := y
  rw [residueEquiv_val, residueEquiv_val, allowed_mul_add_iff (by omega) a.isLt b.isLt]
  constructor
  · rintro ⟨h, hstep⟩
    obtain rfl : a = b := Fin.ext h
    exact ⟨y, rfl, hstep⟩
  · intro h
    change ∃ z : Fin (residueSize i r a),
      (⟨b, y⟩ : Σ u : Fin m, Fin (residueSize i r u)) = ⟨a, z⟩ ∧ LineStep j x z at h
    obtain ⟨z, hz, hstep⟩ := h
    cases hz
    exact ⟨rfl, hstep⟩

private noncomputable def fiberPermEquiv (m i r j : ℕ) :
    (∀ a : Fin m, LinePerm j (residueSize i r a)) ≃
      {p : Equiv.Perm (Σ a : Fin m, Fin (residueSize i r a)) // ∀ x, FiberStep j x (p x)} := by
  let f (p : ∀ a : Fin m, LinePerm j (residueSize i r a)) :
      {p : Equiv.Perm (Σ a : Fin m, Fin (residueSize i r a)) // ∀ x, FiberStep j x (p x)} :=
    ⟨Equiv.sigmaCongrRight fun a => (p a).val, fun ⟨a, x⟩ =>
      ⟨(p a).val x, rfl, (p a).property x⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro p q hpq
    funext a
    apply Subtype.ext
    apply Equiv.ext
    intro x
    have h := congrArg (fun z => z.val ⟨a, x⟩) hpq
    exact Sigma.mk.inj_iff.mp h |>.2 |> eq_of_heq
  · intro p
    let localFun (a : Fin m) (x : Fin (residueSize i r a)) := (p.property ⟨a, x⟩).choose
    have hlocal (a : Fin m) (x : Fin (residueSize i r a)) :
        p.val ⟨a, x⟩ = ⟨a, localFun a x⟩ ∧ LineStep j x (localFun a x) :=
      (p.property ⟨a, x⟩).choose_spec
    have hinj (a : Fin m) : Function.Injective (localFun a) := by
      intro x y hxy
      have h : p.val ⟨a, x⟩ = p.val ⟨a, y⟩ := by rw [(hlocal a x).1, (hlocal a y).1, hxy]
      exact Sigma.mk.inj_iff.mp (p.val.injective h) |>.2 |> eq_of_heq
    let g (a : Fin m) : LinePerm j (residueSize i r a) :=
      ⟨Equiv.ofBijective (localFun a) ⟨hinj a, Finite.surjective_of_injective (hinj a)⟩,
        fun x => (hlocal a x).2⟩
    refine ⟨g, Subtype.ext (Equiv.ext ?_)⟩
    rintro ⟨a, x⟩
    exact (hlocal a x).1.symm

private noncomputable def multiplePermEquiv (m i r j : ℕ) (hr : r < m) :
    (∀ a : Fin m, LinePerm j (residueSize i r a)) ≃
      {p : Equiv.Perm (Fin (i * m + r)) // ∀ x : Fin (i * m + r), Allowed m j x (p x)} :=
  (fiberPermEquiv m i r j).trans <|
    Equiv.subtypeEquiv (residueEquiv hr).permCongr fun p => by
      constructor
      · intro hp x
        obtain ⟨x, rfl⟩ := (residueEquiv hr).surjective x
        simpa using (fiberStep_iff hr x (p x)).mpr (hp x)
      · intro hp x
        apply (fiberStep_iff hr x (p x)).mp
        simpa using hp (residueEquiv hr x)

private theorem prod_residueSize {R : Type*} [CommMonoid R] {m i r : ℕ} (hr : r < m)
    (f : ℕ → R) : (∏ a : Fin m, f (residueSize i r a)) = f i ^ (m - r) * f (i + 1) ^ r := by
  let e := splitLine (show r + (m - r) = m by omega)
  rw [← e.prod_comp, Fintype.prod_sum_type]
  have hleft (a : Fin r) : residueSize i r (e (.inl a)) = i + 1 := by
    simp [residueSize, e, a.isLt]
  have hright (a : Fin (m - r)) : residueSize i r (e (.inr a)) = i := by
    simp [residueSize, e]
  simp only [hleft, hright, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]

/-- **Counting strongly restricted permutations with displacements $-m$, $0$, $jm$.** Let
$m, j, i, r$ be natural numbers with $j \ge 1$ and $r < m$, and let $F_j$ be the Fibonacci
$j$-numbers: $F_j(0) = 0$, $F_j(n) = 1$ for $1 \le n \le j$, and
$F_j(n) = F_j(n-1) + F_j(n-j-1)$ for $n > j$. Then the number of permutations $\pi$ of
$\{0, 1, \dots, im + r - 1\}$ such that $\pi(x) - x \in \{-m, 0, jm\}$ for every $x$ equals
$F_j(i+1)^{m-r} \, F_j(i+2)^r$.

In the paper's notation this is
$P^{\{-m,0,jm\}}_{im+r} = (f^{(j+1)}_i)^{m-r} (f^{(j+1)}_{i+1})^r$, where the
$(1,t)$-bonacci numbers $f^{(t)}_n$ satisfy $f^{(j+1)}_n = F_j(n+1)$.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Corollary 14. -/
public theorem card_strongPerms_multiples_eq_fibonacciP
    (m j i r : ℕ) (hj : 1 ≤ j) (hr : r < m) :
    Nat.card {π : Equiv.Perm (Fin (i * m + r)) //
        ∀ x, ((π x : ℕ) : ℤ) - (x : ℕ) ∈ ({-(m : ℤ), 0, ((j * m : ℕ) : ℤ)} : Finset ℤ)} =
      fibonacciP j (i + 1) ^ (m - r) * fibonacciP j (i + 2) ^ r := by
  classical
  change Nat.card {p : Equiv.Perm (Fin (i * m + r)) //
      ∀ x : Fin (i * m + r), Allowed m j x (p x)} = _
  rw [← Nat.card_congr (multiplePermEquiv m i r j hr), Nat.card_pi]
  simp only [card_linePerm _ _ hj]
  exact prod_residueSize hr (fun n => fibonacciP j (n + 1))

/-- **The $(1,t)$-bonacci polynomials.** Fix a natural number $s$ and put $t = s + 1$. The
$(1,t)$-bonacci polynomials $f^{(t)}_n(x)$, $n \ge 0$, are the polynomials with natural-number
coefficients defined by $f^{(t)}_0(x) = 1$ and, for every $n \ge 0$,
$f^{(t)}_{n+1}(x) = f^{(t)}_n(x) + x \, f^{(t)}_{n-s}(x)$ if $s \le n$ and
$f^{(t)}_{n+1}(x) = f^{(t)}_n(x)$ if $n < s$.

Equivalently, $f^{(t)}_n(x) = f^{(t)}_{n-1}(x) + x \, f^{(t)}_{n-t}(x) + \delta_{n,0}$ with
$f^{(t)}_n(x) = 0$ for $n < 0$.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 3.2. -/
@[expose] public noncomputable def oneTBonacciPolynomial (s : ℕ) : ℕ → Polynomial ℕ
  | 0 => 1
  | n + 1 =>
    oneTBonacciPolynomial s n +
      Polynomial.X * (if s ≤ n then oneTBonacciPolynomial s (n - s) else 0)
termination_by n => n
decreasing_by all_goals omega

/-- **Initial value of the $(1,t)$-bonacci polynomials.** For every natural number $s$, the
$(1,s+1)$-bonacci polynomial of index $0$ is $f^{(s+1)}_0(x) = 1$.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 3.2. -/
public theorem oneTBonacciPolynomial_zero (s : ℕ) : oneTBonacciPolynomial s 0 = 1 := by
  rw [oneTBonacciPolynomial]

/-- **Recurrence for the $(1,t)$-bonacci polynomials.** For all natural numbers $s$ and $n$ with
$s \le n$, the $(1,s+1)$-bonacci polynomials $f^{(s+1)}_m(x)$, $m \ge 0$, satisfy
$f^{(s+1)}_{n+1}(x) = f^{(s+1)}_n(x) + x \, f^{(s+1)}_{n-s}(x)$.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 3.2. -/
public theorem oneTBonacciPolynomial_succ_of_le (s n : ℕ) (h : s ≤ n) :
    oneTBonacciPolynomial s (n + 1) =
      oneTBonacciPolynomial s n + Polynomial.X * oneTBonacciPolynomial s (n - s) := by
  rw [oneTBonacciPolynomial]
  simp [h]

/-- **The $(1,t)$-bonacci polynomials below the recurrence range.** For all natural numbers $s$
and $n$ with $n < s$, the $(1,s+1)$-bonacci polynomials $f^{(s+1)}_m(x)$, $m \ge 0$, satisfy
$f^{(s+1)}_{n+1}(x) = f^{(s+1)}_n(x)$.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 3.2. -/
public theorem oneTBonacciPolynomial_succ_of_lt (s n : ℕ) (h : n < s) :
    oneTBonacciPolynomial s (n + 1) = oneTBonacciPolynomial s n := by
  rw [oneTBonacciPolynomial]
  simp [show ¬ s ≤ n by omega]

private theorem excedanceCount_appendLine {j k l n : ℕ} (h : k + l = n)
    (p : LinePerm j k) (q : LinePerm j l) :
    excedanceCount n (appendLine h p q).val.val =
      excedanceCount k p.val + excedanceCount l q.val := by
  rw [excedanceCount_eq_sum, excedanceCount_eq_sum, excedanceCount_eq_sum]
  change (∑ x : Fin n, if x < (splitLine h).permCongr (Equiv.sumCongr p.val q.val) x
    then 1 else 0) = _
  rw [← (splitLine h).sum_comp, Fintype.sum_sum_type]
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.sumCongr_apply, Sum.map_inl,
    Sum.map_inr, Fin.lt_def, splitLine_left_val, splitLine_right_val, Nat.add_lt_add_iff_left]

private theorem excedanceCount_cycleLine {j : ℕ} (hj : 1 ≤ j) :
    excedanceCount (j + 1) (cycleLine j).val = 1 := by
  rw [excedanceCount_eq_sum]
  have h (x : Fin (j + 1)) : x < (cycleLine j).val x ↔ x = 0 := by
    rw [Fin.lt_def, ← Fin.val_eq_zero_iff]
    change x.val < (if x.val = 0 then j else x.val - 1) ↔ x.val = 0
    split <;> omega
  simp [h]

open scoped Classical in
private noncomputable def lineExcedancePolynomial (j n : ℕ) : Polynomial ℕ :=
  ∑ p : LinePerm j n, Polynomial.X ^ excedanceCount n p.val

private theorem lineExcedancePolynomial_eq (j n : ℕ) (hj : 1 ≤ j) :
    lineExcedancePolynomial j n = oneTBonacciPolynomial j n := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      let : Unique (LinePerm j 0) :=
        ⟨⟨identityLine j 0⟩, fun p => Subtype.ext (Equiv.ext fun x => Fin.elim0 x)⟩
      simp [lineExcedancePolynomial, excedanceCount_eq_sum, oneTBonacciPolynomial_zero]
    | succ n =>
      let fixed := fixedEquiv j (n + 1) (Nat.succ_pos n)
      have hfixed (p : LinePerm j n) :
          excedanceCount (n + 1) (fixed p).val.val = excedanceCount n p.val := by
        change excedanceCount (n + 1) (appendLine _ (identityLine j 1) p).val.val = _
        rw [excedanceCount_appendLine]
        simp [excedanceCount_eq_sum, identityLine]
      by_cases h : j ≤ n
      · let t := n + 1 - (j + 1)
        let jump := jumpEquiv hj (Nat.lt_succ_of_le h)
        let e := (fixed.sumCongr jump).trans (Equiv.sumCompl (FixesFirst (Nat.succ_pos n)))
        have hjump (p : LinePerm j t) :
            excedanceCount (n + 1) (jump p).val.val = 1 + excedanceCount t p.val := by
          change excedanceCount (n + 1) (appendLine _ (cycleLine j) p).val.val = _
          rw [excedanceCount_appendLine, excedanceCount_cycleLine hj]
        rw [lineExcedancePolynomial, ← e.sum_comp, Fintype.sum_sum_type]
        change (∑ p : LinePerm j n,
          (Polynomial.X : Polynomial ℕ) ^ excedanceCount (n + 1) (fixed p).val.val) +
          (∑ p : LinePerm j t, Polynomial.X ^ excedanceCount (n + 1) (jump p).val.val) = _
        simp only [hfixed, hjump, pow_add, pow_one, ← Finset.mul_sum]
        change lineExcedancePolynomial j n + Polynomial.X * lineExcedancePolynomial j t = _
        rw [ih n (by omega), ih t (by dsimp [t]; omega),
          oneTBonacciPolynomial_succ_of_le j n h, show t = n - j from Nat.succ_sub_succ_eq_sub n j]
      · have hall (p : LinePerm j (n + 1)) : FixesFirst (Nat.succ_pos n) p := by
          rcases first_fixed_or_jump p (Nat.succ_pos n) with h₀ | h₀
          · exact h₀
          · have := (p.val ⟨0, Nat.succ_pos n⟩).isLt
            omega
        let e := fixed.trans (Equiv.subtypeUnivEquiv hall)
        rw [lineExcedancePolynomial, ← e.sum_comp]
        change (∑ p : LinePerm j n,
          (Polynomial.X : Polynomial ℕ) ^ excedanceCount (n + 1) (fixed p).val.val) = _
        simp only [hfixed]
        exact (ih n (by omega)).trans (oneTBonacciPolynomial_succ_of_lt j n (by omega)).symm

private theorem excedanceCount_multiplePermEquiv {m j i r : ℕ} (hr : r < m)
    (p : ∀ a : Fin m, LinePerm j (residueSize i r a)) :
    excedanceCount (i * m + r) (multiplePermEquiv m i r j hr p).val =
      ∑ a : Fin m, excedanceCount (residueSize i r a) (p a).val := by
  rw [excedanceCount_eq_sum, ← (residueEquiv hr).sum_comp, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  rw [excedanceCount_eq_sum]
  apply Finset.sum_congr rfl
  intro x _
  let e := residueEquiv (i := i) hr
  change (if e ⟨a, x⟩ < e.permCongr (Equiv.sigmaCongrRight fun b => (p b).val) (e ⟨a, x⟩)
    then 1 else 0) = _
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.sigmaCongrRight_apply,
    Fin.lt_def, e, residueEquiv_val, Nat.add_lt_add_iff_right,
    Nat.mul_lt_mul_right (Nat.zero_lt_of_lt hr)]

open scoped Classical in
private theorem sum_excedanceWeights (m j i r : ℕ) (hj : 1 ≤ j) (hr : r < m) :
    (∑ p : {p : Equiv.Perm (Fin (i * m + r)) // ∀ x : Fin (i * m + r), Allowed m j x (p x)},
      (Polynomial.X : Polynomial ℕ) ^ excedanceCount (i * m + r) p.val) =
      oneTBonacciPolynomial j i ^ (m - r) * oneTBonacciPolynomial j (i + 1) ^ r := by
  classical
  rw [← (multiplePermEquiv m i r j hr).sum_comp]
  simp only [excedanceCount_multiplePermEquiv hr, ← Finset.prod_pow_eq_pow_sum]
  rw [← Fintype.prod_sum (fun (a : Fin m) (p : LinePerm j (residueSize i r a)) =>
    (Polynomial.X : Polynomial ℕ) ^ excedanceCount (residueSize i r a) p.val)]
  change (∏ a : Fin m, lineExcedancePolynomial j (residueSize i r a)) = _
  simp only [lineExcedancePolynomial_eq _ _ hj, prod_residueSize hr]

/-- **Excedances of strongly restricted permutations with displacements $-m$, $0$, $jm$.** Let
$m, j, i, r, k$ be natural numbers with $j \ge 1$ and $r < m$, and let $f_n(x)$ be the
$(1, j+1)$-bonacci polynomials with natural-number coefficients: $f_0(x) = 1$, and
$f_{n+1}(x) = f_n(x) + x f_{n-j}(x)$ if $n \ge j$, $f_{n+1}(x) = f_n(x)$ if $n < j$. Then the
number of permutations $\pi$ of $\{0, 1, \dots, im + r - 1\}$ with $\pi(a) - a \in \{-m, 0, jm\}$
for every $a$ and with exactly $k$ excedances (points $a$ with $\pi(a) > a$) equals the
coefficient of $x^k$ in $f_i(x)^{m-r} f_{i+1}(x)^r$.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Corollary 14. -/
public theorem card_strongPerms_multiples_excedance_eq_coeff
    (m j i r k : ℕ) (hj : 1 ≤ j) (hr : r < m) :
    Nat.card {π : Equiv.Perm (Fin (i * m + r)) //
        (∀ x, ((π x : ℕ) : ℤ) - (x : ℕ) ∈ ({-(m : ℤ), 0, ((j * m : ℕ) : ℤ)} : Finset ℤ)) ∧
        excedanceCount (i * m + r) π = k} =
      ((oneTBonacciPolynomial j i) ^ (m - r) * (oneTBonacciPolynomial j (i + 1)) ^ r).coeff k := by
  classical
  let P := {p : Equiv.Perm (Fin (i * m + r)) // ∀ x : Fin (i * m + r), Allowed m j x (p x)}
  let count (p : P) := excedanceCount (i * m + r) p.val
  let e : {p : P // count p = k} ≃
      {p : Equiv.Perm (Fin (i * m + r)) // (∀ x : Fin (i * m + r), Allowed m j x (p x)) ∧
        excedanceCount (i * m + r) p = k} :=
    Equiv.subtypeSubtypeEquivSubtypeInter
      (fun (p : Equiv.Perm (Fin (i * m + r))) => ∀ x : Fin (i * m + r), Allowed m j x (p x))
      (fun p => excedanceCount (i * m + r) p = k)
  change Nat.card {p : Equiv.Perm (Fin (i * m + r)) //
    (∀ x : Fin (i * m + r), Allowed m j x (p x)) ∧ excedanceCount (i * m + r) p = k} = _
  rw [← Nat.card_congr e, ← sum_excedanceWeights m j i r hj hr, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_X_pow]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_boole]
  congr 1
  exact Finset.filter_congr fun _ _ => eq_comm

end MetaMathlibExt
