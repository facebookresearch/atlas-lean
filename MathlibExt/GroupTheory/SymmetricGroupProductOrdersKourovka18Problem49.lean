/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Orders of two permutations and of their product

We prove that the symmetric group on `n` letters realizes any prescribed triple of orders
between `2` and `n - 2` as the orders of two permutations and their product.

The construction first realizes suitable cycle lengths for two permutations whose product
is a full cycle. At the smallest possible degree, induction attaches one new letter to a
cycle in one factor and makes it a fixed point in the other. At larger degrees, induction
inserts two letters at a time. One of the two insertion orders preserves a full product
cycle. To handle the remaining parity cases, we use the two extra letters to enlarge selected
cycles while keeping the product order.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.49 (S.
Kohl). UnsolvedMath record UM-00701478 (`KOU-18.49`), dataset ulamai/UnsolvedMath v1.8.0.

`Sₙ = Equiv.Perm (Fin n)`; for `n ≤ 3` there are no admissible `a, b, c`, and natural subtraction
matches `n - 2` there.
-/

open Equiv Equiv.Perm

namespace MathlibExt.GroupTheory.SymmetricGroupProductOrdersKourovka18Problem49Wanted

/-! ## Splitting and joining cycles -/

private def TransitivePerm {α : Type*} (f : Perm α) : Prop :=
  ∀ p q, f.SameCycle p q

private theorem invariant_sameCycle {α : Type*} {f : Perm α} {P : α → Prop}
    (hP : ∀ p, P (f p) ↔ P p) {p q : α} (h : f.SameCycle p q) : P q ↔ P p := by
  obtain ⟨k, rfl⟩ := h
  have pow_invariant (g : Perm α) (hg : ∀ p, P (g p) ↔ P p) (n : ℕ) (u : α) :
      P ((g ^ n) u) ↔ P u := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_apply, hg, ih]
  cases k with
  | ofNat n => change P ((f ^ (n : ℤ)) p) ↔ P p; rw [zpow_natCast]; exact pow_invariant f hP n p
  | negSucc n =>
    rw [zpow_negSucc, ← inv_pow]
    exact pow_invariant f⁻¹ (fun u => by simpa using (hP (f⁻¹ u)).symm) (n + 1) p

private theorem sameCycle_of_steps {α β : Type*} {f : Perm α} {g : Perm β} {e : α → β}
    (he : ∀ p, g.SameCycle (e p) (e (f p))) {p q : α} (h : f.SameCycle p q) :
    g.SameCycle (e p) (e q) :=
  (invariant_sameCycle (P := fun u => g.SameCycle (e p) (e u))
    (fun u => ⟨fun h => h.trans (he u).symm, fun h => h.trans (he u)⟩) h).2
    (SameCycle.refl _ _)

private theorem swap_orbits {α : Type*} [DecidableEq α] (f : Perm α) (p q : α)
    (hf : ∀ x, f.SameCycle x p ∨ f.SameCycle x q) :
    ∀ x, (f * swap p q).SameCycle x p ∨ (f * swap p q).SameCycle x q := by
  intro x
  by_contra! hx
  let P := fun u => (f * swap p q).SameCycle x u
  have hP (u : α) : P (f u) ↔ P u := by
    have eqP (v : α) : P (f (swap p q v)) ↔ P v :=
      sameCycle_apply_right (f := f * swap p q)
    by_cases hp : u = p
    · subst u
      simpa [P, hx.1, hx.2] using eqP q
    by_cases hq : u = q
    · subst u
      simpa [P, hx.1, hx.2] using eqP p
    simpa [swap_apply_of_ne_of_ne hp hq] using eqP u
  rcases hf x with hp | hq
  · exact hx.1 ((invariant_sameCycle hP hp).2 (SameCycle.refl _ _))
  · exact hx.2 ((invariant_sameCycle hP hq).2 (SameCycle.refl _ _))

private theorem transitive_of_orbits {α : Type*} {f : Perm α} {p q : α}
    (h : ∀ x, f.SameCycle x p ∨ f.SameCycle x q) (hpq : f.SameCycle p q) :
    TransitivePerm f := by
  have h' (x) : f.SameCycle x q := (h x).elim (fun hp => hp.trans hpq) id
  exact fun x y => (h' x).trans (h' y).symm

private theorem join_swap {α : Type*} [Finite α] [DecidableEq α] (f : Perm α) {p q : α}
    (hf : ∀ x, f.SameCycle x p ∨ f.SameCycle x q) (hpq : ¬f.SameCycle p q) :
    TransitivePerm (f * swap p q) := by
  apply transitive_of_orbits (swap_orbits f p q hf)
  by_contra h
  let g := f * swap p q
  have hneq : ¬ g.SameCycle p q := h
  let s : Set α := {x | f.SameCycle q x ∧ g.SameCycle p x}
  have hmaps : Set.MapsTo g s s := by
    intro x hx
    change f.SameCycle q x ∧ g.SameCycle p x at hx
    have hxq : x ≠ q := by
      intro he
      subst x
      exact hneq hx.2
    have hxp : x ≠ p := fun he => hpq (he ▸ hx.1).symm
    refine ⟨?_, sameCycle_apply_right.2 hx.2⟩
    simpa [g, Perm.mul_apply, swap_apply_of_ne_of_ne hxp hxq] using
      (sameCycle_apply_right.2 hx.1 : f.SameCycle q (f x))
  have hp : g p ∈ s := by
    refine ⟨?_, sameCycle_apply_right.2 (SameCycle.refl _ _)⟩
    simpa [g, Perm.mul_apply] using (sameCycle_apply_right.2 (SameCycle.refl f q) :
      f.SameCycle q (f q))
  have hm := perm_symm_mapsTo_of_mapsTo g hmaps hp
  rw [symm_apply_apply] at hm
  exact hpq hm.1.symm

private theorem full_cycle_sign {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    {f : Perm α} (hf : TransitivePerm f) : sign f = -(-1 : ℤˣ) ^ Fintype.card α := by
  have hmove (p : α) : f p ≠ p := fun h =>
    let ⟨q, hq⟩ := exists_ne p
    hq ((hf p q).eq_of_left h).symm
  obtain ⟨p⟩ := (inferInstance : Nonempty α)
  have hc : f.IsCycle := ⟨p, hmove p, fun q _ => hf p q⟩
  have hs : f.support = Finset.univ := by ext; simp [Perm.mem_support, hmove]
  rw [hc.sign, hs, Finset.card_univ]

private theorem split_swap {α : Type*} [Finite α] [DecidableEq α]
    (f : Perm α) {p q : α} (hf : TransitivePerm f) (hpq : p ≠ q) :
    ¬ (f * swap p q).SameCycle p q := by
  let := Fintype.ofFinite α
  have : Nontrivial α := ⟨p, q, hpq⟩
  intro hs
  have ht := transitive_of_orbits (swap_orbits f p q (fun x => Or.inl (hf x p))) hs
  have he := (full_cycle_sign ht).trans (full_cycle_sign hf).symm
  rw [map_mul, sign_swap hpq] at he
  exact (by decide : (-1 : ℤˣ) ≠ 1) (mul_left_cancel (he.trans (mul_one _).symm))

private theorem transitive_mul_three {α : Type*} [Finite α] [DecidableEq α]
    {f : Perm α} (hf : TransitivePerm f) {p q r : α} (hpq : p ≠ q) :
    TransitivePerm (f * swap p q * swap p r) ∨ TransitivePerm (f * swap p q * swap q r) := by
  by_cases hr : (f * swap p q).SameCycle r p
  · right
    apply join_swap
    · intro x
      rcases swap_orbits f p q (fun x => Or.inl (hf x p)) x with h | h
      · exact Or.inr (h.trans hr.symm)
      · exact Or.inl h
    · exact fun h => split_swap f hf hpq (hr.symm.trans h.symm)
  · left
    apply join_swap
    · intro x
      rcases swap_orbits f p q (fun x => Or.inl (hf x p)) x with h | h
      · exact Or.inl h
      · have hrq := (swap_orbits f p q (fun x => Or.inl (hf x p)) r).resolve_left hr
        exact Or.inr (h.trans hrq.symm)
    · exact fun h => hr h.symm

private theorem transitive_mul_comm {α : Type*} (x y : Perm α)
    (h : TransitivePerm (x * y)) : TransitivePerm (y * x) := by
  intro p q
  have h' := (h (y⁻¹ p) (y⁻¹ q)).conj (g := y)
  simpa [mul_assoc] using h'

/-! ## Inserting letters in cycles -/

private def pad {α : Type*} : Perm α →* Perm (Option α) where
  toFun := Equiv.optionCongr
  map_one' := by ext (a | a) <;> rfl
  map_mul' _ _ := by ext (a | a) <;> rfl

@[simp] private theorem pad_some {α : Type*} (f : Perm α) (a : α) :
    pad f (some a) = some (f a) := by change f.optionCongr (some a) = _; rfl

@[simp] private theorem pad_none {α : Type*} (f : Perm α) :
    pad f none = none := by change f.optionCongr none = _; rfl

private def insertPoint {α : Type*} [DecidableEq α] (f : Perm α) (p : α) :
    Perm (Option α) :=
  pad f * swap (some p) none

@[simp] private theorem insertPoint_none {α : Type*} [DecidableEq α] (f : Perm α) (p : α) :
    insertPoint f p none = some (f p) := by simp [insertPoint, Perm.mul_apply]

@[simp] private theorem insertPoint_some {α : Type*} [DecidableEq α] (f : Perm α)
    (p : α) : insertPoint f p (some p) = none := by simp [insertPoint, Perm.mul_apply]

private theorem insertPoint_some_ne {α : Type*} [DecidableEq α] (f : Perm α) {p a : α}
    (h : a ≠ p) : insertPoint f p (some a) = some (f a) := by
  simp [insertPoint, Perm.mul_apply, swap_apply_of_ne_of_ne (Option.some_injective α |>.ne h)
    (Option.some_ne_none a)]

private theorem sameCycle_insertPoint {α : Type*} [DecidableEq α] (f : Perm α) (p : α)
    {a b : α} (h : f.SameCycle a b) :
    (insertPoint f p).SameCycle (some a) (some b) := by
  apply sameCycle_of_steps (f := f) (e := some) _ h
  intro u
  by_cases hu : u = p
  · subst u
    rw [← insertPoint_none f p, sameCycle_apply_right]
    simpa only [insertPoint_some] using
      (sameCycle_apply_right.2 (SameCycle.refl (insertPoint f p) (some p)))
  · rw [← insertPoint_some_ne f hu, sameCycle_apply_right]

private theorem transitive_insertPoint {α : Type*} [DecidableEq α] (f : Perm α) (p : α)
    (hf : TransitivePerm f) : TransitivePerm (insertPoint f p) := by
  have hs (u : Option α) : (insertPoint f p).SameCycle u (some p) := by
    cases u with
    | none => rw [← insertPoint_some f p, sameCycle_apply_left]
    | some u => exact sameCycle_insertPoint f p (hf u p)
  exact fun u v => (hs u).trans (hs v).symm

private theorem swap_pad {α : Type*} [DecidableEq α] (f : Perm α) (p : α) :
    swap (some p) none * pad f = insertPoint f (f⁻¹ p) := by
  ext (u | u)
  · simp [Perm.mul_apply]
  · by_cases h : f u = p
    · have he : u = f⁻¹ p := by simpa using congrArg f.symm h
      subst u
      simp [Perm.mul_apply]
    · have he : u ≠ f⁻¹ p := fun he => h (by simp [he])
      rw [insertPoint_some_ne f he]
      simp [Perm.mul_apply, swap_apply_of_ne_of_ne
        ((Option.some_injective α).ne h) (Option.some_ne_none _)]

private def Tagged {α ι : Type*} (f : Perm α) (tag : α → ι) : Prop :=
  ∀ p q, f.SameCycle p q ↔ tag p = tag q

private theorem Tagged.invariant {α ι : Type*} {f : Perm α} {tag : α → ι}
    (h : Tagged f tag) (p : α) : tag (f p) = tag p :=
  (h p (f p)).1 (sameCycle_apply_right.2 (SameCycle.refl f p)) |>.symm

private theorem Tagged.inv_invariant {α ι : Type*} {f : Perm α} {tag : α → ι}
    (h : Tagged f tag) (p : α) : tag (f⁻¹ p) = tag p := by
  simpa using (h.invariant (f⁻¹ p)).symm

private theorem tag_left_of_invariant {α ι : Type*} {f : Perm α} {tag : α → ι}
    (hi : ∀ p, tag (f p) = tag p) {p q : α} (h : f.SameCycle p q) :
    tag p = tag q :=
  (invariant_sameCycle (P := fun u => tag p = tag u) (fun u => by rw [hi u]) h).2 rfl

private theorem Tagged.insert {α ι : Type*} [DecidableEq α]
    {f : Perm α} {tag : α → ι} (h : Tagged f tag) (p : α) :
    Tagged (insertPoint f p) (Option.elim' (tag p) tag) := by
  let g := insertPoint f p
  let tag' := Option.elim' (tag p) tag
  have hinv (u : Option α) : tag' (g u) = tag' u := by
    cases u with
    | none => rw [insertPoint_none]; exact h.invariant p
    | some u =>
      by_cases hu : u = p
      · subst u; rw [insertPoint_some]; rfl
      · rw [insertPoint_some_ne f hu]; exact h.invariant u
  have map_none (u : Option α) : g.SameCycle u (some (u.getD p)) := by
    cases u with
    | none =>
      change g.SameCycle none (some p)
      rw [← insertPoint_some f p, sameCycle_apply_left]
    | some u => exact SameCycle.refl _ _
  intro u v
  refine ⟨tag_left_of_invariant hinv, fun huv => ?_⟩
  have he (u : Option α) : tag (u.getD p) = tag' u := by cases u <;> rfl
  have hold := (h (u.getD p) (v.getD p)).2 (by simpa only [he] using huv)
  exact (map_none u).trans ((sameCycle_insertPoint f p hold).trans (map_none v).symm)

private theorem Tagged.insert_left {α ι : Type*} [DecidableEq α]
    {f : Perm α} {tag : α → ι} (h : Tagged f tag) (p : α) :
    Tagged (swap (some p) none * pad f) (Option.elim' (tag p) tag) := by
  rw [swap_pad, ← h.inv_invariant p]
  exact h.insert _

private theorem Tagged.fixed {α ι : Type*} {f : Perm α} {tag : α → ι}
    (h : Tagged f tag) {i : ι} (hi : ∀ p, tag p ≠ i) :
    Tagged (pad f) (Option.elim' i tag) := by
  have hinv (u : Option α) : Option.elim' i tag (pad f u) = Option.elim' i tag u := by
    cases u with
    | none => rw [pad_none]
    | some u => rw [pad_some]; exact h.invariant u
  intro u v
  refine ⟨tag_left_of_invariant hinv, fun huv => ?_⟩
  cases u <;> cases v
  · exact SameCycle.refl _ _
  · exact (hi _ huv.symm).elim
  · exact (hi _ huv).elim
  · apply sameCycle_of_steps (f := f) (e := some) _ ((h _ _).2 huv)
    intro x
    rw [← pad_some, sameCycle_apply_right]

private def tagSize {α ι : Type*} [Fintype α] [DecidableEq ι]
    (tag : α → ι) (i : ι) : ℕ :=
  (Finset.univ.filter (fun p => tag p = i)).card

private theorem exists_tag_of_size_pos {α ι : Type*} [Fintype α] [DecidableEq ι]
    {tag : α → ι} {i : ι}
    (h : 0 < tagSize tag i) : ∃ p, tag p = i := by
  classical
  obtain ⟨p, hp⟩ := Finset.card_pos.1 h
  exact ⟨p, (Finset.mem_filter.1 hp).2⟩

private theorem not_exists_tag_of_size_zero {α ι : Type*} [Fintype α] [DecidableEq ι]
    {tag : α → ι} {i : ι}
    (h : tagSize tag i = 0) (p : α) : tag p ≠ i := by
  classical
  intro hp
  exact Finset.notMem_empty p
    (Finset.card_eq_zero.1 h ▸ Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩)

private theorem tagSize_option {α ι : Type*} [Fintype α] [DecidableEq ι]
    (tag : α → ι) (i j : ι) :
    tagSize (Option.elim' i tag) j = tagSize tag j + if i = j then 1 else 0 := by
  classical
  let f : α ↪ Option α := ⟨some, Option.some_injective α⟩
  let s := (Finset.univ.filter (fun p => tag p = j)).map f
  have hs : (none : Option α) ∉ s := by simp [s, f]
  by_cases h : i = j
  · have he : Finset.univ.filter (fun p : Option α => Option.elim' i tag p = j) =
        insert none s := by
      ext (p | p) <;> simp [s, f, h]
    unfold tagSize
    rw [he, Finset.card_insert_of_notMem hs]
    simp [h, s, Nat.add_comm]
  · have he : Finset.univ.filter (fun p : Option α => Option.elim' i tag p = j) = s := by
      ext (p | p) <;> simp [s, f, h]
    unfold tagSize
    rw [he]
    simp [h, s]

private theorem pad_swap {α : Type*} [DecidableEq α] (p q : α) :
    pad (swap p q) = swap (some p) (some q) := Equiv.optionCongr_swap p q

private def oldPoint {α : Type*} (p : α) : Option (Option α) := some (some p)

private abbrev firstPoint {α : Type*} : Option (Option α) := some none

private theorem insertPoint_twice {α : Type*} [DecidableEq α]
    (f : Perm α) (p : α) (r : Option α) :
    insertPoint (insertPoint f p) r =
      pad (pad f) * (swap (oldPoint p) firstPoint * swap (some r) none) := by
  simp only [insertPoint, map_mul, pad_swap, oldPoint, mul_assoc]

private theorem two_swaps_extend {α : Type*} [DecidableEq α]
    (f : Perm α) (p q r s : α) :
    pad (pad (f * swap p q * swap r s)) =
      pad (pad f) * (swap (oldPoint p) (oldPoint q) * swap (oldPoint r) (oldPoint s)) := by
  simp only [map_mul, pad_swap, oldPoint, mul_assoc]

private theorem transitive_double_insert {α : Type*} [Finite α] [DecidableEq α]
    (f : Perm α) (p r q : α) (hf : TransitivePerm f) :
    let X := swap (oldPoint p) firstPoint * swap (oldPoint r) none
    let U := swap (oldPoint q) firstPoint
    let V := swap (oldPoint q) none
    TransitivePerm (pad (pad f) * (X * (U * V))) ∨
      TransitivePerm (pad (pad f) * (X * (V * U))) := by
  -- Coincident insertion points need no change to the old cycle.
  dsimp only
  by_cases hpr : p = r
  · subst r
    left
    by_cases hpq : p = q
    · subst q
      convert transitive_insertPoint (insertPoint f p) none (transitive_insertPoint f p hf) using 1
      rw [insertPoint_twice]
      congr 1
      ext x : 1
      rcases x with (_ | _ | x)
      · simp [oldPoint, Perm.mul_apply, Equiv.swap_apply_def, *]
      · simp [oldPoint, Perm.mul_apply, Equiv.swap_apply_def, *]
      · by_cases hxp : x = p <;>
          (try subst x) <;>
          (try have hpx := Ne.symm hxp) <;>
          simp [oldPoint, Perm.mul_apply, Equiv.swap_apply_def, *]
    · have hqp := Ne.symm hpq
      convert transitive_insertPoint (insertPoint f q) (some p)
          (transitive_insertPoint f q hf) using 1
      rw [insertPoint_twice]
      congr 1
      ext x : 1
      rcases x with (_ | _ | x)
      · simp [oldPoint, Perm.mul_apply, Equiv.swap_apply_def, *]
      · simp [oldPoint, Perm.mul_apply, Equiv.swap_apply_def, *]
      · by_cases hxp : x = p <;> by_cases hxq : x = q <;>
          (try subst x) <;>
          (try have hpx := Ne.symm hxp) <;>
          (try have hqx := Ne.symm hxq) <;>
          (first | contradiction | simp [oldPoint, Perm.mul_apply, Equiv.swap_apply_def, *])
  by_cases hpq : p = q
  · subst q
    right
    have hrp := Ne.symm hpr
    convert transitive_insertPoint (insertPoint f r) (some r)
      (transitive_insertPoint f r hf) using 1
    rw [insertPoint_twice]
    congr 1
    ext x : 1
    rcases x with (_ | _ | x)
    · simp [oldPoint, Perm.mul_apply, Equiv.swap_apply_def, *]
    · simp [oldPoint, Perm.mul_apply, Equiv.swap_apply_def, *]
    · by_cases hxp : x = p <;> by_cases hxr : x = r <;>
        (try subst x) <;>
        (try have hpx := Ne.symm hxp) <;>
        (try have hrx := Ne.symm hxr) <;>
        (first | contradiction | simp [oldPoint, Perm.mul_apply, Equiv.swap_apply_def, *])
  by_cases hrq : r = q
  · subst q
    left
    have hrp := Ne.symm hpr
    convert transitive_insertPoint (insertPoint f p) none (transitive_insertPoint f p hf) using 1
    rw [insertPoint_twice]
    congr 1
    ext x : 1
    rcases x with (_ | _ | x)
    · simp [oldPoint, Perm.mul_apply, Equiv.swap_apply_def, *]
    · simp [oldPoint, Perm.mul_apply, Equiv.swap_apply_def, *]
    · by_cases hxp : x = p <;> by_cases hxr : x = r <;>
        (try subst x) <;>
        (try have hpx := Ne.symm hxp) <;>
        (try have hrx := Ne.symm hxr) <;>
        simp [oldPoint, Perm.mul_apply, Equiv.swap_apply_def, *]
  have hqp := Ne.symm hpq
  have hrp := Ne.symm hpr
  have hqr := Ne.symm hrq
  -- For three distinct points, a suitable three-cycle keeps the old product transitive.
  rcases transitive_mul_three (r := r) hf hpq with h | h
  · right
    convert transitive_insertPoint (insertPoint _ p) (some r) (transitive_insertPoint _ p h) using 1
    rw [insertPoint_twice, two_swaps_extend]
    simp only [mul_assoc]
    congr 1
    ext x : 1
    rcases x with (_ | _ | x)
    · simp [oldPoint, Perm.mul_apply, Equiv.swap_apply_def, *]
    · simp [oldPoint, Perm.mul_apply, Equiv.swap_apply_def, *]
    · by_cases hxp : x = p <;> by_cases hxr : x = r <;> by_cases hxq : x = q <;>
        (try subst x) <;>
        (try have hpx := Ne.symm hxp) <;>
        (try have hrx := Ne.symm hxr) <;>
        (try have hqx := Ne.symm hxq) <;>
        (first | contradiction | simp [oldPoint, Perm.mul_apply, Equiv.swap_apply_def, *])
  · left
    convert transitive_insertPoint (insertPoint _ p) (some r) (transitive_insertPoint _ p h) using 1
    rw [insertPoint_twice, two_swaps_extend]
    simp only [mul_assoc]
    congr 1
    ext x : 1
    rcases x with (_ | _ | x)
    · simp [oldPoint, Perm.mul_apply, Equiv.swap_apply_def, *]
    · simp [oldPoint, Perm.mul_apply, Equiv.swap_apply_def, *]
    · by_cases hxp : x = p <;> by_cases hxr : x = r <;> by_cases hxq : x = q <;>
        (try subst x) <;>
        (try have hpx := Ne.symm hxp) <;>
        (try have hrx := Ne.symm hxr) <;>
        (try have hqx := Ne.symm hxq) <;>
        (first | contradiction | simp [oldPoint, Perm.mul_apply, Equiv.swap_apply_def, *])

private theorem two_insert_left {α ι : Type*} [DecidableEq α]
    {f : Perm α} {tag : α → ι} (h : Tagged f tag) (q : α) :
    let tag' := Option.elim' (tag q) (Option.elim' (tag q) tag)
    let U := swap (oldPoint q) firstPoint
    let V := swap (oldPoint q) none
    Tagged ((U * V) * pad (pad f)) tag' ∧ Tagged ((V * U) * pad (pad f)) tag' := by
  dsimp only
  have h₀ := h.insert_left q
  have hv := h₀.insert_left (some q)
  have hu := h₀.insert_left none
  rw [map_mul, pad_swap, ← mul_assoc] at hv hu
  refine ⟨?_, hv⟩
  have he : swap firstPoint none * swap (oldPoint q) firstPoint =
      swap (oldPoint q) firstPoint * swap (oldPoint q) none := by
    ext x : 1
    rcases x with (_ | _ | x)
    · simp [oldPoint, Perm.mul_apply, Equiv.swap_apply_def]
    · simp [oldPoint, Perm.mul_apply, Equiv.swap_apply_def]
    · by_cases hx : x = q <;> simp [oldPoint, Perm.mul_apply, Equiv.swap_apply_def, hx]
  rw [← he]
  exact hu

open scoped BigOperators

/-! ## Prescribing both factors with a full cycle as product -/

private structure Factors (α ι κ : Type) [Fintype α] [DecidableEq ι] [DecidableEq κ]
    (A : ι → ℕ) (B : κ → ℕ) (marked : Prop) (i₀ : ι) (j₀ : κ) where
  x : Perm α
  y : Perm α
  leftTag : α → ι
  rightTag : α → κ
  leftCycles : Tagged x leftTag
  rightCycles : Tagged y rightTag
  leftSizes : ∀ i, tagSize leftTag i = A i
  rightSizes : ∀ j, tagSize rightTag j = B j
  product : TransitivePerm (x * y)
  common : marked → ∃ p, leftTag p = i₀ ∧ rightTag p = j₀

private def Realizes {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    (A : ι → ℕ) (B : κ → ℕ) (marked : Prop) (i₀ : ι) (j₀ : κ) : Prop :=
  ∃ (α : Type) (inst : Fintype α), Nonempty (@Factors α ι κ inst _ _ A B marked i₀ j₀)

private theorem Realizes.comm {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    {A : ι → ℕ} {B : κ → ℕ} {m : Prop} {i : ι} {j : κ}
    (h : Realizes A B m i j) : Realizes B A m j i := by
  obtain ⟨α, _, ⟨F⟩⟩ := h
  exact ⟨α, inferInstance, ⟨{
    x := F.y, y := F.x, leftTag := F.rightTag, rightTag := F.leftTag
    leftCycles := F.rightCycles, rightCycles := F.leftCycles
    leftSizes := F.rightSizes, rightSizes := F.leftSizes
    product := transitive_mul_comm _ _ F.product
    common := fun hm => by simpa only [and_comm] using F.common hm }⟩⟩

private def growAt {ι : Type*} [DecidableEq ι] (A : ι → ℕ) (i : ι) : ι → ℕ :=
  fun k => A k + if i = k then 1 else 0

private theorem Realizes.leaf {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    {A : ι → ℕ} {B : κ → ℕ} {m : Prop} {i₀ : ι} {j₀ : κ}
    (h : Realizes A B m i₀ j₀) {i : ι} {j : κ} (hi : A i = 0) (hj : 0 < B j) :
    Realizes (growAt A i) (growAt B j) m i₀ j₀ := by
  classical
  obtain ⟨α, _, ⟨F⟩⟩ := h
  obtain ⟨p, hp⟩ := exists_tag_of_size_pos (show 0 < tagSize F.rightTag j by rwa [F.rightSizes])
  have hnew : TransitivePerm (pad F.x * insertPoint F.y p) := by
    rw [insertPoint, ← mul_assoc, ← map_mul, ← insertPoint]
    exact transitive_insertPoint _ _ F.product
  refine ⟨Option α, inferInstance, ⟨{
    x := pad F.x, y := insertPoint F.y p
    leftTag := Option.elim' i F.leftTag, rightTag := Option.elim' j F.rightTag
    leftCycles := F.leftCycles.fixed (not_exists_tag_of_size_zero ((F.leftSizes i).trans hi))
    rightCycles := hp ▸ F.rightCycles.insert p
    leftSizes := fun k => by rw [tagSize_option, F.leftSizes, growAt]
    rightSizes := fun k => by rw [tagSize_option, F.rightSizes, growAt]
    product := hnew
    common := fun hm => by
      obtain ⟨p, h₁, h₂⟩ := F.common hm
      exact ⟨some p, h₁, h₂⟩ }⟩⟩

private theorem Realizes.double {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    {A : ι → ℕ} {B : κ → ℕ} {m : Prop} {i₀ : ι} {j₀ : κ}
    (h : Realizes A B m i₀ j₀) {i k : ι} {j : κ} (hi : 0 < A i) (hk : 0 < A k)
    (hj : 0 < B j) : Realizes (growAt (growAt A i) k) (growAt (growAt B j) j) m i₀ j₀ := by
  classical
  obtain ⟨α, _, ⟨F⟩⟩ := h
  obtain ⟨p, hp⟩ := exists_tag_of_size_pos (show 0 < tagSize F.leftTag i by rwa [F.leftSizes])
  obtain ⟨r, hr⟩ := exists_tag_of_size_pos (show 0 < tagSize F.leftTag k by rwa [F.leftSizes])
  obtain ⟨q, hq⟩ := exists_tag_of_size_pos (show 0 < tagSize F.rightTag j by rwa [F.rightSizes])
  let x := insertPoint (insertPoint F.x p) (some r)
  let U := swap (oldPoint q) firstPoint
  let V := swap (oldPoint q) none
  let tx := Option.elim' k (Option.elim' i F.leftTag)
  let ty := Option.elim' j (Option.elim' j F.rightTag)
  have hleft : Tagged x tx := by
    simpa only [x, tx, hp, hr, Option.elim'_some] using (F.leftCycles.insert p).insert (some r)
  have htag := two_insert_left F.rightCycles q
  simp only [hq] at htag
  have build (W : Perm (Option (Option α))) (ht : Tagged (W * pad (pad F.y)) ty)
      (hp : TransitivePerm (pad (pad F.y) * x * W)) :
      Realizes (growAt (growAt A i) k) (growAt (growAt B j) j) m i₀ j₀ := by
    refine ⟨_, inferInstance, ⟨{
      x := x, y := W * pad (pad F.y), leftTag := tx, rightTag := ty
      leftCycles := hleft, rightCycles := ht
      leftSizes := fun u => by
        dsimp only [tx]
        rw [tagSize_option, tagSize_option, F.leftSizes]
        rfl
      rightSizes := fun u => by
        dsimp only [ty]
        rw [tagSize_option, tagSize_option, F.rightSizes]
        rfl
      product := transitive_mul_comm _ _ (by
        simpa only [mul_assoc] using (transitive_mul_comm _ _ hp))
      common := fun hm => by
        obtain ⟨t, ht₁, ht₂⟩ := F.common hm
        exact ⟨oldPoint t, ht₁, ht₂⟩ }⟩⟩
  have hp' := transitive_double_insert (F.y * F.x) p r q
    (transitive_mul_comm _ _ F.product)
  rcases hp' with h₁ | h₂
  · exact build (U * V) htag.1 (by
      simpa only [x, insertPoint_twice, U, V, map_mul, mul_assoc, oldPoint] using h₁)
  · exact build (V * U) htag.2 (by
      simpa only [x, insertPoint_twice, U, V, map_mul, mul_assoc, oldPoint] using h₂)

private def active {ι : Type*} [Fintype ι] (A : ι → ℕ) : Finset ι :=
  Finset.univ.filter fun i => 0 < A i

private theorem mem_active {ι : Type*} [Fintype ι] (A : ι → ℕ) (i : ι) :
    i ∈ active A ↔ 0 < A i := by simp [active]

private theorem sum_sizes {ι : Type*} [Fintype ι] (A : ι → ℕ) :
    (∑ i, A i) = (active A).card + ∑ i, (A i - 1) := by
  have hb : (∑ i, if 0 < A i then 1 else 0) = (active A).card :=
    Finset.sum_boole (R := ℕ) _ _
  rw [← hb, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> omega

private theorem sum_growAt {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ι → ℕ) (i : ι) :
    (∑ k, growAt A i k) = (∑ k, A k) + 1 := by
  simp [growAt, Finset.sum_add_distrib]

private theorem grow_shrink {ι : Type*} [DecidableEq ι] (A : ι → ℕ) {i : ι} (hi : 0 < A i) :
    growAt (Function.update A i (A i - 1)) i = A := by
  funext k
  by_cases h : k = i
  · subst k
    simp [growAt, Nat.sub_add_cancel hi]
  · simp [growAt, Function.update_of_ne h, Ne.symm h]

private theorem active_shrink {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ℕ) {i : ι} (hi : 0 < A i) :
    active (Function.update A i (A i - 1)) =
      if A i = 1 then (active A).erase i else active A := by
  ext k
  by_cases h : k = i
  · subst k
    by_cases h₁ : A i = 1
    · simp [h₁, mem_active]
    · simp only [h₁, ite_false, mem_active, Function.update_self]
      omega
  · split_ifs <;> simp [Finset.mem_erase, h, mem_active, Function.update_of_ne]

private theorem no_leaf_bound {ι : Type*} [Fintype ι]
    (A : ι → ℕ) (i₀ : ι) (hn : ∀ i, i ≠ i₀ → A i ≠ 1) :
    (active A).card + (A i₀ - 1) ≤ (∑ i, (A i - 1)) + 1 := by
  classical
  calc
    _ = ∑ i, ((if 0 < A i then 1 else 0) + (if i₀ = i then A i₀ - 1 else 0)) := by
      rw [Finset.sum_add_distrib, Finset.sum_boole]
      simp [active]
    _ ≤ ∑ i, ((A i - 1) + (if i₀ = i then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases h : i = i₀
      · subst i; by_cases hpos : 0 < A i₀ <;> simp [hpos, Nat.add_comm]
      · have h' := hn i h
        simp only [Ne.symm h, ite_false, add_zero]
        split_ifs <;> omega
    _ = _ := by simp [Finset.sum_add_distrib]

private theorem leaf_neighbor {ι κ : Type} [Fintype ι] [Fintype κ]
    {A : ι → ℕ} {B : κ → ℕ} {n : ℕ} {i i₀ : ι} {j₀ : κ}
    (hA : (∑ k, A k) = n) (hB : (∑ k, B k) = n)
    (hn : n + 1 = (active A).card + (active B).card)
    (hi : A i = 1) (hi₀ : 0 < A i₀) (hne : i ≠ i₀) :
    ∃ j, 1 < B j ∧ (n = 2 ∨ 1 < A i₀ ∨ j ≠ j₀ ∨ 2 < B j) := by
  classical
  by_cases hex : ∃ j, j ≠ j₀ ∧ 1 < B j
  · obtain ⟨j, hj, hj'⟩ := hex
    exact ⟨j, hj', Or.inr (Or.inr (Or.inl hj))⟩
  push Not at hex
  have hsub : {i, i₀} ⊆ active A := by
    simp [Finset.insert_subset_iff, mem_active, hi, hi₀]
  have hpair : ({i, i₀} : Finset ι).card = 2 := by simp [hne]
  have htwo : 2 ≤ (active A).card := hpair ▸ Finset.card_le_card hsub
  have sumB := sum_sizes B
  have exB : (∑ k, (B k - 1)) = B j₀ - 1 :=
    Fintype.sum_eq_single j₀ fun k hk => Nat.sub_eq_zero_of_le (hex k hk)
  rw [hB, exB] at sumB
  have hj : 1 < B j₀ := by omega
  refine ⟨j₀, hj, ?_⟩
  by_cases hbig : 2 < B j₀
  · exact Or.inr (Or.inr (Or.inr hbig))
  by_cases ha : 1 < A i₀
  · exact Or.inr (Or.inl ha)
  left
  have hc : (active A).card = 2 := by omega
  have he : active A = {i, i₀} :=
    (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  have hfilter : ∑ k ∈ active A, A k = ∑ k, A k := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ hk
    rw [mem_active, not_lt] at hk
    omega
  rw [he, Finset.sum_insert (by simp [hne]), Finset.sum_singleton, hi, hA] at hfilter
  omega

private theorem realizable_tree_marked {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (n : ℕ) :
    ∀ (A : ι → ℕ) (B : κ → ℕ) (i₀ : ι) (j₀ : κ),
      (∑ i, A i) = n → (∑ j, B j) = n → n + 1 = (active A).card + (active B).card →
      0 < A i₀ → 0 < B j₀ → (n = 1 ∨ 1 < A i₀ ∨ 1 < B j₀) →
      Realizes A B True i₀ j₀ := by
  classical
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro A B i₀ j₀ hA hB hn hi₀ hj₀ hmark
    have hnp : 0 < n := hA ▸ lt_of_lt_of_le hi₀
      (Finset.single_le_sum (f := A) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i₀))
    by_cases hn₁ : n = 1
    · have one_size {ι' : Type} [Fintype ι'] [DecidableEq ι']
          (S : ι' → ℕ) (a : ι') (hs : (∑ k, S k) = 1) (ha : 0 < S a) (k : ι') :
          S k = if a = k then 1 else 0 := by
        have hm (r : ι') :=
          Finset.single_le_sum (f := S) (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
        by_cases h : a = k
        · subst k; simp only [↓reduceIte]; have := hm a; omega
        · have hpair : ∑ r ∈ ({k, a} : Finset ι'), S r ≤ ∑ r, S r :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ _)
          rw [Finset.sum_insert (by simpa using Ne.symm h), Finset.sum_singleton] at hpair
          simp only [ite_eq_right h]
          omega
      refine ⟨Unit, inferInstance, ⟨{
        x := 1, y := 1, leftTag := fun _ => i₀, rightTag := fun _ => j₀
        leftCycles := by intro p q; cases p; cases q; simp
        rightCycles := by intro p q; cases p; cases q; simp
        leftSizes := fun k => by
          rw [one_size A i₀ (hA.trans hn₁) hi₀]
          by_cases hh : i₀ = k <;> simp [tagSize, hh]
        rightSizes := fun k => by
          rw [one_size B j₀ (hB.trans hn₁) hj₀]
          by_cases hh : j₀ = k <;> simp [tagSize, hh]
        product := fun p q => by cases p; cases q; exact SameCycle.refl _ _
        common := fun _ => ⟨(), rfl, rfl⟩ }⟩⟩
    have step {ι' κ' : Type} [Fintype ι'] [Fintype κ'] [DecidableEq ι'] [DecidableEq κ']
        (S : ι' → ℕ) (T : κ' → ℕ) (a₀ : ι') (b₀ : κ')
        (hs : (∑ i, S i) = n) (ht : (∑ j, T j) = n)
        (hab : n + 1 = (active S).card + (active T).card)
        (ha₀ : 0 < S a₀) (hb₀ : 0 < T b₀)
        (hmark : n = 1 ∨ 1 < S a₀ ∨ 1 < T b₀) {a : ι'} (ha : S a = 1) (hne : a ≠ a₀) :
        ∃ (S' : ι' → ℕ) (T' : κ' → ℕ) (b : κ'),
          S = growAt S' a ∧ T = growAt T' b ∧ S' a = 0 ∧ 0 < T' b ∧
          (∑ i, S' i) = n - 1 ∧ (∑ j, T' j) = n - 1 ∧
          (n - 1) + 1 = (active S').card + (active T').card ∧
          0 < S' a₀ ∧ 0 < T' b₀ ∧ (n - 1 = 1 ∨ 1 < S' a₀ ∨ 1 < T' b₀) := by
      obtain ⟨b, hb, hb'⟩ := leaf_neighbor hs ht hab ha ha₀ hne
      let S' := Function.update S a (S a - 1)
      let T' := Function.update T b (T b - 1)
      have hs' : growAt S' a = S := grow_shrink S (by omega : 0 < S a)
      have ht' : growAt T' b = T := grow_shrink T (by omega : 0 < T b)
      have hsa : S' a = 0 := by simp [S', ha]
      have htb : 0 < T' b := by simp [T']; omega
      have hs₁ : (∑ i, S' i) = n - 1 := by rw [← hs', sum_growAt] at hs; omega
      have ht₁ : (∑ j, T' j) = n - 1 := by rw [← ht', sum_growAt] at ht; omega
      have hsa₀ : S' a₀ = S a₀ := Function.update_of_ne (Ne.symm hne) _ _
      have htb₀ : 0 < T' b₀ := by
        by_cases he : b₀ = b
        · rwa [he]
        · simpa [T', Function.update_of_ne he] using hb₀
      refine ⟨S', T', b, hs'.symm, ht'.symm, hsa, htb, hs₁, ht₁, ?_, hsa₀ ▸ ha₀, htb₀, ?_⟩
      · have ha' : a ∈ active S := (mem_active _ _).2 (by omega)
        have hb₁ : T b ≠ 1 := by omega
        dsimp only [S', T']
        rw [active_shrink S (by omega), active_shrink T (by omega),
          ite_eq_left ha, ite_eq_right hb₁,
          Finset.card_erase_of_mem ha']
        have := Finset.card_pos.2 ⟨a, ha'⟩
        omega
      · rw [hsa₀]
        rcases hb' with (h₂ | h₁ | h₀ | hbig)
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl h₁)
        · dsimp only [T']
          rw [Function.update_of_ne (Ne.symm h₀)]
          exact hmark.elim (fun h => (hn₁ h).elim) Or.inr
        · by_cases he : b₀ = b
          · right; right; simp [T', he]; omega
          · rcases hmark with (h | h | h)
            · exact (hn₁ h).elim
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (by simpa [T', Function.update_of_ne he] using h))
    -- Remove a leaf outside the marked pair and attach it back to its neighbor.
    by_cases hleaf : ∃ i, i ≠ i₀ ∧ A i = 1
    · obtain ⟨i, hne, hi⟩ := hleaf
      obtain ⟨A', B', j, heA, heB, hi', hj', hs, ht, hsizes, ha, hb, hm⟩ :=
        step A B i₀ j₀ hA hB hn hi₀ hj₀ hmark hi hne
      rw [heA, heB]
      exact (ih (n - 1) (by omega) A' B' i₀ j₀ hs ht hsizes ha hb hm).leaf hi' hj'
    by_cases hleaf' : ∃ j, j ≠ j₀ ∧ B j = 1
    · obtain ⟨j, hne, hj⟩ := hleaf'
      obtain ⟨B', A', i, heB, heA, hj', hi', ht, hs, hsizes, hb, ha, hm⟩ :=
        step B A j₀ i₀ hB hA (by omega) hj₀ hi₀
          (by simpa only [or_comm, or_left_comm] using hmark) hj hne
      rw [heA, heB]
      have hr := ih (n - 1) (by omega) A' B' i₀ j₀ hs ht (by omega) ha hb
        (by simpa only [or_comm, or_left_comm] using hm)
      exact (hr.comm.leaf hj' hi').comm
    push Not at hleaf hleaf'
    have ha := no_leaf_bound A i₀ hleaf
    have hb := no_leaf_bound B j₀ hleaf'
    have hsa := sum_sizes A
    have hsb := sum_sizes B
    omega

private theorem Realizes.forget {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    {A : ι → ℕ} {B : κ → ℕ} {m : Prop} {i i' : ι} {j j' : κ}
    (h : Realizes A B m i j) : Realizes A B False i' j' := by
  obtain ⟨α, _, ⟨F⟩⟩ := h
  exact ⟨α, inferInstance, ⟨{
    x := F.x, y := F.y, leftTag := F.leftTag, rightTag := F.rightTag
    leftCycles := F.leftCycles, rightCycles := F.rightCycles
    leftSizes := F.leftSizes, rightSizes := F.rightSizes
    product := F.product, common := False.elim }⟩⟩

private theorem exists_size_gt_one {ι : Type*} [Fintype ι] (A : ι → ℕ)
    (h : (active A).card < ∑ i, A i) : ∃ i, 1 < A i := by
  by_contra! hm
  have hzero : (∑ i, (A i - 1)) = 0 := by
    simp [Nat.sub_eq_zero_of_le (hm _)]
  have := sum_sizes A
  omega

private theorem exists_size_pos {ι : Type*} [Fintype ι] (A : ι → ℕ)
    (h : 0 < ∑ i, A i) : ∃ i, 0 < A i := by
  by_contra! hm
  have hzero : ∀ i, A i = 0 := fun i => Nat.eq_zero_of_le_zero (hm i)
  simp only [hzero, Finset.sum_const_zero, lt_irrefl] at h

private theorem realizable_tree {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {n : ℕ}
    {A : ι → ℕ} {B : κ → ℕ} {m : Prop} {i₀ : ι} {j₀ : κ}
    (hn₀ : 0 < n) (hA : (∑ i, A i) = n) (hB : (∑ j, B j) = n)
    (hn : n + 1 = (active A).card + (active B).card)
    (hm : m → 0 < A i₀ ∧ 1 < B j₀) : Realizes A B m i₀ j₀ := by
  classical
  by_cases hmark : m
  · obtain ⟨hi, hj⟩ := hm hmark
    have h := realizable_tree_marked n A B i₀ j₀ hA hB hn hi (by omega)
      (Or.inr (Or.inr hj))
    rwa [eq_true hmark]
  rw [eq_false hmark]
  obtain ⟨i, hi⟩ := exists_size_pos A (by omega)
  obtain ⟨j, hj⟩ := exists_size_pos B (by omega)
  by_cases hn₁ : n = 1
  · exact (realizable_tree_marked n A B i j hA hB hn hi hj (Or.inl hn₁)).forget
  by_cases ha : (active A).card < n
  · obtain ⟨i, hi⟩ := exists_size_gt_one A (by omega)
    exact (realizable_tree_marked n A B i j hA hB hn (by omega) hj (Or.inr (Or.inl hi))).forget
  obtain ⟨j, hj⟩ := exists_size_gt_one B (by omega)
  exact (realizable_tree_marked n A B i j hA hB hn hi (by omega) (Or.inr (Or.inr hj))).forget

/-! ## Reducing the degree by two -/

private def minSize (n : ℕ) : ℕ :=
  if n = 0 then 0 else if n % 2 = 0 then 2 else 1

private theorem minSize_sub_two {n : ℕ} (h : minSize n < n) :
    2 < n ∧ minSize (n - 2) = minSize n := by
  unfold minSize at *
  split_ifs at h ⊢ <;> omega

private theorem realizable_full_marked {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (n : ℕ) :
    ∀ (A : ι → ℕ) (B : κ → ℕ) (m : Prop) (i₀ : ι) (j₀ : κ),
      0 < n → (∑ i, A i) = n → (∑ j, B j) = n →
      (active A).card + (active B).card ≤ n + 1 →
      ((active A).card + (active B).card) % 2 = (n + 1) % 2 →
      (∑ j, minSize (B j)) + 1 ≤ (active A).card + (active B).card →
      (m → 0 < A i₀ ∧ 0 < B j₀ ∧ B j₀ % 2 = 0) →
      Realizes A B m i₀ j₀ := by
  classical
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro A B m i₀ j₀ hn hA hB hle hpar hmin hm
    by_cases he : (active A).card + (active B).card = n + 1
    · exact realizable_tree hn hA hB he.symm fun h => by
        obtain ⟨ha, hb, hp⟩ := hm h
        exact ⟨ha, by omega⟩
    have hlt : (active A).card + (active B).card ≤ n - 1 := by omega
    have hposA : (active A).Nonempty := by
      obtain ⟨i, hi⟩ := exists_size_pos A (by omega)
      exact ⟨i, (mem_active _ _).2 hi⟩
    have hposB : (active B).Nonempty := by
      obtain ⟨j, hj⟩ := exists_size_pos B (by omega)
      exact ⟨j, (mem_active _ _).2 hj⟩
    have ha₁ := Finset.card_pos.2 hposA
    have hb₁ := Finset.card_pos.2 hposB
    obtain ⟨i, hi⟩ := exists_size_gt_one A (by omega)
    let A' := Function.update A i (A i - 1)
    have hg₁ : growAt A' i = A := grow_shrink A (by omega)
    have hA' : (∑ k, A' k) + 1 = n := by rwa [← sum_growAt A' i, hg₁]
    have hs₁ : active A' = active A := by
      dsimp only [A']
      rw [active_shrink A (by omega), ite_eq_right (by omega)]
    obtain ⟨k, hk⟩ := exists_size_gt_one A' (by rw [hs₁]; omega)
    let A'' := Function.update A' k (A' k - 1)
    have hg₂ : growAt A'' k = A' := grow_shrink A' (by omega)
    have hA'' : (∑ l, A'' l) + 1 = ∑ l, A' l := by rw [← sum_growAt A'' k, hg₂]
    have hs₂ : active A'' = active A' := by
      dsimp only [A'']
      rw [active_shrink A' (by omega), ite_eq_right (by omega)]
    have hex : ∃ j, minSize (B j) < B j := by
      by_contra! hbad
      have hsum : (∑ j, B j) ≤ ∑ j, minSize (B j) :=
        Finset.sum_le_sum fun j _ => hbad j
      omega
    obtain ⟨j, hj⟩ := hex
    obtain ⟨hj₂, hjp⟩ := minSize_sub_two hj
    let B' := Function.update B j (B j - 1)
    let B'' := Function.update B j (B j - 2)
    have hgj₁ : growAt B' j = B := grow_shrink B (by omega)
    have hj₁ : B' j = B j - 1 := Function.update_self _ _ _
    have hgj₂ : growAt B'' j = B' := by
      have ht : Function.update B' j (B' j - 1) = B'' := by
        simp [B', B'', Nat.sub_sub]
      rw [← ht]
      exact grow_shrink B' (by omega)
    have hB' : (∑ l, B' l) + 1 = n := by rwa [← sum_growAt B' j, hgj₁]
    have hB'' : (∑ l, B'' l) + 1 = ∑ l, B' l := by rw [← sum_growAt B'' j, hgj₂]
    have hbs : active B'' = active B := by
      ext l
      simp only [mem_active]
      by_cases hl : l = j
      · subst l; simp [B'']; omega
      · simp [B'', Function.update_of_ne hl]
    have hbm : ∑ l, minSize (B'' l) = ∑ l, minSize (B l) := by
      apply Finset.sum_congr rfl
      intro l _
      by_cases hl : l = j
      · subst l; simpa [B''] using hjp
      · simp [B'', Function.update_of_ne hl]
    have hc (l : κ) : B'' l % 2 = B l % 2 := by
      by_cases hl : l = j
      · subst l; simp [B'']; omega
      · simp [B'', Function.update_of_ne hl]
    have hr := ih (n - 2) (by omega) A'' B'' m i₀ j₀ (by omega) (by omega) (by omega)
      (by rw [hs₂, hs₁, hbs]; omega) (by rw [hs₂, hs₁, hbs]; omega)
      (by rwa [hs₂, hs₁, hbs, hbm]) (fun h => by
        obtain ⟨ha, hb, hc'⟩ := hm h
        refine ⟨(mem_active _ _).1 ?_, (mem_active _ _).1 ?_, (hc j₀).trans hc'⟩
        · rw [hs₂, hs₁]; exact (mem_active _ _).2 ha
        · rw [hbs]; exact (mem_active _ _).2 hb)
    have hpi : 0 < A'' i := (mem_active _ _).1 (by
      rw [hs₂, hs₁]
      exact (mem_active _ _).2 (by omega))
    have hpk : 0 < A'' k := (mem_active _ _).1 (by rw [hs₂]; exact (mem_active _ _).2 (by omega))
    have hpj : 0 < B'' j := (mem_active _ _).1 (by rw [hbs]; exact (mem_active _ _).2 (by omega))
    -- Insert the two new letters in the reverse order of the two reductions on the left.
    simpa only [hg₂, hg₁, hgj₂, hgj₁] using hr.double hpk hpi hpj

private def evenActive {ι : Type*} [Fintype ι] (A : ι → ℕ) : Finset ι :=
  (active A).filter fun i => A i % 2 = 0

private theorem sum_minSize {ι : Type*} [Fintype ι] (A : ι → ℕ) :
    (∑ i, minSize (A i)) = (active A).card + (evenActive A).card := by
  classical
  have he : evenActive A = Finset.univ.filter (fun i => 0 < A i ∧ A i % 2 = 0) := by
    ext i; simp [evenActive, mem_active]
  have hb₁ : (∑ i, if 0 < A i then 1 else 0) = (active A).card :=
    Finset.sum_boole (R := ℕ) _ _
  have hb₂ : (∑ i, if 0 < A i ∧ A i % 2 = 0 then 1 else 0) = (evenActive A).card :=
    he.symm ▸ Finset.sum_boole (R := ℕ) _ _
  rw [← hb₁, ← hb₂, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold minSize
  split_ifs <;> omega

private theorem realizable_full {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {A : ι → ℕ} {B : κ → ℕ} {n : ℕ} (i₀ : ι) (j₀ : κ)
    (hn : 0 < n) (hA : (∑ i, A i) = n) (hB : (∑ j, B j) = n)
    (hle : (active A).card + (active B).card ≤ n + 1)
    (hp : ((active A).card + (active B).card) % 2 = (n + 1) % 2) :
    Realizes A B False i₀ j₀ := by
  by_cases hB' : (∑ j, minSize (B j)) + 1 ≤ (active A).card + (active B).card
  · exact realizable_full_marked n A B False i₀ j₀ hn hA hB hle hp hB' False.elim
  by_cases hA' : (∑ i, minSize (A i)) + 1 ≤ (active A).card + (active B).card
  · exact (realizable_full_marked n B A False j₀ i₀ hn hB hA (by omega) (by omega)
      (by omega) False.elim).comm
  -- If neither side can supply paired reductions, all active lengths on both sides are even.
  rw [sum_minSize] at hA' hB'
  have hsa : evenActive A ⊆ active A := Finset.filter_subset _ _
  have hsb : evenActive B ⊆ active B := Finset.filter_subset _ _
  have hea := Finset.card_le_card hsa
  have heb := Finset.card_le_card hsb
  have he : evenActive A = active A := Finset.eq_of_subset_of_card_le hsa (by omega)
  have hall (i : ι) : Even (A i) := by
    by_cases ha : 0 < A i
    · have hm : i ∈ evenActive A := he ▸ (mem_active _ _).2 ha
      exact Nat.even_iff.2 (Finset.mem_filter.1 hm).2
    · have hz : A i = 0 := by omega
      simp [hz]
  have heven : Even n := hA ▸ Finset.even_sum _ (fun i _ => hall i)
  have := Nat.even_iff.1 heven
  omega

/-! ## Deriving permutation orders from the cycle lengths -/

private theorem Tagged.order_eq {α ι : Type*} [Fintype α] [DecidableEq ι]
    {f : Perm α} {tag : α → ι} (h : Tagged f tag) {m : ℕ}
    (hdvd : ∀ i, tagSize tag i ∣ m) (hex : ∃ i, 0 < tagSize tag i ∧ tagSize tag i = m) :
    orderOf f = m := by
  classical
  have hpow (p : α) (k : ℕ) : (f ^ k) p = p ↔ tagSize tag (tag p) ∣ k := by
    let s := Finset.univ.filter fun q => tag q = tag p
    have hs : p ∈ s := by simp [s]
    have hf : f.IsCycleOn (s : Set α) := by
      refine ⟨f.bijOn (fun q => ?_), fun q hq r hr => (h q r).2 ?_⟩
      · simp [s, h.invariant]
      · have hq' : tag q = tag p := by simpa [s] using hq
        have hr' : tag r = tag p := by simpa [s] using hr
        exact hq'.trans hr'.symm
    exact hf.pow_apply_eq hs
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    ext p : 1
    exact (hpow p m).2 (hdvd _)
  · obtain ⟨i, hi, he⟩ := hex
    obtain ⟨p, hp⟩ := exists_tag_of_size_pos hi
    have hh : tagSize tag (tag p) ∣ orderOf f := (hpow p _).1 (by simp)
    rwa [hp, he] at hh

private theorem TransitivePerm.order_eq_card {α : Type*} [Fintype α] [Nonempty α]
    {f : Perm α} (h : TransitivePerm f) : orderOf f = Fintype.card α := by
  have ht : Tagged f (fun _ => ()) := fun p q => ⟨fun _ => rfl, fun _ => h p q⟩
  apply ht.order_eq <;> simp [tagSize, Fintype.card_pos]

private theorem card_eq_sum_tagSize {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (tag : α → ι) : Fintype.card α = ∑ i, tagSize tag i := by
  exact Finset.card_eq_sum_card_fiberwise (f := tag) (s := Finset.univ) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)

private theorem pad_order {α : Type*} (f : Perm α) : orderOf (pad f) = orderOf f :=
  orderOf_injective pad Equiv.optionCongr_injective f

private def Prescribed {α : Type*} (a b c : ℕ) : Prop :=
  ∃ x y : Perm α, orderOf x = a ∧ orderOf y = b ∧ orderOf (x * y) = c

private theorem Prescribed.reverse {α : Type*} {a b c : ℕ}
    (h : @Prescribed α a b c) : @Prescribed α b a c := by
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  refine ⟨y⁻¹, x⁻¹, by simpa using hy, by simpa using hx, ?_⟩
  simpa only [← mul_inv_rev, orderOf_inv] using hxy

private theorem Prescribed.rotate {α : Type*} {a b c : ℕ}
    (h : @Prescribed α a b c) : @Prescribed α b c a := by
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  refine ⟨y, (x * y)⁻¹, hy, by simpa only [orderOf_inv] using hxy, ?_⟩
  simpa [mul_inv_rev, ← mul_assoc] using hx

private theorem Prescribed.extend {α : Type} [Fintype α] {a b c n : ℕ}
    (hα : Fintype.card α ≤ n) (h : @Prescribed α a b c) : @Prescribed (Fin n) a b c := by
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  let e : α ↪ Fin n := (Fintype.equivFin α).toEmbedding.trans (Fin.castLEEmb hα)
  let ϕ := Equiv.Perm.viaEmbeddingHom e
  have ho (f : Perm α) : orderOf (ϕ f) = orderOf f :=
    orderOf_injective ϕ (Equiv.Perm.viaEmbeddingHom_injective e) f
  exact ⟨ϕ x, ϕ y, (ho x).trans hx, (ho y).trans hy, by rw [← map_mul, ho, hxy]⟩

private theorem order_of_sizes {α ι : Type*} [Fintype α] [DecidableEq ι]
    {x : Perm α} {tx : α → ι} {A : ι → ℕ} (h : Tagged x tx)
    (hs : ∀ i, tagSize tx i = A i) {a : ℕ} (ha : 0 < a)
    (hdvd : ∀ i, A i ∣ a) (hex : ∃ i, A i = a) : orderOf x = a := by
  apply h.order_eq
  · simpa only [hs] using hdvd
  · obtain ⟨i, hi⟩ := hex
    exact ⟨i, by rw [hs, hi]; exact ha, by rw [hs, hi]⟩

private theorem Realizes.orders {ι κ : Type} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    {A : ι → ℕ} {B : κ → ℕ} {m : Prop} {i : ι} {j : κ} (h : Realizes A B m i j)
    {a b c n : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hsum : ∑ i, A i = c)
    (hcn : c ≤ n) (hA : ∀ i, A i ∣ a) (hB : ∀ j, B j ∣ b)
    (hexA : ∃ i, A i = a) (hexB : ∃ j, B j = b) : @Prescribed (Fin n) a b c := by
  obtain ⟨α, _, ⟨F⟩⟩ := h
  have hα : Fintype.card α = c := by
    simpa only [card_eq_sum_tagSize F.leftTag, F.leftSizes] using hsum
  have : Nonempty α := Fintype.card_pos_iff.1 (by omega)
  apply Prescribed.extend (hα.trans_le hcn)
  exact ⟨F.x, F.y, order_of_sizes F.leftCycles F.leftSizes ha hA hexA,
    order_of_sizes F.rightCycles F.rightSizes hb hB hexB, F.product.order_eq_card.trans hα⟩

private theorem shared_insert {α : Type*} [DecidableEq α] (x y : Perm α) (p : α) :
    insertPoint x p * (swap (some p) none * pad y) = pad (x * y) := by
  rw [insertPoint, map_mul]
  simp [mul_assoc]

private theorem Tagged.some {α ι : Type*} {f : Perm α} {tag : α → ι} (h : Tagged f tag) :
    Tagged f (fun p => some (tag p)) := by
  intro p q
  simpa only [Option.some.injEq] using h p q

private theorem order_insert_pair {ι κ α : Type} [Fintype α]
    [DecidableEq ι] [DecidableEq κ]
    {x y : Perm α} {tx : α → ι} {ty : α → κ} (hx : Tagged x tx) (hy : Tagged y ty) (p : α)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hA : ∀ i, growAt (tagSize tx) (tx p) i ∣ a) (hB : ∀ j, growAt (tagSize ty) (ty p) j ∣ b)
    (hexA : ∃ i, growAt (tagSize tx) (tx p) i = a)
    (hexB : ∃ j, growAt (tagSize ty) (ty p) j = b) :
    @Prescribed (Option α) a b (orderOf (x * y)) := by
  classical
  refine ⟨insertPoint x p, swap (some p) none * pad y, ?_, ?_, ?_⟩
  · exact order_of_sizes (hx.insert p) (fun i => tagSize_option tx _ i) ha hA hexA
  · exact order_of_sizes (hy.insert_left p) (fun j => tagSize_option ty _ j) hb hB hexB
  · rw [shared_insert, pad_order]

private theorem tagged_double_cancel {α ι κ : Type}
    {x y : Perm α} {tx : α → ι} {ty : α → κ}
    (hx : Tagged x tx) (hy : Tagged y ty) (p : α) :
    ∃ x' y' : Perm (Option (Option α)),
      Tagged x' (Option.elim' (tx p) (Option.elim' (tx p) tx)) ∧
      Tagged y' (Option.elim' (ty p) (Option.elim' (ty p) ty)) ∧
      x' * y' = pad (pad (x * y)) := by
  classical
  let x₁ := insertPoint x p
  let y₁ := swap (some p) none * pad y
  refine ⟨insertPoint x₁ (some p), swap (oldPoint p) none * pad y₁,
    (hx.insert p).insert (some p), (hy.insert_left p).insert_left (some p), ?_⟩
  change insertPoint x₁ (some p) * (swap (some (some p)) none * pad y₁) = _
  rw [shared_insert, show x₁ * y₁ = pad (x * y) from shared_insert _ _ _]

private theorem tagged_insert_with_swap {α ι κ : Type} [Finite α]
    {x y : Perm α} {tx : α → ι} {ty : α → κ}
    (hx : Tagged x tx) (hy : Tagged y ty) (p : α) :
    ∃ x' y' : Perm (Option (Option α)),
      Tagged x' (Option.elim' none (fun u => some (Option.elim' (tx p) tx u))) ∧
      Tagged y' (Option.elim' (ty p) (Option.elim' (ty p) ty)) ∧
      orderOf (x' * y') = (orderOf (x * y)).lcm 2 := by
  classical
  let S : Perm (Option (Option α)) := swap firstPoint none
  let U := swap (oldPoint p) firstPoint
  let V := swap (oldPoint p) none
  let x' := pad (insertPoint x p)
  let y' := (V * U) * pad (pad y)
  have hUV : V * U = U * S := by
    ext z : 1
    rcases z with (_ | _ | z)
    · simp [U, V, S, oldPoint, Perm.mul_apply, Equiv.swap_apply_def]
    · simp [U, V, S, oldPoint, Perm.mul_apply, Equiv.swap_apply_def]
    · by_cases hz : z = p <;>
        simp [U, V, S, oldPoint, Perm.mul_apply, Equiv.swap_apply_def, hz]
  have disjoint (f : Perm α) : Disjoint (pad (pad f)) S := by
    intro z
    rcases z with (_ | _ | z)
    · left; simp
    · left; simp
    · right; simp [S, Equiv.swap_apply_def]
  have hxy : x' * y' = pad (pad (x * y)) * S := by
    have he : x' = pad (pad x) * U := by
      dsimp only [x', U, oldPoint]
      rw [insertPoint, map_mul, pad_swap]
    rw [he]
    dsimp only [y']
    rw [hUV, map_mul, map_mul]
    calc
      _ = pad (pad x) * (S * pad (pad y)) := by
        simp only [mul_assoc]
        rw [← mul_assoc U U]
        simp [U]
      _ = _ := by rw [← (disjoint y).commute.eq, mul_assoc]
  refine ⟨x', y', (hx.insert p).some.fixed (by simp), (two_insert_left hy p).2, ?_⟩
  rw [hxy, (disjoint (x * y)).orderOf, pad_order, pad_order]
  have hS : S.IsSwap := ⟨firstPoint, none, by simp, rfl⟩
  rw [hS.orderOf]

/-! ## Cycle lengths for prescribed orders -/

private abbrev BlockLabels (k l : ℕ) := Unit ⊕ (Fin k ⊕ Fin l)

private def blockSizes {k l : ℕ} (d e : ℕ) : BlockLabels k l → ℕ
  | .inl _ => d
  | .inr (.inl _) => e
  | .inr (.inr _) => 1

private theorem blockSizes_sum (d e k l : ℕ) :
    ∑ i : BlockLabels k l, blockSizes d e i = d + k * e + l := by
  simp [blockSizes, Fintype.sum_sum_type, Nat.add_assoc]

private theorem active_blockSizes (d e k l : ℕ) (hd : 0 < d) (he : 0 < e) :
    (active (blockSizes (k := k) (l := l) d e)).card = 1 + k + l := by
  have h : active (blockSizes (k := k) (l := l) d e) = Finset.univ := by
    ext i
    rcases i with (_ | _ | _) <;> simp [mem_active, blockSizes, hd, he]
  simp [h, Nat.add_assoc]

private theorem growAt_blockSizes (d e k l : ℕ) :
    growAt (blockSizes (k := k) (l := l) d e) (Sum.inl ()) = blockSizes (d + 1) e := by
  funext i
  rcases i with (_ | _ | _) <;> simp [growAt, blockSizes]

private theorem blockSizes_dvd {a d e k l : ℕ} (hd : d ∣ a) (he : e ∣ a)
    (i : BlockLabels k l) : blockSizes d e i ∣ a := by
  rcases i with (_ | _ | _) <;> simp [blockSizes, hd, he]

private theorem full_blocks_large {a m : ℕ} (ha : 2 ≤ a) (ham : a ≤ m) :
    m / 2 ≤ (m / a) * (a - 1) := by
  let q := m / a
  have hq : 0 < q := Nat.div_pos ham (by omega)
  have hr : m % a < a := Nat.mod_lt _ (by omega)
  have hm : q * a + m % a = m := by
    simpa only [Nat.mul_comm q a] using Nat.div_add_mod m a
  have h₁ : q * (a - 1) + q = q * a := by
    calc
      _ = q * ((a - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by rw [Nat.sub_add_cancel (by omega)]
  have h₂ : q * (a - 2) + 2 * q = q * a := by
    rw [Nat.mul_comm 2 q, ← Nat.mul_add, Nat.sub_add_cancel ha]
  have h₃ : a - 2 ≤ q * (a - 2) := Nat.le_mul_of_pos_left _ hq
  change m / 2 ≤ q * (a - 1)
  omega

private theorem shortened_blocks_stats {a c k : ℕ} (ha : k < a) (hac : a ≤ c + k) :
    let q := (c + k) / a
    let r := (c + k) % a
    let A := blockSizes (k := q - 1) (l := r) (a - k) a
    (∑ i, A i) = c ∧ (active A).card + q * (a - 1) = c + k := by
  dsimp only
  have hq : 0 < (c + k) / a := Nat.div_pos hac (by omega)
  have hm : (c + k) / a * a + (c + k) % a = c + k := by
    simpa only [Nat.mul_comm ((c + k) / a) a] using Nat.div_add_mod (c + k) a
  have hmul : ((c + k) / a - 1) * a + a = (c + k) / a * a := by
    calc
      _ = ((c + k) / a - 1 + 1) * a := by rw [Nat.add_mul, Nat.one_mul]
      _ = _ := by rw [Nat.sub_add_cancel hq]
  have hmul' : (c + k) / a * (a - 1) + (c + k) / a = (c + k) / a * a := by
    calc
      _ = (c + k) / a * ((a - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by rw [Nat.sub_add_cancel (by omega)]
  rw [blockSizes_sum, active_blockSizes _ _ _ _ (by omega) (by omega)]
  omega

private structure OrderShape (m a d : ℕ) where
  Label : Type
  finite : Fintype Label
  decEq : DecidableEq Label
  sizes : Label → ℕ
  root : Label
  total : @Finset.sum Label ℕ _ finite.elems sizes = m
  count : (@active Label finite sizes).card + d = m
  divisors : ∀ i, sizes i ∣ a
  rootSize : sizes root = a

private def maxDefect (c a : ℕ) : ℕ :=
  if a % 2 = 0 then a - 1 + (c - a) / 2 else (c / a) * (a - 1)

private theorem maxDefect_large {c a : ℕ} (ha : 2 ≤ a) (hac : a ≤ c) :
    c / 2 ≤ maxDefect c a := by
  unfold maxDefect
  split_ifs with hp
  · omega
  · exact full_blocks_large ha hac

private theorem maxDefect_odd_order {c a : ℕ} (hp : a % 2 ≠ 0) :
    maxDefect c a % 2 = 0 := by
  rw [maxDefect, ite_eq_right hp, Nat.mul_mod]
  have : (a - 1) % 2 = 0 := by omega
  simp [this]

private theorem best_shape {a c k : ℕ} (ha : 2 ≤ a) (hac : a ≤ c)
    (hk : k = 0 ∨ k = 1 ∧ a % 2 = 0 ∧ a + 2 ≤ c) :
    Nonempty (OrderShape c a (maxDefect c a - k)) := by
  by_cases hp : a % 2 = 0
  · let t := (c - a) / 2 - k
    let r := c - a - 2 * t
    have hsum : a + t * 2 + r = c := by dsimp [r, t]; omega
    have hcard : 1 + t + r + (maxDefect c a - k) = c := by
      simp only [maxDefect, ite_eq_left hp, t, r]
      rcases hk with h | ⟨h, _, _⟩ <;> omega
    have h2 : 2 ∣ a := Nat.dvd_of_mod_eq_zero hp
    exact ⟨{
      Label := BlockLabels t r, finite := inferInstance, decEq := inferInstance
      sizes := blockSizes a 2, root := .inl ()
      total := (blockSizes_sum a 2 t r).trans hsum
      count := by rw [active_blockSizes _ _ _ _ (by omega) (by omega)]; exact hcard
      divisors := blockSizes_dvd dvd_rfl h2
      rootSize := rfl }⟩
  · have hk₀ : k = 0 := hk.elim id (fun ⟨_, h, _⟩ => (hp h).elim)
    let q := c / a
    let r := c % a
    have h := shortened_blocks_stats (a := a) (c := c) (k := 0) (by omega) (by omega)
    simp only [Nat.add_zero, Nat.sub_zero] at h
    refine ⟨{
      Label := BlockLabels (q - 1) r, finite := inferInstance, decEq := inferInstance
      sizes := blockSizes a a, root := .inl ()
      total := h.1, count := ?_, divisors := blockSizes_dvd dvd_rfl dvd_rfl, rootSize := rfl }⟩
    rw [maxDefect, ite_eq_right hp, hk₀, Nat.sub_zero]
    exact h.2

private theorem orders_of_shapes {c a b d e n : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : c ≤ n) (hA : Nonempty (OrderShape c a d)) (hB : Nonempty (OrderShape c b e))
    (hde : c - 1 ≤ d + e) (hp : (d + e) % 2 = (c + 1) % 2) :
    @Prescribed (Fin n) a b c := by
  obtain ⟨A⟩ := hA
  obtain ⟨B⟩ := hB
  let := A.finite
  let := B.finite
  let := A.decEq
  let := B.decEq
  have hcountA := A.count
  have hcountB := B.count
  have hsize := realizable_full A.root B.root hc A.total B.total (by omega) (by omega)
  exact hsize.orders ha hb hc A.total hn A.divisors B.divisors
    ⟨A.root, A.rootSize⟩ ⟨B.root, B.rootSize⟩

private theorem minSize_sum_blocks {d e k l : ℕ} :
    (∑ i : BlockLabels k l, minSize (blockSizes d e i)) = minSize d + k * minSize e + l := by
  have h : minSize 1 = 1 := rfl
  simp [blockSizes, Fintype.sum_sum_type, Nat.add_assoc, h]

private theorem minSize_odd {a : ℕ} (h : a % 2 = 1) : minSize a = 1 := by
  have hn : a ≠ 0 := by omega
  simp [minSize, hn, h]

private theorem minSize_even {a : ℕ} (ha : 0 < a) (h : a % 2 = 0) : minSize a = 2 := by
  simp [minSize, Nat.ne_of_gt ha, h]

private theorem even_defect {a : ℕ} (h : a % 2 = 1) (q : ℕ) : (q * (a - 1)) % 2 = 0 := by
  have ha : (a - 1) % 2 = 0 := by omega
  rw [Nat.mul_mod, ha, Nat.mul_zero, Nat.zero_mod]

/-! ## Parity cases using extra letters -/

private theorem odd_factors_even_product {a b c n : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hac : a ≤ c) (hbc : b ≤ c) (hn : c + 2 ≤ n)
    (pa : a % 2 = 1) (pb : b % 2 = 1) (pc : c % 2 = 0) :
    @Prescribed (Fin n) a b c := by
  classical
  let qa := (c + 1) / a
  let qb := (c + 2) / b
  let ra := (c + 1) % a
  let rb := (c + 2) % b
  let A := blockSizes (k := qa - 1) (l := ra) (a - 1) a
  let B := blockSizes (k := qb - 1) (l := rb) (b - 2) b
  let i₀ : BlockLabels (qa - 1) ra := .inl ()
  let j₀ : BlockLabels (qb - 1) rb := .inl ()
  have hA : (∑ i, A i) = c ∧ (active A).card + qa * (a - 1) = c + 1 :=
    shortened_blocks_stats (by omega) (by omega)
  have hB : (∑ j, B j) = c ∧ (active B).card + qb * (b - 1) = c + 2 :=
    shortened_blocks_stats (by omega) (by omega)
  have ha' : (c + 1) / 2 ≤ qa * (a - 1) := full_blocks_large ha (by omega)
  have hb' : (c + 2) / 2 ≤ qb * (b - 1) := full_blocks_large hb (by omega)
  have hpa := even_defect pa qa
  have hpb := even_defect pb qb
  have hpa' : (a - 1) % 2 = 0 := by omega
  have hcountB : 2 ≤ (active B).card := by
    by_contra! h
    have hcard : (active B).card = 1 + (qb - 1) + rb :=
      active_blockSizes _ _ _ _ (by omega) (by omega)
    have hs : b - 2 + (qb - 1) * b + rb = c :=
      (blockSizes_sum _ _ _ _).symm.trans hB.1
    have hq : qb - 1 = 0 := by omega
    rw [hq, Nat.zero_mul] at hs
    omega
  have hmin : ∑ i, minSize (A i) = (active A).card + 1 := by
    change (∑ i : BlockLabels _ _, minSize (blockSizes _ _ i)) = _
    rw [minSize_sum_blocks, minSize_even (by omega) hpa', minSize_odd pa]
    have hh : (active A).card = 1 + (qa - 1) + ra :=
      active_blockSizes _ _ _ _ (by omega) (by omega)
    omega
  have hreal : Realizes A B True i₀ j₀ := (realizable_full_marked c B A True j₀ i₀
    (by omega) hB.1 hA.1 (by have := hA.2; have := hB.2; omega)
    (by have := hA.2; have := hB.2; omega) (by rw [hmin]; omega)
    (fun _ => ⟨show 0 < b - 2 by omega, show 0 < a - 1 by omega, hpa'⟩)).comm
  obtain ⟨α, _, ⟨F⟩⟩ := hreal
  obtain ⟨p, hp, hq⟩ := F.common trivial
  have hα : Fintype.card α = c := by
    simpa only [card_eq_sum_tagSize F.leftTag, F.leftSizes] using hA.1
  have : Nonempty α := ⟨p⟩
  have hprod : orderOf (F.x * F.y) = c := F.product.order_eq_card.trans hα
  obtain ⟨x, y, hx, hy, hxy⟩ := tagged_insert_with_swap F.leftCycles F.rightCycles p
  let tx := Option.elim' none (fun u => some (Option.elim' (F.leftTag p) F.leftTag u))
  let ty := Option.elim' (F.rightTag p) (Option.elim' (F.rightTag p) F.rightTag)
  have hx' : Tagged x tx := hx
  have hy' : Tagged y ty := hy
  have hsizeX (i : BlockLabels (qa - 1) ra) : tagSize tx (some i) = blockSizes a a i := by
    dsimp only [tx]
    rw [tagSize_option, ite_eq_right (by simp : none ≠ some i), Nat.add_zero]
    have he (g : Option α → BlockLabels (qa - 1) ra) :
        tagSize (fun u => some (g u)) (some i) = tagSize g i := by
      simp only [tagSize, Option.some.injEq]
    rw [he, tagSize_option, F.leftSizes, hp]
    change growAt A i₀ i = _
    rw [show growAt A i₀ = blockSizes (a - 1 + 1) a from growAt_blockSizes _ _ _ _]
    rw [Nat.sub_add_cancel (by omega)]
  have hsX : tagSize tx none = 1 := by
    dsimp only [tx]
    rw [tagSize_option]
    simp [tagSize]
  have hsizeY (j : BlockLabels (qb - 1) rb) : tagSize ty j = blockSizes b b j := by
    dsimp only [ty]
    rw [tagSize_option, tagSize_option, F.rightSizes, hq]
    change growAt (growAt B j₀) j₀ j = _
    rw [show growAt B j₀ = blockSizes (b - 2 + 1) b from growAt_blockSizes _ _ _ _,
      growAt_blockSizes, show b - 2 + 1 + 1 = b by omega]
  apply Prescribed.extend (α := Option (Option α))
    (by simpa only [Fintype.card_option, hα, Nat.add_assoc] using hn)
  refine ⟨x, y, hx'.order_eq ?_ ?_, order_of_sizes hy' hsizeY (by omega)
    (blockSizes_dvd dvd_rfl dvd_rfl) ⟨j₀, rfl⟩, ?_⟩
  · intro i
    cases i with
    | none => simp [hsX]
    | some i => rw [hsizeX]; exact blockSizes_dvd dvd_rfl dvd_rfl i
  · exact ⟨some i₀, by rw [hsizeX]; exact lt_of_lt_of_le (by decide) ha, by rw [hsizeX]; rfl⟩
  · rw [hxy, hprod]
    exact Nat.lcm_eq_left (Nat.dvd_of_mod_eq_zero pc)

private theorem mixed_near_odd_product {a b c n : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (ha' : a + 1 = c) (hbc : b ≤ c) (hn : c + 1 ≤ n)
    (pa : a % 2 = 0) (pb : b % 2 = 1) :
    @Prescribed (Fin n) a b c := by
  let qb := (c + 1) / b
  let rb := (c + 1) % b
  let A := blockSizes (k := 1) (l := 0) 1 a
  let B := blockSizes (k := qb - 1) (l := rb) (b - 1) b
  let i₀ : BlockLabels 1 0 := .inl ()
  let j₀ : BlockLabels (qb - 1) rb := .inl ()
  have hA : ∑ i, A i = c := by
    change (∑ i : BlockLabels 1 0, blockSizes 1 a i) = c
    rw [blockSizes_sum]
    omega
  have hcA : (active A).card = 2 :=
    active_blockSizes _ _ _ _ (by omega) (by omega)
  have hB : (∑ j, B j) = c ∧ (active B).card + qb * (b - 1) = c + 1 :=
    shortened_blocks_stats (by omega) (by omega)
  have hb' : (c + 1) / 2 ≤ qb * (b - 1) := full_blocks_large hb (by omega)
  have hpb := even_defect pb qb
  have hpb' : (b - 1) % 2 = 0 := by omega
  have hmin : ∑ i, minSize (B i) = (active B).card + 1 := by
    change (∑ i : BlockLabels _ _, minSize (blockSizes _ _ i)) = _
    rw [minSize_sum_blocks, minSize_even (by omega) hpb', minSize_odd pb]
    have hh : (active B).card = 1 + (qb - 1) + rb :=
      active_blockSizes _ _ _ _ (by omega) (by omega)
    omega
  have hreal : Realizes A B True i₀ j₀ :=
    realizable_full_marked c A B True i₀ j₀ (by omega) hA hB.1
      (by have := hB.2; omega) (by have := hB.2; omega) (by rw [hmin, hcA]; omega)
      (fun _ => ⟨Nat.one_pos, show 0 < b - 1 by omega, hpb'⟩)
  obtain ⟨α, _, ⟨F⟩⟩ := hreal
  obtain ⟨p, hp, hq⟩ := F.common trivial
  have : Nonempty α := ⟨p⟩
  classical
  have hα : Fintype.card α = c := by
    simpa only [card_eq_sum_tagSize F.leftTag, F.leftSizes] using hA
  have hprod : orderOf (F.x * F.y) = c := F.product.order_eq_card.trans hα
  have hsX : growAt (tagSize F.leftTag) (F.leftTag p) = blockSizes 2 a := by
    rw [hp, funext F.leftSizes]
    exact growAt_blockSizes _ _ _ _
  have hsY : growAt (tagSize F.rightTag) (F.rightTag p) = blockSizes b b := by
    rw [hq, funext F.rightSizes]
    rw [show growAt B j₀ = blockSizes (b - 1 + 1) b from growAt_blockSizes _ _ _ _]
    rw [Nat.sub_add_cancel (by omega)]
  apply Prescribed.extend (α := Option α) (by simpa only [Fintype.card_option, hα] using hn)
  rw [← hprod]
  apply order_insert_pair F.leftCycles F.rightCycles p (by omega) (by omega)
  · rw [hsX]
    exact blockSizes_dvd (Nat.dvd_of_mod_eq_zero pa) dvd_rfl
  · rw [hsY]
    exact blockSizes_dvd dvd_rfl dvd_rfl
  · rw [hsX]
    exact ⟨.inr (.inl 0), rfl⟩
  · rw [hsY]
    exact ⟨j₀, rfl⟩

private theorem equal_even_orders {c n : ℕ}
    (hc : 4 ≤ c) (hn : c + 2 ≤ n) (pc : c % 2 = 0) : @Prescribed (Fin n) c c c := by
  let A := blockSizes (k := 1) (l := 0) (c - 2) 2
  let B := blockSizes (k := 0) (l := 2) (c - 2) 1
  let i₀ : BlockLabels 1 0 := .inl ()
  let j₀ : BlockLabels 0 2 := .inl ()
  have hA : ∑ i, A i = c := by
    change (∑ i : BlockLabels 1 0, blockSizes (c - 2) 2 i) = c
    rw [blockSizes_sum]; omega
  have hB : ∑ i, B i = c := by
    change (∑ i : BlockLabels 0 2, blockSizes (c - 2) 1 i) = c
    rw [blockSizes_sum]; omega
  have hcA : (active A).card = 2 := active_blockSizes _ _ _ _ (by omega) (by omega)
  have hcB : (active B).card = 3 := active_blockSizes _ _ _ _ (by omega) (by omega)
  have hp' : (c - 2) % 2 = 0 := by omega
  have hmin : ∑ i, minSize (B i) = 4 := by
    change (∑ i : BlockLabels 0 2, minSize (blockSizes (c - 2) 1 i)) = _
    rw [minSize_sum_blocks, minSize_even (by omega) hp']
    decide
  have hreal : Realizes A B True i₀ j₀ :=
    realizable_full_marked c A B True i₀ j₀ (by omega) hA hB
      (by omega) (by omega) (by omega)
      (fun _ => ⟨show 0 < c - 2 by omega, show 0 < c - 2 by omega, hp'⟩)
  obtain ⟨α, _, ⟨F⟩⟩ := hreal
  obtain ⟨p, hp, hq⟩ := F.common trivial
  have : Nonempty α := ⟨p⟩
  classical
  have hα : Fintype.card α = c := by
    simpa only [card_eq_sum_tagSize F.leftTag, F.leftSizes] using hA
  obtain ⟨x, y, hx, hy, hxy⟩ := tagged_double_cancel F.leftCycles F.rightCycles p
  have hsizeX (i : BlockLabels 1 0) :
      tagSize (Option.elim' (F.leftTag p) (Option.elim' (F.leftTag p) F.leftTag)) i =
        blockSizes c 2 i := by
    rw [tagSize_option, tagSize_option, F.leftSizes, hp]
    change growAt (growAt A i₀) i₀ i = _
    rw [show growAt A i₀ = blockSizes (c - 2 + 1) 2 from growAt_blockSizes _ _ _ _,
      growAt_blockSizes, show c - 2 + 1 + 1 = c by omega]
  have hsizeY (i : BlockLabels 0 2) :
      tagSize (Option.elim' (F.rightTag p) (Option.elim' (F.rightTag p) F.rightTag)) i =
        blockSizes c 1 i := by
    rw [tagSize_option, tagSize_option, F.rightSizes, hq]
    change growAt (growAt B j₀) j₀ i = _
    rw [show growAt B j₀ = blockSizes (c - 2 + 1) 1 from growAt_blockSizes _ _ _ _,
      growAt_blockSizes, show c - 2 + 1 + 1 = c by omega]
  apply Prescribed.extend (α := Option (Option α))
    (by simpa only [Fintype.card_option, hα, Nat.add_assoc] using hn)
  exact ⟨x, y, order_of_sizes hx hsizeX (by omega)
    (blockSizes_dvd dvd_rfl (Nat.dvd_of_mod_eq_zero pc)) ⟨i₀, rfl⟩,
    order_of_sizes hy hsizeY (by omega) (blockSizes_dvd dvd_rfl (one_dvd _)) ⟨j₀, rfl⟩,
    by rw [hxy, pad_order, pad_order, F.product.order_eq_card, hα]⟩

private theorem three_involutions {n : ℕ} (hn : 4 ≤ n) :
    @Prescribed (Fin n) 2 2 2 := by
  let x : Perm (Fin 4) := swap 0 1 * swap 2 3
  let y : Perm (Fin 4) := swap 0 2 * swap 1 3
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply Prescribed.extend (α := Fin 4) (by simpa using hn)
  refine ⟨x, y, ?_, ?_, ?_⟩
  · exact orderOf_eq_prime (p := 2) (by decide) (by decide)
  · exact orderOf_eq_prime (p := 2) (by decide) (by decide)
  · exact orderOf_eq_prime (p := 2) (by decide) (by decide)

private theorem orders_with_largest_product {a b c n : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (ha' : a ≤ c) (hb' : b ≤ c) (hn : c + 2 ≤ n) :
    @Prescribed (Fin n) a b c := by
  by_cases hc : c = 2
  · have h₁ : a = 2 := by omega
    have h₂ : b = 2 := by omega
    subst a b c
    exact three_involutions (by omega)
  have hc₃ : 3 ≤ c := by omega
  let d := maxDefect c a
  let e := maxDefect c b
  have hd : c / 2 ≤ d := maxDefect_large ha ha'
  have he : c / 2 ≤ e := maxDefect_large hb hb'
  have hd₀ : Nonempty (OrderShape c a d) := by
    simpa only [Nat.sub_zero] using best_shape ha ha' (k := 0) (Or.inl rfl)
  have he₀ : Nonempty (OrderShape c b e) := by
    simpa only [Nat.sub_zero] using best_shape hb hb' (k := 0) (Or.inl rfl)
  by_cases hpar : (d + e) % 2 = (c + 1) % 2
  · exact orders_of_shapes (by omega) (by omega) (by omega) (by omega) hd₀ he₀
      (by omega) hpar
  -- A spare transposition can be replaced by two fixed points to adjust the parity.
  have hlarge : c ≤ d + e := by omega
  by_cases hsa : a % 2 = 0 ∧ a + 2 ≤ c
  · have hA := best_shape ha ha' (k := 1) (Or.inr ⟨rfl, hsa⟩)
    exact orders_of_shapes (by omega) (by omega) (by omega) (by omega) hA he₀
      (by change c - 1 ≤ d - 1 + e; omega)
      (by change (d - 1 + e) % 2 = _; omega)
  by_cases hsb : b % 2 = 0 ∧ b + 2 ≤ c
  · have hB := best_shape hb hb' (k := 1) (Or.inr ⟨rfl, hsb⟩)
    exact orders_of_shapes (by omega) (by omega) (by omega) (by omega) hd₀ hB
      (by change c - 1 ≤ d + (e - 1); omega)
      (by change (d + (e - 1)) % 2 = _; omega)
  have hnearA (h : a % 2 = 0) : c < a + 2 := by omega
  have hnearB (h : b % 2 = 0) : c < b + 2 := by omega
  by_cases pc : c % 2 = 0
  · by_cases pa : a % 2 = 0
    · have haa : a = c := by have := hnearA pa; omega
      by_cases pb : b % 2 = 0
      · have hbb : b = c := by have := hnearB pb; omega
        subst a b
        exact equal_even_orders (by omega) hn pc
      · have hp := maxDefect_odd_order (c := c) pb
        have hda : d = c - 1 := by simp [d, maxDefect, haa, pc]
        change e % 2 = 0 at hp
        omega
    · by_cases pb : b % 2 = 0
      · have hbb : b = c := by have := hnearB pb; omega
        have hp := maxDefect_odd_order (c := c) pa
        have heb : e = c - 1 := by simp [e, maxDefect, hbb, pc]
        change d % 2 = 0 at hp
        omega
      · exact odd_factors_even_product ha hb ha' hb' hn (by omega) (by omega) pc
  · by_cases pa : a % 2 = 0
    · have haa : a + 1 = c := by have := hnearA pa; omega
      by_cases pb : b % 2 = 0
      · have hbb : b + 1 = c := by have := hnearB pb; omega
        have hab : a = b := by omega
        have hde : d = e := by simp [d, e, hab]
        omega
      · exact mixed_near_odd_product ha hb haa hb' (by omega) pa (by omega)
    · by_cases pb : b % 2 = 0
      · have hbb : b + 1 = c := by have := hnearB pb; omega
        exact (mixed_near_odd_product hb ha hbb ha' (by omega) pb (by omega)).reverse
      · have hdpar : d % 2 = 0 := maxDefect_odd_order pa
        have hepar : e % 2 = 0 := maxDefect_odd_order pb
        omega

@[expose] public section

/-- **Kohl's question on orders of products in symmetric groups.** For every natural number $n$
and all natural numbers $a, b, c$ with $1 < a \le n - 2$, $1 < b \le n - 2$ and $1 < c \le n - 2$,
the symmetric group $S_n$ contains permutations $x$ and $y$ such that $x$ has order $a$, $y$ has
order $b$ and $xy$ has order $c$. -/
def symmetricGroupHasProductWithOrders : Prop :=
  ∀ n a b c : ℕ, 1 < a → 1 < b → 1 < c → a ≤ n - 2 → b ≤ n - 2 → c ≤ n - 2 →
    ∃ x y : Equiv.Perm (Fin n), orderOf x = a ∧ orderOf y = b ∧ orderOf (x * y) = c

/-- **Permutations of prescribed orders with product of prescribed order.** For every natural
number $n$ and all natural numbers $a, b, c$ with $1 < a \le n - 2$, $1 < b \le n - 2$ and
$1 < c \le n - 2$, the symmetric group $S_n$ contains permutations $x$ and $y$ of orders $a$ and
$b$ whose product $xy$ has order $c$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 18.49 (S. Kohl); resolution: G. A. Miller, Amer. J. Math. 22 (1900), no. 2, 185-190; J.
König, European J. Combin. 57 (2016), 50-56, Kourovka Archive, Problem 18.49: Yes, it is (Miller);
another solution by König, https://arxiv.org/abs/1401.0300v49.
-/
theorem symmetricGroupHasProductWithOrders_holds : symmetricGroupHasProductWithOrders := by
  intro n a b c ha hb hc hnA hnB hnC
  change @Prescribed (Fin n) a b c
  by_cases h : a ≤ c ∧ b ≤ c
  · exact orders_with_largest_product ha hb h.1 h.2 (by omega)
  by_cases h' : b ≤ a ∧ c ≤ a
  · exact (orders_with_largest_product hb hc h'.1 h'.2 (show a + 2 ≤ n by omega)).rotate.rotate
  · exact (orders_with_largest_product hc ha (show c ≤ b by omega) (show a ≤ b by omega)
      (show b + 2 ≤ n by omega)).rotate

end

end MathlibExt.GroupTheory.SymmetricGroupProductOrdersKourovka18Problem49Wanted
