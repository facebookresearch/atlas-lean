/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.GroupTheory.Perm.List
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Tactic.FinCases

/-!
# Quasi-identities and geometric equivalence of groups (Kourovka Notebook Problem 14.71)

Kourovka Notebook, Archive of Solved Problems, Problem 14.71 (B. I. Plotkin): groups `G` and `H` are
geometrically equivalent if `cl_G(T) = cl_H(T)` for every free group `F` of finite rank and every `T
⊆ F`, where `cl_G(T)` is the intersection of the kernels of all homomorphisms `F → G` vanishing on
`T`. If two groups have the same quasi-identities, are they geometrically equivalent?

The answer is no. The finitely supported wreath group built below and its ultrapower by the
hyperfilter on `ℕ` have the same quasi-identities but are not geometrically equivalent, so
`sameQuasiIdentitiesImpliesGeometricallyEquivalent` is false.
-/

@[expose] public section

open Filter

namespace MathlibExt.GroupTheory.QuasiIdentitiesGeometricEquivalenceKourovka14Problem71Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.71 (B. I.
Plotkin). UnsolvedMath record UM-00701056 (`KOU-14.71`), dataset ulamai/UnsolvedMath v1.8.0.

Homomorphisms `F_n → G` are given by the images of the basis; `T` ranges over all subsets (possibly
infinite), which is where the two notions can differ. Quasi-identities are `∀ x (w₁ = 1 ∧ ⋯ ∧ wₖ = 1
→ w = 1)` with finitely many premises.
-/


/-- A finitely supported wreath element: a finitely supported permutation of `ℕ`
together with a finitely supported function `ℕ → Perm (Fin 3)`. -/
private structure Wreath where
  perm : Equiv.Perm ℕ
  func : ℕ → Equiv.Perm (Fin 3)
  perm_fin : Set.Finite {i | perm i ≠ i}
  func_fin : Set.Finite {i | func i ≠ 1}

@[ext]
private theorem ext {a b : Wreath} (h1 : a.perm = b.perm) (h2 : a.func = b.func) : a = b := by
  cases a; cases b; simp_all

private instance : Mul Wreath where
  mul a b :=
    { perm := a.perm * b.perm
      func := fun k => a.func k * b.func (a.perm.symm k)
      perm_fin := by
        apply Set.Finite.subset (a.perm_fin.union b.perm_fin)
        intro i hi
        simp only [Equiv.Perm.mul_apply] at hi
        rcases eq_or_ne (a.perm i) i with ha | ha
        · rcases eq_or_ne (b.perm i) i with hb | hb
          · exact absurd (by simp [hb, ha]) hi
          · exact Or.inr hb
        · exact Or.inl ha
      func_fin := by
        apply Set.Finite.subset (a.func_fin.union (b.func_fin.image a.perm))
        intro k hk
        simp only [Set.mem_ofPred_eq] at hk
        rcases eq_or_ne (a.func k) 1 with h1 | h1
        · rcases eq_or_ne (b.func (a.perm.symm k)) 1 with h2 | h2
          · exact absurd (by rw [h1, h2]; simp : a.func k * b.func (a.perm.symm k) = 1) hk
          · right
            refine ⟨a.perm.symm k, h2, ?_⟩
            rw [Equiv.apply_symm_apply]
        · exact Or.inl h1 }

private instance : One Wreath where
  one :=
    { perm := 1
      func := fun _ => 1
      perm_fin := by
        have : {i : ℕ | (1 : Equiv.Perm ℕ) i ≠ i} = ∅ := by
          ext i; simp
        rw [this]; exact Set.finite_empty
      func_fin := by
        have : {i : ℕ | (fun _ : ℕ => (1 : Equiv.Perm (Fin 3))) i ≠ 1} = ∅ := by
          ext i; simp
        rw [this]; exact Set.finite_empty }

private instance : Inv Wreath where
  inv a :=
    { perm := a.perm.symm
      func := fun j => (a.func (a.perm j))⁻¹
      perm_fin := by
        apply Set.Finite.subset (a.perm_fin.image a.perm.symm)
        intro i hi
        simp only [Set.mem_ofPred_eq] at hi
        refine ⟨a.perm i, ?_, Equiv.symm_apply_apply a.perm i⟩
        · simp only [Set.mem_ofPred_eq]
          intro hcon
          apply hi
          have h1 : a.perm i = i := a.perm.injective hcon
          have h2 : a.perm.symm i = a.perm.symm (a.perm i) := congrArg _ h1.symm
          exact h2.trans (Equiv.symm_apply_apply a.perm i)
      func_fin := by
        apply Set.Finite.subset (a.func_fin.image a.perm.symm)
        intro j hj
        simp only [Set.mem_ofPred_eq] at hj
        refine ⟨a.perm j, ?_, ?_⟩
        · simp only [Set.mem_ofPred_eq]
          intro hcon
          apply hj
          rw [hcon]; simp
        · exact Equiv.symm_apply_apply a.perm j }

@[simp] private theorem mul_perm (a b : Wreath) : (a * b).perm = a.perm * b.perm := rfl
@[simp] private theorem mul_func (a b : Wreath) (k : ℕ) :
    (a * b).func k = a.func k * b.func (a.perm.symm k) := rfl
@[simp] private theorem one_perm : (1 : Wreath).perm = 1 := rfl
@[simp] private theorem one_func (k : ℕ) : (1 : Wreath).func k = 1 := rfl
@[simp] private theorem inv_perm (a : Wreath) : a⁻¹.perm = a.perm.symm := rfl
@[simp] private theorem inv_func (a : Wreath) (j : ℕ) :
    a⁻¹.func j = (a.func (a.perm j))⁻¹ := rfl

private theorem mul_assoc' (a b c : Wreath) : a * b * c = a * (b * c) := by
  refine ext (mul_assoc _ _ _) ?_
  funext k
  have hsym : (a.perm * b.perm).symm k = b.perm.symm (a.perm.symm k) := by
    rw [← Equiv.Perm.inv_def, mul_inv_rev, Equiv.Perm.inv_def, Equiv.Perm.inv_def,
      Equiv.Perm.mul_apply]
  simp only [mul_perm, mul_func, hsym, mul_assoc]

private theorem one_mul' (a : Wreath) : 1 * a = a := by
  refine ext (one_mul _) ?_
  funext k
  simp only [mul_func, one_func, one_perm, one_mul]
  rfl

private theorem mul_one' (a : Wreath) : a * 1 = a := by
  refine ext (mul_one _) ?_
  funext k
  simp only [mul_func, one_func, mul_one]

private theorem inv_mul_cancel' (a : Wreath) : a⁻¹ * a = 1 := by
  refine ext ?_ ?_
  · simp only [mul_perm, inv_perm]
    exact inv_mul_cancel a.perm
  · funext k
    simp only [mul_func, inv_func, inv_perm, one_func, Equiv.symm_symm]
    exact inv_mul_cancel _

private instance : Group Wreath where
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  inv_mul_cancel := inv_mul_cancel'

/-- The base element with coordinate function `f`. -/
private def base (f : ℕ → Equiv.Perm (Fin 3)) (hf : Set.Finite {i | f i ≠ 1}) : Wreath :=
  { perm := 1, func := f, perm_fin := by
      have : {i : ℕ | (1 : Equiv.Perm ℕ) i ≠ i} = ∅ := by ext i; simp
      rw [this]; exact Set.finite_empty
    func_fin := hf }

/-- The top element given by a finitely supported permutation. -/
private def top (σ : Equiv.Perm ℕ) (hσ : Set.Finite {i | σ i ≠ i}) : Wreath :=
  { perm := σ, func := fun _ => 1
    perm_fin := hσ
    func_fin := by
      have : {i : ℕ | (fun _ : ℕ => (1 : Equiv.Perm (Fin 3))) i ≠ 1} = ∅ := by
        ext i; simp
      rw [this]; exact Set.finite_empty }

@[simp] private theorem base_perm (f : ℕ → Equiv.Perm (Fin 3)) (hf) : (base f hf).perm = 1 := rfl
@[simp] private theorem base_func (f : ℕ → Equiv.Perm (Fin 3)) (hf) (k : ℕ) :
    (base f hf).func k = f k := rfl
@[simp] private theorem top_perm (σ : Equiv.Perm ℕ) (hσ) : (top σ hσ).perm = σ := rfl
@[simp] private theorem top_func (σ : Equiv.Perm ℕ) (hσ) (k : ℕ) : (top σ hσ).func k = 1 := rfl

private theorem base_mul_base (f g : ℕ → Equiv.Perm (Fin 3)) (hf hg) :
    base f hf * base g hg = base (fun k => f k * g k) (by
      apply Set.Finite.subset (hf.union hg)
      intro k hk
      simp only [Set.mem_ofPred_eq] at hk
      by_contra hcon
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hcon
      exact hk (by rw [not_not.mp hcon.1, not_not.mp hcon.2]; simp)) := by
  refine ext rfl ?_
  funext k; rfl

private theorem top_mul_top (σ τ : Equiv.Perm ℕ) (hσ hτ) :
    top σ hσ * top τ hτ = top (σ * τ) (by
      apply Set.Finite.subset (hσ.union hτ)
      intro i hi
      simp only [Equiv.Perm.mul_apply] at hi
      by_contra hcon
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hcon
      exact hi (by rw [not_not.mp hcon.2, not_not.mp hcon.1])) := by
  refine ext rfl ?_
  funext k; rfl

private theorem pow_perm (w : Wreath) (n : ℕ) : (w ^ n).perm = w.perm ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_perm, ih, pow_succ]

private theorem pow_apply_eq_of_fixed {σ : Equiv.Perm ℕ} {i : ℕ} (h : σ i = i) (n : ℕ) :
    (σ ^ n) i = i := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Equiv.Perm.mul_apply, h]; exact ih

private theorem support_pow_subset (σ : Equiv.Perm ℕ) (n : ℕ) :
    {i | (σ ^ n) i ≠ i} ⊆ {i | σ i ≠ i} := by
  intro i hi hcon
  exact hi (pow_apply_eq_of_fixed hcon n)

private theorem pow_top (σ : Equiv.Perm ℕ) (hσ) (n : ℕ) :
    (top σ hσ) ^ n = top (σ ^ n) (hσ.subset (support_pow_subset σ n)) := by
  induction n with
  | zero => exact ext (by simp) (by funext k; simp)
  | succ n ih =>
    rw [pow_succ, ih, top_mul_top]
    refine ext ?_ ?_
    · exact (pow_succ σ n).symm
    · funext k; simp

/-- Every element of the symmetric group on three points has order dividing six. -/
private theorem perm3_pow_six (p : Equiv.Perm (Fin 3)) : p ^ 6 = 1 := by
  have h : orderOf p ∣ 6 := by
    have h1 : orderOf p ∣ Fintype.card (Equiv.Perm (Fin 3)) := orderOf_dvd_card
    rwa [Fintype.card_perm, Fintype.card_fin] at h1
  exact (orderOf_dvd_iff_pow_eq_one).mp h

private theorem base_pow (f : ℕ → Equiv.Perm (Fin 3)) (hf) (n : ℕ) :
    (base f hf) ^ n = base (fun k => f k ^ n) (by
      apply Set.Finite.subset hf
      intro k hk
      simp only [Set.mem_ofPred_eq] at hk
      by_contra hcon
      exact hk (by
        have h1 : f k = 1 := by by_contra h'; exact hcon h'
        rw [h1]; simp)) := by
  induction n with
  | zero => exact ext (by simp) (by funext k; simp)
  | succ n ih =>
    rw [pow_succ, ih, base_mul_base]
    refine ext rfl ?_
    funext k; simp only [base_func, pow_succ]

/-- A finitely supported permutation of `ℕ` has finite order. -/
private theorem perm_fin_order {σ : Equiv.Perm ℕ} (hσ : Set.Finite {i | σ i ≠ i}) :
    ∃ m, 0 < m ∧ σ ^ m = 1 := by
  classical
  let S : Set ℕ := {i | σ i ≠ i}
  have : Fintype S := hσ.fintype
  have hbase : Set.MapsTo σ S S := by
    intro x hx
    have hx' : σ x ≠ x := hx
    intro hcon
    exact hx' (σ.injective hcon)
  have hmaps : ∀ n : ℕ, Set.MapsTo (σ ^ n) S S := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      rw [pow_succ, Equiv.Perm.mul_apply]
      exact ih (hbase hx)
  have hpow : ∀ {n : ℕ} {x : ℕ}, x ∉ S → (σ ^ n) x = x := by
    intro n x hx
    exact pow_apply_eq_of_fixed (by simpa [S] using hx) n
  obtain ⟨a, b, hne, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun n => Equiv.Perm.subtypePermOfFintype (σ ^ n) (fun x hx => hmaps n hx))
  wlog hab : a < b generalizing a b
  · exact this b a (Ne.symm hne) heq.symm (lt_of_le_of_ne (Nat.le_of_not_lt hab) hne.symm)
  have hpow_eq : σ ^ a = σ ^ b := by
    ext x
    by_cases hx : x ∈ S
    · have h1 := congrArg (fun τ : Equiv.Perm S => (τ ⟨x, hx⟩).val) heq
      simpa [Equiv.Perm.subtypePermOfFintype_apply] using h1
    · rw [hpow hx, hpow hx]
  have hle : a ≤ b := le_of_lt hab
  have hsplit : σ ^ b = σ ^ a * σ ^ (b - a) := by
    rw [← pow_add, Nat.add_sub_cancel' hle]
  refine ⟨b - a, Nat.sub_pos_of_lt hab, ?_⟩
  have hcan : σ ^ a * σ ^ (b - a) = σ ^ a * 1 := by rw [← hsplit, hpow_eq, mul_one]
  exact mul_left_cancel hcan


private theorem torsion (w : Wreath) : ∃ m, 0 < m ∧ w ^ m = 1 := by
  obtain ⟨m0, hm0, hσ⟩ := perm_fin_order w.perm_fin
  have hg : w ^ m0 = base (w ^ m0).func (w ^ m0).func_fin := by
    refine ext ?_ rfl
    rw [pow_perm, hσ]; rfl
  refine ⟨m0 * 6, Nat.mul_pos hm0 (Nat.succ_pos 5), ?_⟩
  rw [pow_mul, hg, base_pow]
  refine ext (by simp) ?_
  funext k
  simp [perm3_pow_six]

private theorem support_symm_subset (σ : Equiv.Perm ℕ) :
    {i | σ.symm i ≠ i} ⊆ {i | σ i ≠ i} := by
  intro i hi hcon
  have h2 : σ.symm (σ i) = σ.symm i := congrArg _ hcon
  rw [Equiv.symm_apply_apply] at h2
  exact hi h2.symm

private theorem conj_top_base (τ : Equiv.Perm ℕ) (hτ) (f : ℕ → Equiv.Perm (Fin 3)) (hf) :
    top τ hτ * base f hf * (top τ hτ)⁻¹ =
      base (fun k => f (τ.symm k)) (by
        have hsub : {k | f (τ.symm k) ≠ 1} ⊆ τ '' {k | f k ≠ 1} := by
          intro k hk
          have hk2 : (τ.symm k) ∈ {k | f k ≠ 1} := hk
          have h2 := Set.mem_image_of_mem τ hk2
          rwa [Equiv.apply_symm_apply] at h2
        exact (hf.image τ).subset hsub) := by
  refine ext ?_ ?_
  · simp only [mul_perm, top_perm, base_perm, inv_perm, mul_one]
    rw [← Equiv.Perm.inv_def]; exact mul_inv_cancel τ
  · funext k; simp

/-- The element supported at a single coordinate. -/
private def point (i : ℕ) (p : Equiv.Perm (Fin 3)) : Wreath :=
  base (Function.update 1 i p) (by
    apply Set.Finite.subset (Set.finite_singleton i)
    intro k hk
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff] at hk ⊢
    by_contra h
    exact hk (by simp [Function.update_of_ne h p (1 : ℕ → Equiv.Perm (Fin 3))]))

private theorem point_func (i : ℕ) (p : Equiv.Perm (Fin 3)) (k : ℕ) :
    (point i p).func k = Function.update (1 : ℕ → Equiv.Perm (Fin 3)) i p k := rfl

private theorem point_perm (i : ℕ) (p : Equiv.Perm (Fin 3)) : (point i p).perm = 1 := rfl

private theorem point_eq_base (i : ℕ) (p : Equiv.Perm (Fin 3)) :
    point i p = base (Function.update (1 : ℕ → Equiv.Perm (Fin 3)) i p) (by
      apply Set.Finite.subset (Set.finite_singleton i)
      intro k hk
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff] at hk ⊢
      by_contra h
      exact hk (by simp [Function.update_of_ne h p (1 : ℕ → Equiv.Perm (Fin 3))])) := rfl

/-- The transpositions generating the noncommuting pair in `S₃`. -/
private def aPerm : Equiv.Perm (Fin 3) := Equiv.swap 0 1
private def bPerm : Equiv.Perm (Fin 3) := Equiv.swap 0 2

private theorem commutator_ab_ne_one :
    aPerm * bPerm * aPerm⁻¹ * bPerm⁻¹ ≠ 1 := by decide

/-- The cycle `(0 1 ⋯ k)` on `ℕ`. -/
private def cyclePerm (k : ℕ) : Equiv.Perm ℕ := (List.range (k + 1)).formPerm

private theorem cycle_support_fin (k : ℕ) :
    Set.Finite {i | cyclePerm k i ≠ i} :=
  Set.Finite.subset (List.range (k + 1)).toFinset.finite_toSet
    (List.support_formPerm_le' _)

private theorem cycle_pow_zero {n k : ℕ} (h : n ≤ k) :
    ((cyclePerm k) ^ n) 0 = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : n ≤ k := le_trans (Nat.le_succ n) h
    rw [pow_succ', Equiv.Perm.mul_apply, ih hn]
    have hlen : n + 1 < (List.range (k + 1)).length := by simp; omega
    have happ := List.formPerm_apply_lt_getElem (List.range (k + 1))
      List.nodup_range n hlen
    have happ2 : cyclePerm k n = n + 1 := by
      change (List.range (k + 1)).formPerm n = n + 1
      simpa [List.getElem_range] using happ
    exact happ2


/-- The word `zⁿ y z⁻ⁿ` in the free group on three generators. -/
private def conjWord (n : ℕ) : FreeGroup (Fin 3) :=
  (FreeGroup.of 2) ^ n * FreeGroup.of 1 * ((FreeGroup.of 2) ^ n)⁻¹

/-- The commutator word `[x, zⁿ y z⁻ⁿ]`. -/
private def commWord (n : ℕ) : FreeGroup (Fin 3) :=
  FreeGroup.of 0 * conjWord n * (FreeGroup.of 0)⁻¹ * (conjWord n)⁻¹

private theorem lift_conjWord {G : Type} [Group G] (x : Fin 3 → G) (n : ℕ) :
    FreeGroup.lift x (conjWord n) = (x 2) ^ n * x 1 * ((x 2) ^ n)⁻¹ := by
  simp [conjWord]

private theorem lift_commWord {G : Type} [Group G] (x : Fin 3 → G) (n : ℕ) :
    FreeGroup.lift x (commWord n) =
      x 0 * ((x 2) ^ n * x 1 * ((x 2) ^ n)⁻¹) * (x 0)⁻¹ *
        ((x 2) ^ n * x 1 * ((x 2) ^ n)⁻¹)⁻¹ := by
  simp [commWord, lift_conjWord]

private theorem comm_prod_eq_one_iff {G : Type} [Group G] {a b : G} :
    a * b * a⁻¹ * b⁻¹ = 1 ↔ Commute a b := by
  constructor
  · intro h
    have h1 : a * b * a⁻¹ = b := mul_inv_eq_one.mp h
    change a * b = b * a
    calc a * b = (a * b * a⁻¹) * a := by simp [mul_assoc]
      _ = b * a := by rw [h1]
  · intro h
    rw [h.eq]
    simp [mul_assoc]

private theorem inv_base (f : ℕ → Equiv.Perm (Fin 3)) (hf) :
    (base f hf)⁻¹ = base (fun k => (f k)⁻¹) (by
      apply Set.Finite.subset hf
      intro k hk
      simp only [Set.mem_ofPred_eq] at hk ⊢
      intro hcon
      exact hk (by rw [hcon]; simp)) := by
  refine ext rfl ?_
  funext k; simp

private theorem base_commutator (f g : ℕ → Equiv.Perm (Fin 3)) (hf hg) :
    (base f hf) * (base g hg) * (base f hf)⁻¹ * (base g hg)⁻¹ =
      base (fun k => f k * g k * (f k)⁻¹ * (g k)⁻¹) (by
        apply Set.Finite.subset (hf.union hg)
        intro k hk
        simp only [Set.mem_ofPred_eq] at hk ⊢
        by_contra hcon
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hcon
        apply hk
        rw [not_not.mp hcon.1, not_not.mp hcon.2]
        simp) := by
  rw [inv_base, inv_base, base_mul_base, base_mul_base, base_mul_base]

private theorem point_commute {i j : ℕ} (hij : i ≠ j) (p q : Equiv.Perm (Fin 3)) :
    Commute (point i p) (point j q) := by
  refine ext rfl ?_
  funext k
  have hsym : (1 : Equiv.Perm ℕ).symm k = k := rfl
  simp only [mul_func, point_func, point_perm, hsym]
  by_cases hki : k = i
  · subst hki
    rw [Function.update_self, Function.update_of_ne hij q (1 : ℕ → Equiv.Perm (Fin 3))]
    simp
  · by_cases hkj : k = j
    · subst hkj
      rw [Function.update_of_ne (Ne.symm hij) p (1 : ℕ → Equiv.Perm (Fin 3)),
        Function.update_self]
      simp
    · rw [Function.update_of_ne hki p (1 : ℕ → Equiv.Perm (Fin 3)),
        Function.update_of_ne hkj q (1 : ℕ → Equiv.Perm (Fin 3))]

/-- Conjugating a point element by a power of a top element moves its support. -/
private theorem conj_point (σ : Equiv.Perm ℕ) (hσ) (n : ℕ) (i : ℕ) (p : Equiv.Perm (Fin 3)) :
    (top σ hσ) ^ n * point i p * ((top σ hσ) ^ n)⁻¹ = point ((σ ^ n) i) p := by
  rw [pow_top, point_eq_base]
  have hconj := conj_top_base (σ ^ n)
    (hσ.subset (support_pow_subset σ n))
    (Function.update (1 : ℕ → Equiv.Perm (Fin 3)) i p)
    (by
      apply Set.Finite.subset (Set.finite_singleton i)
      intro k hk
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff] at hk ⊢
      by_contra h
      exact hk (by simp [Function.update_of_ne h p (1 : ℕ → Equiv.Perm (Fin 3))]))
  rw [hconj]
  refine ext rfl ?_
  funext k
  change Function.update (1 : ℕ → Equiv.Perm (Fin 3)) i p (((σ ^ n).symm) k) =
    Function.update (1 : ℕ → Equiv.Perm (Fin 3)) ((σ ^ n) i) p k
  by_cases hkj : k = (σ ^ n) i
  · subst hkj
    rw [Function.update_self]
    have : ((σ ^ n).symm) ((σ ^ n) i) = i := Equiv.symm_apply_apply _ _
    rw [this, Function.update_self]
  · have h2 : ((σ ^ n).symm) k ≠ i := by
      intro hcon
      apply hkj
      have := congrArg (σ ^ n) hcon
      rwa [Equiv.apply_symm_apply] at this
    rw [Function.update_of_ne hkj p (1 : ℕ → Equiv.Perm (Fin 3)),
      Function.update_of_ne h2 p (1 : ℕ → Equiv.Perm (Fin 3))]
    rfl



open Filter in
/-- The ultrapower of the wreath group by the hyperfilter on `ℕ`. -/
private noncomputable abbrev UltraWreath : Type :=
  Filter.Germ (Filter.hyperfilter ℕ).toFilter Wreath

/-- Lifting a word commutes with taking germs of tuples. -/
private noncomputable def liftGermHom {α : Type} (x : α → ℕ → Wreath) :
    FreeGroup α →* UltraWreath where
  toFun w := Filter.Germ.ofFun (fun k => FreeGroup.lift (fun j => x j k) w)
  map_one' := by
    rw [show (fun k => FreeGroup.lift (fun j => x j k) (1 : FreeGroup α)) =
      (1 : ℕ → Wreath) from funext fun k => map_one _]
    exact Filter.Germ.coe_one
  map_mul' := by
    intro a b
    rw [show (fun k => FreeGroup.lift (fun j => x j k) (a * b)) =
      (fun k => FreeGroup.lift (fun j => x j k) a) *
        (fun k => FreeGroup.lift (fun j => x j k) b) from
      funext fun k => map_mul _ _ _]
    exact Filter.Germ.coe_mul _ _

private theorem lift_ofFun {α : Type} (x : α → ℕ → Wreath) (w : FreeGroup α) :
    (Filter.Germ.ofFun (fun k => FreeGroup.lift (fun j => x j k) w) : UltraWreath) =
      FreeGroup.lift (fun j => (Filter.Germ.ofFun (x j) : UltraWreath)) w := by
  have hg : ∀ j : α, (liftGermHom x) (FreeGroup.of j) =
      (Filter.Germ.ofFun (x j) : UltraWreath) := by
    intro j
    change (Filter.Germ.ofFun (fun k => FreeGroup.lift (fun j' => x j' k)
      (FreeGroup.of j)) : UltraWreath) = _
    simp only [FreeGroup.lift_apply_of]
  exact FreeGroup.lift_unique (liftGermHom x) hg

private theorem ofFun_eq_one_iff (s : ℕ → Wreath) :
    (Filter.Germ.ofFun s : UltraWreath) = 1 ↔
      ∀ᶠ k in (Filter.hyperfilter ℕ).toFilter, s k = 1 := by
  constructor
  · intro h
    rw [← Filter.Germ.coe_one, Filter.Germ.coe_eq] at h
    exact h
  · intro h
    rw [← Filter.Germ.coe_one]
    exact Filter.Germ.coe_eq.mpr h

private theorem eventually_ge (n : ℕ) :
    ∀ᶠ k in (Filter.hyperfilter ℕ).toFilter, n ≤ k :=
  Nat.hyperfilter_le_atTop (Filter.eventually_ge_atTop n)


/-- **Quasi-identities of groups.** A quasi-identity consists of a natural number $n$, a finite
list of premises $w_1, \dots, w_k$ and a conclusion $w$, all elements of the free group $F_n$ on
the unknowns $x_0, \dots, x_{n-1}$. It stands for the formula
$\forall x_0, \dots, x_{n-1}\, (w_1 = 1 \wedge \dots \wedge w_k = 1 \to w = 1)$. -/
structure QuasiIdentity where
  /-- The number of unknowns. -/
  n : ℕ
  /-- The premises `w₁, …, wₖ`. -/
  premises : List (FreeGroup (Fin n))
  /-- The conclusion `w`. -/
  conclusion : FreeGroup (Fin n)

/-- **Satisfaction of a quasi-identity in a group.** Let $q$ be a quasi-identity with unknowns
$x_0, \dots, x_{n-1}$, premises $w_1, \dots, w_k$ and conclusion $w$, all in the free group $F_n$
on $x_0, \dots, x_{n-1}$. For $g_0, \dots, g_{n-1}$ in a group $G$ and $u \in F_n$, write
$u(g_0, \dots, g_{n-1})$ for the image of $u$ under the homomorphism $F_n \to G$ sending each
$x_j$ to $g_j$. Then $q$ holds in $G$ when for all $g_0, \dots, g_{n-1} \in G$ with
$w_i(g_0, \dots, g_{n-1}) = 1$ for every premise $w_i$, also $w(g_0, \dots, g_{n-1}) = 1$. -/
def QuasiIdentity.HoldsIn (q : QuasiIdentity) (G : Type*) [Group G] : Prop :=
  ∀ x : Fin q.n → G, (∀ w ∈ q.premises, FreeGroup.lift x w = 1) →
    FreeGroup.lift x q.conclusion = 1

/-- **Closure of a set of words with respect to a group.** Let $G$ be a group, let $F_n$ be the
free group on the basis $x_0, \dots, x_{n-1}$, and let $T \subseteq F_n$. The $G$-closure
$\mathrm{cl}_G(T)$ is the set of $w \in F_n$ such that $\mu(w) = 1$ for every homomorphism
$\mu : F_n \to G$ with $\mu(t) = 1$ for all $t \in T$, that is, the intersection of the kernels
of all homomorphisms $F_n \to G$ that vanish on $T$. -/
def gClosure (G : Type*) [Group G] {n : ℕ} (T : Set (FreeGroup (Fin n))) :
    Set (FreeGroup (Fin n)) :=
  {w | ∀ x : Fin n → G, (∀ t ∈ T, FreeGroup.lift x t = 1) → FreeGroup.lift x w = 1}

/-- **Geometrically equivalent groups.** Two groups $G$ and $H$ are geometrically equivalent
(B. I. Plotkin) when $\mathrm{cl}_G(T) = \mathrm{cl}_H(T)$ for every natural number $n$ and
every subset $T$ of the free group $F_n$ of rank $n$, where $\mathrm{cl}_G(T)$ is the
$G$-closure of $T$: the intersection of the kernels of all homomorphisms $F_n \to G$ that
vanish on $T$. -/
def GeometricallyEquivalent (G H : Type*) [Group G] [Group H] : Prop :=
  ∀ (n : ℕ) (T : Set (FreeGroup (Fin n))), gClosure G T = gClosure H T

/-- **Plotkin's problem on quasi-identities and geometric equivalence.** The proposition
(Kourovka Problem 14.71, B. I. Plotkin) that any two groups $G$ and $H$ satisfying the same
quasi-identities, meaning that every quasi-identity holds in $G$ if and only if it holds in $H$,
are geometrically equivalent. -/
def sameQuasiIdentitiesImpliesGeometricallyEquivalent : Prop :=
  ∀ (G H : Type) [Group G] [Group H], (∀ q : QuasiIdentity, q.HoldsIn G ↔ q.HoldsIn H) →
    GeometricallyEquivalent G H

open Filter in
private theorem holdsIn_ultra_iff (q : QuasiIdentity) :
    q.HoldsIn UltraWreath ↔ q.HoldsIn Wreath := by
  constructor
  · intro h x hx
    have hprem : ∀ w ∈ q.premises,
        FreeGroup.lift (fun j => (Filter.Germ.ofFun (fun _ => x j) : UltraWreath)) w = 1 := by
      intro w hw
      have h2 := lift_ofFun (fun j _ => x j) w
      have h3 : (Filter.Germ.ofFun (fun _ => FreeGroup.lift x w) : UltraWreath) = 1 := by
        rw [ofFun_eq_one_iff]
        filter_upwards with k
        exact hx w hw
      exact h2.symm.trans h3
    have hcon := h _ hprem
    have h2 := lift_ofFun (fun j _ => x j) q.conclusion
    have h3 := h2.trans hcon
    rw [ofFun_eq_one_iff] at h3
    obtain ⟨k, hk⟩ := h3.exists
    exact hk
  · intro h x hx
    choose f hf using fun j => Quotient.exists_rep (x j)
    have hf' : ∀ j, (Filter.Germ.ofFun (f j) : UltraWreath) = x j := fun j => hf j
    have hEv : ∀ w ∈ q.premises,
        ∀ᶠ k in (Filter.hyperfilter ℕ).toFilter,
          FreeGroup.lift (fun j => f j k) w = 1 := by
      intro w hw
      have hw1 : FreeGroup.lift (fun j => x j) w = 1 := hx w hw
      simp only [← hf'] at hw1
      have h2 := lift_ofFun (fun j => f j) w
      have hw2 : (Filter.Germ.ofFun (fun k => FreeGroup.lift (fun j => f j k) w) :
          UltraWreath) = 1 := h2.trans hw1
      exact (ofFun_eq_one_iff _).mp hw2
    have hall : ∀ (ws : List (FreeGroup (Fin q.n))),
        (∀ w ∈ ws, ∀ᶠ k in (Filter.hyperfilter ℕ).toFilter,
          FreeGroup.lift (fun j => f j k) w = 1) →
        ∀ᶠ k in (Filter.hyperfilter ℕ).toFilter,
          ∀ w ∈ ws, FreeGroup.lift (fun j => f j k) w = 1 := by
      intro ws
      induction ws with
      | nil => intro _; filter_upwards with k; simp
      | cons w ws ih =>
        intro hh
        have hw := hh w (by simp)
        have hws := ih (fun w' hw' => hh w' (by simp [hw']))
        filter_upwards [hw, hws] with k hk1 hk2 w' hw'
        rcases List.mem_cons.mp hw' with rfl | hw''
        · exact hk1
        · exact hk2 w' hw''
    have hEvAll := hall q.premises hEv
    have hconEv : ∀ᶠ k in (Filter.hyperfilter ℕ).toFilter,
        FreeGroup.lift (fun j => f j k) q.conclusion = 1 := by
      filter_upwards [hEvAll] with k hk
      exact h (fun j => f j k) hk
    have hcon : (Filter.Germ.ofFun (fun k => FreeGroup.lift (fun j => f j k) q.conclusion) :
        UltraWreath) = 1 := (ofFun_eq_one_iff _).mpr hconEv
    have h2 := lift_ofFun (fun j => f j) q.conclusion
    rw [h2] at hcon
    have hcon2 : FreeGroup.lift (fun j => x j) q.conclusion = 1 := by
      simpa only [hf'] using hcon
    exact hcon2


open Filter in
/-- The constant sequences giving the two point elements in the ultrapower. -/
private def seqX : ℕ → Wreath := fun _ => point 0 aPerm
private def seqY : ℕ → Wreath := fun _ => point 0 bPerm
private def seqZ : ℕ → Wreath :=
  fun k => top (cyclePerm k) (cycle_support_fin k)

/-- The matrix of sequences for the three variables in the ultrapower. -/
private def seqMat : Fin 3 → ℕ → Wreath := ![seqX, seqY, seqZ]

/-- The top element of the `k`-th approximating tuple. -/
private abbrev topCycle (k : ℕ) : Wreath :=
  top (cyclePerm k) (cycle_support_fin k)

/-- The `k`-th approximating tuple in the wreath group. -/
private def tupleAt (k : ℕ) : Fin 3 → Wreath :=
  ![point 0 aPerm, point 0 bPerm, topCycle k]

private theorem seqMat_eq (j : Fin 3) (k : ℕ) : seqMat j k = tupleAt k j := by
  fin_cases j <;> rfl

private theorem lift_tupleAt (k : ℕ) (n : ℕ) :
    FreeGroup.lift (tupleAt k) (commWord n) =
      point 0 aPerm *
        ((topCycle k) ^ n * point 0 bPerm * ((topCycle k) ^ n)⁻¹) *
        (point 0 aPerm)⁻¹ *
        ((topCycle k) ^ n * point 0 bPerm * ((topCycle k) ^ n)⁻¹)⁻¹ :=
  lift_commWord _ _

private theorem lift_germTuple (n : ℕ) :
    FreeGroup.lift (fun j => (Filter.Germ.ofFun (seqMat j) : UltraWreath)) (commWord n) =
      (Filter.Germ.ofFun (fun k => FreeGroup.lift (tupleAt k) (commWord n)) :
        UltraWreath) := by
  have h2 := lift_ofFun seqMat (commWord n)
  have h3 : (fun k => FreeGroup.lift (fun j => seqMat j k) (commWord n)) =
      (fun k => FreeGroup.lift (tupleAt k) (commWord n)) := funext fun k =>
    congrArg (fun f => FreeGroup.lift f (commWord n)) (funext fun j => seqMat_eq j k)
  rw [h3] at h2
  exact h2.symm

/-- The tuple in the ultrapower satisfies every commutator equation of the system. -/
private theorem germTuple_premise (n : ℕ) (hn : 1 ≤ n) :
    FreeGroup.lift (fun j => (Filter.Germ.ofFun (seqMat j) : UltraWreath)) (commWord n) = 1 := by
  rw [lift_germTuple, ofFun_eq_one_iff]
  filter_upwards [eventually_ge n] with k hk
  rw [lift_tupleAt]
  have hd : (topCycle k) ^ n * point 0 bPerm * ((topCycle k) ^ n)⁻¹ =
      point n bPerm := by
    rw [conj_point, cycle_pow_zero hk]
  rw [hd]
  exact (comm_prod_eq_one_iff).mpr
    (point_commute (show (0 : ℕ) ≠ n by omega) _ _)

/-- The tuple in the ultrapower does not satisfy the commutator conclusion. -/
private theorem germTuple_conclusion_ne :
    FreeGroup.lift (fun j => (Filter.Germ.ofFun (seqMat j) : UltraWreath)) (commWord 0) ≠ 1 := by
  rw [lift_germTuple]
  intro hcon
  rw [ofFun_eq_one_iff] at hcon
  obtain ⟨k, hk⟩ := hcon.exists
  rw [lift_tupleAt] at hk
  simp only [pow_zero, one_mul, inv_one, mul_one] at hk
  rw [point_eq_base, point_eq_base, base_commutator] at hk
  have h0 := congrArg (fun w : Wreath => w.func 0) hk
  simp only [base_func, Function.update_self] at h0
  exact commutator_ab_ne_one h0

/-- The commutator conclusion lies in the `Wreath`-closure of the system. -/
private theorem mem_gClosure_wreath :
    commWord 0 ∈ gClosure Wreath {w | ∃ n, 1 ≤ n ∧ w = commWord n} := by
  intro x hx
  obtain ⟨m, hm, hpow⟩ := torsion (x 2)
  have hmem : commWord m ∈ {w | ∃ n, 1 ≤ n ∧ w = commWord n} := ⟨m, hm, rfl⟩
  have h1 := hx _ hmem
  rw [lift_commWord] at h1
  rw [hpow] at h1
  simp only [one_mul, inv_one, mul_one] at h1
  have hcomm : Commute (x 0) (x 1) := (comm_prod_eq_one_iff).mp h1
  rw [lift_commWord]
  simp only [pow_zero, one_mul, inv_one, mul_one]
  exact (comm_prod_eq_one_iff).mpr hcomm

/--
**Groups with the same quasi-identities need not be geometrically equivalent.** The statement
of Kourovka Problem 14.71 is false: there are groups $G$ and $H$ such that every quasi-identity
holds in $G$ if and only if it holds in $H$, but $G$ and $H$ are not geometrically equivalent.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 14.71 (B. I. Plotkin); resolution: V. V. Bludov, Abstracts of the 7th Int. Conf. Groups and
Group Rings, Supraśl, 1999, p. 6; R. Göbel and S. Shelah, Proc. Amer. Math. Soc. 130 (2002),
673-674; A. G. Myasnikov and V. N. Remeslennikov, J. Algebra 234 (2000), no. 1, 225-276, Kourovka
Archive, Problem 14.71 (answer: No, not always).
-/
theorem sameQuasiIdentitiesImpliesGeometricallyEquivalent_refuted :
    ¬ sameQuasiIdentitiesImpliesGeometricallyEquivalent := by
  intro h
  have hiff : ∀ q : QuasiIdentity, q.HoldsIn Wreath ↔ q.HoldsIn UltraWreath :=
    fun q => (holdsIn_ultra_iff q).symm
  have hgeom := h Wreath UltraWreath hiff
  have heq := hgeom 3 {w | ∃ n, 1 ≤ n ∧ w = commWord n}
  have hmemU : commWord 0 ∈
      gClosure UltraWreath {w | ∃ n, 1 ≤ n ∧ w = commWord n} :=
    heq ▸ mem_gClosure_wreath
  have hprem : ∀ t ∈ {w | ∃ n, 1 ≤ n ∧ w = commWord n},
      FreeGroup.lift (fun j => (Filter.Germ.ofFun (seqMat j) : UltraWreath)) t = 1 := by
    intro t ht
    obtain ⟨n, hn, rfl⟩ := ht
    exact germTuple_premise n hn
  have hcon := hmemU _ hprem
  exact germTuple_conclusion_ne hcon

end MathlibExt.GroupTheory.QuasiIdentitiesGeometricEquivalenceKourovka14Problem71Wanted
