/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Fin

/-!
# Permutations and unsigned Stirling numbers

This file identifies unsigned Stirling numbers of the first kind with permutations having a
prescribed number of cycles, counting fixed points as cycles.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Number of cycles of a permutation.** For a permutation $\sigma$ of a finite type $\alpha$,
the number of cycles of $\sigma$, counting each fixed point as a cycle of length one, is the
number of equivalence classes of $\alpha$ under the relation that holds between $x$ and $y$ when
$\sigma^i(x) = y$ for some integer $i$. -/
public noncomputable def cycleQuotientCount {α : Type*} [Fintype α]
    (σ : Equiv.Perm α) : ℕ :=
  Nat.card (Quotient (Equiv.Perm.SameCycle.setoid σ))

private noncomputable def cycleQuotientEquiv {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) :
    Quotient (Equiv.Perm.SameCycle.setoid σ) ≃
      Function.fixedPoints σ ⊕ σ.cycleFactorsFinset := by
  classical
  let toCycle : α → Function.fixedPoints σ ⊕ σ.cycleFactorsFinset := fun x =>
    if hx : σ x = x then
      Sum.inl ⟨x, hx⟩
    else
      Sum.inr ⟨σ.cycleOf x,
        Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Equiv.Perm.mem_support.mpr hx)⟩
  have toCycle_eq (x y : α) (hxy : σ.SameCycle x y) : toCycle x = toCycle y := by
    by_cases hx : σ x = x
    · have hxy' : x = y := hxy.eq_of_left hx
      subst y
      rfl
    · have hy : σ y ≠ y := fun hy => hx (hxy.apply_eq_self_iff.mpr hy)
      simp only [toCycle, hx, hy, dite_false, Sum.inr.injEq, Subtype.mk.injEq]
      exact hxy.cycleOf_eq
  refine Equiv.ofBijective (Quotient.lift toCycle toCycle_eq) ?_
  constructor
  · intro a b hab
    refine Quotient.inductionOn₂ a b ?_ hab
    intro x y hxy
    change toCycle x = toCycle y at hxy
    apply Quotient.sound
    by_cases hx : σ x = x
    · by_cases hy : σ y = y
      · simp only [toCycle, hx, hy, dite_true, Sum.inl.injEq] at hxy
        exact (congrArg Subtype.val hxy).sameCycle σ
      · simp only [toCycle, hx, hy, dite_true, dite_false] at hxy
        exact (Sum.inl_ne_inr hxy).elim
    · by_cases hy : σ y = y
      · simp only [toCycle, hx, hy, dite_true, dite_false] at hxy
        exact (Sum.inr_ne_inl hxy).elim
      · simp only [toCycle, hx, hy, dite_false, Sum.inr.injEq, Subtype.mk.injEq] at hxy
        exact (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support
          (Equiv.Perm.mem_support.mpr hx) (Equiv.Perm.mem_support.mpr hy)).mpr hxy
  · rintro (x | c)
    · refine ⟨Quotient.mk _ x.1, ?_⟩
      change toCycle x.1 = Sum.inl x
      have hx : σ x.1 = x.1 := x.2
      simp only [toCycle, hx, dite_true]
    · obtain ⟨x, hxc⟩ :=
        (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.property).1.nonempty_support
      have hx : σ x ≠ x := Equiv.Perm.mem_support.mp
        (Equiv.Perm.mem_cycleFactorsFinset_support_le c.property hxc)
      refine ⟨Quotient.mk _ x, ?_⟩
      change toCycle x = Sum.inr c
      simp only [toCycle, hx, dite_false, Sum.inr.injEq]
      apply Subtype.ext
      exact (Equiv.Perm.cycle_is_cycleOf hxc c.property).symm

/-- **Counting cycles via the cycle type.** For a permutation $\sigma$ of a finite type, the
number of cycles of $\sigma$, counting each fixed point as a cycle of length one, equals the
number of cycles of $\sigma$ of length at least $2$ (the length of its cycle type) plus the
number of fixed points of $\sigma$. -/
public theorem cycleQuotientCount_eq {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) :
    cycleQuotientCount σ =
      Multiset.card σ.cycleType + Fintype.card (Function.fixedPoints σ) := by
  rw [cycleQuotientCount, Nat.card_congr (cycleQuotientEquiv σ), Nat.card_sum,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simp only [Equiv.Perm.cycleType_def, Multiset.card_map, Finset.card_def,
    Fintype.card_coe]
  omega

private theorem decomposeFin_sameCycle_succ {n : ℕ} (q : Fin n)
    (e : Equiv.Perm (Fin n)) (x : Fin n) :
    (Equiv.Perm.decomposeFin.symm (q.succ, e)).SameCycle x.succ (e x).succ := by
  by_cases hx : e x = q
  · refine ⟨2, ?_⟩
    simp [pow_two, hx]
  · refine ⟨1, ?_⟩
    simp only [zpow_one, Equiv.Perm.decomposeFin_symm_apply_succ]
    exact Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) ((Fin.succ_injective n).ne hx)

private theorem decomposeFin_sameCycle_lift {n : ℕ} (q : Fin n)
    (e : Equiv.Perm (Fin n)) {x y : Fin n} (hxy : e.SameCycle x y) :
    (Equiv.Perm.decomposeFin.symm (q.succ, e)).SameCycle x.succ y.succ := by
  obtain ⟨m, hm⟩ := hxy.exists_nat_pow_eq
  have hpow (r : ℕ) :
      (Equiv.Perm.decomposeFin.symm (q.succ, e)).SameCycle
        x.succ ((e ^ r) x).succ := by
    induction r with
    | zero => exact Equiv.Perm.SameCycle.rfl
    | succ r ih =>
        exact Equiv.Perm.SameCycle.trans ih (by
          simpa [pow_succ'] using decomposeFin_sameCycle_succ q e ((e ^ r) x))
  simpa [hm] using hpow m

private def dropFin {n : ℕ} (q : Fin n) : Fin (n + 1) → Fin n :=
  Fin.cases q id

private theorem decomposeFin_drop_step {n : ℕ} (q : Fin n)
    (e : Equiv.Perm (Fin n)) (x : Fin (n + 1)) :
    e.SameCycle (dropFin q x)
      (dropFin q (Equiv.Perm.decomposeFin.symm (q.succ, e) x)) := by
  refine Fin.cases ?_ (fun a => ?_) x
  · change e.SameCycle q q
    exact Equiv.Perm.SameCycle.rfl
  · have hstep : e.SameCycle a (e a) := by
      exact Equiv.Perm.sameCycle_apply_right.mpr Equiv.Perm.SameCycle.rfl
    by_cases ha : e a = q
    · simpa [dropFin, ha] using hstep
    · rw [Equiv.Perm.decomposeFin_symm_apply_succ,
        Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) ((Fin.succ_injective n).ne ha)]
      exact hstep

private theorem decomposeFin_sameCycle_drop {n : ℕ} (q : Fin n)
    (e : Equiv.Perm (Fin n)) {x y : Fin (n + 1)}
    (hxy : (Equiv.Perm.decomposeFin.symm (q.succ, e)).SameCycle x y) :
    e.SameCycle (dropFin q x) (dropFin q y) := by
  let g := Equiv.Perm.decomposeFin.symm (q.succ, e)
  change g.SameCycle x y at hxy
  obtain ⟨m, hm⟩ := hxy.exists_nat_pow_eq
  have hpow (r : ℕ) : e.SameCycle (dropFin q x) (dropFin q ((g ^ r) x)) := by
    induction r with
    | zero => exact Equiv.Perm.SameCycle.rfl
    | succ r ih =>
        exact Equiv.Perm.SameCycle.trans ih (by
          simpa [g, pow_succ'] using decomposeFin_drop_step q e ((g ^ r) x))
  simpa [hm] using hpow m

private theorem decomposeFin_sameCycle_drop_succ {n : ℕ} (q : Fin n)
    (e : Equiv.Perm (Fin n)) (x : Fin (n + 1)) :
    (Equiv.Perm.decomposeFin.symm (q.succ, e)).SameCycle x (dropFin q x).succ := by
  refine Fin.cases ?_ (fun a => ?_) x
  · refine ⟨1, ?_⟩
    simp [dropFin]
  · exact Equiv.Perm.SameCycle.rfl

private theorem decomposeFin_sameCycle_iff {n : ℕ} (q : Fin n)
    (e : Equiv.Perm (Fin n)) (x y : Fin (n + 1)) :
    (Equiv.Perm.decomposeFin.symm (q.succ, e)).SameCycle x y ↔
      e.SameCycle (dropFin q x) (dropFin q y) := by
  constructor
  · exact decomposeFin_sameCycle_drop q e
  · intro hxy
    exact Equiv.Perm.SameCycle.trans (decomposeFin_sameCycle_drop_succ q e x)
      (Equiv.Perm.SameCycle.trans (decomposeFin_sameCycle_lift q e hxy)
        (decomposeFin_sameCycle_drop_succ q e y).symm)

private noncomputable def decomposeFinQuotientEquiv {n : ℕ} (q : Fin n)
    (e : Equiv.Perm (Fin n)) :
    Quotient (Equiv.Perm.SameCycle.setoid
      (Equiv.Perm.decomposeFin.symm (q.succ, e))) ≃
      Quotient (Equiv.Perm.SameCycle.setoid e) := by
  let mapCycle :
      Quotient (Equiv.Perm.SameCycle.setoid
        (Equiv.Perm.decomposeFin.symm (q.succ, e))) →
        Quotient (Equiv.Perm.SameCycle.setoid e) :=
    Quotient.map (dropFin q)
    (fun {a b} h => show e.SameCycle (dropFin q a) (dropFin q b) from
      (decomposeFin_sameCycle_iff q e a b).mp h)
  refine Equiv.ofBijective mapCycle ?_
  constructor
  · intro a b hab
    refine Quotient.inductionOn₂ a b ?_ hab
    intro x y hxy
    apply Quotient.sound
    apply (decomposeFin_sameCycle_iff q e x y).mpr
    change (Quotient.mk _ (dropFin q x) :
      Quotient (Equiv.Perm.SameCycle.setoid e)) = Quotient.mk _ (dropFin q y) at hxy
    exact Quotient.exact hxy
  · intro a
    refine Quotient.inductionOn a ?_
    intro x
    exact ⟨Quotient.mk _ x.succ, rfl⟩

private theorem decomposeFin_zero_pow_succ {n m : ℕ} (e : Equiv.Perm (Fin n))
    (x : Fin n) :
    ((Equiv.Perm.decomposeFin.symm (0, e)) ^ m) x.succ = ((e ^ m) x).succ := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ', Equiv.Perm.mul_apply,
        Equiv.Perm.decomposeFin_symm_apply_succ]
      simp

private theorem decomposeFin_zero_sameCycle_succ_iff {n : ℕ}
    (e : Equiv.Perm (Fin n)) (x y : Fin n) :
    (Equiv.Perm.decomposeFin.symm (0, e)).SameCycle x.succ y.succ ↔
      e.SameCycle x y := by
  constructor
  · intro hxy
    obtain ⟨m, hm⟩ := hxy.exists_nat_pow_eq
    refine ⟨(m : ℤ), ?_⟩
    rw [zpow_natCast]
    exact (Fin.succ_injective n) (by simpa [decomposeFin_zero_pow_succ] using hm)
  · intro hxy
    obtain ⟨m, hm⟩ := hxy.exists_nat_pow_eq
    refine ⟨(m : ℤ), ?_⟩
    rw [zpow_natCast, decomposeFin_zero_pow_succ, hm]

private noncomputable def decomposeFinZeroQuotientEquiv {n : ℕ}
    (e : Equiv.Perm (Fin n)) :
    Quotient (Equiv.Perm.SameCycle.setoid
      (Equiv.Perm.decomposeFin.symm (0, e))) ≃
      Option (Quotient (Equiv.Perm.SameCycle.setoid e)) := by
  let toBase : Fin (n + 1) → Option (Quotient (Equiv.Perm.SameCycle.setoid e)) :=
    Fin.cases none (fun x => some (Quotient.mk _ x))
  have toBase_eq (x y : Fin (n + 1))
      (hxy : (Equiv.Perm.decomposeFin.symm (0, e)).SameCycle x y) :
      toBase x = toBase y := by
    cases x using Fin.cases with
    | zero =>
        cases y using Fin.cases with
        | zero => rfl
        | succ b =>
            have hfix : Function.IsFixedPt
                (Equiv.Perm.decomposeFin.symm (0, e)) (0 : Fin (n + 1)) := by
              change Equiv.Perm.decomposeFin.symm (0, e) 0 = 0
              simp
            have h : (0 : Fin (n + 1)) = b.succ := hxy.eq_of_left hfix
            exact (Fin.succ_ne_zero b h.symm).elim
    | succ a =>
        cases y using Fin.cases with
        | zero =>
            have hfix : Function.IsFixedPt
                (Equiv.Perm.decomposeFin.symm (0, e)) (0 : Fin (n + 1)) := by
              change Equiv.Perm.decomposeFin.symm (0, e) 0 = 0
              simp
            have h : a.succ = (0 : Fin (n + 1)) := hxy.eq_of_right hfix
            exact (Fin.succ_ne_zero a h).elim
        | succ b =>
            apply congrArg some
            apply Quotient.sound
            exact (decomposeFin_zero_sameCycle_succ_iff e a b).mp hxy
  refine Equiv.ofBijective (Quotient.lift toBase toBase_eq) ?_
  constructor
  · intro a b hab
    refine Quotient.inductionOn₂ a b ?_ hab
    intro x y hxy
    change toBase x = toBase y at hxy
    apply Quotient.sound
    cases x using Fin.cases with
    | zero =>
        cases y using Fin.cases with
        | zero => exact Equiv.Perm.SameCycle.rfl
        | succ v => simp [toBase] at hxy
    | succ u =>
        cases y using Fin.cases with
        | zero => simp [toBase] at hxy
        | succ v =>
            apply (decomposeFin_zero_sameCycle_succ_iff e u v).mpr
            have hquot : (Quotient.mk _ u : Quotient (Equiv.Perm.SameCycle.setoid e)) =
                Quotient.mk _ v := by simpa [toBase] using hxy
            exact Quotient.exact hquot
  · rintro (_ | a)
    · exact ⟨Quotient.mk _ 0, rfl⟩
    · refine Quotient.inductionOn a ?_
      intro x
      exact ⟨Quotient.mk _ x.succ, rfl⟩

private theorem natCardOption (α : Type*) [Finite α] :
    Nat.card (Option α) = Nat.card α + 1 := by
  let finiteType : Fintype α := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Fintype.card_option, Nat.card_eq_fintype_card]

private theorem cycleQuotientCount_decomposeFin_zero {n : ℕ}
    (e : Equiv.Perm (Fin n)) :
    cycleQuotientCount (Equiv.Perm.decomposeFin.symm (0, e)) =
      cycleQuotientCount e + 1 := by
  rw [cycleQuotientCount, cycleQuotientCount,
    Nat.card_congr (decomposeFinZeroQuotientEquiv e), natCardOption]

private theorem cycleQuotientCount_decomposeFin_succ {n : ℕ} (q : Fin n)
    (e : Equiv.Perm (Fin n)) :
    cycleQuotientCount (Equiv.Perm.decomposeFin.symm (q.succ, e)) =
      cycleQuotientCount e := by
  exact Nat.card_congr (decomposeFinQuotientEquiv q e)

private def subtypeProdEquivSigma {α β : Type*} (p : α × β → Prop) :
    {x : α × β // p x} ≃ Σ a : α, {b : β // p (a, b)} where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨(x.1, x.2.1), x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem card_perm_qcycle_zero (k : ℕ) :
    Fintype.card {σ : Equiv.Perm (Fin 0) // cycleQuotientCount σ = k} =
      Nat.stirlingFirst 0 k := by
  classical
  simp only [cycleQuotientCount_eq]
  have hσ (σ : Equiv.Perm (Fin 0)) : Multiset.card σ.cycleType = 0 := by
    rw [Subsingleton.elim σ 1]
    simp
  simp_rw [hσ]
  cases k <;> simp

private theorem card_perm_qcycle_succ_succ (n k : ℕ) :
    Fintype.card {σ : Equiv.Perm (Fin (n + 1)) //
        cycleQuotientCount σ = k + 1} =
      n * Fintype.card {σ : Equiv.Perm (Fin n) //
        cycleQuotientCount σ = k + 1} +
      Fintype.card {σ : Equiv.Perm (Fin n) // cycleQuotientCount σ = k} := by
  classical
  let split :
      {σ : Equiv.Perm (Fin (n + 1)) // cycleQuotientCount σ = k + 1} ≃
        {pe : Fin (n + 1) × Equiv.Perm (Fin n) //
          cycleQuotientCount (Equiv.Perm.decomposeFin.symm pe) = k + 1} :=
    Equiv.subtypeEquiv Equiv.Perm.decomposeFin (fun σ => by simp)
  let zeroPart :
      {e : Equiv.Perm (Fin n) //
        cycleQuotientCount (Equiv.Perm.decomposeFin.symm (0, e)) = k + 1} ≃
        {e : Equiv.Perm (Fin n) // cycleQuotientCount e = k} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun e => by
      change cycleQuotientCount (Equiv.Perm.decomposeFin.symm (0, e)) = k + 1 ↔
        cycleQuotientCount e = k
      rw [cycleQuotientCount_decomposeFin_zero]
      omega)
  let succPart (q : Fin n) :
      {e : Equiv.Perm (Fin n) //
        cycleQuotientCount (Equiv.Perm.decomposeFin.symm (q.succ, e)) = k + 1} ≃
        {e : Equiv.Perm (Fin n) // cycleQuotientCount e = k + 1} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun e => by
      change cycleQuotientCount (Equiv.Perm.decomposeFin.symm (q.succ, e)) = k + 1 ↔
        cycleQuotientCount e = k + 1
      rw [cycleQuotientCount_decomposeFin_succ])
  rw [Fintype.card_congr split,
    Fintype.card_congr (subtypeProdEquivSigma fun pe =>
      cycleQuotientCount (Equiv.Perm.decomposeFin.symm pe) = k + 1),
    Fintype.card_sigma, Fin.sum_univ_succ, Fintype.card_congr zeroPart]
  simp_rw [Fintype.card_congr (succPart _)]
  simp [add_comm]

private theorem card_perm_qcycle_eq_stirlingFirst (n k : ℕ) :
    Fintype.card {σ : Equiv.Perm (Fin n) // cycleQuotientCount σ = k} =
      Nat.stirlingFirst n k := by
  induction n generalizing k with
  | zero => exact card_perm_qcycle_zero k
  | succ n ih =>
      cases k with
      | zero =>
          rw [show Nat.stirlingFirst (n + 1) 0 = 0 by simp]
          apply Fintype.card_eq_zero_iff.mpr
          exact ⟨fun σ => by
            have hpos : 0 < cycleQuotientCount σ.1 := by
              rw [cycleQuotientCount]
              let _ : Nonempty (Quotient (Equiv.Perm.SameCycle.setoid σ.1)) :=
                ⟨Quotient.mk _ 0⟩
              exact Nat.card_pos
            exact (Nat.ne_of_gt hpos) σ.2⟩
      | succ k =>
          rw [card_perm_qcycle_succ_succ, ih, ih, Nat.stirlingFirst_succ_succ]

/-- **Stirling numbers of the first kind count permutations by cycles.** For all natural
numbers $n$ and $k$, the number of permutations $\sigma$ of $\{0, \dots, n-1\}$ such that the
number of cycles of $\sigma$ of length at least $2$ plus the number of fixed points of $\sigma$
equals $k$ is the unsigned Stirling number of the first kind $c(n, k)$. In other words,
$c(n, k)$ counts the permutations of an $n$-element set with exactly $k$ cycles, each fixed
point counted as a cycle of length one. -/
public theorem card_perm_cycleCount_eq_stirlingFirst (n k : ℕ) :
    Fintype.card {σ : Equiv.Perm (Fin n) //
      Multiset.card σ.cycleType + Fintype.card (Function.fixedPoints σ) = k} =
      Nat.stirlingFirst n k := by
  simpa only [cycleQuotientCount_eq] using card_perm_qcycle_eq_stirlingFirst n k

end MetaMathlibExt
