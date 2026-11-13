/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.PermSameCycleSwap
import Code.FrontierD.FiniteSurjectionOneExcess



open Equiv

namespace StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

variable {D : Type*} [Fintype D] [DecidableEq D]

private theorem sameCycle_mul_swap_contained
    (σ : Perm D) {a b : D} (hab : σ.SameCycle a b)
    {x y : D}
    (hxy : (σ * Equiv.swap a b).SameCycle x y) :
    σ.SameCycle x y := by
  apply sameCycle_mono_of_step σ (σ * Equiv.swap a b) _ hxy
  intro z
  have hswap : σ.SameCycle z (Equiv.swap a b z) := by
    by_cases hza : z = a
    · subst z
      simpa using hab
    · by_cases hzb : z = b
      · subst z
        simpa [Equiv.swap_apply_right] using hab.symm
      · rw [Equiv.swap_apply_of_ne_of_ne hza hzb]
  rw [Equiv.Perm.mul_apply]
  exact hswap.apply_right



theorem sameCycle_mul_swap_partition_of_count
    (σ : Perm D) {a b : D} (habne : a ≠ b)
    (hab : σ.SameCycle a b)
    (hcount : permCycleCount (σ * Equiv.swap a b) =
      permCycleCount σ + 1) (x : D) :
    σ.SameCycle a x ↔
      (σ * Equiv.swap a b).SameCycle a x ∨
        (σ * Equiv.swap a b).SameCycle b x := by
  classical
  let τ := σ * Equiv.swap a b
  let A := PermCycleClass τ
  let B := PermCycleClass σ
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype B := Fintype.ofFinite B
  let f : A → B := Quot.map id (fun u v huv =>
    sameCycle_mul_swap_contained σ hab huv)
  have hf : Function.Surjective f := by
    intro C
    induction C using Quot.ind with
    | _ z => exact ⟨Quot.mk _ z, rfl⟩
  have hcard : Fintype.card A = Fintype.card B + 1 := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      natCard_permCycleClass, natCard_permCycleClass]
    exact hcount
  let ca : A := Quot.mk _ a
  let cb : A := Quot.mk _ b
  have hcab : ca ≠ cb := by
    intro h
    have hnew : τ.SameCycle a b := Quotient.exact h
    exact (not_sameCycle_mul_swap_of_sameCycle σ habne hab) hnew
  have hfc : f ca = f cb := by
    apply Quot.sound
    exact hab
  constructor
  · intro hax
    let cx : A := Quot.mk _ x
    have hfx : f cx = f ca := by
      apply Quot.sound
      exact hax.symm
    rcases finiteSurjection_fiber_eq_pair_of_card_eq_add_one
        f hf hcard hcab hfc cx hfx with hxca | hxcb
    · left
      exact (Quotient.exact hxca).symm
    · right
      exact (Quotient.exact hxcb).symm
  · rintro (hax | hbx)
    · exact sameCycle_mul_swap_contained σ hab hax
    · exact hab.trans (sameCycle_mul_swap_contained σ hab hbx)


theorem sameCycle_mul_swap_iff_of_not_sameCycle
    (σ : Perm D) {a b : D} (habne : a ≠ b)
    (hab : σ.SameCycle a b)
    (hcount : permCycleCount (σ * Equiv.swap a b) =
      permCycleCount σ + 1)
    {x y : D} (hx : ¬ σ.SameCycle a x) :
    (σ * Equiv.swap a b).SameCycle x y ↔ σ.SameCycle x y := by
  classical
  let τ := σ * Equiv.swap a b
  let A := PermCycleClass τ
  let B := PermCycleClass σ
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype B := Fintype.ofFinite B
  let f : A → B := Quot.map id (fun u v huv =>
    sameCycle_mul_swap_contained σ hab huv)
  have hf : Function.Surjective f := by
    intro C
    induction C using Quot.ind with
    | _ z => exact ⟨Quot.mk _ z, rfl⟩
  have hcard : Fintype.card A = Fintype.card B + 1 := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      natCard_permCycleClass, natCard_permCycleClass]
    exact hcount
  let ca : A := Quot.mk _ a
  let cb : A := Quot.mk _ b
  have hcab : ca ≠ cb := by
    intro h
    have hnew : τ.SameCycle a b := Quotient.exact h
    exact (not_sameCycle_mul_swap_of_sameCycle σ habne hab) hnew
  have hfc : f ca = f cb := by
    apply Quot.sound
    exact hab
  constructor
  · exact sameCycle_mul_swap_contained σ hab
  · intro hxy
    let cx : A := Quot.mk _ x
    let cy : A := Quot.mk _ y
    have haway : f cx ≠ f ca := by
      intro h
      apply hx
      exact (Quotient.exact h).symm
    have hfy : f cy = f cx := by
      apply Quot.sound
      exact hxy.symm
    have hyx :=
      finiteSurjection_fiber_eq_singleton_away_of_card_eq_add_one
        f hf hcard hcab hfc haway cy hfy
    exact (Quotient.exact hyx).symm

end

end StatMech.FrontierD
