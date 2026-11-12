/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.PermCycleQuotientCount

open Equiv

namespace StatMech.FrontierA

variable {D : Type*} [Fintype D] [DecidableEq D]



theorem sameCycle_mono_of_step (sigma tau : Perm D)
    (hstep : forall x, sigma.SameCycle x (tau x)) {x y : D}
    (hxy : tau.SameCycle x y) : sigma.SameCycle x y := by
  obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
  have hpow : forall n : Nat, sigma.SameCycle x ((tau ^ n) x) := by
    intro n
    induction n with
    | zero => exact Equiv.Perm.SameCycle.rfl
    | succ n ih =>
        rw [pow_succ']
        exact ih.trans (hstep ((tau ^ n) x))
  simpa only [hn] using hpow n



theorem permCycleCount_eq_of_sameCycle_iff (sigma tau : Perm D)
    (h : forall x y, sigma.SameCycle x y <-> tau.SameCycle x y) :
    permCycleCount sigma = permCycleCount tau := by
  classical
  let f : PermCycleClass sigma -> PermCycleClass tau :=
    Quot.map id (fun x y hxy => (h x y).1 hxy)
  have hf : Function.Bijective f := by
    constructor
    · intro A B hAB
      induction A using Quot.ind with
      | _ x =>
        induction B using Quot.ind with
        | _ y =>
          apply Quot.sound
          exact (h x y).2 (Quotient.exact hAB)
    · intro B
      induction B using Quot.ind with
      | _ y => exact ⟨Quot.mk _ y, rfl⟩
  rw [<- natCard_permCycleClass, <- natCard_permCycleClass]
  exact Nat.card_congr (Equiv.ofBijective f hf)

private theorem sameCycle_swap_step (sigma : Perm D) {a b : D}
    (hab : sigma.SameCycle a b) (x : D) :
    sigma.SameCycle x ((sigma * Equiv.swap a b) x) := by
  have hswap : sigma.SameCycle x (Equiv.swap a b x) := by
    by_cases hxa : x = a
    · subst x
      simpa using hab
    · by_cases hxb : x = b
      · subst x
        simpa [Equiv.swap_apply_right] using hab.symm
      · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
  rw [Equiv.Perm.mul_apply]
  exact hswap.apply_right



theorem not_sameCycle_mul_swap_of_sameCycle (sigma : Perm D) {a b : D}
    (hne : a ≠ b) (hab : sigma.SameCycle a b) :
    ¬((sigma * Equiv.swap a b).SameCycle a b) := by
  intro hnew
  let tau := sigma * Equiv.swap a b
  have hforward : forall x y,
      tau.SameCycle x y -> sigma.SameCycle x y := by
    intro x y hxy
    exact sameCycle_mono_of_step sigma tau
      (sameCycle_swap_step sigma hab) hxy
  have htau_swap : tau * Equiv.swap a b = sigma := by
    unfold tau
    rw [mul_assoc]
    have hs : (Equiv.swap a b : Perm D) * Equiv.swap a b = 1 := by
      apply Equiv.ext
      intro x
      exact Equiv.swap_apply_self a b x
    rw [hs, mul_one]
  have hbackward : forall x y,
      sigma.SameCycle x y -> tau.SameCycle x y := by
    intro x y hxy
    rw [<- htau_swap] at hxy
    exact sameCycle_mono_of_step tau (tau * Equiv.swap a b)
      (sameCycle_swap_step tau hnew) hxy
  have hcount : permCycleCount sigma = permCycleCount tau :=
    permCycleCount_eq_of_sameCycle_iff sigma tau fun x y =>
      ⟨hbackward x y, hforward x y⟩
  have hsign : ((Equiv.Perm.sign tau : Units Int) : Int) =
      -((Equiv.Perm.sign sigma : Units Int) : Int) := by
    unfold tau
    rw [map_mul, Equiv.Perm.sign_swap hne]
    norm_num
  have hparity := permCycleCount_mod_two_toggle_of_sign_neg sigma tau hsign
  rw [<- hcount] at hparity
  omega

end StatMech.FrontierA
