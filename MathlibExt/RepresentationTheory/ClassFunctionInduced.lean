/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from:

`Definitions/Def_ClassFunction_Induced.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source file at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Group

/-!
# Induced class functions

For a subgroup `H` of a finite group `G` and a function `φ : G → K` into a field in which the
order of `H` is invertible (`NeZero (Nat.card H : K)`, as in Mathlib's Maschke theorem), the
induced function is given by the Frobenius formula
`induced H φ g = |H|⁻¹ * ∑ x : G, [x⁻¹ * g * x ∈ H] * φ (x⁻¹ * g * x)`.
Only the values of `φ` on `H` matter (`ClassFunction.induced_congr`).

The hypothesis cannot be dropped: when the characteristic of `K` divides `|H|` the normalized
sum is not induction. For `H = ⊤` in a group of prime order `p` and `K = ZMod p`, it sends the
constant function `1` to `0`.

This file proves the basic algebra of the construction: it is a class function
(`ClassFunction.induced_conj`), it is additive and `K`-linear, inducing from `⊤`
fixes class functions when `|G|` is invertible in `K`, the projection formula
(`ClassFunction.induced_mul_of_conj_invariant`), and transitivity of induction in
characteristic zero (`ClassFunction.induced_induced`).
-/

@[expose] public section

noncomputable section

namespace ClassFunction

variable {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K]

open scoped Classical in
/-- **Induced class function.** For a subgroup `H` of a finite group `G`, a field `K` in which
the order of `H` is invertible (the instance argument `[NeZero (Nat.card H : K)]`) and
`φ : G → K`, the normalized Frobenius sum
`induced H φ g = |H|⁻¹ * ∑ x : G, [x⁻¹ * g * x ∈ H] * φ (x⁻¹ * g * x)`. It uses only the
values of `φ` on `H`. For `K = ℂ` and `φ` restricting on `H` to the character of a complex
representation of `H`, it is the character of the induced representation of `G`. -/
def induced (H : Subgroup G) [NeZero (Nat.card H : K)] (φ : G → K) : G → K :=
  fun g => (Nat.card H : K)⁻¹ * ∑ x : G, if x⁻¹ * g * x ∈ H then φ (x⁻¹ * g * x) else 0

/-- **Frobenius formula for induced class functions.** For a field `K` in which the order of
`H` is invertible (the instance argument `[NeZero (Nat.card H : K)]`) and every decidability
instance for membership in `H`,
`induced H φ g = |H|⁻¹ * ∑ x : G, [x⁻¹ * g * x ∈ H] * φ (x⁻¹ * g * x)`. -/
theorem induced_apply (H : Subgroup G) [DecidablePred (· ∈ H)] [NeZero (Nat.card H : K)]
    (φ : G → K) (g : G) :
    induced H φ g =
      (Nat.card H : K)⁻¹ * ∑ x : G, if x⁻¹ * g * x ∈ H then φ (x⁻¹ * g * x) else 0 := by
  unfold induced
  congr 1
  exact Finset.sum_congr rfl fun x _ => by congr

/-- **Induction depends only on the values on the subgroup.** For a field `K` in which the
order of `H` is invertible (the instance argument `[NeZero (Nat.card H : K)]`), if
`φ ψ : G → K` agree on `H`, then `induced H φ = induced H ψ`. -/
theorem induced_congr (H : Subgroup G) [NeZero (Nat.card H : K)] {φ ψ : G → K}
    (h : ∀ x ∈ H, φ x = ψ x) :
    induced H φ = induced H ψ := by
  classical
  funext g
  rw [induced_apply, induced_apply]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with hx
  · exact h _ hx
  · rfl

/-- **Induced functions are class functions.** For a field `K` in which the order of `H` is
invertible (the instance argument `[NeZero (Nat.card H : K)]`),
`induced H φ (y⁻¹ * g * y) = induced H φ g` for all `y g : G`. -/
theorem induced_conj (H : Subgroup G) [NeZero (Nat.card H : K)] (φ : G → K) (y g : G) :
    induced H φ (y⁻¹ * g * y) = induced H φ g := by
  classical
  rw [induced_apply, induced_apply]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft y) _ _ fun x => ?_
  have : x⁻¹ * (y⁻¹ * g * y) * x = (y * x)⁻¹ * g * (y * x) := by group
  simp only [Equiv.coe_mulLeft, this]
  congr

theorem induced_add (H : Subgroup G) [NeZero (Nat.card H : K)] (φ ψ : G → K) :
    induced H (φ + ψ) = induced H φ + induced H ψ := by
  classical
  funext g
  simp only [Pi.add_apply, induced_apply]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

@[simp]
theorem induced_zero (H : Subgroup G) [NeZero (Nat.card H : K)] :
    induced H (0 : G → K) = 0 := by
  classical
  funext g
  rw [induced_apply, Pi.zero_apply]
  simp only [Pi.zero_apply, ite_self, Finset.sum_const_zero, mul_zero]

theorem induced_const_mul (H : Subgroup G) [NeZero (Nat.card H : K)] (c : K) (φ : G → K) :
    induced H (fun x => c * φ x) = fun g => c * induced H φ g := by
  classical
  funext g
  simp only [induced_apply]
  rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

theorem induced_sum {ι : Type*} (H : Subgroup G) [NeZero (Nat.card H : K)] (s : Finset ι)
    (φ : ι → G → K) :
    induced H (fun x => ∑ i ∈ s, φ i x) = fun g => ∑ i ∈ s, induced H (φ i) g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact induced_zero H
  | insert i s hi ih =>
    funext g
    simp only [Finset.sum_insert hi]
    have : (fun x => φ i x + ∑ j ∈ s, φ j x) = φ i + fun x => ∑ j ∈ s, φ j x := by
      funext x; simp
    rw [this, induced_add, Pi.add_apply, ih]

/-- **Projection formula for induction.** For a field `K` in which the order of `H` is
invertible (the instance argument `[NeZero (Nat.card H : K)]`), if `f : G → K` is a class
function, that is, `f (x⁻¹ * g * x) = f g` for all `x g : G`, then
`induced H φ g * f g = induced H (fun y => φ y * f y) g` for every `g : G`. -/
theorem induced_mul_of_conj_invariant (H : Subgroup G) [NeZero (Nat.card H : K)] (φ f : G → K)
    (hf : ∀ x g : G, f (x⁻¹ * g * x) = f g) (g : G) :
    induced H φ g * f g = induced H (fun y => φ y * f y) g := by
  classical
  simp only [induced_apply]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs
  · rw [hf]
  · simp

/-- **Induction from the whole group.** If the order of `G` is invertible in `K` (the instance
argument `[NeZero (Nat.card (⊤ : Subgroup G) : K)]`) and `φ : G → K` is a class function, then
`induced ⊤ φ = φ`. -/
theorem induced_top_of_conj_invariant [NeZero (Nat.card (⊤ : Subgroup G) : K)] (φ : G → K)
    (hφ : ∀ x g : G, φ (x⁻¹ * g * x) = φ g) : induced (⊤ : Subgroup G) φ = φ := by
  classical
  funext g
  rw [induced_apply, Subgroup.card_top, Nat.card_eq_fintype_card]
  simp only [Subgroup.mem_top, ite_true, hφ, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [← mul_assoc]
  have hG : (Fintype.card G : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.card_top]
    exact NeZero.ne _
  rw [inv_mul_cancel₀ hG, one_mul]

/-- **Transitivity of induction.** Over a field `K` of characteristic zero, let `H` be a
subgroup of `G`, `L` a subgroup of `H` and `ψ : H → K`. Inducing `ψ` from `L` to `H`, extending
the result by zero to `G` and inducing it from `H` to `G` gives the same function as extending
`ψ` by zero to `G` and inducing it from the image of `L` in `G`. -/
theorem induced_induced [CharZero K] (H : Subgroup G) [Fintype H] [DecidablePred (· ∈ H)]
    (L : Subgroup H) (ψ : H → K) :
    induced H (fun g => if hg : g ∈ H then induced L ψ ⟨g, hg⟩ else 0) =
      induced (L.map H.subtype) (fun g => if hg : g ∈ H then ψ ⟨g, hg⟩ else 0) := by
  classical
  funext g
  rw [induced_apply, induced_apply]
  set ψ' : G → K := fun g => if hg : g ∈ H then ψ ⟨g, hg⟩ else 0 with hψ'
  set L' : Subgroup G := L.map H.subtype with hL'
  have hLcard : (Nat.card L' : K) = Nat.card L := by
    congr 1
    exact Nat.card_congr (L.equivMapOfInjective H.subtype H.subtype_injective).toEquiv.symm
  have hmemL : ∀ y : G, y ∈ L' ↔ ∃ hy : y ∈ H, (⟨y, hy⟩ : H) ∈ L := by
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, by simpa using hz⟩
    · rintro ⟨hy, hL⟩
      exact ⟨⟨y, hy⟩, hL, rfl⟩
  have hL'H : L' ≤ H := by
    intro y hy
    rw [hmemL] at hy
    exact hy.1
  set F : G → K := fun z => if z⁻¹ * g * z ∈ L' then ψ' (z⁻¹ * g * z) else 0 with hF
  have hH0 : (Nat.card H : K) ≠ 0 := by
    have : 0 < Nat.card H := Nat.card_pos
    exact_mod_cast this.ne'
  have hinner : ∀ x : G,
      (if x⁻¹ * g * x ∈ H then
        (if hx : x⁻¹ * g * x ∈ H then induced L ψ ⟨x⁻¹ * g * x, hx⟩ else 0) else 0) =
      (Nat.card L : K)⁻¹ * ∑ y : G, if y ∈ H then F (x * y) else 0 := by
    intro x
    by_cases hx : x⁻¹ * g * x ∈ H
    · rw [ite_eq_left hx, dite_eq_left hx, induced_apply]
      congr 1
      have key : ∀ y : H, (if y⁻¹ * ⟨x⁻¹ * g * x, hx⟩ * y ∈ L then
          ψ (y⁻¹ * ⟨x⁻¹ * g * x, hx⟩ * y) else 0) = F (x * y) := by
        intro y
        have hcoe : (x * y)⁻¹ * g * (x * y) = ((y⁻¹ * ⟨x⁻¹ * g * x, hx⟩ * y : H) : G) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        have hmemL' : ∀ w : H, (w : G) ∈ L' ↔ w ∈ L := by
          intro w
          rw [hmemL]
          exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨w.2, h⟩⟩
        rw [hF]
        dsimp only
        rw [hcoe, hmemL']
        split_ifs with hw
        · rw [hψ']
          beta_reduce
          split_ifs with h'
          · rfl
          · exact absurd (Subtype.coe_prop _) h'
        · rfl
      rw [Finset.sum_congr rfl (fun y _ => key y)]
      rw [← Finset.sum_subtype (Finset.univ.filter (· ∈ H)) (by simp) (fun y => F (x * y)),
        Finset.sum_filter]
    · rw [ite_eq_right hx]
      symm
      rw [mul_eq_zero]
      right
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [ite_eq_right_iff]
      intro hy
      rw [hF]
      dsimp only
      rw [ite_eq_right]
      intro hyL
      apply hx
      have hmem : (x * y)⁻¹ * g * (x * y) ∈ H := hL'H hyL
      have : x⁻¹ * g * x = y * ((x * y)⁻¹ * g * (x * y)) * y⁻¹ := by group
      rw [this]
      exact H.mul_mem (H.mul_mem hy hmem) (H.inv_mem hy)
  have hswap : ∑ x : G, (Nat.card L : K)⁻¹ * ∑ y : G, (if y ∈ H then F (x * y) else 0) =
      (Nat.card L : K)⁻¹ * ((Nat.card H : K) * ∑ z : G, F z) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    have : ∀ y : G, ∑ x : G, (if y ∈ H then F (x * y) else 0) =
        if y ∈ H then ∑ z : G, F z else 0 := by
      intro y
      split_ifs with hy
      · exact Fintype.sum_equiv (Equiv.mulRight y) _ _ fun x => rfl
      · simp
    simp_rw [this]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have : (Finset.univ.filter (· ∈ H)).card = Nat.card H := by
      rw [← Fintype.card_subtype]
      convert (Nat.card_eq_fintype_card (α := H)).symm
    exact_mod_cast this
  have hL0 : (Nat.card L : K) ≠ 0 := by
    have : 0 < Nat.card L := Nat.card_pos
    exact_mod_cast this.ne'
  simp_rw [hinner]
  rw [hswap, hLcard]
  field_simp

end ClassFunction

end
