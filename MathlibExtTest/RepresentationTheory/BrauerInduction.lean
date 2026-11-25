/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter.lean`
and
`Theorems/Thm_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_
hyperelementary.lean`
and
`Theorems/Thm_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_
normal_comm_of_pow_prime_pow_mem.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.RepresentationTheory.BrauerInduction
public import MathlibExt.RepresentationTheory.MonomialCharacter
public import MathlibExt.RepresentationTheory.SolomonInduction
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Defs

@[expose] public section

open scoped MatrixGroups

/-! The source statements, with their original binders (`G : Type`). -/

open scoped Classical in
private theorem exactSource
    {G : Type} [Group G] [Fintype G] {n : ℕ} (ρ : G →* GL (Fin n) ℂ) :
    ∃ (k : ℕ) (H : Fin k → Subgroup G) (ψ : (i : Fin k) → (H i →* ℂˣ)) (a : Fin k → ℤ),
      ∀ g : G, ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
        ∑ i : Fin k, (a i : ℂ) * ((Nat.card (H i) : ℂ)⁻¹ *
          ∑ x : G, if hx : x⁻¹ * g * x ∈ H i then (((ψ i) ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ)
            else 0) :=
  BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter ρ

private theorem exactSource_solomon
    {G : Type} [Group G] [Fintype G] :
    ∃ (k : ℕ) (H : Fin k → Subgroup G) (a : Fin k → ℤ),
      (∀ i, ∃ q : ℕ, q.Prime ∧ ∃ C : Subgroup G, C ≤ H i ∧ IsCyclic C ∧
        (Nat.card C).Coprime q ∧
        (∀ h ∈ H i, ∀ c ∈ C, h * c * h⁻¹ ∈ C) ∧ (∀ h ∈ H i, ∃ n : ℕ, h ^ q ^ n ∈ C)) ∧
      ∀ g : G, (1 : ℚ) = ∑ i, (a i : ℚ) * ClassFunction.induced (H i) (fun _ => (1 : ℚ)) g :=
  ClassFunction.exists_one_eq_sum_zsmul_induced_one_of_hyperelementary

open scoped Classical in
private theorem exactSource_monomial
    {G : Type} [Group G] [Fintype G] {p : ℕ} (hp : p.Prime) (A : Subgroup G) (hA : A.Normal)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hquot : ∀ g : G, ∃ n : ℕ, g ^ p ^ n ∈ A)
    {n : ℕ} (ρ : G →* GL (Fin n) ℂ) :
    ∃ (k : ℕ) (H : Fin k → Subgroup G) (ψ : (i : Fin k) → (H i →* ℂˣ)),
      ∀ g : G, ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
        ∑ i : Fin k, ClassFunction.induced (H i)
          (fun x => if hx : x ∈ H i then (((ψ i) ⟨x, hx⟩ : ℂˣ) : ℂ) else 0) g :=
  ClassFunction.exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem
    hp A hA hcomm hquot ρ

/-! The statements are universe-polymorphic: a group in a higher universe. -/

open scoped Classical in
example {G : Type 1} [Group G] [Fintype G] {n : ℕ} (ρ : G →* GL (Fin n) ℂ) :
    ∃ (k : ℕ) (H : Fin k → Subgroup G) (ψ : (i : Fin k) → (H i →* ℂˣ)) (a : Fin k → ℤ),
      ∀ g : G, ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
        ∑ i : Fin k, (a i : ℂ) * ClassFunction.induced (H i)
          (fun x => if hx : x ∈ H i then (((ψ i) ⟨x, hx⟩ : ℂˣ) : ℂ) else 0) g :=
  BrauerInduction.exists_trace_eq_sum_zsmul_induced ρ

example {G : Type 2} [Group G] [Fintype G] :
    ∃ (k : ℕ) (H : Fin k → Subgroup G) (a : Fin k → ℤ),
      (∀ i, ∃ q : ℕ, q.Prime ∧ ∃ C : Subgroup G, C ≤ H i ∧ IsCyclic C ∧
        (Nat.card C).Coprime q ∧
        (∀ h ∈ H i, ∀ c ∈ C, h * c * h⁻¹ ∈ C) ∧ (∀ h ∈ H i, ∃ n : ℕ, h ^ q ^ n ∈ C)) ∧
      ∀ g : G, (1 : ℚ) = ∑ i, (a i : ℚ) * ClassFunction.induced (H i) (fun _ => (1 : ℚ)) g :=
  ClassFunction.exists_one_eq_sum_zsmul_induced_one_of_hyperelementary

/-! A concrete consumer: the trivial one-dimensional representation of `ℤ/2`. -/

open scoped Classical in
example :
    ∃ (k : ℕ) (H : Fin k → Subgroup (Multiplicative (ZMod 2)))
      (ψ : (i : Fin k) → (H i →* ℂˣ)) (a : Fin k → ℤ),
      ∀ g : Multiplicative (ZMod 2), (1 : ℂ) =
        ∑ i : Fin k, (a i : ℂ) * ClassFunction.induced (H i)
          (fun x => if hx : x ∈ H i then (((ψ i) ⟨x, hx⟩ : ℂˣ) : ℂ) else 0) g := by
  obtain ⟨k, H, ψ, a, h⟩ := BrauerInduction.exists_trace_eq_sum_zsmul_induced
    (1 : Multiplicative (ZMod 2) →* GL (Fin 1) ℂ)
  refine ⟨k, H, ψ, a, fun g => ?_⟩
  rw [← h g]
  simp

/-! Inducing a class function from the whole group returns it. -/

example {G : Type*} [Group G] [Fintype G] :
    ClassFunction.induced (⊤ : Subgroup G) (fun _ => (1 : ℚ)) = fun _ => 1 :=
  ClassFunction.induced_top_of_conj_invariant _ fun _ _ => rfl

/-! The order of the subgroup must be invertible in the field. Over `ZMod 3` the order `2` of
`ℤ/2` is invertible, and inducing the constant function `1` from the whole group returns it. -/

private instance : NeZero ((Nat.card (⊤ : Subgroup (Multiplicative (ZMod 2))) : ℕ) : ZMod 3) :=
  ⟨by rw [Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
      decide⟩

example : ClassFunction.induced (⊤ : Subgroup (Multiplicative (ZMod 2)))
    (fun _ => (1 : ZMod 3)) = fun _ => 1 :=
  ClassFunction.induced_top_of_conj_invariant _ fun _ _ => rfl

/-! Over `ZMod 2` the order `2` vanishes, so `ClassFunction.induced` does not apply: the
normalized Frobenius sum of the constant function `1` over the whole group `ℤ/2` is `0`, not
`1`. -/

example : ¬ NeZero ((Nat.card (⊤ : Subgroup (Multiplicative (ZMod 2))) : ℕ) : ZMod 2) := by
  rw [Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card,
    ZMod.natCast_self]
  exact fun h => h.out rfl

open scoped Classical in
example (g : Multiplicative (ZMod 2)) :
    (Nat.card (⊤ : Subgroup (Multiplicative (ZMod 2))) : ZMod 2)⁻¹ *
      ∑ x : Multiplicative (ZMod 2),
        (if x⁻¹ * g * x ∈ (⊤ : Subgroup (Multiplicative (ZMod 2))) then (1 : ZMod 2) else 0) =
      0 := by
  rw [Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card,
    ZMod.natCast_self, ZMod.inv_zero, zero_mul]
