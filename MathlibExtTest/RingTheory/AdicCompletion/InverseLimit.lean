/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.AdicCompletion.InverseLimit

@[expose] public section

universe u v

/-- Consumer with the original binders. -/
example {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (t : ∀ n : ℕ, M (n + 1) →ₗ[R] M n)
    (hI : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (M n)) = ⊥)
    (ht : ∀ n : ℕ, Function.Surjective (t n))
    (hker : ∀ n : ℕ, LinearMap.ker (t n) ≤ I ^ (n + 1) • ⊤)
    [Module.Finite R (M 0)]
    (L : Submodule R (∀ n, M n)) (hL : ∀ x, x ∈ L ↔ ∀ n, t n (x (n + 1)) = x n) :
    Module.Finite R L ∧
      (∀ (n : ℕ) (y : M n), ∃ x ∈ L, x n = y) ∧
      (∀ (n : ℕ) (x : ∀ n, M n), x ∈ L → (x n = 0 ↔ x ∈ I ^ (n + 1) • L)) :=
  IsAdicComplete.finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top
    I M t hI ht hker L hL

/-- Compatible families in the constant inverse system. -/
private def constantCompatible (R : Type u) [CommRing R] : Submodule R (∀ _ : ℕ, R) where
  carrier := {x | ∀ n, x (n + 1) = x n}
  zero_mem' := fun _ => rfl
  add_mem' := fun hx hy n => by rw [Pi.add_apply, Pi.add_apply, hx n, hy n]
  smul_mem' := fun c _ hx n => by rw [Pi.smul_apply, Pi.smul_apply, hx n]

/-- The constant inverse system with identity transitions has surjective
projections from its compatible submodule. -/
example {R : Type u} [CommRing R] :
    ∀ (n : ℕ) (y : R), ∃ x ∈ constantCompatible R, x n = y := by
  intro n y
  obtain ⟨_, hproj, _⟩ :=
    IsAdicComplete.finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top
      (⊥ : Ideal R) (fun _ => R) (fun _ => LinearMap.id) (fun n => by
        simp [pow_succ]) (fun _ => Function.surjective_id)
      (fun _ => by simp) (constantCompatible R)
        (fun x => ⟨fun hx n => hx n, fun hx n => hx n⟩)
  exact hproj n y
