/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.MazurAdmissible

@[expose] public section

open MazurAdmissible

/-- Consumer with the original binders: an admissible chain for a prime
`q` in a finite additive commutative group has ambient cardinality
`q ^ filtLength`. -/
example {M : Type*} [AddCommGroup M] {q : ℕ} (hq : q.Prime) {Φ : OpenAction M}
    (c : AdmissibleChain q Φ) : Nat.card M = q ^ filtLength c :=
  c.natCard_eq_pow_filtLength hq

/-- Higher-universe consumer: the same statement in `Type 1`. -/
example {M : Type 1} [AddCommGroup M] {q : ℕ} (hq : q.Prime)
    {Φ : OpenAction M} (c : AdmissibleChain q Φ) :
    Nat.card M = q ^ filtLength c :=
  c.natCard_eq_pow_filtLength hq

/-- `filtLength` is the indexed length `n` of the chain. -/
example {M : Type*} [AddCommGroup M] {q : ℕ} {Φ : OpenAction M}
    (c : AdmissibleChain q Φ) : filtLength c = c.n :=
  rfl

/-- The bundled action has Mathlib's `MonoidHom` API: by `map_inv`, `σ⁻¹`
undoes `σ`. -/
example {M : Type*} [AddCommGroup M] (Φ : OpenAction M)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : M) :
    (Φ.φ σ⁻¹).toAdd ((Φ.φ σ).toAdd x) = x := by
  rw [map_inv, toAdd_inv, AddAut.neg_apply_self]

/-- The unbundled laws are corollaries: the action is compatible with
composition, and the identity acts as the identity. -/
example {M : Type*} [AddCommGroup M] (Φ : OpenAction M)
    (σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : M) :
    (Φ.φ (σ * τ)).toAdd x = (Φ.φ σ).toAdd ((Φ.φ τ).toAdd x) ∧
      (Φ.φ 1).toAdd x = x := by
  rw [Φ.map_mul, Φ.map_one, AddAut.add_apply, AddAut.zero_apply]
  exact ⟨rfl, rfl⟩

/-- A Galois element lies in the kernel of the bundled action exactly when it
fixes `M` pointwise. -/
example {M : Type*} [AddCommGroup M] (Φ : OpenAction M)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    σ ∈ Φ.φ.ker ↔ ∀ x, (Φ.φ σ).toAdd x = x := by
  rw [MonoidHom.mem_ker, ← toAdd_eq_zero, AddEquiv.ext_iff]
  simp only [AddAut.zero_apply]

/-- The trivial action is an open action: its kernel is the whole group. -/
private noncomputable def trivialAction (M : Type*) [AddCommGroup M] : OpenAction M where
  φ := 1
  hker := by
    rw [MonoidHom.ker_one, Subgroup.coe_top]
    exact isOpen_univ

/-- Every step is trivial for the trivial action. -/
example {M : Type*} [AddCommGroup M] (A B : AddSubgroup M) :
    IsTrivialStep (trivialAction M) A B := by
  intro σ x _
  simp [trivialAction]

/-- Mathlib's `DistribMulAction.toAddAut` has the bundled form, so a
distributive Galois action with open kernel is an open action, acting by
`σ • x`. -/
example {M : Type*} [AddCommGroup M]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (h : IsOpen
      ((DistribMulAction.toAddAut (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M).ker :
        Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : M) :
    ((⟨DistribMulAction.toAddAut _ M, h⟩ : OpenAction M).φ σ).toAdd x = σ • x :=
  rfl
