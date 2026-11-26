/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.DifferentialFormProjection

/-!
# Surjectivity onto coefficient differential forms

Let k be a commutative ring, A a commutative unital k-algebra, and
M a compatible A-module. In every degree n, the k-linear projection
φ_n : M ⊗[k] A^{⊗n} → M ⊗_A ∧_A^n Ω_{A/k},
m ⊗ a_1 ⊗ ⋯ ⊗ a_n ↦ m ⊗ (da_1 ∧ ⋯ ∧ da_n),
is surjective.

The elements da generate Ω_{A/k} as an A-module, and their exterior
words generate its exterior powers. In a coefficient tensor, the
A-scalar coefficients move to M, giving a preimage for every form.
The whole-form lift used in the chain complex preserves this
degreewise surjectivity.

Reference: J.-L. Loday, Cyclic Homology, §3.2.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

local notation "Ω" => KaehlerDifferential k A

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write Ω = Ω_{A/k}, Ω^n = ∧_A^n Ω, and d : A → Ω for the
universal k-derivation.
Let M be an A-module with a compatible k-module action, viewed as
a symmetric bimodule, and set F_n = M ⊗_A Ω^n.
The projection φ_n : M ⊗[k] A^{⊗n} → F_n is surjective
for every n ≥ 0. Equivalently, every coefficient differential form
has a preimage under m ⊗ tprod(a) ↦ m ⊗_A D_n(a), extended
k-linearly to sums. -/
theorem coefficientFormProjection_surjective (n : ℕ) :
    Function.Surjective (coefficientFormProjection k A M n) := by
  classical
  let R := LinearMap.range (coefficientFormProjection k A M n)
  let S : Set (Fin n → Ω) := {a | Set.range a ⊆ Set.range (KaehlerDifferential.D k A)}
  have hspan : Submodule.span A (exteriorPower.ιMulti A n '' S) = ⊤ :=
    exteriorPower.ιMulti_span_of_span A n Ω
      (KaehlerDifferential.span_range_derivation k A)
  let W : Submodule A (⋀[A]^n Ω) :=
    { carrier := {ω | ∀ m : M, m ⊗ₜ[A] ω ∈ R}
      zero_mem' := by intro m; rw [TensorProduct.tmul_zero]; exact R.zero_mem
      add_mem' := by
        intro y z hy hz m
        rw [TensorProduct.tmul_add]
        exact R.add_mem (hy m) (hz m)
      smul_mem' := by
        intro a y hy m
        rw [TensorProduct.tmul_smul]
        exact hy (a • m) }
  have hW : exteriorPower.ιMulti A n '' S ⊆ W := by
    rintro _ ⟨a, ha, rfl⟩
    have hpre : ∀ j : Fin n, ∃ p : A, KaehlerDifferential.D k A p = a j :=
      fun j => ha ⟨j, rfl⟩
    choose p hp using hpre
    intro m
    refine ⟨m ⊗ₜ[k] PiTensorProduct.tprod k p, ?_⟩
    rw [coefficientFormProjection_tprod]
    apply congrArg (fun x => m ⊗ₜ[A] x)
    apply congrArg (exteriorPower.ιMulti A n)
    funext j
    exact hp j
  have htop : W = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact Submodule.span_le.mpr hW
  have hword (ω : ⋀[A]^n Ω) : ∀ m : M, m ⊗ₜ[A] ω ∈ R := by
    have hω : ω ∈ W := by rw [htop]; trivial
    exact hω
  intro x
  change x ∈ R
  induction x using TensorProduct.inductionOn with
  | tmul m ω => exact hword ω m
  | add x y hx hy => exact R.add_mem hx hy

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write Ω = Ω_{A/k}, Ω^n = ∧_A^n Ω, and d : A → Ω for the
universal k-derivation.
Let M be an A-module with a compatible k-module action, viewed as
a symmetric bimodule, and set F_n = M ⊗_A Ω^n.
In each chain degree n, the lifted projection
C_n(A,M) → ULift.{u} F_n is surjective. Thus every element of the
coefficient form complex has a degree-n Hochschild-chain preimage. -/
theorem coefficientDifferentialFormChainMap_surjective (n : ℕ) :
    Function.Surjective ((coefficientDifferentialFormChainMap k A M).f n).hom := by
  intro x
  obtain ⟨z, hz⟩ := coefficientFormProjection_surjective k A M n x.down
  refine ⟨z, ?_⟩
  change ULift.up (coefficientFormProjection k A M n z) = x
  rw [hz]
  rfl

end ModuleCat.Algebra.Hochschild.Symmetric
