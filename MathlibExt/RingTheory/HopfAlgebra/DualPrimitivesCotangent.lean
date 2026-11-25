/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_HopfAlgebra_finrank_primitives_cartierDual_eq_finrank_cotangentSpace.lean`
and
`P2M/Sol/S_HopfAlgebra_finrank_primitives_cartierDual_eq_finrank_cotangentSpace.lean`
and
`Definitions/Def_HopfAlgebra_CartierDual.lean`
and
`Definitions/Def_Dieudonne_ModpRealization.lean`
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

public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Cotangent

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section

open scoped TensorProduct

universe u v

/-- The cotangent space of a bialgebra `A` at its counit: the cotangent
space of the kernel of the counit. -/
abbrev cotangentSpaceAtCounit (k : Type u) (A : Type v) [CommRing k] [CommRing A]
    [Bialgebra k A] : Type v :=
  (RingHom.ker (Bialgebra.counitAlgHom k A)).Cotangent

/-- The primitives of the Cartier dual of a Hopf algebra, stated directly
on the dual module: a linear functional `φ : A →ₗ[k] k` is a dual primitive
if it is a derivation at the counit, that is
`φ (a * b) = φ a * ε b + ε a * φ b` for all `a b`. This is the submodule
that the FLT development obtains as the primitives of its Cartier dual,
whose underlying module is the dual module with the dual coalgebra
structure. -/
def dualPrimitives (k : Type u) (A : Type v) [Field k] [CommRing A] [HopfAlgebra k A] :
    Submodule k (Module.Dual k A) where
  carrier := { φ | ∀ a b : A, φ (a * b)
    = φ a * Coalgebra.counit (R := k) b + Coalgebra.counit (R := k) a * φ b }
  add_mem' := by
    intro φ ψ hφ hψ a b
    simp only [LinearMap.add_apply, hφ a b, hψ a b]
    ring
  zero_mem' := by
    intro a b
    simp
  smul_mem' := by
    intro c φ hφ a b
    simp only [LinearMap.smul_apply, hφ a b, smul_eq_mul]
    ring

theorem mem_dualPrimitives_iff {k : Type u} {A : Type v} [Field k] [CommRing A]
    [HopfAlgebra k A] {φ : Module.Dual k A} :
    φ ∈ dualPrimitives k A ↔ ∀ a b : A, φ (a * b)
      = φ a * Coalgebra.counit (R := k) b + Coalgebra.counit (R := k) a * φ b :=
  Iff.rfl

section Proof

variable (k : Type u) [Field k] (A : Type v) [CommRing A] [HopfAlgebra k A]
  [Coalgebra.IsCocomm k A] [Module.Finite k A]

local notation "ε" => Coalgebra.counit (R := k) (A := A)

private theorem apply_one_eq_zero {φ : Module.Dual k A}
    (hφ : φ ∈ dualPrimitives k A) : φ 1 = 0 := by
  have h := (mem_dualPrimitives_iff).1 hφ 1 1
  rw [mul_one, Bialgebra.counit_one, mul_one, one_mul] at h
  have h2 : φ 1 + φ 1 = φ 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

private theorem apply_mul_of_counit_eq_zero {φ : Module.Dual k A}
    (hφ : φ ∈ dualPrimitives k A) (a x : A) (hx : ε x = 0) :
    φ (a * x) = ε a * φ x := by
  rw [(mem_dualPrimitives_iff).1 hφ, hx, mul_zero, zero_add]

private theorem apply_mul_eq_zero {φ : Module.Dual k A}
    (hφ : φ ∈ dualPrimitives k A) (x y : A) (hx : ε x = 0) (hy : ε y = 0) :
    φ (x * y) = 0 := by
  rw [apply_mul_of_counit_eq_zero k A hφ x y hy, hx, zero_mul]

/-- The kernel of the counit, as an ideal. -/
private abbrev I : Ideal A := RingHom.ker (Bialgebra.counitAlgHom k A)

private theorem mem_I {x : A} : x ∈ I k A ↔ ε x = 0 := RingHom.mem_ker

private theorem sub_algebraMap_counit_mem (a : A) :
    a - algebraMap k A (ε a) ∈ I k A := by
  rw [mem_I, map_sub]
  change ε a - Bialgebra.counitAlgHom k A (algebraMap k A (ε a)) = 0
  rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]

private noncomputable def restrictI (φ : Module.Dual k A) : ↥(I k A) →ₗ[k] k :=
  φ.comp ((I k A).subtype.restrictScalars k)

private theorem restrictI_apply (φ : Module.Dual k A) (x : ↥(I k A)) :
    restrictI k A φ x = φ x :=
  rfl

private theorem restrictI_vanishes {φ : Module.Dual k A}
    (hφ : φ ∈ dualPrimitives k A) :
    ((I k A) • ⊤ : Submodule A ↥(I k A)).restrictScalars k
      ≤ LinearMap.ker (restrictI k A φ) := by
  intro x hx
  rw [Submodule.restrictScalars_mem] at hx
  rw [LinearMap.mem_ker, restrictI_apply]
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y _
    change φ (a • (y : A)) = 0
    rw [smul_eq_mul]
    exact apply_mul_eq_zero k A hφ a y ((mem_I k A).1 ha) ((mem_I k A).1 y.2)
  · intro x y hx hy
    change φ ((x : A) + y) = 0
    rw [map_add]
    change φ x + φ y = 0
    rw [hx, hy, add_zero]

private noncomputable def toCotDual {φ : Module.Dual k A}
    (hφ : φ ∈ dualPrimitives k A) :
    Module.Dual k (cotangentSpaceAtCounit k A) :=
  ((((I k A) • ⊤ : Submodule A ↥(I k A)).restrictScalars k).liftQ
    (restrictI k A φ) (restrictI_vanishes k A hφ)).comp
    (Submodule.Quotient.restrictScalarsEquiv k
      ((I k A) • ⊤ : Submodule A ↥(I k A))).symm.toLinearMap

private theorem toCotDual_toCotangent {φ : Module.Dual k A}
    (hφ : φ ∈ dualPrimitives k A) (x : ↥(I k A)) :
    toCotDual k A hφ ((I k A).toCotangent x) = φ x := by
  change ((((I k A) • ⊤ : Submodule A ↥(I k A)).restrictScalars k).liftQ
    (restrictI k A φ) (restrictI_vanishes k A hφ))
    ((Submodule.Quotient.restrictScalarsEquiv k
      ((I k A) • ⊤ : Submodule A ↥(I k A))).symm (Submodule.Quotient.mk x)) = φ x
  rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.liftQ_apply]
  rfl

private noncomputable def ofCotDualFun
    (ψ : Module.Dual k (cotangentSpaceAtCounit k A)) : A →ₗ[k] k where
  toFun a := ψ ((I k A).toCotangent ⟨a - algebraMap k A (ε a),
    sub_algebraMap_counit_mem k A a⟩)
  map_add' a b := by
    rw [← map_add, ← map_add]
    congr 2
    apply Subtype.ext
    change a + b - algebraMap k A (ε (a + b))
      = (a - algebraMap k A (ε a)) + (b - algebraMap k A (ε b))
    rw [map_add, map_add]; abel
  map_smul' c a := by
    rw [RingHom.id_apply, ← map_smul, ← LinearMap.map_smul_of_tower]
    congr 2
    apply Subtype.ext
    change c • a - algebraMap k A (ε (c • a)) = c • (a - algebraMap k A (ε a))
    rw [map_smul, smul_eq_mul, smul_sub, Algebra.smul_def, Algebra.smul_def, map_mul]

private theorem ofCotDualFun_mem (ψ : Module.Dual k (cotangentSpaceAtCounit k A)) :
    ofCotDualFun k A ψ ∈ dualPrimitives k A := by
  rw [mem_dualPrimitives_iff]
  intro a b
  change ofCotDualFun k A ψ (a * b)
    = ofCotDualFun k A ψ a * ε b + ε a * ofCotDualFun k A ψ b
  change ψ ((I k A).toCotangent ⟨a * b - algebraMap k A (ε (a * b)), _⟩) =
    ψ ((I k A).toCotangent ⟨a - algebraMap k A (ε a), _⟩) * ε b
      + ε a * ψ ((I k A).toCotangent ⟨b - algebraMap k A (ε b), _⟩)
  have hlin : ∀ (c : k) (y : ↥(I k A)),
      c • (I k A).toCotangent y = (I k A).toCotangent (c • y) := fun c y =>
    (((I k A).toCotangent.restrictScalars k).map_smul c y).symm
  rw [mul_comm (ψ _) (ε b)]
  change _ = ε b • ψ ((I k A).toCotangent
      ⟨a - algebraMap k A (ε a), sub_algebraMap_counit_mem k A a⟩) +
    ε a • ψ ((I k A).toCotangent
      ⟨b - algebraMap k A (ε b), sub_algebraMap_counit_mem k A b⟩)
  rw [← LinearMap.map_smul, ← LinearMap.map_smul, ← LinearMap.map_add ψ, hlin, hlin,
    ← LinearMap.map_add]
  congr 1
  rw [Ideal.toCotangent_eq]
  have key : (a * b - algebraMap k A (ε (a * b)))
      - (ε b • (a - algebraMap k A (ε a)) + ε a • (b - algebraMap k A (ε b)))
      = (a - algebraMap k A (ε a)) * (b - algebraMap k A (ε b)) := by
    rw [Bialgebra.counit_mul, map_mul, Algebra.smul_def, Algebra.smul_def]
    ring
  change ((a * b - algebraMap k A (ε (a * b)))
    - (ε b • (a - algebraMap k A (ε a)) + ε a • (b - algebraMap k A (ε b))) : A)
    ∈ (I k A) ^ 2
  rw [key, pow_two]
  exact Ideal.mul_mem_mul (sub_algebraMap_counit_mem k A a)
    (sub_algebraMap_counit_mem k A b)

private instance finite_cotangent : Module.Finite k (cotangentSpaceAtCounit k A) := by
  haveI : Module.Finite k ↥(I k A) :=
    Module.IsNoetherian.finite k _
  exact Module.Finite.of_surjective (((I k A).toCotangent).restrictScalars k)
    (I k A).toCotangent_surjective

/-- The primitives of the dual are linearly equivalent to the dual of the
cotangent space at the counit. -/
private noncomputable def dualPrimitivesEquivDualCotangent :
    ↥(dualPrimitives k A) ≃ₗ[k] Module.Dual k (cotangentSpaceAtCounit k A) where
  toFun φ := toCotDual k A φ.2
  map_add' φ ψ := by
    apply LinearMap.ext; intro c
    obtain ⟨x, rfl⟩ := (I k A).toCotangent_surjective c
    rw [LinearMap.add_apply, toCotDual_toCotangent, toCotDual_toCotangent,
      toCotDual_toCotangent]
    rfl
  map_smul' c φ := by
    apply LinearMap.ext; intro d
    obtain ⟨x, rfl⟩ := (I k A).toCotangent_surjective d
    rw [RingHom.id_apply, LinearMap.smul_apply, toCotDual_toCotangent,
      toCotDual_toCotangent]
    rfl
  invFun ψ := ⟨ofCotDualFun k A ψ, ofCotDualFun_mem k A ψ⟩
  left_inv φ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    change ofCotDualFun k A (toCotDual k A φ.2) a = φ.1 a
    change toCotDual k A φ.2 ((I k A).toCotangent
      ⟨a - algebraMap k A (ε a), _⟩) = φ.1 a
    rw [toCotDual_toCotangent]
    change φ.1 (a - algebraMap k A (ε a)) = φ.1 a
    rw [map_sub, Algebra.algebraMap_eq_smul_one, map_smul,
      apply_one_eq_zero k A φ.2, smul_zero, sub_zero]
  right_inv ψ := by
    apply LinearMap.ext; intro c
    obtain ⟨x, rfl⟩ := (I k A).toCotangent_surjective c
    rw [toCotDual_toCotangent]
    change ofCotDualFun k A ψ x = ψ ((I k A).toCotangent x)
    change ψ ((I k A).toCotangent ⟨(x : A) - algebraMap k A (ε x), _⟩)
      = ψ ((I k A).toCotangent x)
    congr 2
    apply Subtype.ext
    change (x : A) - algebraMap k A (ε x) = x
    rw [(mem_I k A).1 x.2, map_zero, sub_zero]

end Proof

/-- The dimension of the primitives of the Cartier dual of a finite Hopf
algebra over a field equals the dimension of its cotangent space at the
counit. -/
theorem finrank_dualPrimitives_eq_finrank_cotangentSpaceAtCounit
    (k : Type u) [Field k] (A : Type v) [CommRing A] [HopfAlgebra k A]
    [Coalgebra.IsCocomm k A] [Module.Finite k A] :
    Module.finrank k ↥(dualPrimitives k A)
      = Module.finrank k (cotangentSpaceAtCounit k A) := by
  rw [LinearEquiv.finrank_eq (dualPrimitivesEquivDualCotangent k A)]
  exact Subspace.dual_finrank_eq
