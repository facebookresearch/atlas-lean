/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Lie.UniversalEnveloping

/-!
# Induction on the native universal enveloping algebra

The original quotient map is surjective. Native tensor-algebra induction
therefore supplies scalar, Lie-generator, product and sum induction on the
original UEA. This owner is independent of PBW, filtrations and CE chains.
-/

@[expose] public section

universe u v

namespace UniversalEnvelopingAlgebra

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

/-- Induction on the actual quotient algebra, using its scalar and Lie
generators. No injectivity, basis or PBW input is needed. -/
@[elab_as_elim]
theorem induction {C : UniversalEnvelopingAlgebra R L → Prop}
    (algebraMap : ∀ r : R, C (algebraMap R (UniversalEnvelopingAlgebra R L) r))
    (ι : ∀ x : L, C (UniversalEnvelopingAlgebra.ι R x))
    (mul : ∀ a b, C a → C b → C (a * b))
    (add : ∀ a b, C a → C b → C (a + b))
    (a : UniversalEnvelopingAlgebra R L) : C a := by
  have hsurj : Function.Surjective (mkAlgHom R L) :=
    fun a => Quotient.exists_rep a
  obtain ⟨t, rfl⟩ := hsurj a
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
      rw [(mkAlgHom R L).commutes]
      exact algebraMap r
  | ι x => exact ι x
  | mul t s ht hs =>
      rw [map_mul]
      exact mul _ _ ht hs
  | add t s ht hs =>
      rw [map_add]
      exact add _ _ ht hs

end UniversalEnvelopingAlgebra
