/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.ConductorIdeal

@[expose] public section

-- Conductor of the top subalgebra.
example : (⊤ : Subalgebra ℤ ℤ).conductorIdeal = ⊤ :=
  Subalgebra.conductorIdeal_top

-- Monogenic specialization recovers Mathlib's element-generated conductor.
example (x : ℤ) :
    (Algebra.adjoin ℤ ({x} : Set ℤ)).conductorIdeal = conductor ℤ x :=
  Subalgebra.adjoin_conductorIdeal x

-- Universal property for an arbitrary ideal.
example (A : Subalgebra ℤ ℤ) (I : Ideal ℤ) (h : (I : Set ℤ) ⊆ (A : Set ℤ)) :
    I ≤ A.conductorIdeal :=
  Subalgebra.le_conductorIdeal_iff.mpr h

/-- The diagonal subalgebra of `ℤ × ℤ`. -/
def diagSubalgebra : Subalgebra ℤ (ℤ × ℤ) where
  carrier := {p | p.1 = p.2}
  mul_mem' ha hb := by
    simp only [Set.mem_ofPred_eq, Prod.fst_mul, Prod.snd_mul] at ha hb ⊢
    rw [ha, hb]
  add_mem' ha hb := by
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add] at ha hb ⊢
    rw [ha, hb]
  algebraMap_mem' r := by
    simp only [Set.mem_ofPred_eq, Prod.algebraMap_apply]

/-- Membership in the diagonal subalgebra. -/
theorem mem_diagSubalgebra {p : ℤ × ℤ} : p ∈ diagSubalgebra ↔ p.1 = p.2 :=
  Iff.rfl

-- The diagonal subalgebra of `ℤ × ℤ` has bottom conductor.
example : diagSubalgebra.conductorIdeal = ⊥ := by
  rw [eq_bot_iff]
  intro p hp
  have hp' : ∀ t : ℤ × ℤ, (p * t).1 = (p * t).2 := fun t =>
    mem_diagSubalgebra.mp (Subalgebra.mem_conductorIdeal.mp hp t)
  have h1 := hp' (1, 0)
  have h2 := hp' (0, 1)
  simp only [Prod.fst_mul, Prod.snd_mul, mul_one, mul_zero] at h1 h2
  exact (Submodule.mem_bot _).mpr (Prod.ext h1 h2.symm)

-- Finiteness characterization for overrings of `ℤ` in `ℚ`.
example (T : Subalgebra ℤ ℚ) :
    (⊥ : Subalgebra ℤ ↥T).conductorIdeal ≠ ⊥ ↔ Module.Finite ℤ ↥T :=
  Subalgebra.bot_conductorIdeal_ne_bot_iff T

-- Nonzero conductor forces finiteness.
example (T : Subalgebra ℤ ℚ)
    (h : (⊥ : Subalgebra ℤ ↥T).conductorIdeal ≠ ⊥) : Module.Finite ℤ ↥T :=
  Subalgebra.finite_of_conductorIdeal_bot_ne_bot T h

-- The characterization for the integral closure of `ℤ` in `ℚ`.
example :
    (⊥ : Subalgebra ℤ ↥(integralClosure ℤ ℚ)).conductorIdeal ≠ ⊥ ↔
      Module.Finite ℤ ↥(integralClosure ℤ ℚ) :=
  Subalgebra.integralClosure_bot_conductorIdeal_ne_bot_iff

#print axioms Subalgebra.bot_conductorIdeal_ne_bot_iff
#print axioms Subalgebra.integralClosure_bot_conductorIdeal_ne_bot_iff
