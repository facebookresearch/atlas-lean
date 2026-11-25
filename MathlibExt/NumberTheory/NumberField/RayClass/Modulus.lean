/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Moduli for ray class groups (N403 foundation)

Multiplication on the infinite part uses union of real-place sets.
This represents truncated exponent addition `min (m v + n v) 1`:
a real place appears in the product iff it appears in either factor.
The ATLAS-extracted `max` formula for this operation was a typo.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace NumberField

abbrev RealPlace (K : Type*) [Field K] [NumberField K] :=
  { v : InfinitePlace K // v.IsReal }

@[ext] structure Modulus (K : Type*) [Field K] [NumberField K] where
  finitePart : (Ideal (𝓞 K))⁰
  infinitePart : Finset (RealPlace K)

namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

@[simp] theorem mk_finitePart (a : (Ideal (𝓞 K))⁰) (b : Finset (RealPlace K)) :
    (⟨a, b⟩ : Modulus K).finitePart = a := rfl

@[simp] theorem mk_infinitePart (a : (Ideal (𝓞 K))⁰) (b : Finset (RealPlace K)) :
    (⟨a, b⟩ : Modulus K).infinitePart = b := rfl

instance : One (Modulus K) := ⟨⟨1, ∅⟩⟩

open Classical in
/-- Multiplication uses union on infinite places: truncated exponent addition
`min (m v + n v) 1` (the ATLAS `max` formula was a typo). -/
instance : Mul (Modulus K) :=
  ⟨fun m n => ⟨m.finitePart * n.finitePart, m.infinitePart ∪ n.infinitePart⟩⟩

@[simp] theorem one_finitePart : (1 : Modulus K).finitePart = 1 := rfl

@[simp] theorem one_infinitePart : (1 : Modulus K).infinitePart = ∅ := rfl

@[simp] theorem mul_finitePart (m n : Modulus K) :
    (m * n).finitePart = m.finitePart * n.finitePart := rfl

open Classical in
@[simp] theorem mul_infinitePart (m n : Modulus K) :
    (m * n).infinitePart = m.infinitePart ∪ n.infinitePart := rfl

open Classical in
instance : CommMonoid (Modulus K) where
  one_mul m := by ext <;> simp [Finset.empty_union]
  mul_one m := by ext <;> simp [Finset.union_empty]
  mul_assoc m n p := by ext <;> simp [mul_assoc, Finset.union_assoc]
  mul_comm m n := by ext <;> simp [mul_comm, Finset.union_comm]

def divides (m n : Modulus K) : Prop :=
  (n.finitePart : Ideal (𝓞 K)) ≤ (m.finitePart : Ideal (𝓞 K)) ∧
    (↑m.infinitePart : Set (RealPlace K)) ⊆ ↑n.infinitePart

instance : Dvd (Modulus K) := ⟨divides⟩

@[simp] theorem dvd_unfold (m n : Modulus K) :
    (m ∣ n) ↔ (n.finitePart : Ideal (𝓞 K)) ≤ (m.finitePart : Ideal (𝓞 K)) ∧
      (↑m.infinitePart : Set (RealPlace K)) ⊆ ↑n.infinitePart := Iff.rfl

open Classical in
noncomputable def gcd (m n : Modulus K) : Modulus K :=
  ⟨⟨(m.finitePart : Ideal (𝓞 K)) ⊔ (n.finitePart : Ideal (𝓞 K)),
    mem_nonZeroDivisors_iff_ne_zero.mpr (by
      intro h
      have hm0 : (m.finitePart : Ideal (𝓞 K)) ≠ 0 :=
        mem_nonZeroDivisors_iff_ne_zero.mp m.finitePart.property
      exact hm0 (le_antisymm (h ▸ le_sup_left) zero_le))⟩,
    m.infinitePart ∩ n.infinitePart⟩

open Classical in
noncomputable def lcm (m n : Modulus K) : Modulus K :=
  ⟨⟨(m.finitePart : Ideal (𝓞 K)) ⊓ (n.finitePart : Ideal (𝓞 K)),
    mem_nonZeroDivisors_iff_ne_zero.mpr (by
      have h1 : (m.finitePart : Ideal (𝓞 K)) ≠ ⊥ := by
        have h := mem_nonZeroDivisors_iff_ne_zero.mp m.finitePart.property
        simpa using h
      have h2 : (n.finitePart : Ideal (𝓞 K)) ≠ ⊥ := by
        have h := mem_nonZeroDivisors_iff_ne_zero.mp n.finitePart.property
        simpa using h
      have h := Ideal.inf_ne_bot_of_ne_bot h1 h2
      simpa using h)⟩,
    m.infinitePart ∪ n.infinitePart⟩

open Classical in
@[simp] theorem gcd_infinitePart (m n : Modulus K) :
    (gcd m n).infinitePart = m.infinitePart ∩ n.infinitePart := rfl

open Classical in
@[simp] theorem lcm_infinitePart (m n : Modulus K) :
    (lcm m n).infinitePart = m.infinitePart ∪ n.infinitePart := rfl

@[simp] theorem gcd_finitePart (m n : Modulus K) :
    ((gcd m n).finitePart : Ideal (𝓞 K)) =
      (m.finitePart : Ideal (𝓞 K)) ⊔ (n.finitePart : Ideal (𝓞 K)) := rfl

@[simp] theorem lcm_finitePart (m n : Modulus K) :
    ((lcm m n).finitePart : Ideal (𝓞 K)) =
      (m.finitePart : Ideal (𝓞 K)) ⊓ (n.finitePart : Ideal (𝓞 K)) := rfl

noncomputable def infinite (v : RealPlace K) : Modulus K := ⟨1, {v}⟩

/-- **Finite part of the modulus of a real place.** For a real place $v$ of a number field $K$,
let $\mathfrak m_v$ be the modulus of $K$ with finite part the unit ideal $\mathcal O_K$ and
infinite part $\{v\}$. The finite part of $\mathfrak m_v$ is the unit ideal $\mathcal O_K$. -/
@[simp] theorem infinite_finitePart (v : RealPlace K) :
    (infinite v).finitePart = 1 := rfl

/-- **Infinite part of the modulus of a real place.** For a real place $v$ of a number field $K$,
let $\mathfrak m_v$ be the modulus of $K$ with finite part the unit ideal $\mathcal O_K$ and
infinite part $\{v\}$. The infinite part of $\mathfrak m_v$ is the singleton $\{v\}$. -/
@[simp] theorem infinite_infinitePart (v : RealPlace K) :
    (infinite v).infinitePart = {v} := rfl

open Classical in
theorem infinite_mul_self (v : RealPlace K) : infinite v * infinite v = infinite v := by
  ext <;> simp [infinite, Finset.union_idempotent]

end Modulus
end NumberField
