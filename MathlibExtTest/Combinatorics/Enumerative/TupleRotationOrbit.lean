/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.TupleRotationOrbit
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi

/-! # Tests for rotation orbits of tuples -/

open MetaMathlibExt

-- One step of `finRotate` moves every entry one place to the left: `(0, 1)` becomes `(1, 0)`,
-- and two steps take `(1, 2, 3)` to `(3, 1, 2)`.
example : (![1, 0] : Fin 2 → ℕ) ∈ tupleRotationOrbit ![0, 1] := ⟨1, by decide⟩

example : (![3, 1, 2] : Fin 3 → ℕ) ∈ tupleRotationOrbit ![1, 2, 3] := ⟨2, by decide⟩

-- Rotations only permute the entries, so `(1, 1)` is not a rotation of `(0, 1)`: some entry of
-- each rotation of `(0, 1)` is `0`.
example : (![1, 1] : Fin 2 → ℕ) ∉ tupleRotationOrbit ![0, 1] := by
  rintro ⟨m, hm⟩
  have key : ∀ i : Fin 2, (![1, 1] : Fin 2 → ℕ) i ≠ (![0, 1] : Fin 2 → ℕ) 0 := by decide
  apply key (((finRotate 2) ^ m).symm 0)
  rw [hm, Function.comp_apply, Equiv.apply_symm_apply]

-- The two basic lemmas.
example (x : Fin 4 → ℤ) : x ∈ tupleRotationOrbit x := self_mem_tupleRotationOrbit x

example (x : Fin 4 → ℤ) : x ∘ ⇑(finRotate 4) ∈ tupleRotationOrbit x :=
  comp_finRotate_mem_tupleRotationOrbit x

-- A constant tuple is fixed by every rotation, so its orbit is a single tuple.
example {α : Type*} {n : ℕ} (a : α) :
    tupleRotationOrbit (fun _ : Fin n => a) = {fun _ => a} := by
  ext y
  exact ⟨fun ⟨m, hm⟩ => hm, fun hy => ⟨0, by simpa using hy⟩⟩

-- For `n = 0` the only tuple is the empty one.
example {α : Type*} (x : Fin 0 → α) : tupleRotationOrbit x = {x} := by
  ext y
  exact ⟨fun _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
