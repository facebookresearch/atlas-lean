/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_M4aHerbrand_IdeleClassVocab.lean`
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

public import Mathlib.Algebra.Ring.Aut
public import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# Galois descent data on the adele ring

For a Dedekind domain `R` with fraction field `F` and a field `E` with `Algebra E F`, an
`IdeleGaloisDescent R E F` is an action of `F ≃ₐ[E] F` on the adele ring of `F` by continuous
ring automorphisms, extending the action on the diagonal copy of `F`.
-/

@[expose] public section

namespace NumberField

variable (R E F : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
  [Algebra R F] [IsFractionRing R F] [Algebra E F]

/-- An action of `F ≃ₐ[E] F` on the adele ring of `F` by continuous ring automorphisms that
restricts to the given action on the diagonal copy of `F`. -/
structure IdeleGaloisDescent where
  /-- The action on the adele ring. -/
  act : (F ≃ₐ[E] F) →* RingAut (AdeleRing R F)
  /-- On the diagonal copy of `F`, the action is the given one. -/
  compat : ∀ (g : F ≃ₐ[E] F) (x : F),
    act g (algebraMap F (AdeleRing R F) x) = algebraMap F (AdeleRing R F) (g x)
  /-- Each automorphism of the action is continuous. -/
  continuous_act : ∀ g : F ≃ₐ[E] F, Continuous (act g)

namespace IdeleGaloisDescent

variable {R E F}

/-- The inverse of each automorphism of the action is continuous. -/
theorem continuous_act_symm (D : IdeleGaloisDescent R E F) (g : F ≃ₐ[E] F) :
    Continuous (D.act g).symm := by
  have h := D.continuous_act g⁻¹
  rw [map_inv] at h
  exact h

variable (R E F)

/-- The trivial descent datum, when `F ≃ₐ[E] F` is trivial. -/
noncomputable def identityDescent [Subsingleton (F ≃ₐ[E] F)] : IdeleGaloisDescent R E F where
  act := 1
  compat g x := by
    obtain rfl : g = 1 := Subsingleton.elim g 1
    rfl
  continuous_act g := by
    obtain rfl : g = 1 := Subsingleton.elim g 1
    exact continuous_id

end IdeleGaloisDescent

end NumberField
