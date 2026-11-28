/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.BrauerCharacterInCyclotomic
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! # A nonreal character value for a group of order 16 and exponent 4 -/

open MathlibExt.GroupTheory.BrauerCharacterInCyclotomicWanted.RepresentationTheory

-- The pair (I, 1) acts on the complex line through its first coordinate and has trace I.
example : ∃ φ : CyclotomicField 4 ℚ →+* ℂ, Complex.I ∈ φ.range := by
  let H := rootsOfUnity 4 ℂ
  let : Fintype H := Fintype.ofFinite _
  let χ : H →* ℂ := (Units.coeHom ℂ).comp H.subtype
  let ρ : Representation ℂ (H × H) ℂ := (algebraMap ℂ (Module.End ℂ ℂ)).toMonoidHom.comp
    (χ.comp (MonoidHom.fst H H))
  have hexp : Monoid.exponent (H × H) = 4 := by
    rw [Monoid.exponent_prod, IsCyclic.exponent_eq_card, Complex.card_rootsOfUnity]
    decide
  rw [← hexp]
  obtain ⟨φ, hφ⟩ := brauer_character_in_cyclotomic (H × H)
  have hI := hφ ℂ inferInstance inferInstance inferInstance ρ
    (Complex.isPrimitiveRoot_I.toRootsOfUnity, 1)
  change LinearMap.trace ℂ ℂ (algebraMap ℂ (Module.End ℂ ℂ) Complex.I) ∈ φ.range at hI
  exact ⟨φ, by simpa [Module.algebraMap_end_eq_smul_id] using hI⟩
