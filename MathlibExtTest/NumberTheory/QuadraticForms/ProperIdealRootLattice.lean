/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QuadraticForms.ProperIdealRootLattice

open Complex PeriodPair

open scoped ComplexConjugate UpperHalfPlane

/-- Every lattice is homothetic to `ℤ + ℤτ` for some `τ` in the upper half-plane. -/
example (L : PeriodPair) : ∃ τ : ℍ, (ofTau τ τ.im_pos.ne').IsHomothetic L :=
  exists_isHomothetic_ofTau L

/-- Homothety preserves the endomorphism ring. -/
example {L L' : PeriodPair} (h : L.IsHomothetic L') :
    L'.endomorphismRing = L.endomorphismRing :=
  h.endomorphismRing_eq

/-- A proper ideal of `ℤ + ℤω` comes from a primitive form of the order's discriminant. -/
example {L : PeriodPair} {𝒪 : Subring ℂ} {ω : ℂ} (hω : ω.im ≠ 0)
    (h𝒪 : (𝒪 : Set ℂ) = (ofTau ω hω).lattice) {D : ℤ} (hD : (ω - conj ω) ^ 2 = D)
    (hL : L.IsProperIdeal 𝒪) :
    ∃ (a b c : ℤ) (τ : ℍ), discrim a b c = D ∧ (ofTau τ τ.im_pos.ne').IsHomothetic L := by
  obtain ⟨a, b, c, τ, -, -, hd, -, hhom, -⟩ := exists_root_of_isProperIdeal hω h𝒪 hD hL
  exact ⟨a, b, c, τ, hd, hhom⟩
