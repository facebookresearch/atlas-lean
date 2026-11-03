/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one.lean`
and
`P2M/Sol/S_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one.lean`
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

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.Algebra.Polynomial.Lifts

/-!
# Integrality in the algebraic closure of the `p`-adics

An element of the algebraic closure of `ℚ_[p]` is integral over the `p`-adic
integers if and only if its norm is at most one: in the forward direction
the minimal polynomial over `ℚ_[p]` is the image of the integral minimal
polynomial, so all its roots have norm at most one; in the reverse direction
the minimal polynomial over `ℚ_[p]` has all coefficients of norm at most
one, hence lifts to a monic polynomial over `ℤ_[p]`.
-/

@[expose] public section

open Polynomial

namespace PadicAlgCl

/-- The `p`-adic integers are integrally closed, since they form a discrete
valuation ring. Mathlib has no such instance. -/
private instance {p : ℕ} [Fact p.Prime] : IsIntegrallyClosed ℤ_[p] := by
  have h : IsDiscreteValuationRing ℤ_[p] ↔
      (IsIntegrallyClosed ℤ_[p] ∧ ∃! P : Ideal ℤ_[p], P ≠ ⊥ ∧ P.IsPrime) :=
    (IsDiscreteValuationRing.TFAE ℤ_[p]
      (IsDiscreteValuationRing.not_isField ℤ_[p])).out 1 4
  exact (h.mp inferInstance).1

private theorem norm_le_one_of_isIntegral {p : ℕ} [Fact p.Prime] {x : PadicAlgCl p}
    (hx : IsIntegral ℤ_[p] x) : ‖x‖ ≤ 1 := by
  have h1 : minpoly ℚ_[p] x = (minpoly ℤ_[p] x).map (algebraMap ℤ_[p] ℚ_[p]) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] hx
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm,
    spectralValue_le_one_iff (minpoly.monic (Algebra.IsIntegral.isIntegral x))]
  intro n
  rw [h1, coeff_map]
  exact PadicInt.norm_le_one _

private theorem isIntegral_of_norm_le_one {p : ℕ} [Fact p.Prime] {x : PadicAlgCl p}
    (hx : ‖x‖ ≤ 1) : IsIntegral ℤ_[p] x := by
  have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  have hmonic : (minpoly ℚ_[p] x).Monic := minpoly.monic hint
  have hcoeff : ∀ n, ‖(minpoly ℚ_[p] x).coeff n‖ ≤ 1 := by
    rw [← spectralValue_le_one_iff hmonic]
    change spectralNorm ℚ_[p] (PadicAlgCl p) x ≤ 1
    rwa [PadicAlgCl.spectralNorm_eq]
  have hlifts : minpoly ℚ_[p] x ∈ Polynomial.lifts (algebraMap ℤ_[p] ℚ_[p]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨(minpoly ℚ_[p] x).coeff n, hcoeff n⟩, rfl⟩
  obtain ⟨g, hgmap, -, hgmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hmonic
  refine ⟨g, hgmonic, ?_⟩
  rw [← aeval_def, ← minpoly.aeval ℚ_[p] x, aeval_def, aeval_def,
    IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (PadicAlgCl p), ← eval₂_map, hgmap]

/-- An element of the algebraic closure of `ℚ_[p]` is integral over `ℤ_[p]`
if and only if its norm is at most one. -/
theorem isIntegral_padicInt_iff_norm_le_one (p : ℕ) [Fact p.Prime] (x : PadicAlgCl p) :
    IsIntegral ℤ_[p] x ↔ ‖x‖ ≤ 1 :=
  ⟨norm_le_one_of_isIntegral, isIntegral_of_norm_le_one⟩

end PadicAlgCl
