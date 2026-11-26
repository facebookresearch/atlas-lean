/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from https://github.com/anthropics/fermats-last-theorem, compared with the
source files at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`:
`Definitions/Def_LatticeTreeOrbital.lean`
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.AlgebraicGeometry.FormalOmega.LatticeGalois
public import Mathlib.Basic.Complex.Basic

@[expose] public section

open scoped Matrix
open LT.LatticeTree

universe u

/-- `i ≠ -i` in `ℂ`. -/
private theorem complex_I_ne_neg_I : Complex.I ≠ -Complex.I := by
  intro h
  have h2 : Complex.I.im = (-Complex.I).im := congrArg Complex.im h
  rw [Complex.neg_im, Complex.I_im] at h2
  norm_num at h2

/-- Complex conjugation, as an integral automorphism of `ℂ` over itself. -/
private noncomputable def conjAut : IntegralAut ℂ ℂ where
  toField := starRingAut
  toBase := starRingAut
  commutes r := by
    simp [Algebra.algebraMap_self]

/-- Complex conjugation has order two. -/
private theorem conjAut_comp_conjAut : conjAut.comp conjAut = IntegralAut.refl ℂ ℂ := by
  unfold conjAut IntegralAut.comp IntegralAut.refl
  congr 1 <;>
  · ext x
    exact star_star x

/-- Complex conjugation is not the identity of `ℂ`. -/
example : conjAut.toField ≠ RingEquiv.refl ℂ := by
  intro h
  have hI : conjAut.toField Complex.I = Complex.I := by rw [h]; rfl
  have hI' : conjAut.toField Complex.I = -Complex.I := Complex.conj_I
  rw [hI'] at hI
  exact complex_I_ne_neg_I hI.symm

/-- Complex conjugation moves the vector `(1, i)`. -/
example : galVec conjAut ![1, Complex.I] ≠ ![1, Complex.I] := by
  intro h
  have h1 : conjAut.toField (![1, Complex.I] 1) = ![1, Complex.I] 1 := congrFun h 1
  have h2 : (![1, Complex.I] 1 : ℂ) = Complex.I := by simp
  rw [h2] at h1
  rw [show conjAut.toField Complex.I = -Complex.I from Complex.conj_I] at h1
  exact complex_I_ne_neg_I h1.symm

/-- Complex conjugation moves the complex line through `(1, i)`. -/
private theorem latticeGal_conj_line_ne :
    latticeGal conjAut (Submodule.span ℂ {![1, Complex.I]}) ≠
      Submodule.span ℂ {![1, Complex.I]} := by
  intro h
  have hmem : galVec conjAut ![1, Complex.I] ∈
      Submodule.span ℂ {![(1 : ℂ), Complex.I]} := by
    rw [← h]
    exact galVec_mem_latticeGal (Submodule.mem_span_singleton_self _)
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have h0 : c * 1 = 1 := by
    have := congrFun hc 0
    simpa [galVec, conjAut, Pi.smul_apply, smul_eq_mul] using this
  have h1 : c * Complex.I = -Complex.I := by
    have := congrFun hc 1
    simpa [galVec, conjAut, Pi.smul_apply, smul_eq_mul, Complex.conj_I] using this
  rw [mul_one] at h0
  rw [h0, one_mul] at h1
  exact complex_I_ne_neg_I h1

/-- Consumer with the original binders: if `σ² = id`, applying the twisted action twice is the
action of `normTwo δ σ`. -/
private theorem exactSource {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) {σ : IntegralAut R K}
    (hσ : σ.comp σ = IntegralAut.refl R K) (L : Submodule R (Fin 2 → K)) :
    twistedLatticeMap δ σ (twistedLatticeMap δ σ L) = latticeMap (normTwo δ σ) L :=
  twistedLatticeMap_two_of_orderTwo δ hσ L

/-- Higher-universe consumer: integral automorphisms preserve full lattices. -/
example {R : Type (u + 1)} [CommRing R] {K : Type (u + 1)} [Field K] [Algebra R K]
    {L : Submodule R (Fin 2 → K)} (hL : Submodule.IsFullLattice K L) (σ : IntegralAut R K) :
    Submodule.IsFullLattice K (latticeGal σ L) :=
  IsFullLattice.gal hL σ

example (δ : Matrix.GeneralLinearGroup (Fin 2) ℂ) (L : Submodule ℂ (Fin 2 → ℂ)) :
    twistedLatticeMap δ conjAut (twistedLatticeMap δ conjAut L) =
      latticeMap (normTwo δ conjAut) L :=
  twistedLatticeMap_two_of_orderTwo δ conjAut_comp_conjAut L

/-- Boundary: the identity automorphism fixes every lattice, while complex conjugation moves the
line through `(1, i)`. -/
example : latticeGal (IntegralAut.refl ℂ ℂ) (Submodule.span ℂ {![1, Complex.I]}) =
      Submodule.span ℂ {![1, Complex.I]} ∧
    latticeGal conjAut (Submodule.span ℂ {![1, Complex.I]}) ≠
      Submodule.span ℂ {![1, Complex.I]} :=
  ⟨latticeGal_refl _, latticeGal_conj_line_ne⟩
