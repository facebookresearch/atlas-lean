/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_ringKrullDim_eq_toENat_trdeg_of_finiteType.lean`
and
`P2M/Sol/S_Algebra_ringKrullDim_eq_toENat_trdeg_of_finiteType.lean`
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

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.SetTheory.Cardinal.ENat
public import MathlibExt.RingTheory.Ideal.IntegralKrullDim

import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.NoetherNormalization

@[expose] public section

universe u v

namespace Algebra

private theorem ringKrullDim_mvPolynomial_fin (k : Type u) [Field k] (s : ℕ) :
    ringKrullDim (MvPolynomial (Fin s) k) = s := by
  simp [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]

private theorem isTranscendenceBasis_of_injective_of_isIntegral (k : Type u)
    (A : Type v) [Field k] [CommRing A] [IsDomain A] [Algebra k A] (s : ℕ)
    (g : MvPolynomial (Fin s) k →ₐ[k] A) (hinj : Function.Injective g)
    (hint : g.IsIntegral) :
    IsTranscendenceBasis k (fun i : Fin s => g (MvPolynomial.X i)) := by
  have hind : AlgebraicIndependent k (fun i : Fin s => g (MvPolynomial.X i)) := by
    have hae : MvPolynomial.aeval (fun i : Fin s => g (MvPolynomial.X i)) = g := by
      ext i
      simp
    change Function.Injective (MvPolynomial.aeval (fun i : Fin s => g (MvPolynomial.X i)))
    rw [hae]
    exact hinj
  refine hind.isTranscendenceBasis_iff_isAlgebraic.mpr ?_
  have hrange : Algebra.adjoin k (Set.range fun i : Fin s => g (MvPolynomial.X i)) =
      g.range := by
    have hset : (Set.range fun i : Fin s => g (MvPolynomial.X i)) =
        g '' Set.range (MvPolynomial.X : Fin s → MvPolynomial (Fin s) k) := by
      ext a
      simp only [Set.mem_range, Set.mem_image, exists_exists_eq_and]
    rw [hset, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top]
  rw [hrange]
  haveI : Algebra.IsIntegral g.range A := by
    constructor
    intro a
    obtain ⟨p, hp, hpa⟩ := hint a
    refine ⟨p.map (g.rangeRestrict : MvPolynomial (Fin s) k →+* g.range), hp.map _, ?_⟩
    have h1 : (algebraMap g.range A).comp
        (g.rangeRestrict : MvPolynomial (Fin s) k →+* g.range) =
        (g : MvPolynomial (Fin s) k →+* A) := by
      ext x <;> rfl
    rw [Polynomial.eval₂_map, h1]
    exact hpa
  exact Algebra.IsIntegral.isAlgebraic

/-- The Krull dimension of a finite-type domain over a field equals its
transcendence degree over that field. -/
public theorem ringKrullDim_eq_toENat_trdeg_of_finiteType
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] :
    ringKrullDim A = (Cardinal.toENat (Algebra.trdeg k A) : WithBot ℕ∞) := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  have hdim : ringKrullDim A = s := by
    letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨fun a => hint a⟩
    have h := ringKrullDim_eq_of_integral_of_injective
      (A := MvPolynomial (Fin s) k) (B := A) hinj
    rw [h, ringKrullDim_mvPolynomial_fin]
  have htr : Algebra.trdeg k A = s := by
    have hB := isTranscendenceBasis_of_injective_of_isIntegral k A s g hinj hint
    have h1 := hB.lift_cardinalMk_eq_trdeg
    rw [Cardinal.mk_fin, Cardinal.lift_natCast] at h1
    have h2 : Cardinal.lift.{0} (Algebra.trdeg k A) =
        Cardinal.lift.{0} (s : Cardinal.{v}) := by
      rw [Cardinal.lift_natCast]
      exact h1.symm
    exact Cardinal.lift_injective h2
  rw [hdim, htr, Cardinal.toENat_nat]
  rfl

end Algebra
