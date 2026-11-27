/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BerkovichAnalytification
public import MathlibExt.AlgebraicGeometry.TropicalCycleIntersections
public import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Tropical support from actual residue-valued analytic points

This support uses all actual scheme points equipped with a real residue-field
absolute value extending the ground norm. It therefore retains nonzero tropical
directions over a trivially valued ground field. The closure of ground-field
point valuations alone would discard those directions. Every coordinate is the
evaluation of the actual Laurent character in the quotient-Spec global sections.
Scalar extension uses the existing literal coefficient ideal map.

References: Gubler, 1108.6126, sections 3--5; Osserman--Payne, 1007.1314v3,
Appendix A.4; Berkovich, *Spectral theory and analytic geometry*, section 3.4.
Native Gamma-Spec, residue-field and absolute-value operations are Mathlib at
56a005855ea17e0b0958f73ec801ae140b0a1679, Apache 2.0.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AnalyticTropicalSupport

open _root_.AlgebraicGeometry CategoryTheory TopologicalSpace
open ValuativeTropicalization

variable (K : Type) [NormedField K] (n : ℕ)
  (I : Ideal (CoordinateRing K n))

def coordinateSection (i : Fin n) : Γ((subscheme I).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing K n ⧸ I))).inv
    (Ideal.Quotient.mk I ((characterUnit K n (coordinateExponent i)) : CoordinateRing K n))

def coordinateAbsolute (p : BerkovichAnalytification.Point K (subscheme I)) (i : Fin n) : ℝ :=
  p.eval (coordinateSection K n I i) (by trivial)

def valuationVector (p : BerkovichAnalytification.Point K (subscheme I)) :
    FiniteToricCoordinates.RealSpace n :=
  fun i ↦ -Real.log (coordinateAbsolute K n I p i)

def tropicalization : Set (FiniteToricCoordinates.RealSpace n) :=
  closure (Set.range (valuationVector K n I))

variable [Valued K NNReal]

def ValuationNormCompatibility : Prop :=
  ∀ a : K, ((Valued.v : Valuation K NNReal) a : ℝ) = ‖a‖

variable (L : Type) [NormedField L] [Algebra K L]

def NormExtension : Prop := ∀ a : K, ‖algebraMap K L a‖ = ‖a‖

end MathlibExt.AlgebraicGeometry.AnalyticTropicalSupport
