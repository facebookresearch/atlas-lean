/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HallNumericalGradingModels

/-!
# Actual Laurent support and finite Hall convolution completions

For every actual curve class β, the χ indices in the support must
be bounded below. Products sum over actual decompositions in the
native effective numerical monoid; their finiteness is an explicit
shared proof dependency. Hall coefficients belong to the actual
geometric Hall quotient and its actual numerical component images.

The target is the corresponding completed complex monoid algebra.
No arbitrary completed ring or infinite summation rule is supplied.

Reference: Bridgeland, arXiv:1002.4374v3, Definition 5.2 and §5.2.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HallLaurentCompletion

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open HallNumericalGradingModels HallFamilyStackModels HallConvolutionOperations
open GeometricHallStackFunctions HallExactSequenceFamilies StablePairFamilies

universe u

variable {X : Over (Spec (.of ℂ))} {HX : Threefold X} (N : NumericalData X HX)

/-- Laurent support is the source's bound for every actual integral curve class. -/
def LaurentSet (S : Set (Delta N)) : Prop :=
  ∀ β : CurveLattice X, BddBelow {n : ℤ | ∃ α : Delta N, α ∈ S ∧ α.val=(β,n)}

/-- Only actual finite numerical decompositions are used in a product coefficient. -/
def decompositionSet (S T : Set (Delta N)) (α : Delta N) : Set (Delta N × Delta N) :=
  {p | p.1+p.2=α ∧ p.1∈S ∧ p.2∈T}

/-- This is a proof-only finiteness dependency for the specified monoid and supports. -/
class FiniteLaurentProducts : Prop where
  finite : ∀ (S T : Set (Delta N)), LaurentSet N S → LaurentSet N T →
    ∀ α : Delta N, Finite (decompositionSet N S T α)

/-- A literal coefficient function with the required source support. -/
structure LaurentFunction (A : Type u) [Zero A] where
  coefficient : Delta N → A
  support : LaurentSet N {α | coefficient α≠0}

variable {N}

/-- The actual complex target product coefficient, as a finite decomposition sum. -/
def targetProductValue (F : FiniteLaurentProducts N)
    (a b : LaurentFunction N ℂ) (α : Delta N) : ℂ := by
  letI : Finite (decompositionSet N {β | a.coefficient β≠0} {β | b.coefficient β≠0} α) :=
    F.finite _ _ a.support b.support α
  letI := Fintype.ofFinite
    (decompositionSet N {β | a.coefficient β≠0} {β | b.coefficient β≠0} α)
  exact ∑ p : decompositionSet N {β | a.coefficient β≠0} {β | b.coefficient β≠0} α,
    a.coefficient p.val.1 * b.coefficient p.val.2

def targetProduct (F : FiniteLaurentProducts N) (a b : LaurentFunction N ℂ)
    (h : LaurentSet N {α | targetProductValue F a b α≠0}) : LaurentFunction N ℂ :=
  ⟨targetProductValue F a b,h⟩

/-- Completed Hall coefficients lie in the images of the actual component restrictions. -/
structure HallSeries (H : HallStacks X) (P : NumericalProjectionData N H) where
  coefficient : Delta N → LefschetzStackFunctions H.moduli
  support : LaurentSet N {α | coefficient α≠0}
  homogeneous : ∀ α : Delta N, P.projection α (coefficient α)=coefficient α

structure RegularHallSeries (H : HallStacks X) (P : NumericalProjectionData N H)
    extends HallSeries H P where
  regular : ∀ α : Delta N, coefficient α∈regularSubmodule H.moduli

/-- The coefficient uses the already specified geometric convolution, in its actual order. -/
def hallProductValue {H : HallStacks X} {D : ConvolutionModels H} (h : ConvolutionDescent D)
    (F : FiniteLaurentProducts N) {P : NumericalProjectionData N H}
    (a b : HallSeries H P) (α : Delta N) : LefschetzStackFunctions H.moduli := by
  letI : Finite (decompositionSet N {β | a.coefficient β≠0} {β | b.coefficient β≠0} α) :=
    F.finite _ _ a.support b.support α
  letI := Fintype.ofFinite
    (decompositionSet N {β | a.coefficient β≠0} {β | b.coefficient β≠0} α)
  exact ∑ p : decompositionSet N {β | a.coefficient β≠0} {β | b.coefficient β≠0} α,
    convolution h (a.coefficient p.val.1) (b.coefficient p.val.2)

/-- Construction properties concern that fixed finite sum, without algebra laws. -/
structure HallProductData {H : HallStacks X} {D : ConvolutionModels H}
    (h : ConvolutionDescent D) (F : FiniteLaurentProducts N)
    {P : NumericalProjectionData N H} (a b : HallSeries H P) : Prop where
  support : LaurentSet N {α | hallProductValue h F a b α≠0}
  homogeneous : ∀ α : Delta N,
    P.projection α (hallProductValue h F a b α)=hallProductValue h F a b α

def hallProduct {H : HallStacks X} {D : ConvolutionModels H} {h : ConvolutionDescent D}
    {F : FiniteLaurentProducts N} {P : NumericalProjectionData N H} {a b : HallSeries H P}
    (K : HallProductData h F a b) : HallSeries H P :=
  ⟨hallProductValue h F a b,K.support,K.homogeneous⟩

/-- Regular completion is the actual coefficientwise regular subspace. -/
def regularCoefficient {H : HallStacks X} {P : NumericalProjectionData N H}
    (a : RegularHallSeries H P) (α : Delta N) : Regular H.moduli :=
  ⟨a.coefficient α,a.regular α⟩

def regularHallProduct {H : HallStacks X} {D : ConvolutionModels H} {h : ConvolutionDescent D}
    {F : FiniteLaurentProducts N} {P : NumericalProjectionData N H}
    {a b : RegularHallSeries H P} (K : HallProductData h F a.toHallSeries b.toHallSeries)
    (r : ∀ α : Delta N, hallProductValue h F a.toHallSeries b.toHallSeries α ∈
      regularSubmodule H.moduli) : RegularHallSeries H P :=
  { toHallSeries := hallProduct K, regular := r }

end MathlibExt.AlgebraicGeometry.HallLaurentCompletion
