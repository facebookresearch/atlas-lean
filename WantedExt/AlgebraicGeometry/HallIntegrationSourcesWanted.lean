/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.HallBehrendIntegrationModels
public import MathlibExt.AlgebraicGeometry.HallZeroObjectModels

/-!
# Actual numerical grading, Laurent completion and canonical integration requests

The constructors return numerical components with all geometric
field tests, actual component fibre-product projections, actual
finite decomposition support and the generator-normalized map (25).
Algebra/Poisson compatibility is requested only after that output
map and its canonical Behrend/Betti normalization have been fixed.

The CY3 hypothesis below includes the actual top-form trivialization
and H^1(O_X)=0. Projective-space inverses remain part of the corrected
regular coefficient ring. No task-generation or theorem-solver result
is imported into these mathematical declarations.

Reference: Bridgeland, arXiv:1002.4374v3, Lemma 2.1,
equations (24)–(25), Definition 5.2, Theorem 5.1 and §7.3–7.4.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.HallIntegrationSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open GeometricHallStackFunctions HallFamilyStackModels HallConvolutionOperations
open HallSemiclassicalOperations HallExactSequenceFamilies StablePairFamilies
open HallNumericalGradingModels HallLaurentCompletion HallBehrendIntegrationModels
open StackBehrendModels StablePairParameterPullbacks CoherentCurveLinearSeries
open HallZeroObjectModels

def_wanted actual_zero_sheaf_generator {X : Over (Spec (.of ℂ))}
    (H : HallStacks X) : ZeroObjectModel H

theorem_wanted actual_hall_left_unit {X : Over (Spec (.of ℂ))} {H : HallStacks X}
    {D : ConvolutionModels H} (h : ConvolutionDescent D) (Z : ZeroObjectModel H)
    (a : LefschetzStackFunctions H.moduli) : convolution h (hallUnit Z) a=a

theorem_wanted actual_hall_right_unit {X : Over (Spec (.of ℂ))} {H : HallStacks X}
    {D : ConvolutionModels H} (h : ConvolutionDescent D) (Z : ZeroObjectModel H)
    (a : LefschetzStackFunctions H.moduli) : convolution h a (hallUnit Z)=a

def_wanted actual_coherent_numerical_data (X : Over (Spec (.of ℂ))) (HX : Threefold X) :
    NumericalData X HX

theorem_wanted actual_effective_monoid_realization {X : Over (Spec (.of ℂ))}
    {HX : Threefold X} (N : NumericalData X HX) (α : Delta N) :
    ∃ F : CoherentObject X, actualClass N F=α.val

theorem_wanted actual_geometric_fibre_cohomology (X : Over (Spec (.of ℂ))) (HX : Threefold X)
    {T : Over (Spec (.of ℂ))} (F : HallExactSequenceFamilies.Family X T)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℂ Ω] (p : geometricParameter Ω ⟶ T) :
    FiniteDimensional Ω
      (cohomology (projection X (geometricParameter Ω)) (geometricModule X F Ω p) 0) ∧
    FiniteDimensional Ω
      (cohomology (projection X (geometricParameter Ω)) (geometricModule X F Ω p) 1) ∧
    ∀ n : ℕ, 1<n →
      IsZero (cohomology (projection X (geometricParameter Ω)) (geometricModule X F Ω p) n)

def_wanted actual_numerical_component {X : Over (Spec (.of ℂ))} {HX : Threefold X}
    (N : NumericalData X HX) (H : HallStacks X) (α : Delta N) : NumericalComponent N H α

def_wanted actual_numerical_projections {X : Over (Spec (.of ℂ))} {HX : Threefold X}
    (N : NumericalData X HX) (H : HallStacks X) : NumericalProjectionData N H

theorem_wanted actual_numerical_projection_regular {X : Over (Spec (.of ℂ))} {HX : Threefold X}
    {N : NumericalData X HX} {H : HallStacks X} (P : NumericalProjectionData N H)
    (α : Delta N) (a : Regular H.moduli) : P.projection α a.val∈regularSubmodule H.moduli

theorem_wanted actual_numerical_projection_idempotent {X : Over (Spec (.of ℂ))}
    {HX : Threefold X} {N : NumericalData X HX} {H : HallStacks X}
    (P : NumericalProjectionData N H) (α : Delta N) (a : LefschetzStackFunctions H.moduli) :
    P.projection α (P.projection α a)=P.projection α a

theorem_wanted actual_numerical_projection_orthogonal {X : Over (Spec (.of ℂ))}
    {HX : Threefold X} {N : NumericalData X HX} {H : HallStacks X}
    (P : NumericalProjectionData N H) (α β : Delta N) (hne : α≠β)
    (a : LefschetzStackFunctions H.moduli) : P.projection α (P.projection β a)=0

theorem_wanted actual_regular_finite_numerical_decomposition {X : Over (Spec (.of ℂ))}
    {HX : Threefold X} {N : NumericalData X HX} {H : HallStacks X}
    (P : NumericalProjectionData N H) (a : Regular H.moduli) :
    ∃ S : Finset (Delta N), (∀ α : Delta N, α∉S → P.projection α a.val=0) ∧
      ∑ α ∈ S, P.projection α a.val=a.val

theorem_wanted actual_finite_laurent_products {X : Over (Spec (.of ℂ))} {HX : Threefold X}
    (N : NumericalData X HX) : FiniteLaurentProducts N

theorem_wanted actual_target_laurent_product_support {X : Over (Spec (.of ℂ))}
    {HX : Threefold X} {N : NumericalData X HX} (F : FiniteLaurentProducts N)
    (a b : LaurentFunction N ℂ) : LaurentSet N {α | targetProductValue F a b α≠0}

theorem_wanted actual_completed_hall_product {X : Over (Spec (.of ℂ))} {HX : Threefold X}
    {N : NumericalData X HX} {H : HallStacks X} {D : ConvolutionModels H}
    (h : ConvolutionDescent D) (F : FiniteLaurentProducts N) {P : NumericalProjectionData N H}
    (a b : HallSeries H P) : HallProductData h F a b

variable {X : Over (Spec (.of ℂ))} {HX : Threefold X}
  {N : NumericalData X HX} {H : HallStacks X} {D : ConvolutionModels H}
  {h : ConvolutionDescent D} {L : ∀ g : Generator H.moduli, LefschetzProduct g}
  {hL : LefschetzDescent L}

def_wanted actual_generator_normalized_integration (CY : CalabiYauThreefold X)
    (C : RegularClosure h hL)
    (P : NumericalProjectionData N H) (W : StackBehrendModel H.families.carrier) :
    NormalizedIntegration C P W

theorem_wanted actual_integration_multiplicative (CY : CalabiYauThreefold X)
    {C : RegularClosure h hL}
    {P : NumericalProjectionData N H} {W : StackBehrendModel H.families.carrier}
    (I : NormalizedIntegration C P W) (S : SemiclassicalMultiplicationDescent C)
    (a b : Semiclassical C) : I.map (semiclassicalMultiplication S a b)=I.map a*I.map b

theorem_wanted actual_integration_poisson (CY : CalabiYauThreefold X)
    {C : RegularClosure h hL}
    {P : NumericalProjectionData N H} {W : StackBehrendModel H.families.carrier}
    (I : NormalizedIntegration C P W) {B : DividedCommutatorData C}
    (S : SemiclassicalBracketDescent B) (a b : Semiclassical C) :
    I.map (semiclassicalBracket S a b)=0

theorem_wanted actual_integration_numerical_component (CY : CalabiYauThreefold X)
    {C : RegularClosure h hL}
    {P : NumericalProjectionData N H} {W : StackBehrendModel H.families.carrier}
    (I : NormalizedIntegration C P W) (α : Delta N) (a : Regular H.moduli)
    (ha : P.projection α a.val=a.val) :
    I.map ((semiclassicalRelations C).mkQ a) = AddMonoidAlgebra.single α
      ((I.map ((semiclassicalRelations C).mkQ a)).coeff α)

theorem_wanted actual_integration_unit (CY : CalabiYauThreefold X)
    {C : RegularClosure h hL} {P : NumericalProjectionData N H}
    {W : StackBehrendModel H.families.carrier} (I : NormalizedIntegration C P W)
    (Z : ZeroObjectModel H) : I.map (semiclassicalUnit C Z)=1

end WantedExt.AlgebraicGeometry.HallIntegrationSources
