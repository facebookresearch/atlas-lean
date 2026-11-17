/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AdelicFinitePointNormModels

/-!
# Finite-point norm construction requests

Outputs retain the actual closed image, determinant norm line, completed
tensor factors, original fibre vectors and paired model sequences. The
vector height is the norm-line class divided by its actual residue degree.
Source: Yuan--Zhang, arXiv:2105.13587v9, Sections 3.4 and 5.3.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AdelicFinitePointNormModels

open CategoryTheory _root_.AlgebraicGeometry Module
open MathlibExt.AlgebraicGeometry.PlacewiseMetrizedLineModels
open MathlibExt.AlgebraicGeometry.AdelicSemipositiveClosures
open MathlibExt.AlgebraicGeometry.FinitePointNormLines
open MathlibExt.AlgebraicGeometry.AdelicPicardVectors
open MathlibExt.AlgebraicGeometry.AdelicFinitePointNormModels

/-- Construct full tensor/completion factors preserving the literal base scalar square. -/
public def_wanted placeFactors (K E : Type) [Field K] [Field E]
    [Algebra K E] [FiniteDimensional K E] (A : AdelicField K) : PlaceFactors (E := E) A

/-- A finite-extension point factors through its actual finite closed image. -/
public def_wanted closedImage (K E : Type) [Field K] [Field E]
    [Algebra K E] [FiniteDimensional K E] (X : Over (Spec (.of K)))
    [LocallyOfFiniteType X.hom] (x : ExtensionPoint (K := K) (E := E) X) : ClosedImage x

/-- The constructed target is the actual determinant norm line with source-normalized model norms. -/
public def_wanted normModels (K E : Type) [Field K] [Field E]
    [Algebra K E] [FiniteDimensional K E] (A : AdelicField K)
    (X : Over (Spec (.of K))) (G : GroundBase (K := K))
    (M : LineObject (A := A) (X := X) G) (x : ClosedPoint (K := K) (E := E) X)
    (D : PlaceFactors (E := E) A) (b : Basis Unit E (pointFibre M.line x.map)) :
    NormResult D x G M b

/-- Changing the algebraic fibre frame preserves the actual norm-line isometry class. -/
public theorem_wanted frameIndependent (K E : Type) [Field K] [Field E]
    [Algebra K E] [FiniteDimensional K E] (A : AdelicField K)
    (X : Over (Spec (.of K))) (G : GroundBase (K := K))
    (M : LineObject (A := A) (X := X) G) (x : ClosedPoint (K := K) (E := E) X)
    (D : PlaceFactors (E := E) A) (b c : Basis Unit E (pointFibre M.line x.map))
    (N : NormResult D x G M b) (P : NormResult D x G M c) :
    vectorHeight D x G M b N = vectorHeight D x G M c P

end WantedExt.AlgebraicGeometry.AdelicFinitePointNormModels
