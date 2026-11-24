/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedAlongDerivations
public import MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
public import MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
public import Batteries.Util.ProofWanted

/-!
# Wanted assembly of the actual whole-diagram based deformation map

Projection, path, pullback, replacement and covariant maps are fixed
by the native X(E) → Y(E) postcomposition and actual augmentations.
No cotangent differential, tangent fibre or symplectic comparison is
used as a background provider.

Reference: HAG II math/0404373v7 §1.4.1; PTVV1111.3209v4 §2.2.
-/

open _root_.CategoryTheory
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedCoherentCotangentModels
open MathlibExt.AlgebraicGeometry.DerivedAlongDerivations

universe u
variable (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (R : RawModuleRealization M)
    (X Y : Prestack k) (K : KernelSystem N X)

def_wanted along_split_projection (f : X ⟶ Y) (P : JointLiftProjection M R K) :
    AlongLiftProjection M R K f P

def_wanted along_stack_path (Q : AlgebraReplacementFunctor k) (Z : DerivedStack Q)
    (Y_eq : Y = Z.functor) : AlongPath M R K Y

def_wanted along_stack_path_map (f : X ⟶ Y) (B : JointPath M R K) (C : AlongPath M R K Y) :
    AlongPathMap M R K f B C

def_wanted along_based_pullback_map (f : X ⟶ Y) (P : JointLiftProjection M R K)
    (A : AlongLiftProjection M R K f P) (B : JointPath M R K)
    (C : AlongPath M R K Y) (T : AlongPathMap M R K f B C) :
    AlongRawMap M R K f P A B C T

def_wanted along_joint_derived_diagram (f : X ⟶ Y) (P : JointLiftProjection M R K)
    (A : AlongLiftProjection M R K f P) (C : AlongPath M R K Y) :
    AlongDerivationModel M R K f P A C

def_wanted along_joint_replacement_map (f : X ⟶ Y) (P : JointLiftProjection M R K)
    (A : AlongLiftProjection M R K f P) (B : JointPath M R K)
    (C : AlongPath M R K Y) (T : AlongPathMap M R K f B C)
    (a : AlongRawMap M R K f P A B C T) (D : JointDerivationModel M R K P B)
    (E : AlongDerivationModel M R K f P A C) : AlongReplacementMap M R K a D E

def_wanted along_covariant_fibration (f : X ⟶ Y) (P : JointLiftProjection M R K)
    (A : AlongLiftProjection M R K f P) (C : AlongPath M R K Y)
    (E : AlongDerivationModel M R K f P A C) : AlongFibration M R K E

def_wanted along_covariant_comparison (f : X ⟶ Y) (P : JointLiftProjection M R K)
    (A : AlongLiftProjection M R K f P) (B : JointPath M R K)
    (C : AlongPath M R K Y) (T : AlongPathMap M R K f B C)
    (a : AlongRawMap M R K f P A B C T) (D : JointDerivationModel M R K P B)
    (E : AlongDerivationModel M R K f P A C) (r : AlongReplacementMap M R K a D E)
    (DF : DerivationFibration M R K D) (EF : AlongFibration M R K E) :
    AlongFibrationMap M R K r DF EF
