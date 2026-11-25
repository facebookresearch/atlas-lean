/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedCoherentCotangentModels
public import MathlibExt.AlgebraicGeometry.DerivedArtinAtlasModels
public import Batteries.Util.ProofWanted

/-!
# Wanted complete coefficient diagrams and coherent cotangent representation

Generic raw localization, kernel functors, joint derived diagrams and
covariant assembly are construction requests. The cotangent request
represents the actual complete derivation left fibration by the actual
global Hom left fibration. Perfectness is a separate source theorem.

References: HAG II math/0404373v7 §§1.3.7 and 1.4.1; PTVV1111.3209v4 conventions and §1.2;
Lurie HTT §§2.1--2.2 and Higher Algebra §7.3.
-/

open _root_.CategoryTheory
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
open MathlibExt.AlgebraicGeometry.DerivedStackFibreModels
open MathlibExt.AlgebraicGeometry.DerivedArtinAtlasModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedCoherentCotangentModels

universe u

def_wanted canonical_affine_module_localization (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N) :
    Σ M : AffineModuleFibration N S, RawModuleRealization M

def_wanted canonical_square_zero_kernel_system (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (X : Prestack k) : KernelSystem N X

def_wanted full_kernel_section_functor (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (R : RawModuleRealization M)
    (X : Prestack k) (K : KernelSystem N X) : KernelSectionFunctor M R K

def_wanted full_kernel_dg_functor (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M) (R : RawModuleRealization M)
    (X : Prestack k) [SSet.Quasicategory (qcoh M X)]
    (K : KernelSystem N X) (G : QCohEnhancement M U X)
    (F : KernelSectionFunctor M R K) : KernelDGFunctor M R K G F

def_wanted joint_lift_projection (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (R : RawModuleRealization M)
    (X : Prestack k) (K : KernelSystem N X) : JointLiftProjection M R K

def_wanted joint_derivation_path (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (R : RawModuleRealization M)
    (X : DerivedStack Q) (K : KernelSystem N X.functor) : JointPath M R K

def_wanted joint_derivation_model (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (R : RawModuleRealization M)
    (X : Prestack k) (K : KernelSystem N X)
    (P : JointLiftProjection M R K) (B : JointPath M R K) : JointDerivationModel M R K P B

def_wanted derivation_covariant_fibration (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (R : RawModuleRealization M)
    (X : Prestack k) (K : KernelSystem N X)
    (P : JointLiftProjection M R K) (B : JointPath M R K)
    (D : JointDerivationModel M R K P B) : DerivationFibration M R K D

def_wanted coherent_global_cotangent (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M) (R : RawModuleRealization M)
    (X : DerivedStack Q) (geometric : IsDerivedArtin X)
    (lfp : IsLocallyOfFinitePresentationStack X) [SSet.Quasicategory (qcoh M X.functor)]
    (K : KernelSystem N X.functor) (G : QCohEnhancement M U X.functor)
    (F : KernelSectionFunctor M R K) (KG : KernelDGFunctor M R K G F)
    (P : JointLiftProjection M R K) (B : JointPath M R K)
    (D : JointDerivationModel M R K P B) (DF : DerivationFibration M R K D) :
    CoherentGlobalCotangent KG D DF

theorem_wanted coherent_global_cotangent_perfect (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M) (R : RawModuleRealization M)
    (X : DerivedStack Q) (geometric : IsDerivedArtin X)
    (lfp : IsLocallyOfFinitePresentationStack X) [SSet.Quasicategory (qcoh M X.functor)]
    (K : KernelSystem N X.functor) (G : QCohEnhancement M U X.functor)
    (F : KernelSectionFunctor M R K) (KG : KernelDGFunctor M R K G F)
    (P : JointLiftProjection M R K) (B : JointPath M R K)
    (D : JointDerivationModel M R K P B) (DF : DerivationFibration M R K D)
    (C : CoherentGlobalCotangent KG D DF) : IsPerfect G C.object
