/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralFoundationPackages
public import Mathlib.Analysis.Complex.Basic

/-!
# Native regular-centralizer and ramification foundation requests

The torus models are supplied by the existing expansion-torus interface.
The group-level source is the connected smooth affine reductive complex
group of Donagi--Gaitsgory, with reductivity tested by actual rational
representations. Native symbol reindexing and line-frame construction
are separate adapters to the actual modules and scheme maps.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Sections1--6,11--12.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.CameralFoundationModelsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages CameralSymbolReindexModels CameralRamificationSymbols
open ExpansionParameterModels ContractedTorsorModels TorusLineFrameModels

def_wanted nativeComplexCameralFoundation
    (G : Over (Spec (.of ℂ))) [GrpObj G] [ConnectedSpace G.left]
    [IsAffine G.left] [Smooth G.hom] [LocallyOfFiniteType G.hom]
    (reductive : ReductiveGroupHypotheses.IsLinearlyReductive G)
    (tori : ∀ n : ℕ, TorusTheory ℂ n) : Foundation G tori

def_wanted nativeSymbolCoefficientMap
    {k : Type} [Field k] {B B' : Type} [CommRing B] [Algebra k B]
    [CommRing B'] [Algebra k B'] (s : B ≃ₐ[k] B) (s' : B' ≃ₐ[k] B')
    (f : B →ₐ[k] B') (commutes : ∀ b : B, s' (f b) = f (s b)) :
    CoefficientMap (s := s) (s' := s') f

def_wanted nativeSymbolSheafMap
    {k : Type} [Field k] {B B' : Type} [CommRing B] [Algebra k B]
    [CommRing B'] [Algebra k B'] (s : B ≃ₐ[k] B) (s' : B' ≃ₐ[k] B')
    (f : B →ₐ[k] B') (C : CoefficientMap (s := s) (s' := s') f) : SheafMap f C

def_wanted nativeTorusTensorOperations
    {k : Type} [Field k] {r : ℕ} (T : TorusTheory k r) :
    letI := T.group; TensorOperations (torusScheme k r)

def_wanted nativeTorusBundleFamilies
    {k : Type} [Field k] {r : ℕ} (T : TorusTheory k r) :
    letI := T.group; Families (G := torusScheme k r)

def_wanted nativeLineFrames
    {k : Type} [Field k] (Gm : TorusTheory k 1)
    (Y : Over (Spec (.of k))) (L : Y.left.Modules)
    (line : CoherentCurveLinearSeries.IsLineBundle L) : LineFrames Gm Y L

def_wanted nativeCharacterLine
    {k : Type} [Field k] {r : ℕ} (T : TorusTheory k r) (Gm : TorusTheory k 1)
    (Y : Over (Spec (.of k))) (δ : torusScheme k r ⟶ torusScheme k 1)
    (hom : letI := T.group; letI := Gm.group; IsMonHom δ)
    (P : letI := T.group; Bundle (torusScheme k r) Y) : CharacterLine Gm T Y δ P

end WantedExt.AlgebraicGeometry.CameralFoundationModelsWanted
