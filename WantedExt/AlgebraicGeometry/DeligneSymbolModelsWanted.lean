/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.DeligneSymbolModels
public import MathlibExt.AlgebraicGeometry.DeligneCubicalModels

/-!
# Deligne Cartier/Koszul symbol construction requests

These are direct requests on the actual global bounded determinant line,
actual relative scheme map and actual strongly regular section tuple.
The algebraic, scalar and cochain sources remain in the output telescope.
References: Yuan--Zhang, arXiv:2105.13587v9, Sections 4.2.1--4.2.2.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.DeligneSymbolModels

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.DeligneSymbolModels
open MathlibExt.AlgebraicGeometry.GlobalBoundedDeterminantModels
open MathlibExt.AlgebraicGeometry.RelativeDeterminantPairings

variable [MathlibExt.AlgebraicGeometry.FourierMukai.HasDerivedPullbacks.{0}]
  [MathlibExt.AlgebraicGeometry.FourierMukai.HasDerivedPushforwards.{0}]
  [MathlibExt.AlgebraicGeometry.AffineDerivedCoefficientModules.HasDerivedScalarExtensions.{0}]
  [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
  [∀ R : CommRingCat.{0}, MathlibExt.AlgebraicGeometry.BoundedProjectiveDeterminants.ProjectiveSources R]

/-- Construct the ordered Cartier/Koszul symbol on the SAME full Deligne line. -/
public def_wanted symbols {X Y : Scheme.{0}} (f : X ⟶ Y) (n : ℕ)
    (scope : RelativeScope f n) (L : Fin (n+1) → X.Modules)
    (I : DeterminantSources)
    (cubical : MathlibExt.AlgebraicGeometry.DeligneCubicalModels.CubicalSources I f n)
    (P : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y), Presentations f L R a)
    (D : DeligneLine I f n L P) (s : RegularTuple f n L) :
    SymbolSources I f n L P D s

/-- The source construction is independent of adapted bases, localizations
and coherent affine cochain presentations on the SAME original Deligne line. -/
public theorem_wanted symbols_independent {X Y : Scheme.{0}} (f : X ⟶ Y) (n : ℕ)
    (scope : RelativeScope f n) (L : Fin (n+1) → X.Modules)
    (I : DeterminantSources)
    (P : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y), Presentations f L R a)
    (D : DeligneLine I f n L P) (s : RegularTuple f n L)
    (S T : SymbolSources I f n L P D s) : S.sectionValue = T.sectionValue

end WantedExt.AlgebraicGeometry.DeligneSymbolModels
