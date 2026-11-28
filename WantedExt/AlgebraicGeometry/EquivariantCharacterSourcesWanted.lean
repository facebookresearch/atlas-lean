/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.EquivariantCharacterLineModels

/-!
# Source adapters for actual algebraic characters and quotient modules

The outputs retain the complete all-scheme group map, original torsor
sections, native quotient-point maps and genuine weight-summand maps.
These are shared construction/proof requests, independently of virtual
localization or stable-envelope theorems.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.EquivariantCharacterSources

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open MathlibExt.AlgebraicGeometry
open AlgebraicWeightBundleModels AlgebraicEquivariantChowModels EquivariantCharacterLineModels
open LinearizedLineBundles TorusFixedSchemeModels AlgebraicBundleGeometry

/-- Adapt the actual Laurent-coordinate character classification. -/
def_wanted actual_integer_character (chi : Character Gm) : IntegerCharacter chi

/-- Construct the native cartesian module of these original equivariant functions. -/
def_wanted actual_character_module {X : Over base} [ModObj Gm X]
    (Q : EquivariantSource X) (chi : Character Gm) : CharacterModule Q chi

/-- Realize that same prescribed module as its actual represented section line. -/
def_wanted actual_character_line {X : Over base} [ModObj Gm X]
    (Q : EquivariantSource X) (chi : Character Gm) (M : CharacterModule Q chi) :
    {L : CharacterLine Q chi // L.sections = M}

/-- Torus weight summands over a connected noetherian fixed scheme have constant ranks. -/
def_wanted actual_torus_weight_decomposition {X F : Over base} [ModObj Gm X]
    [IsNoetherian F.left] [ConnectedSpace F.left] (E : X.left.Modules) (r : ℕ)
    (hE : IsBundle E r) (L : Linearization Gm X E) (i : F ⟶ X)
    (hi : FixedPoint Gm X i) : WeightDecomposition L i hi

/-- The native quotient map is normalized on every torsor and every reindexing. -/
def_wanted actual_equivariant_quotient_map {X Y : Over base} [ModObj Gm X] [ModObj Gm Y]
    (Q : EquivariantSource X) (R : EquivariantSource Y) (f : X ⟶ Y)
    (hf : γ[Gm,X] ≫ f = (Gm ◁ f) ≫ γ[Gm,Y]) :
    EquivariantMap Q R f hf

end WantedExt.AlgebraicGeometry.EquivariantCharacterSources
