/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/Homology/DerivedComplete.lean` (AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b), `milnorMap`:
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modifications: form the cochain Milnor fiber of the normalized nilpotent de Rham hypermodels,
rather than a free derived-limit object.
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Abelian.Injective.Basic
public import MathlibExt.AlgebraicGeometry.PadicFormalSchemes
public import MathlibExt.AlgebraicGeometry.RelativeDeRhamModels
public import MathlibExt.AlgebraicGeometry.RelativePrismaticCohomology

/-!
# Normalized de Rham hypermodels of an actual p-adic formal scheme

Every level complex has the actual Kahler/exterior terms. Its chosen
hypermodel is bounded below and quasi-isomorphic to that complex, and its
global sections compute derived global sections: it maps quasi-isomorphically
to a termwise injective resolution, by a map that stays a quasi-isomorphism on
global sections. The hypermodel itself is not required to be injective, since it
carries the strict products of `FormalDeRhamCupModels`, which injective
resolutions need not admit (see below). Adjacent restriction maps are fixed on every
local exact wedge generator; the resolution maps lift them up to an actual
homotopy.

The formal de Rham complex is the literal cochain Milnor fiber of these
global-section complexes. There is no freely named cohomology carrier.

References: EGA I, §10.1; Bhatt--Scholze, arXiv:1905.08229v4,
Definition 4.1 and Theorem 1.8(3); Stacks Project, Tags 070A and 091Z.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FormalDeRhamModels

open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open MathlibExt.RingTheory.BoundedPrisms
open PadicFormalSchemes RelativeDeRhamModels

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime] (P : Prism.{0} p)
  (X : FormalScheme p P.ring P.ideal)

/-- The actual ordinary nth residue-base scheme. -/
abbrev level (n : ℕ) : Over (Spec (CommRingCat.of P.Residue)) :=
  (FormalScheme.algebraicDiagram p P.ring P.ideal X).obj n

/-- The actual closed nilpotent transition of formal levels. -/
abbrev transitionScheme (n : ℕ) : (level p P X n).left ⟶
    (level p P X (n + 1)).left :=
  ((FormalScheme.algebraicDiagram p P.ring P.ideal X).map
    (homOfLE (Nat.le_succ n))).left

/-- The actual direct-image functor of constant-coefficient sheaves. -/
abbrev pushforward (n : ℕ) : Sheaves P.Residue (level p P X n) ⥤
    Sheaves P.Residue (level p P X (n + 1)) :=
  TopCat.Sheaf.pushforward (ModuleCat.{0} P.Residue)
    (TopCat.ofHom (transitionScheme p P X n).base.hom)

instance pushforward_additive (n : ℕ) : (pushforward p P X n).Additive where
  map_add := by intros; rfl

/-- Formal de Rham hypermodels, with their actual terms and restriction
maps pinned independently of any prismatic comparison.

The hypermodel `resolution n` is acyclic for global sections, as witnessed by `toInjective n`,
but is not itself required to be termwise injective, because injective resolutions need not
admit strict unital products: an injective module over `ℤ_p` is `p`-divisible, so it has no
bilinear product with a unit killed by `p`, as the product of a level killed by `p` must be (for
the Breuil–Kisin prism and `X = Spf ℤ_p`, level zero is `Spec 𝔽_p`, and such a product would
force the injective degree-zero term to vanish). -/
structure System where
  differential : ∀ n, Differential P.Residue (level p P X n)
  resolution : ∀ n, CochainComplex
    (Sheaves P.Residue (level p P X n)) ℕ
  unit : ∀ n, (differential n).natComplex ⟶ resolution n
  [unit_quasiIso : ∀ n, QuasiIso (unit n)]
  injectiveResolution : ∀ n, CochainComplex (Sheaves P.Residue (level p P X n)) ℕ
  [injective : ∀ n i, Injective ((injectiveResolution n).X i)]
  toInjective : ∀ n, resolution n ⟶ injectiveResolution n
  [toInjective_quasiIso : ∀ n, QuasiIso (toInjective n)]
  [sections_quasiIso : ∀ n, QuasiIso
    (((sections P.Residue (level p P X n) ⋙ liftModules P.Residue).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (toInjective n))]
  inverseImage_exact : ∀ n, PreservesFiniteLimits
    (TopCat.Sheaf.pullback (ModuleCat.{0} P.Residue)
      (TopCat.ofHom (transitionScheme p P X n).base.hom :
        TopCat.of (level p P X n).left ⟶
          TopCat.of (level p P X (n + 1)).left))
  restriction : ∀ n, (differential (n + 1)).natComplex ⟶
    ((pushforward p P X n).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (differential n).natComplex
  generator : ∀ (n i : ℕ) (U : (level p P X (n + 1)).left.Opensᵒᵖ)
    (a : (level p P X (n + 1)).left.presheaf.obj U)
    (b : Fin i → (level p P X (n + 1)).left.presheaf.obj U),
    ((restriction n).f i).hom.app U
      (Differential.sheafGenerator P.Residue (level p P X (n + 1))
        (differential (n + 1)) i U a b) =
    Differential.sheafGenerator P.Residue (level p P X n) (differential n) i
      (op ((transitionScheme p P X n) ⁻¹ᵁ U.unop))
      (((transitionScheme p P X n).app U.unop).hom a)
      (fun j ↦ ((transitionScheme p P X n).app U.unop).hom (b j))
  comparison : ∀ n, resolution (n + 1) ⟶
    ((pushforward p P X n).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (resolution n)
  unit_square : ∀ n, Homotopy (unit (n + 1) ≫ comparison n)
    (restriction n ≫
      ((pushforward p P X n).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (unit n))

attribute [instance] System.unit_quasiIso System.injective System.toInjective_quasiIso
  System.sections_quasiIso

namespace System

variable {p P X} (S : System p P X)

/-- Actual global sections of the nth form hypermodel; they compute derived global sections. -/
def globalComplex (n : ℕ) : CochainComplex (ModuleCat.{1} P.Residue) ℤ :=
  (((sections P.Residue (level p P X n) ⋙ liftModules P.Residue).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (S.resolution n)).extend
      ComplexShape.embeddingUpNat

/-- The actual global restriction map, with the resolution square fixed. -/
def globalTransition (n : ℕ) : S.globalComplex (n + 1) ⟶
    S.globalComplex n :=
  (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{1} P.Residue)).map
    (((sections P.Residue (level p P X (n + 1)) ⋙
      liftModules P.Residue).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (S.comparison n))

/-- The countable product of the actual level cochain complexes. -/
abbrev productComplex := ∏ᶜ S.globalComplex

/-- The literal Milnor map: its nth component is projection n minus
restriction after projection n+1. -/
def difference : S.productComplex ⟶ S.productComplex :=
  Pi.lift (fun n : ℕ ↦ Pi.π S.globalComplex n -
    Pi.π S.globalComplex (n + 1) ≫ S.globalTransition n)

@[simp] theorem difference_projection (n : ℕ) :
    S.difference ≫ Pi.π S.globalComplex n =
      Pi.π S.globalComplex n -
        Pi.π S.globalComplex (n + 1) ≫ S.globalTransition n := by
  exact Pi.lift_comp_π _ _

/-- The actual formal de Rham complex, as the cochain Milnor fiber. -/
def complex : CochainComplex (ModuleCat.{1} P.Residue) ℤ :=
  (CochainComplex.mappingCone S.difference)⟦(-1 : ℤ)⟧

/-- Its actual object in the residue-ring module derived category. -/
def derived : DerivedCategory (ModuleCat.{1} P.Residue) :=
  DerivedCategory.Q.obj S.complex

end System

end MathlibExt.AlgebraicGeometry.FormalDeRhamModels
