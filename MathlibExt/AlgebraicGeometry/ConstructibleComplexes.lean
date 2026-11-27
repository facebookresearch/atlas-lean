/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.RingTheory.Flat.CategoryTheory
public import MathlibExt.AlgebraicGeometry.PerverseSheaves

/-!
# Operations on constructible complexes

The coefficient sheaves, finite-rank local systems and bounded constructible
complexes with coefficients in a field `k` (`CoefficientSheaf`,
`CoefficientDerived`, `IsFiniteRankLocalSystem`, `boundedConstructible`) are
defined in `MathlibExt.AlgebraicGeometry.PerverseSheaves`, whose rational
notions are their specializations at `k = ℚ`. This module adds change of
coefficients, exact inverse image, the bounded-below derived direct image and
the normalized direct image `Rf_* k_X[n]` of the constant sheaf.

All carriers are actual sheaves on complex analytification. Scalar extension
is performed on presheaves and then sheafified (Mathlib's
`Sheaf.composeAndSheafify`); pointwise tensoring a sheaf with a coefficient
field need not already satisfy the sheaf condition. Inverse image and scalar
extension are exact, so their derived functors need no hypothesis.

The constructions below are complete. The closure and preservation properties
of constructibility are requested in
`WantedExt/AlgebraicGeometry/ConstructibleComplexesWanted.lean`, except
`localSystem_cokernel`, which is proved in
`MathlibExt.AlgebraicGeometry.ConstructibleComplexesLocalSystemCokernel`, and
`localSystem_kernel`, which is proved in
`MathlibExt.AlgebraicGeometry.ConstructibleComplexesLocalSystemKernel`.
The preservation of constructibility under scalar extension
(`constructible_scalarExtension`) is also proved, in
`MathlibExt.AlgebraicGeometry.ConstructibleComplexesConstructibleScalarExtension`.

## References

* A. Dimca, *Sheaves in Topology*, Chapters 2–4.
* M. de Cataldo and L. Migliorini, https://arxiv.org/abs/0712.0349, §1.5.
* The Stacks Project, Tag 00W1 (sheafification).
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ConstructibleComplexes

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry ComplexAnalytification PerverseSheaves

attribute [local instance] HasDerivedCategory.standard

/-- Extension of scalars along a field extension preserves finite limits,
since `l` is flat over `k`; it preserves finite colimits as a left adjoint. -/
instance extendScalars_preservesFiniteLimits (k l : Type) [Field k] [Field l]
    [Algebra k l] :
    PreservesFiniteLimits (ModuleCat.extendScalars.{0, 0, 0} (algebraMap k l)) := by
  let F := ModuleCat.extendScalars.{0, 0, 0} (algebraMap k l)
  have : F.Additive := preservesFiniteColimits_le_additiveFunctor _ _ F
    (show PreservesFiniteColimits F from
      inferInstanceAs (PreservesFiniteColimits (ModuleCat.extendScalars (algebraMap k l))))
  have h (S : ShortComplex (ModuleCat.{0} k)) (hS : S.Exact) : (S.map F).Exact := by
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
    let : Module k l := Module.compHom l (algebraMap k l)
    exact Module.Flat.lTensor_exact l hS
  have h' : PreservesFiniteLimits F ∧ PreservesFiniteColimits F :=
    ((Functor.exact_tfae F).out 2 4).mp h
  exact h'.1

/-- Scalar extension of sheaves: extend coefficients objectwise, then
sheafify. -/
abbrev scalarExtension (k l : Type) [Field k] [Field l] [Algebra k l] (Z : TopCat.{0}) :
    CoefficientSheaf k Z ⥤ CoefficientSheaf l Z :=
  Sheaf.composeAndSheafify (Opens.grothendieckTopology Z)
    (ModuleCat.extendScalars (algebraMap k l))

/-- Scalar extension of sheaves preserves finite limits: objectwise
extension does, and so does sheafification. -/
instance scalarExtension_preservesFiniteLimits (k l : Type) [Field k] [Field l]
    [Algebra k l] (Z : TopCat.{0}) : PreservesFiniteLimits (scalarExtension k l Z) := by
  constructor
  intro J _ _
  let W := (Functor.whiskeringRight (Opens Z)ᵒᵖ (ModuleCat.{0} k) (ModuleCat.{0} l)).obj
    (ModuleCat.extendScalars (algebraMap k l))
  let S := presheafToSheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} l)
  have : PreservesLimitsOfShape J W := by dsimp [W]; infer_instance
  have : PreservesLimitsOfShape J S := by dsimp [S]; infer_instance
  have : PreservesLimitsOfShape J (W ⋙ S) := comp_preservesLimitsOfShape _ _
  change PreservesLimitsOfShape J (TopCat.Sheaf.forget (ModuleCat.{0} k) Z ⋙ W ⋙ S)
  exact comp_preservesLimitsOfShape _ _

/-- Scalar extension of sheaves preserves finite colimits, as a left adjoint. -/
instance scalarExtension_preservesFiniteColimits (k l : Type) [Field k] [Field l]
    [Algebra k l] (Z : TopCat.{0}) : PreservesFiniteColimits (scalarExtension k l Z) := by
  change PreservesFiniteColimits (Sheaf.composeAndSheafify (Opens.grothendieckTopology Z)
    (ModuleCat.extendScalars (algebraMap k l)))
  infer_instance

/-- Scalar extension of sheaves is additive, since it preserves finite
products. -/
instance scalarExtension_additive (k l : Type) [Field k] [Field l] [Algebra k l]
    (Z : TopCat.{0}) : (scalarExtension k l Z).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Derived scalar extension, induced by the exact scalar extension of
sheaves. -/
def derivedScalarExtension (k l : Type) [Field k] [Field l] [Algebra k l]
    (Z : TopCat.{0}) : CoefficientDerived k Z ⥤ CoefficientDerived l Z :=
  (scalarExtension k l Z).mapDerivedCategory

/-- The ordinary inverse-image functor with the coefficient field fixed. -/
abbrev pullback (k : Type) [Field k] {Z W : TopCat.{0}} (f : Z ⟶ W) :=
  TopCat.Sheaf.pullback (ModuleCat.{0} k) f

/-- Inverse image of sheaves preserves finite limits: Mathlib's site pullback
along the representably flat functor `Opens.map f` is left exact. -/
instance pullback_preservesFiniteLimits (k : Type) [Field k] {Z W : TopCat.{0}}
    (f : Z ⟶ W) : PreservesFiniteLimits (pullback k f) := by
  have : RepresentablyFlat (Opens.map f) := flat_of_preservesFiniteLimits _
  have : ReflectsLimits (CategoryTheory.forget (ModuleCat.{0} k)) :=
    reflectsLimits_of_reflectsIsomorphisms
  have : PreservesFiniteLimits
      ((Opens.map f).op.lan : ((Opens W)ᵒᵖ ⥤ ModuleCat.{0} k) ⥤
        (Opens Z)ᵒᵖ ⥤ ModuleCat.{0} k) :=
    lan_preservesFiniteLimits_of_flat (ModuleCat.{0} k) (Opens.map f)
  change PreservesFiniteLimits ((Opens.map f).sheafPullback
    (ModuleCat.{0} k) (Opens.grothendieckTopology W) (Opens.grothendieckTopology Z))
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

/-- Inverse image of sheaves is additive, since it preserves finite products. -/
instance pullback_additive (k : Type) [Field k] {Z W : TopCat.{0}} (f : Z ⟶ W) :
    (pullback k f).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Derived inverse image, induced by the exact inverse-image functor. -/
def derivedPullback (k : Type) [Field k] {Z W : TopCat.{0}} (f : Z ⟶ W) :
    CoefficientDerived k W ⥤ CoefficientDerived k Z :=
  (pullback k f).mapDerivedCategory

/-- Actual bounded-below derived direct image, with its ambient inclusion. -/
def derivedPushforwardPlus (k : Type) [Field k] {X Y : ComplexScheme} (f : X ⟶ Y) :
    DerivedCategory.Plus (CoefficientSheaf k (space X)) ⥤ CoefficientDerived k (space Y) :=
  (TopCat.Sheaf.pushforward (ModuleCat.{0} k) (spaceMap f)).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.ι

/-- The normalized direct image `Rf_* k_X[n]`: the constant sheaf of `X(ℂ)`,
placed in cohomological degree `-n`, pushed forward by the bounded-below derived
direct image. -/
def normalizedDirectImage (k : Type) [Field k] (X Y : ComplexScheme) (f : X ⟶ Y) (n : ℕ) :
    CoefficientDerived k (space Y) :=
  (derivedPushforwardPlus k f).obj
    ((DerivedCategory.Plus.singleFunctor (CoefficientSheaf k (space X)) (-(n : ℤ))).obj
      ((constantSheaf (Opens.grothendieckTopology (space X)) (ModuleCat.{0} k)).obj
        (ModuleCat.of k k)))

end MathlibExt.AlgebraicGeometry.ConstructibleComplexes
