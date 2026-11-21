/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sheaves.Abelian
public import MathlibExt.AlgebraicGeometry.ComplexAnalytification

@[expose] public section

/-!
# Rational perverse sheaves

This module specifies bounded algebraically constructible rational complexes
on general complex varieties and the middle perverse t-structure through its
stalk and costalk dimension conditions. `PerverseSheafTheory` is the
characterized input to the public perverse constructions; its general
provider is requested separately in
`WantedExt/AlgebraicGeometry/PerverseSheavesWanted.lean`.

Given that characterized theory, `PerverseSheaf` is its heart and
`perverseCohomology` is computed using Mathlib's truncations. Consumers can
use this public interface with `[PerverseSheafTheory X]`.

The rational sheaves are on `X(ℂ)` with its usual analytic topology. This is
the topology used for Betti local systems and the Hodge theoretic formulation
of decomposition. `ComplexAnalytification` supplies its underlying
topological space and the continuous maps induced by algebraic morphisms.

## References

* M. A. A. de Cataldo and L. Migliorini, *The Hodge theory of algebraic maps*,
  Ann. Sci. École Norm. Sup. (4) 38 (2005), §§3.3, 3.6, 3.8.
  https://arxiv.org/abs/math/0306030
* Their 2009 survey, §2.3, equations (14) and (15).
  https://arxiv.org/abs/0712.0349
* The imported complex-point topology retains AxiomMath/Weil source paths,
  revision, Apache 2.0 attribution, and its modification notice in
  `MathlibExt/AlgebraicGeometry/ComplexAnalytification.lean`.
-/

namespace MathlibExt.AlgebraicGeometry.PerverseSheaves

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry
open ComplexAnalytification

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- Schemes over the complex numbers. -/
abbrev ComplexScheme := Over (Spec (.of ℂ))

/-- A complex variety is reduced, separated, and of finite type over `ℂ`.
Components of different dimensions are allowed in the target. -/
class IsComplexVariety (X : ComplexScheme) : Prop where
  reduced : IsReduced X.left
  separated : IsSeparated X.hom
  locallyOfFiniteType : LocallyOfFiniteType X.hom
  quasiCompact : QuasiCompact X.hom

attribute [instance] IsComplexVariety.reduced IsComplexVariety.separated
  IsComplexVariety.locallyOfFiniteType IsComplexVariety.quasiCompact

/-- A finite partition by smooth locally closed algebraic subvarieties. -/
structure AlgebraicStratification (X : ComplexScheme) where
  /-- Number of strata; zero is permitted for an empty variety. -/
  count : ℕ
  /-- The strata as schemes over `ℂ`. -/
  stratum : Fin count → ComplexScheme
  /-- Each stratum is a variety. -/
  variety : ∀ a, IsComplexVariety (stratum a)
  /-- Inclusion of each stratum, over `ℂ`. -/
  inclusion : ∀ a, stratum a ⟶ X
  /-- Each inclusion is a locally closed immersion. -/
  immersion : ∀ a, IsImmersion (inclusion a).left
  /-- Each stratum is smooth over `ℂ`. -/
  smooth : ∀ a, Smooth (stratum a).hom
  /-- Distinct strata have disjoint images. -/
  disjoint : Pairwise fun a b ↦
    Disjoint (Set.range (inclusion a).left) (Set.range (inclusion b).left)
  /-- The images cover the whole variety. -/
  cover : (⋃ a, Set.range (inclusion a).left) = Set.univ

attribute [instance] AlgebraicStratification.variety
  AlgebraicStratification.immersion AlgebraicStratification.smooth

/-- Sheaves of rational vector spaces on a topological space. -/
abbrev RationalSheaf (Z : TopCat.{0}) := TopCat.Sheaf (ModuleCat.{0} ℚ) Z

/-- The actual derived category of rational sheaves. -/
abbrev RationalDerived (Z : TopCat.{0}) := DerivedCategory (RationalSheaf Z)

/-- Rational sheaf pushforward acts additively on natural transformations. -/
instance rationalSheafPushforward_additive {Z W : TopCat.{0}} (f : Z ⟶ W) :
    (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).Additive where
  map_add := by
    intro F G a b
    rfl

/-- The constant rational sheaf. -/
def rationalConstantSheaf (Z : TopCat.{0}) : RationalSheaf Z :=
  (constantSheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} ℚ)).obj
    (ModuleCat.of ℚ ℚ)

/-- The continuous inclusion of an open subspace. -/
def openInclusion (Z : TopCat.{0}) (U : Opens Z) : TopCat.of U ⟶ Z :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Local triviality as a finite-dimensional rational constant sheaf.
Finite-dimensional stalks alone would not express the local-system condition. -/
def IsFiniteRankLocalSystem (Z : TopCat.{0}) (F : RationalSheaf Z) : Prop :=
  ∀ x : Z, ∃ U : Opens Z, x ∈ U ∧
    ∃ V : ModuleCat.{0} ℚ, FiniteDimensional ℚ V ∧
      Nonempty
        ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (openInclusion Z U)).obj F ≅
          (constantSheaf (Opens.grothendieckTopology (TopCat.of U))
            (ModuleCat.{0} ℚ)).obj V)

/-- Bounded cohomology with a common finite algebraic stratification on which
every cohomology sheaf is a finite-rank rational local system.
Source: de Cataldo–Migliorini (2005), §3.3. -/
def boundedConstructible (X : ComplexScheme) :
    ObjectProperty (RationalDerived (space X)) := fun K ↦
  (∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j →
    IsZero ((DerivedCategory.homologyFunctor _ j).obj K)) ∧
  ∃ S : AlgebraicStratification X, ∀ a j,
    IsFiniteRankLocalSystem (space (S.stratum a))
      ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (spaceMap (S.inclusion a))).obj
          ((DerivedCategory.homologyFunctor _ j).obj K))

/-- Zariski dimension of a support bounded by an integer. A negative bound
forces the support to be empty, implementing `dim ∅ = -∞`. -/
def SupportDimensionLE (X : ComplexScheme) (s : Set X.left) (d : ℤ) : Prop :=
  if d < 0 then s = ∅ else
    topologicalKrullDim (closure s) ≤ ((d.toNat : ℕ∞) : WithBot ℕ∞)

/-- The algebraic image of the nonzero stalks of the `j`th cohomology sheaf. -/
def stalkSupport (X : ComplexScheme) (K : RationalDerived (space X))
    (j : ℤ) : Set X.left :=
  ComplexPoints.schemePoint ''
    {p : space X | ¬ IsZero
      (((DerivedCategory.homologyFunctor _ j).obj K).presheaf.stalk p)}

/-- The rational skyscraper at a complex point, placed in cohomological
degree zero. -/
def rationalSkyscraper (X : ComplexScheme) (p : space X) :
    RationalDerived (space X) := by
  classical
  exact (DerivedCategory.singleFunctor _ 0).obj
    (skyscraperSheaf p (ModuleCat.of ℚ ℚ))

/-- The algebraic image of nonzero `j`th costalk cohomology.
For a closed point `iₚ`, derived adjunction identifies
`Hom(iₚ* ℚ, K[j])` with `Hʲ(iₚ! K)`. The skyscraper is unshifted and the
target is shifted by `+j`. Source: de Cataldo–Migliorini (2009), §2.3. -/
def costalkSupport (X : ComplexScheme) (K : RationalDerived (space X))
    (j : ℤ) : Set X.left :=
  ComplexPoints.schemePoint ''
    {p : space X | ¬ Subsingleton (rationalSkyscraper X p ⟶ K⟦j⟧)}

/-- The data of the rational middle perverse t-structure on a complex
variety, characterized by its support and cosupport conditions.
The separate WantedExt provider request supplies this interface for every
variety.
Source: de Cataldo–Migliorini (2005), §§3.3, 3.6; (2009), §2.3. -/
class PerverseSheafTheory (X : ComplexScheme) [IsComplexVariety X] where
  /-- Closure of bounded constructible complexes under shifts and triangles. -/
  [isTriangulated : (boundedConstructible X).IsTriangulated]
  /-- The middle perverse t-structure on the bounded constructible category. -/
  t : CategoryTheory.Triangulated.TStructure
    (boundedConstructible X).FullSubcategory
  /-- Stalk support condition in every degree. -/
  le_iff : ∀ K m, t.le m K ↔ ∀ j,
    SupportDimensionLE X (stalkSupport X K.obj j) (m - j)
  /-- Costalk support condition in every degree. -/
  ge_iff : ∀ K m, t.ge m K ↔ ∀ j,
    SupportDimensionLE X (costalkSupport X K.obj j) (j - m)

attribute [instance] PerverseSheafTheory.isTriangulated

/-- The characterized middle perverse t-structure. -/
def perverseTStructure (X : ComplexScheme) [IsComplexVariety X]
    [PerverseSheafTheory X] :
    CategoryTheory.Triangulated.TStructure
      (boundedConstructible X).FullSubcategory :=
  PerverseSheafTheory.t (X := X)

/-- The category of rational perverse sheaves, as the heart of the
characterized middle perverse t-structure. -/
abbrev PerverseSheaf (X : ComplexScheme) [IsComplexVariety X]
    [PerverseSheafTheory X] :=
  (perverseTStructure X).heart.FullSubcategory

/-- Heart-valued perverse cohomology, computed from the degree-zero slice
of the shifted complex. -/
def perverseCohomology (X : ComplexScheme) [IsComplexVariety X]
    [PerverseSheafTheory X] (j : ℤ)
    (K : (boundedConstructible X).FullSubcategory) : PerverseSheaf X :=
  ⟨((perverseTStructure X).truncGELE 0 0).obj (K⟦j⟧), by
    rw [CategoryTheory.Triangulated.TStructure.mem_heart_iff]
    constructor <;> infer_instance⟩

/-- Semisimplicity means a finite sum of objects simple in the perverse
heart. The isomorphism is taken in the ambient triangulated category. -/
def IsSemisimplePerverse {C : Type*} [Category* C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ]
    [∀ j : ℤ, (shiftFunctor C j).Additive] [Pretriangulated C]
    (t : CategoryTheory.Triangulated.TStructure C)
    (P : t.heart.FullSubcategory) : Prop :=
  ∃ n : ℕ, ∃ S : Fin n → t.heart.FullSubcategory,
    (∀ a, Simple (S a)) ∧
      Nonempty (P.obj ≅ biproduct (fun a ↦ (S a).obj))

end

end MathlibExt.AlgebraicGeometry.PerverseSheaves
