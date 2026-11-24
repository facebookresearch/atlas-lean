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
public import MathlibExt.AlgebraicGeometry.GeometricallyReduced
public import MathlibExt.AlgebraicGeometry.Variety

@[expose] public section

/-!
# Constructible complexes and rational perverse sheaves

This module specifies bounded algebraically constructible complexes on
complex varieties and the rational middle perverse t-structure through its
stalk and costalk dimension conditions.

* `PerverseSheaves.IsComplexVariety X` says that `X.left` is a variety over
  `ℂ` in the sense of `AlgebraicGeometry.IsVariety`, for the structure
  morphism `X.hom`.
* The coefficient-generic layer is in the namespace `ConstructibleComplexes`:
  sheaves of `k`-vector spaces (`CoefficientSheaf`), their derived category
  (`CoefficientDerived`), finite-rank local systems
  (`IsFiniteRankLocalSystem`) and bounded constructible complexes
  (`boundedConstructible`). The rational notions of this module are their
  specializations at `k = ℚ`. Change of coefficients, exact inverse image and
  derived direct image are in `MathlibExt.AlgebraicGeometry.ConstructibleComplexes`.
* `CoefficientPerverseModels.CoefficientPerverseTheory k X` is the middle perverse
  t-structure on the bounded constructible complexes with coefficients in `k`,
  characterized by its stalk and costalk support conditions
  (`CoefficientPerverseModels.stalkSupport`, `CoefficientPerverseModels.costalkSupport`).
  The conditions determine it, so any two instances are equal
  (`CoefficientPerverseTheory.instSubsingleton`). `PerverseSheafTheory X` is its case
  `k = ℚ`. Its existence on every complex variety (Beilinson–Bernstein–Deligne)
  is not proved or requested in this module, which provides no instance: the
  constructions below assume it, through `[PerverseSheafTheory X]`.

Given that characterized theory, `PerverseSheaf` is its heart and
`perverseCohomology` is computed using Mathlib's truncations.

The sheaves are on `X(ℂ)` with its analytic topology. This is the topology
used for Betti local systems and the Hodge theoretic formulation of
decomposition. `ComplexAnalytification` supplies its underlying topological
space and the continuous maps induced by algebraic morphisms.

## References

* A. A. Beilinson, J. Bernstein and P. Deligne, *Faisceaux pervers*,
  Astérisque 100 (1982).
* M. A. A. de Cataldo and L. Migliorini, *The Hodge theory of algebraic maps*,
  Ann. Sci. École Norm. Sup. (4) 38 (2005), §§3.3, 3.6, 3.8.
  https://arxiv.org/abs/math/0306030
* Their 2009 survey, §2.3, equations (14) and (15).
  https://arxiv.org/abs/0712.0349
* A. Dimca, *Sheaves in Topology*, Chapters 2–4.
* The imported complex-point topology retains AxiomMath/Weil source paths,
  revision, Apache 2.0 attribution, and its modification notice in
  `MathlibExt/AlgebraicGeometry/ComplexAnalytification.lean`.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ComplexAnalytification

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace MathlibExt.AlgebraicGeometry.PerverseSheaves

/-- Schemes over the complex numbers. -/
abbrev ComplexScheme := Over (Spec (.of ℂ))

/-- A complex variety: `X.left` is a variety over `ℂ` for the structure
morphism `X.hom`, in the sense of `AlgebraicGeometry.IsVariety` (separated,
quasi-compact, locally of finite type and geometrically reduced). Over `ℂ`
geometric reducedness is reducedness (`IsComplexVariety.of_isReduced` and the
instance `IsComplexVariety.isReduced`). Components of different dimensions
are allowed. -/
abbrev IsComplexVariety (X : ComplexScheme) : Prop := IsVariety ℂ X.left

namespace IsComplexVariety

variable (X : ComplexScheme) [IsComplexVariety X]

instance isSeparated : IsSeparated X.hom :=
  IsVariety.isSeparated (k := ℂ) (X := X.left)

instance locallyOfFiniteType : LocallyOfFiniteType X.hom :=
  IsVariety.locallyOfFiniteType (k := ℂ) (X := X.left)

instance quasiCompact : QuasiCompact X.hom :=
  IsVariety.quasiCompact (k := ℂ) (X := X.left)

instance geometricallyReduced : GeometricallyReduced X.hom :=
  IsVariety.geometricallyReduced (k := ℂ) (X := X.left)

/-- A complex variety is reduced: base change along the identity of `Spec ℂ`. -/
instance isReduced : IsReduced X.left :=
  self_of_isIntegral_of_geometrically (f := X.hom)
    GeometricallyReduced.geometrically_isReduced

/-- A reduced separated scheme of finite type over `ℂ` is a complex variety:
over the perfect field `ℂ`, reducedness implies geometric reducedness. -/
theorem of_isReduced (X : ComplexScheme) [IsReduced X.left] [IsSeparated X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : IsComplexVariety X :=
  ⟨‹_›, ‹_›, ‹_›, GeometricallyReduced.of_isReduced_of_perfectField X.hom⟩

end IsComplexVariety

/-- A finite partition by smooth locally closed algebraic subvarieties.
No frontier or Whitney condition is imposed: this is the finite decomposition
into locally closed pieces that defines constructibility in de Cataldo–Migliorini
(2009), §1.5, not a stratification in the sense of their (2005), §3.2. An
arbitrary such partition need not be locally trivial along its pieces. -/
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

/-- The continuous inclusion of an open subspace: Mathlib's
`TopologicalSpace.Opens.inclusion'`, with the ambient space explicit. -/
abbrev openInclusion (Z : TopCat.{0}) (U : Opens Z) : TopCat.of U ⟶ Z :=
  U.inclusion'

end MathlibExt.AlgebraicGeometry.PerverseSheaves

namespace MathlibExt.AlgebraicGeometry.ConstructibleComplexes

open MathlibExt.AlgebraicGeometry.PerverseSheaves

/-- Sheaves of vector spaces over the coefficient field `k` on a space. -/
abbrev CoefficientSheaf (k : Type) [Field k] (Z : TopCat.{0}) :=
  TopCat.Sheaf (ModuleCat.{0} k) Z

/-- The derived category of sheaves with coefficients in `k`. -/
abbrev CoefficientDerived (k : Type) [Field k] (Z : TopCat.{0}) :=
  DerivedCategory (CoefficientSheaf k Z)

/-- Sheaf pushforward is additive. This is the only such instance; the
rational case is `k = ℚ`. -/
instance pushforward_additive (k : Type) [Field k] {Z W : TopCat.{0}} (f : Z ⟶ W) :
    (TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).Additive where
  map_add := by intro F G a b; rfl

/-- A finite-rank local system: around every point, the sheaf is isomorphic to
the constant sheaf of a finite-dimensional vector space. Finite-dimensional
stalks alone would not express the local-system condition. -/
def IsFiniteRankLocalSystem (k : Type) [Field k] (Z : TopCat.{0})
    (F : CoefficientSheaf k Z) : Prop :=
  ∀ x : Z, ∃ U : Opens Z, x ∈ U ∧
    ∃ V : ModuleCat.{0} k, FiniteDimensional k V ∧
      Nonempty ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (openInclusion Z U)).obj F ≅
        (constantSheaf (Opens.grothendieckTopology (TopCat.of U))
          (ModuleCat.{0} k)).obj V)

/-- The constant sheaf of a finite-dimensional vector space is a finite-rank
local system: its inverse image to an open subspace is the constant sheaf
there, by uniqueness of left adjoints to global sections. -/
theorem isFiniteRankLocalSystem_constantSheaf (k : Type) [Field k] (Z : TopCat.{0})
    (V : ModuleCat.{0} k) [FiniteDimensional k V] :
    IsFiniteRankLocalSystem k Z
      ((constantSheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} k)).obj V) := by
  intro x
  refine ⟨⊤, trivial, V, ‹_›, ⟨?_⟩⟩
  let a := (constantSheafAdj (Opens.grothendieckTopology Z) (ModuleCat.{0} k)
    (isTerminalTop (α := Opens Z))).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k)
        (openInclusion Z ⊤))
  let b := constantSheafAdj (Opens.grothendieckTopology (TopCat.of (⊤ : Opens Z)))
    (ModuleCat.{0} k) (isTerminalTop (α := Opens (TopCat.of (⊤ : Opens Z))))
  exact (a.leftAdjointUniq b).app V

/-- Bounded complexes with a common finite partition into smooth locally closed
subvarieties on each of which every cohomology sheaf restricts to a finite-rank
local system.
Source: de Cataldo–Migliorini (2009), §1.5; Dimca, *Sheaves in Topology*,
Chapter 4. -/
def boundedConstructible (k : Type) [Field k] (X : ComplexScheme) :
    ObjectProperty (CoefficientDerived k (space X)) := fun K ↦
  (∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j →
    IsZero ((DerivedCategory.homologyFunctor _ j).obj K)) ∧
  ∃ S : AlgebraicStratification X, ∀ a j,
    IsFiniteRankLocalSystem k (space (S.stratum a))
      ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (spaceMap (S.inclusion a))).obj
        ((DerivedCategory.homologyFunctor _ j).obj K))

end MathlibExt.AlgebraicGeometry.ConstructibleComplexes

namespace MathlibExt.AlgebraicGeometry.PerverseSheaves

/-- Sheaves of rational vector spaces on a topological space: the coefficient
sheaves at `k = ℚ`. -/
abbrev RationalSheaf (Z : TopCat.{0}) := ConstructibleComplexes.CoefficientSheaf ℚ Z

/-- The derived category of rational sheaves. -/
abbrev RationalDerived (Z : TopCat.{0}) := ConstructibleComplexes.CoefficientDerived ℚ Z

/-- The constant rational sheaf. -/
def rationalConstantSheaf (Z : TopCat.{0}) : RationalSheaf Z :=
  (constantSheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} ℚ)).obj
    (ModuleCat.of ℚ ℚ)

/-- Finite-rank rational local systems: `ConstructibleComplexes.IsFiniteRankLocalSystem`
at `k = ℚ`. -/
abbrev IsFiniteRankLocalSystem (Z : TopCat.{0}) (F : RationalSheaf Z) : Prop :=
  ConstructibleComplexes.IsFiniteRankLocalSystem ℚ Z F

/-- Bounded constructible rational complexes:
`ConstructibleComplexes.boundedConstructible` at `k = ℚ`.
Source: de Cataldo–Migliorini (2009), §1.5. -/
abbrev boundedConstructible (X : ComplexScheme) :
    ObjectProperty (RationalDerived (space X)) :=
  ConstructibleComplexes.boundedConstructible ℚ X

/-- Zariski dimension of a support bounded by an integer. A negative bound
forces the support to be empty, implementing `dim ∅ = -∞`. -/
def SupportDimensionLE (X : ComplexScheme) (s : Set X.left) (d : ℤ) : Prop :=
  if d < 0 then s = ∅ else
    topologicalKrullDim (closure s) ≤ ((d.toNat : ℕ∞) : WithBot ℕ∞)

end MathlibExt.AlgebraicGeometry.PerverseSheaves

namespace MathlibExt.AlgebraicGeometry.CoefficientPerverseModels

/-! The support conditions and the middle perverse structure over an arbitrary coefficient field.
They are stated here so that the rational theory below is literally their case `k = ℚ`; the rest of
the coefficient perverse API is in `MathlibExt.AlgebraicGeometry.CoefficientPerverseModels`. -/

open MathlibExt.AlgebraicGeometry.PerverseSheaves

variable (k : Type) [Field k] (X : ComplexScheme)

/-- The algebraic image of the nonzero stalks of the `j`th cohomology sheaf. -/
def stalkSupport (K : ConstructibleComplexes.CoefficientDerived k (space X)) (j : ℤ) :
    Set X.left :=
  ComplexPoints.schemePoint ''
    {p : space X | ¬ IsZero
      (((DerivedCategory.homologyFunctor _ j).obj K).presheaf.stalk p)}

/-- The skyscraper with coefficients in `k` at a complex point, placed in cohomological
degree zero. -/
def coefficientSkyscraper (p : space X) :
    ConstructibleComplexes.CoefficientDerived k (space X) := by
  classical
  exact (DerivedCategory.singleFunctor _ 0).obj (skyscraperSheaf p (ModuleCat.of k k))

/-- The algebraic image of nonzero `j`th costalk cohomology.
For a closed point `iₚ`, derived adjunction identifies
`Hom(iₚ* k, K[j])` with `Hʲ(iₚ! K)`. The skyscraper is unshifted and the
target is shifted by `+j`. Source: de Cataldo–Migliorini (2009), §2.3. -/
def costalkSupport (K : ConstructibleComplexes.CoefficientDerived k (space X)) (j : ℤ) :
    Set X.left :=
  ComplexPoints.schemePoint ''
    {p : space X | ¬ Subsingleton (coefficientSkyscraper k X p ⟶ K⟦j⟧)}

/-- The data of the middle perverse t-structure with coefficients in `k` on a complex
variety, characterized by its support and cosupport conditions: `K` is in
`ᵖD^{≤ m}` iff `dim supp Hʲ(K) ≤ m - j` for all `j`, and in `ᵖD^{≥ m}` iff
`dim {x | Hʲ(iₓ^! K) ≠ 0} ≤ j - m` for all `j`. These conditions determine the
t-structure (`CoefficientPerverseTheory.instSubsingleton`). Its existence on every
complex variety is the theorem of Beilinson–Bernstein–Deligne; no instance is
provided here.
Source: de Cataldo–Migliorini (2005), §§3.3, 3.6; (2009), §2.3, (14), (15). -/
class CoefficientPerverseTheory [IsComplexVariety X] where
  /-- Closure of bounded constructible complexes under shifts and triangles. -/
  [isTriangulated : (ConstructibleComplexes.boundedConstructible k X).IsTriangulated]
  /-- The middle perverse t-structure on the bounded constructible category. -/
  t : CategoryTheory.Triangulated.TStructure
    (ConstructibleComplexes.boundedConstructible k X).FullSubcategory
  /-- Stalk support condition in every degree. -/
  le_iff : ∀ K m, t.le m K ↔ ∀ j,
    SupportDimensionLE X (stalkSupport k X K.obj j) (m - j)
  /-- Costalk support condition in every degree. -/
  ge_iff : ∀ K m, t.ge m K ↔ ∀ j,
    SupportDimensionLE X (costalkSupport k X K.obj j) (j - m)

attribute [instance] CoefficientPerverseTheory.isTriangulated

/-- The support and cosupport conditions determine the t-structure, so a
complex variety has at most one `CoefficientPerverseTheory` for each coefficient field. -/
instance CoefficientPerverseTheory.instSubsingleton [IsComplexVariety X] :
    Subsingleton (CoefficientPerverseTheory k X) where
  allEq := by
    rintro ⟨t₁, hle₁, hge₁⟩ ⟨t₂, hle₂, hge₂⟩
    have hle : t₁.le = t₂.le :=
      funext fun m ↦ funext fun K ↦ propext ((hle₁ K m).trans (hle₂ K m).symm)
    have hge : t₁.ge = t₂.ge :=
      funext fun m ↦ funext fun K ↦ propext ((hge₁ K m).trans (hge₂ K m).symm)
    have ht : t₁ = t₂ := by
      cases t₁
      cases t₂
      cases hle
      cases hge
      rfl
    subst ht
    rfl

end MathlibExt.AlgebraicGeometry.CoefficientPerverseModels

namespace MathlibExt.AlgebraicGeometry.PerverseSheaves

/-- The rational middle perverse t-structure: `CoefficientPerverseModels.CoefficientPerverseTheory`
at `k = ℚ`. Its existence on every complex variety is the theorem of
Beilinson–Bernstein–Deligne; no instance is provided here. -/
abbrev PerverseSheafTheory (X : ComplexScheme) [IsComplexVariety X] :=
  CoefficientPerverseModels.CoefficientPerverseTheory ℚ X

/-- The characterized middle perverse t-structure. -/
def perverseTStructure (X : ComplexScheme) [IsComplexVariety X]
    [PerverseSheafTheory X] :
    CategoryTheory.Triangulated.TStructure
      (boundedConstructible X).FullSubcategory :=
  CoefficientPerverseModels.CoefficientPerverseTheory.t (k := ℚ) (X := X)

/-- The category of rational perverse sheaves, as the heart of the
characterized middle perverse t-structure. -/
abbrev PerverseSheaf (X : ComplexScheme) [IsComplexVariety X]
    [PerverseSheafTheory X] :=
  (perverseTStructure X).heart.FullSubcategory

/-- The inclusion of perverse sheaves into the derived category of rational
sheaves: the inclusion of the heart, followed by that of the bounded
constructible complexes. -/
def perverseAmbient (X : ComplexScheme) [IsComplexVariety X] [PerverseSheafTheory X] :
    PerverseSheaf X ⥤ RationalDerived (space X) :=
  (perverseTStructure X).heart.ι ⋙ (boundedConstructible X).ι

instance perverseAmbient_faithful (X : ComplexScheme) [IsComplexVariety X]
    [PerverseSheafTheory X] : (perverseAmbient X).Faithful := by
  dsimp only [perverseAmbient]
  infer_instance

instance perverseAmbient_full (X : ComplexScheme) [IsComplexVariety X]
    [PerverseSheafTheory X] : (perverseAmbient X).Full := by
  dsimp only [perverseAmbient]
  infer_instance

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

end MathlibExt.AlgebraicGeometry.PerverseSheaves

end
