/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The projectivity definitions are adapted from
`WantedExt/AlgebraicGeometry/TopologicalReconstructionWanted.lean` in ATLAS
at commit 841d5b685836b986f0bb29cd63fd2300f957e849. That file attributes
`LeanEval.AlgebraicGeometry.TopologicalReconstruction` in leanprover/lean-eval
at commit 38361be884302c7edce1908c4aef8296eb2cb27e, distributed under the
Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).

Modification notice: renamed the graded structure morphism, specialized the
projectivity predicate to schemes over `ℂ`, and used `n + 1` homogeneous
coordinates for `ℙⁿ`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import
  Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sheaves.Abelian
public import MathlibExt.AlgebraicGeometry.ComplexAnalytification

@[expose] public section

/-!
# De Cataldo–Migliorini's decomposition and semisimplicity theorems

For an algebraic map `f : X → Y` of complex projective varieties, with `X`
smooth of pure dimension `n`, the rational direct image has a finite splitting

`Rf_* ℚ_X[n] ≅ ⨁ᵢ ᵖHⁱ(Rf_* ℚ_X[n])[-i]`,

and every perverse cohomology object is semisimple. These are parts (b) and (c)
of Theorem 2.1.1 in de Cataldo–Migliorini's Hodge theoretic treatment.
The splitting is an existence statement; no canonical choice is specified.

The ambient derived category, rational constant sheaf, derived pushforward,
finite sums, and simple-object predicate use Mathlib. Algebraic constructibility
is defined by finite smooth algebraic strata and local finite-rank triviality.
The deferred middle perverse t-structure is characterized by stalk and costalk
dimension inequalities, rather than by an arbitrary choice of t-structure.
Costalk vanishing is expressed by derived homs from the rational skyscraper
sheaf. The wanted closure and constructibility results are infrastructure
obligations; the decomposition and semisimplicity conclusions are separate.

## References

* M. A. A. de Cataldo and L. Migliorini, *The Hodge theory of algebraic maps*,
  Ann. Sci. École Norm. Sup. (4) 38 (2005), no. 5, 693–750,
  Theorem 2.1.1(b,c), §§3.3, 3.6, 3.8.
  https://arxiv.org/abs/math/0306030
* M. A. A. de Cataldo and L. Migliorini, *The decomposition theorem, perverse
  sheaves and the topology of algebraic maps*, Bull. Amer. Math. Soc. 46
  (2009), 535–633, §2.3, equations (14) and (15), for the stalk/costalk
  dimension characterization. https://arxiv.org/abs/0712.0349
* The complex-point topology in the imported infrastructure is adapted from
  `AxiomMath/Weil`; its source paths, revision, license, and modification notice
  are recorded in `MathlibExt/AlgebraicGeometry/ComplexAnalytification.lean`.
-/

namespace MathlibExt.AlgebraicGeometry.DeCataldoMiglioriniDecompositionWanted

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

/-- The structure morphism of the projective spectrum of a graded algebra.
This is the same projective-over-a-field construction used by
`WantedExt/AlgebraicGeometry/TopologicalReconstructionWanted.lean`. -/
def gradedProjToSpec {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] :
    Proj 𝒜 ⟶ Spec (.of R) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap ..))

/-- Projectivity over `ℂ`, expressed by a closed immersion into some `ℙⁿ_ℂ`.
The equation requires the immersion to respect the structure morphism. -/
def IsProjectiveOverC (X : ComplexScheme) : Prop :=
  let := @MvPolynomial.gradedAlgebra
  ∃ (n : ℕ)
    (i : X.left ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ)),
    IsClosedImmersion i ∧ X.hom = i ≫ gradedProjToSpec _

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

/-- Closure of bounded algebraically constructible complexes under shifts
and distinguished triangles. Source: de Cataldo–Migliorini (2005), §3.3. -/
public instance_wanted boundedConstructible_isTriangulated (X : ComplexScheme)
    [IsComplexVariety X] : (boundedConstructible X).IsTriangulated

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

/-- A middle perverse t-structure characterized by the support and cosupport
conditions. These fields specify the construction, without assuming a
decomposition or semisimplicity result.
Source: de Cataldo–Migliorini (2005), §3.6; (2009), §2.3, (14),(15). -/
structure MiddlePerverseTStructureData (X : ComplexScheme)
    [IsComplexVariety X] [(boundedConstructible X).IsTriangulated] where
  /-- The t-structure on the actual bounded constructible category. -/
  t : CategoryTheory.Triangulated.TStructure
    (boundedConstructible X).FullSubcategory
  /-- Stalk support condition in every degree. -/
  le_iff : ∀ K m, t.le m K ↔ ∀ j,
    SupportDimensionLE X (stalkSupport X K.obj j) (m - j)
  /-- Costalk support condition in every degree. -/
  ge_iff : ∀ K m, t.ge m K ↔ ∀ j,
    SupportDimensionLE X (costalkSupport X K.obj j) (j - m)

/-- The middle perverse t-structure with its defining dimension conditions.
Source: de Cataldo–Migliorini (2005), §3.6. -/
public def_wanted middlePerverseTStructure (X : ComplexScheme)
    [IsComplexVariety X] : MiddlePerverseTStructureData X

-- Batteries reconstructs wanted dependency binders through the pretty printer.
-- Keep the sheaf-category instance expressions complete during that conversion.
set_option linter.style.setOption false in
set_option pp.maxSteps 1000000 in
set_option pp.deepTerms.threshold 100000 in
set_option pp.proofs.threshold 100000 in
/-- The t-structure component of the characterized construction. -/
public def_wanted perverseTStructure (X : ComplexScheme)
    [IsComplexVariety X] :
    CategoryTheory.Triangulated.TStructure
      (boundedConstructible X).FullSubcategory :=
  (❰middlePerverseTStructure❱ X).t

set_option linter.style.setOption false in
set_option pp.maxSteps 1000000 in
set_option pp.deepTerms.threshold 100000 in
set_option pp.proofs.threshold 100000 in
/-- Heart-valued perverse cohomology: first shift by `j`, then take the
degree-zero slice of the middle perverse t-structure. -/
public def_wanted perverseCohomology (X : ComplexScheme)
    [IsComplexVariety X] :
    ∀ (j : ℤ) (K : (boundedConstructible X).FullSubcategory),
      (❰perverseTStructure❱ X).heart.FullSubcategory :=
  fun j K ↦ ⟨((❰perverseTStructure❱ X).truncGELE 0 0).obj (K⟦j⟧), by
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

/-- The actual derived direct image of the rational constant sheaf placed
in degree `-n`, namely `Rf_* ℚ_X[n]`. -/
def normalizedDirectImage (X Y : ComplexScheme) (f : X ⟶ Y) (n : ℕ) :
    RationalDerived (space Y) :=
  DerivedCategory.Plus.ι.obj
    (((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ)
      (spaceMap f)).rightDerivedFunctorPlus).obj
        ((DerivedCategory.Plus.singleFunctor (RationalSheaf (space X))
          (-(n : ℤ))).obj (rationalConstantSheaf (space X))))

/-- Bounded algebraic constructibility of the projective direct image.
Source: de Cataldo–Migliorini (2005), §§3.2–3.3. -/
public theorem_wanted normalizedDirectImage_boundedConstructible
    (X Y : ComplexScheme) [IsComplexVariety X] [IsComplexVariety Y]
    (f : X ⟶ Y) (n : ℕ) [SmoothOfRelativeDimension n X.hom]
    (hX : IsProjectiveOverC X) (hY : IsProjectiveOverC Y) :
    boundedConstructible Y (normalizedDirectImage X Y f n)

/-- The same actual direct image, packaged in the bounded constructible
full subcategory using the preceding constructibility obligation. -/
public def_wanted constructibleDirectImage
    (X Y : ComplexScheme) [IsComplexVariety X] [IsComplexVariety Y]
    (f : X ⟶ Y) (n : ℕ) [SmoothOfRelativeDimension n X.hom]
    (hX : IsProjectiveOverC X) (hY : IsProjectiveOverC Y) :
    (boundedConstructible Y).FullSubcategory :=
  ⟨normalizedDirectImage X Y f n,
    ❰normalizedDirectImage_boundedConstructible❱ X Y f n hX hY⟩

set_option linter.style.setOption false in
set_option pp.maxSteps 1000000 in
set_option pp.deepTerms.threshold 100000 in
set_option pp.proofs.threshold 100000 in
/-- De Cataldo–Migliorini's decomposition theorem for a smooth projective
source and a projective target. The finite set includes every nonzero perverse
degree, and the summands have the required shifts `-i`.
Source: *The Hodge theory of algebraic maps*, Theorem 2.1.1(b). -/
public theorem_wanted deCataldoMigliorini_decomposition
    (X Y : ComplexScheme) [IsComplexVariety X] [IsComplexVariety Y]
    (f : X ⟶ Y) (n : ℕ) [SmoothOfRelativeDimension n X.hom]
    (hX : IsProjectiveOverC X) (hY : IsProjectiveOverC Y) :
    let K := ❰constructibleDirectImage❱ X Y f n hX hY
    ∃ degrees : Finset ℤ,
      (∀ j : ℤ, j ∉ degrees →
        IsZero ((❰perverseCohomology❱ Y j K).obj)) ∧
      Nonempty (K ≅ biproduct
        (fun j : degrees ↦ (❰perverseCohomology❱ Y (j : ℤ) K).obj⟦-(j : ℤ)⟧))

set_option linter.style.setOption false in
set_option pp.maxSteps 1000000 in
set_option pp.deepTerms.threshold 100000 in
set_option pp.proofs.threshold 100000 in
/-- Every perverse cohomology object of the direct image is a finite sum
of simple perverse sheaves. By the classification in §3.8 of the source,
these are intersection complexes of simple finite-rank rational local systems
on smooth locally closed strata.
Source: *The Hodge theory of algebraic maps*, Theorem 2.1.1(c). -/
public theorem_wanted deCataldoMigliorini_semisimplicity
    (X Y : ComplexScheme) [IsComplexVariety X] [IsComplexVariety Y]
    (f : X ⟶ Y) (n : ℕ) [SmoothOfRelativeDimension n X.hom]
    (hX : IsProjectiveOverC X) (hY : IsProjectiveOverC Y) :
    let K := ❰constructibleDirectImage❱ X Y f n hX hY
    ∀ j : ℤ, IsSemisimplePerverse (❰perverseTStructure❱ Y)
      (❰perverseCohomology❱ Y j K)

end

end MathlibExt.AlgebraicGeometry.DeCataldoMiglioriniDecompositionWanted
