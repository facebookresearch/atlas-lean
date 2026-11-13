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
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import
  Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import
  WantedExt.AlgebraicGeometry.PerverseSheaves.PerverseSheavesWanted

@[expose] public section

/-!
# De Cataldo–Migliorini's decomposition and semisimplicity theorems

For an algebraic map `f : X → Y` of complex projective varieties, with `X`
smooth of pure dimension `n`, request a finite splitting

`Rf_* ℚ_X[n] ≅ ⨁ᵢ ᵖHⁱ(Rf_* ℚ_X[n])[-i]`

and semisimplicity of every perverse cohomology object. These are parts (b)
and (c) of Theorem 2.1.1 in de Cataldo–Migliorini's Hodge theoretic treatment.
The splitting is an existence statement.

The independent construction request for perverse sheaves is in
`PerverseSheaves/PerverseSheavesWanted.lean`. This file uses its public
characterized interface `[PerverseSheafTheory Y]`. The ambient rational
sheaf/derived categories, bounded constructibility, perverse cohomology,
and semisimplicity definitions are in `PerverseSheaves/Basic.lean`.

The normalized direct image uses Mathlib's derived pushforward on the
analytic topological spaces of complex points. In particular, `ℚ_X[n]`
places the rational constant sheaf in cohomological degree `-n`.

## Reference

M. A. A. de Cataldo and L. Migliorini, *The Hodge theory of algebraic maps*,
Ann. Sci. École Norm. Sup. (4) 38 (2005), no. 5, 693–750,
Theorem 2.1.1(b,c). https://arxiv.org/abs/math/0306030
-/

namespace MathlibExt.AlgebraicGeometry.DeCataldoMiglioriniDecompositionWanted

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open ComplexAnalytification PerverseSheaves

noncomputable section

attribute [local instance] HasDerivedCategory.standard

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

/-- De Cataldo–Migliorini's decomposition theorem for a smooth projective
source and a projective target. The finite set includes every nonzero perverse
degree, and the summands have the required shifts `-i`.
Source: *The Hodge theory of algebraic maps*, Theorem 2.1.1(b). -/
public theorem_wanted deCataldoMigliorini_decomposition
    (X Y : ComplexScheme) [IsComplexVariety X] [IsComplexVariety Y]
    [PerverseSheafTheory Y]
    (f : X ⟶ Y) (n : ℕ) [SmoothOfRelativeDimension n X.hom]
    (hX : IsProjectiveOverC X) (hY : IsProjectiveOverC Y) :
    let K := ❰constructibleDirectImage❱ X Y f n hX hY
    ∃ degrees : Finset ℤ,
      (∀ j : ℤ, j ∉ degrees →
        IsZero ((perverseCohomology Y j K).obj)) ∧
      Nonempty (K ≅ biproduct
        (fun j : degrees ↦ (perverseCohomology Y (j : ℤ) K).obj⟦-(j : ℤ)⟧))

/-- Every perverse cohomology object of the direct image is a finite sum
of simple perverse sheaves. By the classification in §3.8 of the source,
these are intersection complexes of simple finite-rank rational local systems
on smooth locally closed strata.
Source: *The Hodge theory of algebraic maps*, Theorem 2.1.1(c). -/
public theorem_wanted deCataldoMigliorini_semisimplicity
    (X Y : ComplexScheme) [IsComplexVariety X] [IsComplexVariety Y]
    [PerverseSheafTheory Y]
    (f : X ⟶ Y) (n : ℕ) [SmoothOfRelativeDimension n X.hom]
    (hX : IsProjectiveOverC X) (hY : IsProjectiveOverC Y) :
    let K := ❰constructibleDirectImage❱ X Y f n hX hY
    ∀ j : ℤ, IsSemisimplePerverse (perverseTStructure Y)
      (perverseCohomology Y j K)

end

end MathlibExt.AlgebraicGeometry.DeCataldoMiglioriniDecompositionWanted
