/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PerverseSheaves
public import MathlibExt.AlgebraicGeometry.ProjectiveDirectImage

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
`PerverseSheavesWanted.lean`. This file uses the public characterized
interface `[PerverseSheafTheory Y]` supplied by
`MathlibExt/AlgebraicGeometry/PerverseSheaves.lean`. The projectivity and
normalized direct-image definitions, with their source attribution, are in
`MathlibExt/AlgebraicGeometry/ProjectiveDirectImage.lean`.

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

/-- Bounded algebraic constructibility of the projective direct image.
Source: de Cataldo–Migliorini (2005), §§3.2–3.3. -/
public theorem_wanted normalizedDirectImage_boundedConstructible
    (X Y : ComplexScheme) [IsComplexVariety X] [IsComplexVariety Y]
    (f : X ⟶ Y) (n : ℕ) [SmoothOfRelativeDimension n X.hom]
    (hX : IsProjectiveOverC X) (hY : IsProjectiveOverC Y) :
    boundedConstructible Y (normalizedDirectImage X Y f n)

/-- De Cataldo–Migliorini's decomposition theorem for a smooth projective
source and a projective target. The finite set includes every nonzero perverse
degree, and the summands have the required shifts `-i`.
Source: *The Hodge theory of algebraic maps*, Theorem 2.1.1(b). -/
public theorem_wanted deCataldoMigliorini_decomposition
    (X Y : ComplexScheme) [IsComplexVariety X] [IsComplexVariety Y]
    [PerverseSheafTheory Y]
    (f : X ⟶ Y) (n : ℕ) [SmoothOfRelativeDimension n X.hom]
    (hX : IsProjectiveOverC X) (hY : IsProjectiveOverC Y) :
    let K : (boundedConstructible Y).FullSubcategory :=
      ⟨normalizedDirectImage X Y f n,
        ❰normalizedDirectImage_boundedConstructible❱ X Y f n hX hY⟩
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
    let K : (boundedConstructible Y).FullSubcategory :=
      ⟨normalizedDirectImage X Y f n,
        ❰normalizedDirectImage_boundedConstructible❱ X Y f n hX hY⟩
    ∀ j : ℤ, IsSemisimplePerverse (perverseTStructure Y)
      (perverseCohomology Y j K)

end

end MathlibExt.AlgebraicGeometry.DeCataldoMiglioriniDecompositionWanted
