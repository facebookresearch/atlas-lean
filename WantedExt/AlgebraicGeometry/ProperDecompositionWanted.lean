/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.ProperDecomposition

/-!
# Proper-map decomposition, amplitude and semismall supports

This expands the projective-source request of PR1970 to general smooth
sources with a proper map, and adds actual self-fiber-product amplitude and
fiber/stalk support conditions. The characterized perverse theory and image
constructibility are explicit external inputs; no C1/C2/C4 goal is imported.

References: BBD (1982), Theorem 6.2.5; de Cataldo–Migliorini,
https://arxiv.org/abs/0712.0349, Theorem 1.6.1, §§3.3.2 and 4.2.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.ProperDecompositionWanted

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry MathlibExt.AlgebraicGeometry
open ComplexAnalytification PerverseSheaves ProperDecomposition

attribute [local instance] HasDerivedCategory.standard

/-- BBD decomposition for a proper map from a smooth pure-dimensional complex
variety. The source need not be projective or proper over `C`. -/
public theorem_wanted proper_decomposition (X Y : ComplexScheme)
    [IsComplexVariety X] [IsComplexVariety Y] [PerverseSheafTheory Y]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] (f : X ⟶ Y) [IsProper f.left]
    (hK : boundedConstructible Y (ProperDecomposition.normalizedDirectImage X Y f d)) :
    ∃ s : Finset ℤ,
      Nonempty (constructibleImage X Y f d hK ≅
        biproduct (fun i : s ↦
          (perverseCohomology Y (i : ℤ) (constructibleImage X Y f d hK)).obj⟦-(i : ℤ)⟧))

/-- Every perverse cohomology object of that proper image is semisimple in
the actual perverse heart, not in the category of ordinary sheaves. -/
public theorem_wanted proper_semisimplicity (X Y : ComplexScheme)
    [IsComplexVariety X] [IsComplexVariety Y] [PerverseSheafTheory Y]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] (f : X ⟶ Y) [IsProper f.left]
    (hK : boundedConstructible Y (ProperDecomposition.normalizedDirectImage X Y f d))
    (i : ℤ) :
    IsSemisimplePerverse (perverseTStructure Y)
      (perverseCohomology Y i (constructibleImage X Y f d hK))

/-- The amplitude is controlled by `dim(X ×_Y X) - dim X`. -/
public theorem_wanted proper_amplitude (X Y : ComplexScheme)
    [IsComplexVariety X] [IsComplexVariety Y] [PerverseSheafTheory Y]
    (d r : ℕ) [SmoothOfRelativeDimension d X.hom] (f : X ⟶ Y) [IsProper f.left]
    (hK : boundedConstructible Y (ProperDecomposition.normalizedDirectImage X Y f d))
    (hdefect : DefectLE f d r) (i : ℤ) (hi : i < -(r : ℤ) ∨ (r : ℤ) < i) :
    IsZero (perverseCohomology Y i (constructibleImage X Y f d hK)).obj

/-- A nonzero normalized stalk of a perverse summand over a semismall
stratum can occur only at equality in the relevance inequality.

Here `s` is the stratum dimension used in the degree `-s`; the supplied
fiber dimension is measured on the actual scheme fiber. This is the local
support condition underlying relevant strata in the semismall theorem. -/
public theorem_wanted semismall_support_relevance (X Y : ComplexScheme)
    [IsComplexVariety X] [IsComplexVariety Y] [PerverseSheafTheory Y]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] (f : X ⟶ Y) [IsProper f.left]
    (P : PerverseSheaf Y) [Simple P]
    (a : (ProperDecomposition.perverseAmbient Y).obj P ⟶
      ProperDecomposition.normalizedDirectImage X Y f d) [IsSplitMono a]
    (S : ComplexScheme) [IsComplexVariety S] (s n : ℕ)
    [SmoothOfRelativeDimension s S.hom] (i : S ⟶ Y) [IsImmersion i.left]
    (p : space S)
    (hstalk : ¬ IsZero
      (((DerivedCategory.homologyFunctor _ (-(s : ℤ))).obj
        ((ProperDecomposition.perverseAmbient Y).obj P)).presheaf.stalk ((spaceMap i) p)))
    (hfiber : topologicalKrullDim (pointFiber f ((spaceMap i) p)) =
      ((n : ℕ∞) : WithBot ℕ∞))
    (hsemismall : 2 * n + s ≤ d) : 2 * n + s = d

end WantedExt.AlgebraicGeometry.ProperDecompositionWanted
