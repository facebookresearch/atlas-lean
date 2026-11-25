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

For a proper map `f : X ⟶ Y` from a smooth complex variety of dimension `d`,
request the decomposition theorem for `Rf_* ℚ_X[d]` (the source need not be
projective or proper over `ℂ`), the semisimplicity of its perverse cohomology,
the vanishing of perverse cohomology outside the semismall defect, and the
equality case of the relevance inequality for supports of perverse summands.

The image is placed in the bounded constructible category by a request for
its constructibility, the special case of
`ConstructibleComplexesWanted.constructible_proper_pushforward` applied to
`ConstructibleComplexesWanted.constructible_constantSheaf`, restated here
because wanted declarations are private to their file. The characterized
perverse t-structure `PerverseSheafTheory Y` is an explicit input; it is unique
when it exists.

References: A. Beilinson, J. Bernstein and P. Deligne, *Faisceaux pervers*,
Astérisque 100 (1982), Theorem 6.2.5; M. A. de Cataldo and L. Migliorini,
https://arxiv.org/abs/0712.0349, Theorem 1.6.1, §§3.3.2 and 4.2.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.ProperDecompositionWanted

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry MathlibExt.AlgebraicGeometry
open ComplexAnalytification PerverseSheaves ProperDecomposition

attribute [local instance] HasDerivedCategory.standard

/-- The proper direct image `Rf_* ℚ_X[d]` of the constant sheaf is bounded
constructible: the constant sheaf of a complex variety is constructible, and
proper direct image preserves bounded constructibility. -/
public theorem_wanted normalizedDirectImage_constructible (X Y : ComplexScheme)
    [IsComplexVariety X] [IsComplexVariety Y] (d : ℕ) (f : X ⟶ Y)
    [IsProper f.left] :
    boundedConstructible Y (ConstructibleComplexes.normalizedDirectImage ℚ X Y f d)

/-- The image `Rf_* ℚ_X[d]` of a proper map of complex varieties, as an object
of the bounded constructible category. -/
public def_wanted properImage (X Y : ComplexScheme) [IsComplexVariety X]
    [IsComplexVariety Y] (d : ℕ) (f : X ⟶ Y) [IsProper f.left] :
    (boundedConstructible Y).FullSubcategory :=
  constructibleImage X Y f d (❰normalizedDirectImage_constructible❱ X Y d f)

/-- BBD decomposition for a proper map from a smooth pure-dimensional complex
variety. The source need not be projective or proper over `ℂ`. -/
public theorem_wanted proper_decomposition (X Y : ComplexScheme)
    [IsComplexVariety X] [IsComplexVariety Y] [PerverseSheafTheory Y]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] (f : X ⟶ Y) [IsProper f.left] :
    ∃ s : Finset ℤ,
      Nonempty (❰properImage❱ X Y d f ≅
        biproduct (fun i : s ↦
          (perverseCohomology Y (i : ℤ) (❰properImage❱ X Y d f)).obj⟦-(i : ℤ)⟧))

/-- Every perverse cohomology object of that proper image is semisimple in
the actual perverse heart, not in the category of ordinary sheaves. -/
public theorem_wanted proper_semisimplicity (X Y : ComplexScheme)
    [IsComplexVariety X] [IsComplexVariety Y] [PerverseSheafTheory Y]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] (f : X ⟶ Y) [IsProper f.left]
    (i : ℤ) :
    IsSemisimplePerverse (perverseTStructure Y)
      (perverseCohomology Y i (❰properImage❱ X Y d f))

/-- The perverse amplitude is bounded by the defect of semismallness
`dim (X ×_Y X) - dim X`: perverse cohomology vanishes in degrees outside
`[-r, r]` when `dim (X ×_Y X) ≤ d + r`. -/
public theorem_wanted proper_amplitude (X Y : ComplexScheme)
    [IsComplexVariety X] [IsComplexVariety Y] [PerverseSheafTheory Y]
    (d r : ℕ) [SmoothOfRelativeDimension d X.hom] (f : X ⟶ Y) [IsProper f.left]
    (hdefect : DefectLE f d r) (i : ℤ) (hi : i < -(r : ℤ) ∨ (r : ℤ) < i) :
    IsZero (perverseCohomology Y i (❰properImage❱ X Y d f)).obj

/-- A nonzero normalized stalk of a perverse summand over a semismall
stratum can occur only at equality in the relevance inequality.

Here `s` is the stratum dimension used in the degree `-s`; the supplied
fiber dimension is measured on the actual scheme fiber. This is the local
support condition underlying relevant strata in the semismall theorem. -/
public theorem_wanted semismall_support_relevance (X Y : ComplexScheme)
    [IsComplexVariety X] [IsComplexVariety Y] [PerverseSheafTheory Y]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] (f : X ⟶ Y) [IsProper f.left]
    (P : PerverseSheaf Y) [Simple P]
    (a : (perverseAmbient Y).obj P ⟶
      ConstructibleComplexes.normalizedDirectImage ℚ X Y f d) [IsSplitMono a]
    (S : ComplexScheme) [IsComplexVariety S] (s n : ℕ)
    [SmoothOfRelativeDimension s S.hom] (i : S ⟶ Y) [IsImmersion i.left]
    (p : space S)
    (hstalk : ¬ IsZero
      (((DerivedCategory.homologyFunctor _ (-(s : ℤ))).obj
        ((perverseAmbient Y).obj P)).presheaf.stalk ((spaceMap i) p)))
    (hfiber : topologicalKrullDim (pointFiber f ((spaceMap i) p)) =
      ((n : ℕ∞) : WithBot ℕ∞))
    (hsemismall : 2 * n + s ≤ d) : 2 * n + s = d

end WantedExt.AlgebraicGeometry.ProperDecompositionWanted
