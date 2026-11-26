/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.PerverseSheaves

@[expose] public section

/-! # Tests for `MathlibExt.AlgebraicGeometry.PerverseSheaves` -/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ComplexAnalytification
open MathlibExt.AlgebraicGeometry.PerverseSheaves

namespace MathlibExtTest.AlgebraicGeometry.PerverseSheaves

/-- The point `Spec ℂ` as a scheme over `ℂ`. -/
abbrev point : ComplexScheme := Over.mk (𝟙 (Spec (.of ℂ)))

/-- The point is a complex variety, built from its reducedness. -/
instance : IsComplexVariety point :=
  have : IsReduced point.left := inferInstanceAs (IsReduced (Spec (.of ℂ)))
  have : IsSeparated point.hom := inferInstanceAs (IsSeparated (𝟙 (Spec (.of ℂ))))
  have : LocallyOfFiniteType point.hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of ℂ))))
  have : QuasiCompact point.hom := inferInstanceAs (QuasiCompact (𝟙 (Spec (.of ℂ))))
  IsComplexVariety.of_isReduced point

/-- An `IsVariety ℂ` instance on a scheme over `ℂ` is an `IsComplexVariety`
instance on the bundled scheme: the two notions are the same class. -/
example (Y : Scheme.{0}) [Y.Over (Spec (.of ℂ))] [h : IsVariety ℂ Y] :
    IsComplexVariety (OverClass.asOver Y (Spec (.of ℂ))) :=
  h

/-- A complex variety is reduced, separated and of finite type over `ℂ`. -/
example (X : ComplexScheme) [IsComplexVariety X] :
    IsReduced X.left ∧ IsSeparated X.hom ∧ LocallyOfFiniteType X.hom ∧
      QuasiCompact X.hom :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The rational notions are the coefficient-generic ones at `k = ℚ`. -/
example (Z : TopCat.{0}) (F : RationalSheaf Z) :
    IsFiniteRankLocalSystem Z F ↔
      MathlibExt.AlgebraicGeometry.ConstructibleComplexes.IsFiniteRankLocalSystem ℚ Z F :=
  Iff.rfl

example (X : ComplexScheme) :
    boundedConstructible X =
      MathlibExt.AlgebraicGeometry.ConstructibleComplexes.boundedConstructible ℚ X :=
  rfl

/-- A single generic instance makes rational sheaf pushforward additive. -/
example {Z W : TopCat.{0}} (f : Z ⟶ W) :
    (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).Additive :=
  inferInstance

/-- The constant rational sheaf is a finite-rank rational local system. -/
example (Z : TopCat.{0}) : IsFiniteRankLocalSystem Z (rationalConstantSheaf Z) :=
  MathlibExt.AlgebraicGeometry.ConstructibleComplexes.isFiniteRankLocalSystem_constantSheaf
    ℚ Z _

/-- `openInclusion` is Mathlib's inclusion of an open subspace. -/
example (Z : TopCat.{0}) (U : Opens Z) : openInclusion Z U = U.inclusion' := rfl

/-- A negative dimension bound forces an empty support. -/
example (X : ComplexScheme) : SupportDimensionLE X ∅ (-1) := by
  simp [SupportDimensionLE]

example (X : ComplexScheme) {s : Set X.left} (hs : s.Nonempty) :
    ¬ SupportDimensionLE X s (-1) := by
  simp [SupportDimensionLE, hs.ne_empty]

/-- The characterized perverse theory is unique. -/
example (X : ComplexScheme) [IsComplexVariety X] (T₁ T₂ : PerverseSheafTheory X) :
    T₁ = T₂ :=
  Subsingleton.elim _ _

/-- Perverse cohomology is the degree-zero truncation of the shifted complex. -/
example (X : ComplexScheme) [IsComplexVariety X] [PerverseSheafTheory X] (j : ℤ)
    (K : (boundedConstructible X).FullSubcategory) :
    (perverseCohomology X j K).obj = ((perverseTStructure X).truncGELE 0 0).obj (K⟦j⟧) :=
  rfl

/-- Perverse sheaves form a full subcategory of the derived category. -/
example (X : ComplexScheme) [IsComplexVariety X] [PerverseSheafTheory X] :
    (perverseAmbient X).Full ∧ (perverseAmbient X).Faithful :=
  ⟨inferInstance, inferInstance⟩

example (X : ComplexScheme) [IsComplexVariety X] [PerverseSheafTheory X]
    (P : PerverseSheaf X) : (perverseAmbient X).obj P = P.obj.obj :=
  rfl

end MathlibExtTest.AlgebraicGeometry.PerverseSheaves

end
