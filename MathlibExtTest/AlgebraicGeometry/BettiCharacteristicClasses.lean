/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.BettiCharacteristicClasses

@[expose] public section

/-! # Tests for bundle geometry and Betti characteristic classes -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ComplexAnalytification
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.ProperBettiFunctoriality
open MathlibExt.AlgebraicGeometry.BettiGysin
open MathlibExt.AlgebraicGeometry.AlgebraicBundleGeometry
open MathlibExt.AlgebraicGeometry.BettiCharacteristicClasses

namespace MathlibExtTest.AlgebraicGeometry.BettiCharacteristicClasses

/-- The structure sheaf is invertible. -/
example (X : Scheme.{0}) : IsLine (SheafOfModules.unit X.ringCatSheaf) :=
  MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries.isLineBundle_structureModule X

/-- The total spaces are smooth of the expected dimensions, and a projective
bundle over a proper base is proper. -/
example {X : ComplexScheme} {dx r : ℕ} {E : X.left.Modules} (B : ProjectiveBundle X dx r E) :
    SmoothOfRelativeDimension (dx + r) B.total.hom :=
  inferInstance

example {X : ComplexScheme} [IsProper X.hom] {dx r : ℕ} {E : X.left.Modules}
    (B : ProjectiveBundle X dx r E) : IsProper B.total.hom :=
  inferInstance

example {X : ComplexScheme} {dx : ℕ} {L : X.left.Modules} (V : LineTotalSpace X dx L) :
    SmoothOfRelativeDimension (dx + 1) V.total.hom :=
  inferInstance

section Classes

variable
  (D : ∀ (X : ComplexScheme) [IsComplexVariety X],
    MathlibExt.AlgebraicGeometry.CompactSupportBetti.DualizingComplex (space X))
  (P : ∀ {X Y : ComplexScheme} [IsComplexVariety X] [IsComplexVariety Y]
    (f : X ⟶ Y) [IsProper f.left], ProperPullback (spaceMap f))
  {X : ComplexScheme} [IsComplexVariety X] (dx r : ℕ) [SmoothOfRelativeDimension dx X.hom]
  (E : X.left.Modules) (B : ProjectiveBundle X dx r E)
  (V : LineTotalSpace B.total (dx + r) B.tautological) (T : ProjectiveBundleTheory D P)

/-- `c₀ = 1`, the Chern classes vanish above the rank, and `s₀ = 1`. -/
example : chern D P dx r E B V T 0 = unitClass (space X) := by
  simp [chern]

example (i : ℕ) (hi : r + 1 < i) : chern D P dx r E B V T i = 0 := by
  simp [chern, show i ≠ 0 by omega, show ¬ i ≤ r + 1 by omega]

example : segre D P dx r E B V T 0 = unitClass (space X) := by
  simp [segre, projectiveSegre]

/-- The first Segre coefficients fix the sign conventions: the recurrence gives
`s₁ = c₁` for `1/c(-t)`, and `1/c(t)` has first coefficient `-c₁`. -/
example : projectiveSegre D P dx r E B V T 1 = chern D P dx r E B V T 1 := by
  have hu : unitClass (space X) = ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 _) := by
    simp [unitClass, ShiftedHom.mk₀, shiftFunctorZero']
  rw [projectiveSegre]
  simp [projectiveSegre, hu, MathlibExt.AlgebraicGeometry.BettiRealization.cup,
    ShiftedHom.comp_mk₀_id]

example : segre D P dx r E B V T 1 = -projectiveSegre D P dx r E B V T 1 := by
  simp [segre]

end Classes

end MathlibExtTest.AlgebraicGeometry.BettiCharacteristicClasses

end
