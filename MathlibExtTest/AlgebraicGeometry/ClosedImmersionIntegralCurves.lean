/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ClosedImmersionIntegralCurves

/-!
# Tests for `MathlibExt.AlgebraicGeometry.ClosedImmersionIntegralCurves`
-/

open CategoryTheory AlgebraicGeometry

#check @AlgebraicGeometry.surjective_of_isClosedImmersion_of_topologicalKrullDim_le
#check @AlgebraicGeometry.isIso_of_isClosedImmersion_of_topologicalKrullDim_le
#check @AlgebraicGeometry.isIso_of_isClosedImmersion_of_topologicalKrullDim_eq_one

/-- The closed immersion `Spec (R ⧸ I) ⟶ Spec R` into an integral one-dimensional affine scheme,
with one-dimensional source, is an isomorphism. -/
example (R : CommRingCat) [IsDomain R] (I : Ideal R)
    (hZ : topologicalKrullDim (Spec (CommRingCat.of (R ⧸ I))) = 1)
    (hX : topologicalKrullDim (Spec R) = 1) :
    IsIso (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
  isIso_of_isClosedImmersion_of_topologicalKrullDim_eq_one _ hZ hX

/-- The identity of an integral scheme of finite dimension is covered by the general statement. -/
example (X : Scheme) [IsIntegral X] (h : topologicalKrullDim X ≠ ⊤) : IsIso (𝟙 X) :=
  isIso_of_isClosedImmersion_of_topologicalKrullDim_le (𝟙 X) h le_rfl

/-- Surjectivity needs only an irreducible target. -/
example {Z X : Scheme} (j : Z ⟶ X) [IsClosedImmersion j] [IrreducibleSpace X]
    (hZ : topologicalKrullDim Z = 1) (hX : topologicalKrullDim X = 1) : Surjective j :=
  surjective_of_isClosedImmersion_of_topologicalKrullDim_le j (by rw [hZ]; decide)
    (by rw [hZ, hX])
