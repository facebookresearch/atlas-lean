/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.AffinePerfectObstructionTheoryPresentationObstructionEqZeroIff

/-!
# Presentation-obstruction lifting tests

Tests derive independence of obstruction vanishing from the presentation theory and the
morphism of extensions, and vanishing for the identity extension.

Reference: Behrend--Fantechi, *The intrinsic normal cone*, §4,
https://arxiv.org/abs/alg-geom/9601010.
-/

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.AffinePerfectObstructionTheoryPresentationObstructionEqZeroIff

open MathlibExt.AlgebraicGeometry.AffineObstructionComplexes
open WantedExt.AlgebraicGeometry.AffinePerfectObstructionTheoryWanted

example {k B : Type} [Field k] [CommRing B] [Algebra k B] {n : ℕ}
    {G : Algebra.Generators k B (Fin n)} (T₁ T₂ : PresentationTheory G)
    {A : Type} [CommRing A] [Algebra k A] [Algebra B A] [IsScalarTower k B A]
    (Q : Algebra.Extension.{0} k A) (squareZero : Q.ker ^ 2 = ⊥)
    (h₁ h₂ : Algebra.Extension.Hom G.toExtension Q) :
    obstruction T₁.model Q h₁ T₁.comparison = 0 ↔
      obstruction T₂.model Q h₂ T₂.comparison = 0 :=
  (presentation_obstruction_eq_zero_iff T₁ Q squareZero h₁).trans
    (presentation_obstruction_eq_zero_iff T₂ Q squareZero h₂).symm

example {k B : Type} [Field k] [CommRing B] [Algebra k B] {n : ℕ}
    {G : Algebra.Generators k B (Fin n)} (T : PresentationTheory G)
    (h : Algebra.Extension.Hom G.toExtension (Algebra.Extension.self k B)) :
    obstruction T.model (Algebra.Extension.self k B) h T.comparison = 0 := by
  apply (presentation_obstruction_eq_zero_iff T (Algebra.Extension.self k B) ?_ h).mpr
  · exact ⟨AlgHom.id k B, by ext; rfl⟩
  · have hk : (Algebra.Extension.self k B).ker = ⊥ := by
      ext x
      change x = 0 ↔ x = 0
      rfl
    simp [hk]

end MathlibExtTest.AlgebraicGeometry.AffinePerfectObstructionTheoryPresentationObstructionEqZeroIff
