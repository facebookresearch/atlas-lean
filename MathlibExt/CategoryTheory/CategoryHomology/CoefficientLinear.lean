/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryHomology.BarLinear
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear

/-!
# Linearity of normalized coefficient-bar complexes and homology

The actual simplicial-bar linear instance is publicly imported from the weak
`BarLinear` layer. The normalized coefficient complex and coefficient homology
retain their Abelian target hypotheses, with independent scalar, indexing and
coefficient universes.

The normalized Moore inclusion and native short-complex homology scalar law
supply the remaining scalar-identity proofs. The clients use the public
simplicial-bar and normalized-complex `map_smul` and `map_id` laws.
-/

public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe wS uJ vJ uV vV uI

namespace CategoryTheory.CategoryHomology

variable {S : Type wS} [Semiring S]
  {J : Type uJ} [Category.{vJ} J]
  {V : Type uV} [Category.{vV} V] [Abelian V] [CategoryTheory.Linear S V]

private theorem normalized_scalar_id (X : SimplicialObject V) (s : S) :
    (AlgebraicTopology.normalizedMooreComplex V).map (s • 𝟙 X) =
      s • 𝟙 ((AlgebraicTopology.normalizedMooreComplex V).obj X) := by
  apply (cancel_mono (AlgebraicTopology.inclusionOfMooreComplexMap X)).1
  have hNat := (AlgebraicTopology.inclusionOfMooreComplex V).naturality (s • 𝟙 X)
  change (AlgebraicTopology.normalizedMooreComplex V).map (s • 𝟙 X) ≫
      AlgebraicTopology.inclusionOfMooreComplexMap X =
    AlgebraicTopology.inclusionOfMooreComplexMap X ≫
      (AlgebraicTopology.alternatingFaceMapComplex V).map (s • 𝟙 X) at hNat
  have hAlt : (AlgebraicTopology.alternatingFaceMapComplex V).map (s • 𝟙 X) =
      s • 𝟙 ((AlgebraicTopology.alternatingFaceMapComplex V).obj X) := by
    apply HomologicalComplex.Hom.ext
    funext n
    rfl
  rw [hNat, hAlt]
  simp

private theorem homology_scalar_id {I : Type uI} (c : ComplexShape I)
    (K : HomologicalComplex V c) (s : S) (i : I) :
    HomologicalComplex.homologyMap (s • 𝟙 K) i = s • 𝟙 (K.homology i) := by
  have hsc : (HomologicalComplex.shortComplexFunctor V c i).map (s • 𝟙 K) =
      s • 𝟙 (K.sc i) := by
    ext <;> rfl
  change ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor V c i).map (s • 𝟙 K)) = _
  rw [hsc, ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

variable [HasCoproducts.{max uJ vJ} V]

/-- The actual normalized coefficient complex functor is linear on all maps. -/
instance normalizedCoefficientBarComplexFunctor_linear :
    Functor.Linear S (CategoryHomology.normalizedCoefficientBarComplexFunctor
      (C := J) (A := V)) := by
  apply (Functor.linear_iff S _).2
  intro M s
  change (AlgebraicTopology.normalizedMooreComplex V).map
      ((CategoryHomology.coefficientBarSimplicialFunctor (C := J) (A := V)).map
        (s • 𝟙 M)) =
    s • 𝟙 ((AlgebraicTopology.normalizedMooreComplex V).obj
      ((CategoryHomology.coefficientBarSimplicialFunctor (C := J) (A := V)).obj M))
  rw [(CategoryHomology.coefficientBarSimplicialFunctor (C := J) (A := V)).map_smul
    s (𝟙 M), Functor.map_id]
  exact normalized_scalar_id _ s

/-- Every degree of the actual coefficient-homology functor is linear on
arbitrary coefficient transformations, with no linear-functor input. -/
instance homologyWithCoefficientsFunctor_linear (n : ℕ) :
    Functor.Linear S (CategoryHomology.homologyWithCoefficientsFunctor
      (C := J) (A := V) n) := by
  apply (Functor.linear_iff S _).2
  intro M s
  change HomologicalComplex.homologyMap
      ((CategoryHomology.normalizedCoefficientBarComplexFunctor
        (C := J) (A := V)).map (s • 𝟙 M)) n =
    s • 𝟙 (((CategoryHomology.normalizedCoefficientBarComplexFunctor
      (C := J) (A := V)).obj M).homology n)
  rw [(CategoryHomology.normalizedCoefficientBarComplexFunctor (C := J) (A := V)).map_smul
    s (𝟙 M), Functor.map_id]
  exact homology_scalar_id (ComplexShape.down ℕ) _ s n

end CategoryTheory.CategoryHomology
