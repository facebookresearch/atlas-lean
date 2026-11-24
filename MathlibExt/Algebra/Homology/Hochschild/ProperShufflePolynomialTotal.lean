/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.ProperShufflePolynomialColumns
public import MathlibExt.AlgebraicTopology.AlternatingSingleTotal
public import MathlibExt.Algebra.Homology.FirstQuadrantTotalQuasiIso
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
# Total cotangent comparisons for polynomial presentations

A simplicial diagram of polynomial presentations defines
total proper-quotient and coefficient-cotangent complexes.
Columnwise polynomial augmentation quasi-isomorphisms
give a quasi-isomorphism on their first-quadrant totals.
Generators may be infinite and vary between columns;
the original coefficient module and carrier universes
are retained.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped TensorProduct Simplicial

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle.AugmentedAlgebra

variable (k : Type u) [CommRing k] [Algebra ℚ k] (B : CommAlgCat.{max u v} k)
  (M : Type w) [AddCommGroup M] [Module k M] [Module B M]
  [SMulCommClass k B M] [IsScalarTower k B M]
  (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B))

/-- The original nonnegative bicomplex of the shifted proper quotient columns. -/
def simplicialBicomplex : HomologicalComplex₂ (ModuleCat.{max u v w} k) (.down ℕ) (.down ℕ) :=
  (alternatingFaceMapComplex (ChainComplex (ModuleCat.{max u v w} k) ℕ)).obj
    (simplicialDiagram k B M P)

/-- The original single-zero coefficient cotangent columns with the same simplicial operators. -/
def simplicialCotangentBicomplex :
    HomologicalComplex₂ (ModuleCat.{max u v w} k) (.down ℕ) (.down ℕ) :=
  (alternatingFaceMapComplex (ChainComplex (ModuleCat.{max u v w} k) ℕ)).obj
    (simplicialCotangentDiagram k B M P ⋙ ChainComplex.single₀ (ModuleCat.{max u v w} k))

/-- The original augmentation induces the native bicomplex map. -/
def simplicialBicomplexMap : simplicialBicomplex k B M P ⟶ simplicialCotangentBicomplex k B M P :=
  (alternatingFaceMapComplex (ChainComplex (ModuleCat.{max u v w} k) ℕ)).map
    (simplicialAugmentation k B M P)

/-- Every native outer component is the original all-degree proper-shuffle augmentation. -/
theorem simplicialBicomplexMap_f (p : ℕ) :
    @Eq ((simplicialDiagram k B M P).obj (op ⦋p⦌) ⟶
      ((simplicialCotangentDiagram k B M P) ⋙ ChainComplex.single₀ (ModuleCat.{max u v w} k)).obj (op ⦋p⦌))
      ((simplicialBicomplexMap k B M P).f p) ((simplicialAugmentation k B M P).app (op ⦋p⦌)) := rfl

/-- The original full direct-sum total complex of the proper quotient columns. -/
abbrev simplicialTotalComplex := (simplicialBicomplex k B M P).total (.down ℕ)

/-- The original full direct-sum total of the coefficient cotangent columns. -/
abbrev simplicialCotangentTotalComplex := (simplicialCotangentBicomplex k B M P).total (.down ℕ)

/-- The native signed direct-sum total map retains the original simplicial augmentation. -/
def simplicialTotalMap : simplicialTotalComplex k B M P ⟶ simplicialCotangentTotalComplex k B M P :=
  HomologicalComplex₂.total.map (simplicialBicomplexMap k B M P) (.down ℕ)

/-- Actual polynomial presentations earn the full original total quasi-isomorphism.
No column quasi-isomorphism, flat coefficient or total comparison is an input. -/
theorem simplicialTotalMap_quasiIso_of_polynomialPresentations
    (σ : ℕ → Type (max u v))
    (e : ∀ p : ℕ, P.left.obj (op ⦋p⦌) ≅ CommAlgCat.of k (MvPolynomial (σ p) k)) :
    _root_.QuasiIso (simplicialTotalMap k B M P) := by
  exact HomologicalComplex₂.quasiIso_totalMap_of_objwise_firstQuadrant
    (simplicialBicomplexMap k B M P) (fun p => by
      rw [simplicialBicomplexMap_f]
      exact simplicialAugmentation_app_quasiIso_of_polynomialPresentation k B M P
        (op ⦋p⦌) (σ p) (e p))

/-- Homology of the constructed total map gives the original total comparison in every degree. -/
def simplicialTotalHomologyIso_of_polynomialPresentations
    (σ : ℕ → Type (max u v))
    (e : ∀ p : ℕ, P.left.obj (op ⦋p⦌) ≅ CommAlgCat.of k (MvPolynomial (σ p) k)) (n : ℕ) :
    (simplicialTotalComplex k B M P).homology n ≅ (simplicialCotangentTotalComplex k B M P).homology n := by
  let _ : _root_.QuasiIso (simplicialTotalMap k B M P) :=
    simplicialTotalMap_quasiIso_of_polynomialPresentations k B M P σ e
  exact _root_.isoOfQuasiIsoAt (simplicialTotalMap k B M P) n

/-- The alternating-face complex of the original coefficient cotangent diagram. -/
def simplicialCotangentComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  (alternatingFaceMapComplex (ModuleCat.{max u v w} k)).obj (simplicialCotangentDiagram k B M P)

/-- The native generic single-total isomorphism identifies this original cotangent target. -/
def simplicialCotangentTotalIso :
    simplicialCotangentTotalComplex k B M P ≅ simplicialCotangentComplex k B M P :=
  alternatingSingleTotalIso (ModuleCat.{max u v w} k) (simplicialCotangentDiagram k B M P)

/-- The polynomial proper-shuffle total maps into the original alternating cotangent complex. -/
def simplicialCotangentComparison : simplicialTotalComplex k B M P ⟶ simplicialCotangentComplex k B M P :=
  simplicialTotalMap k B M P ≫ (simplicialCotangentTotalIso k B M P).hom

/-- Actual polynomial presentations earn the comparison with the original cotangent diagram,
using the native target isomorphism rather than a desired target certificate. -/
theorem simplicialCotangentComparison_quasiIso_of_polynomialPresentations
    (σ : ℕ → Type (max u v))
    (e : ∀ p : ℕ, P.left.obj (op ⦋p⦌) ≅ CommAlgCat.of k (MvPolynomial (σ p) k)) :
    _root_.QuasiIso (simplicialCotangentComparison k B M P) := by
  let _ : _root_.QuasiIso (simplicialTotalMap k B M P) :=
    simplicialTotalMap_quasiIso_of_polynomialPresentations k B M P σ e
  unfold simplicialCotangentComparison
  infer_instance

end ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle.AugmentedAlgebra
