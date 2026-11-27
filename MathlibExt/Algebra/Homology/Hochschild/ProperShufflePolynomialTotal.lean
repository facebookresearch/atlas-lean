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
# Total proper-shuffle comparisons for simplicial polynomial presentations

Let k be a commutative ℚ-algebra, P → B an augmented simplicial commutative k-algebra, and M a
compatible B-module. The chain columns of the proper-shuffle cotangent complexes form a first-
quadrant bicomplex. The column augmentations give its signed direct-sum total map to the
cotangent-module columns. If every Pₚ admits a polynomial presentation, this map is a quasi-
isomorphism in every total degree. The cotangent total is canonically the alternating-face
complex of the simplicial modules M ⊗[Pₚ] Ω¹(Pₚ/k).

See J.-L. Loday, Cyclic Homology, 2nd ed., §4.5, for rational Harrison/cotangent comparisons.
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

/-- The first-quadrant bicomplex of proper-shuffle polynomial columns.

For a commutative ℚ-algebra k, P → B and a compatible B-module M, this bicomplex has
simplicial degree p and cotangent-chain degree q, both natural indices. The qth entry of
column p comes from Hochschild degree q+1. -/
def simplicialBicomplex : HomologicalComplex₂ (ModuleCat.{max u v w} k) (.down ℕ) (.down ℕ) :=
  (alternatingFaceMapComplex (ChainComplex (ModuleCat.{max u v w} k) ℕ)).obj
    (simplicialDiagram k B M P)

/-- The bicomplex of cotangent modules concentrated in vertical degree zero.

For a commutative ℚ-algebra k, P → B and a compatible B-module M, column p is M ⊗[Pₚ] Ω¹(Pₚ/k)
placed in chain degree zero; its horizontal differential is the alternating simplicial face
sum. -/
def simplicialCotangentBicomplex :
    HomologicalComplex₂ (ModuleCat.{max u v w} k) (.down ℕ) (.down ℕ) :=
  (alternatingFaceMapComplex (ChainComplex (ModuleCat.{max u v w} k) ℕ)).obj
    (simplicialCotangentDiagram k B M P ⋙ ChainComplex.single₀ (ModuleCat.{max u v w} k))

/-- The augmentation between the two cotangent bicomplexes.

For a commutative ℚ-algebra k, P → B and a compatible B-module M, the map in column p is the
proper-shuffle cotangent augmentation to M ⊗[Pₚ] Ω¹(Pₚ/k). -/
def simplicialBicomplexMap : simplicialBicomplex k B M P ⟶ simplicialCotangentBicomplex k B M P :=
  (alternatingFaceMapComplex (ChainComplex (ModuleCat.{max u v w} k) ℕ)).map
    (simplicialAugmentation k B M P)

/-- The column component of the cotangent bicomplex map.

For a commutative ℚ-algebra k, P → B and a compatible B-module M, its component at p is
exactly simplicialAugmentation at the opposite simplex [p]. -/
theorem simplicialBicomplexMap_f (p : ℕ) :
    @Eq ((simplicialDiagram k B M P).obj (op ⦋p⦌) ⟶
      ((simplicialCotangentDiagram k B M P) ⋙ ChainComplex.single₀ (ModuleCat.{max u v w} k)).obj (op ⦋p⦌))
      ((simplicialBicomplexMap k B M P).f p) ((simplicialAugmentation k B M P).app (op ⦋p⦌)) := rfl

/-- The direct-sum total of the proper-shuffle cotangent bicomplex.

For a commutative ℚ-algebra k, P → B and a compatible B-module M, total degree n sums the
bicomplex entries with p+q=n and uses the signed chain-total differential. -/
abbrev simplicialTotalComplex := (simplicialBicomplex k B M P).total (.down ℕ)

/-- The direct-sum total of the coefficient cotangent bicomplex.

For a commutative ℚ-algebra k, P → B and a compatible B-module M, only vertical degree zero
contributes, so total degree n is the cotangent module of Pₙ with coefficients M. -/
abbrev simplicialCotangentTotalComplex := (simplicialCotangentBicomplex k B M P).total (.down ℕ)

/-- The signed total map induced by the cotangent column augmentations.

For a commutative ℚ-algebra k, P → B and a compatible B-module M, totalizing
simplicialBicomplexMap gives a chain map from the proper-shuffle total to the coefficient
cotangent total. -/
def simplicialTotalMap : simplicialTotalComplex k B M P ⟶ simplicialCotangentTotalComplex k B M P :=
  HomologicalComplex₂.total.map (simplicialBicomplexMap k B M P) (.down ℕ)

/-- Polynomial presentations of all columns give a total quasi-isomorphism.

For a commutative ℚ-algebra k, P → B and a compatible B-module M, isomorphisms Pₚ ≅ k[σₚ] for
every p make simplicialTotalMap a quasi-isomorphism. Generator sets may vary with p and may be
infinite. -/
theorem simplicialTotalMap_quasiIso_of_polynomialPresentations
    (σ : ℕ → Type (max u v))
    (e : ∀ p : ℕ, P.left.obj (op ⦋p⦌) ≅ CommAlgCat.of k (MvPolynomial (σ p) k)) :
    _root_.QuasiIso (simplicialTotalMap k B M P) := by
  exact HomologicalComplex₂.quasiIso_totalMap_of_objwise_firstQuadrant
    (simplicialBicomplexMap k B M P) (fun p => by
      rw [simplicialBicomplexMap_f]
      exact simplicialAugmentation_app_quasiIso_of_polynomialPresentation k B M P
        (op ⦋p⦌) (σ p) (e p))

/-- The homology isomorphism of the total polynomial cotangent comparison.

Under the commutative ℚ-algebra setup and polynomial presentations Pₚ ≅ k[σₚ] in every column,
simplicialTotalMap induces an isomorphism in each homology degree n. -/
def simplicialTotalHomologyIso_of_polynomialPresentations
    (σ : ℕ → Type (max u v))
    (e : ∀ p : ℕ, P.left.obj (op ⦋p⦌) ≅ CommAlgCat.of k (MvPolynomial (σ p) k)) (n : ℕ) :
    (simplicialTotalComplex k B M P).homology n ≅ (simplicialCotangentTotalComplex k B M P).homology n := by
  let _ : _root_.QuasiIso (simplicialTotalMap k B M P) :=
    simplicialTotalMap_quasiIso_of_polynomialPresentations k B M P σ e
  exact _root_.isoOfQuasiIsoAt (simplicialTotalMap k B M P) n

/-- The alternating-face complex of simplicial coefficient cotangent modules.

For a commutative ℚ-algebra k, P → B and a compatible B-module M, degree n is M ⊗[Pₙ]
Ω¹(Pₙ/k), and the differential is the signed sum of the simplicial face maps. -/
def simplicialCotangentComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  (alternatingFaceMapComplex (ModuleCat.{max u v w} k)).obj (simplicialCotangentDiagram k B M P)

/-- The cotangent bicomplex total equals its alternating-face complex.

For a commutative ℚ-algebra k, P → B and a compatible B-module M, the coefficient cotangent
columns are concentrated in degree zero, giving a canonical chain isomorphism from their total
to simplicialCotangentComplex. -/
def simplicialCotangentTotalIso :
    simplicialCotangentTotalComplex k B M P ≅ simplicialCotangentComplex k B M P :=
  alternatingSingleTotalIso (ModuleCat.{max u v w} k) (simplicialCotangentDiagram k B M P)

/-- The chain comparison from the proper-shuffle total to the cotangent face complex.

For a commutative ℚ-algebra k, P → B and a compatible B-module M, compose the total
augmentation with simplicialCotangentTotalIso to obtain this comparison. -/
def simplicialCotangentComparison : simplicialTotalComplex k B M P ⟶ simplicialCotangentComplex k B M P :=
  simplicialTotalMap k B M P ≫ (simplicialCotangentTotalIso k B M P).hom

/-- The cotangent face-complex comparison is a quasi-isomorphism for polynomial columns.

For a commutative ℚ-algebra k, P → B and a compatible B-module M, presentations Pₚ ≅ k[σₚ] for
every p imply that simplicialCotangentComparison induces homology isomorphisms in all degrees. -/
theorem simplicialCotangentComparison_quasiIso_of_polynomialPresentations
    (σ : ℕ → Type (max u v))
    (e : ∀ p : ℕ, P.left.obj (op ⦋p⦌) ≅ CommAlgCat.of k (MvPolynomial (σ p) k)) :
    _root_.QuasiIso (simplicialCotangentComparison k B M P) := by
  let _ : _root_.QuasiIso (simplicialTotalMap k B M P) :=
    simplicialTotalMap_quasiIso_of_polynomialPresentations k B M P σ e
  unfold simplicialCotangentComparison
  infer_instance

end ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle.AugmentedAlgebra
