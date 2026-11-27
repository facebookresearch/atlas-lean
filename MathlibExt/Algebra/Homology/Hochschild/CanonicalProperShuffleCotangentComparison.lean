/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.ProperShufflePolynomialTotal
public import MathlibExt.Algebra.Category.CommAlgCat.CotangentSimplicial

/-!
# Canonical polynomial proper-shuffle cotangent totals

Over a rational ground algebra, canonical simplicial polynomial
levels carry proper-shuffle
cotangent augmentation quasi-isomorphisms. Their naturality
under algebra maps and the first-quadrant total comparison
give the total quasi-isomorphism of these diagrams.
This concerns the proper both-positive relation model;
identification with the full coefficient-ideal quotient
or the ordinary Harrison–AQ functor is a separate statement.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped TensorProduct Simplicial

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle.Canonical

open AugmentedAlgebra

variable (k : Type u) [CommRing k] [Algebra ℚ k] (B : CommAlgCat.{max u v} k)
  (M : Type w) [AddCommGroup M] [Module k M] [Module B M]
  [SMulCommClass k B M] [IsScalarTower k B M]

/-- The original canonical augmented polynomial resolution. -/
abbrev resolution := (CommAlgCat.polynomialResolutionOverFunctor.{u, v} k B).obj (Over.mk (𝟙 B))

/-- The shifted proper quotients of the original canonical polynomial levels. -/
def diagram : SimplicialObject (ChainComplex (ModuleCat.{max u v w} k) ℕ) :=
  simplicialDiagram k B M (resolution k B)

/-- The original coefficient cotangents of the same original polynomial levels. -/
def cotangentDiagram : SimplicialObject (ModuleCat.{max u v w} k) :=
  simplicialCotangentDiagram k B M (resolution k B)

/-- The original polynomial cotangent augmentation, natural for every original operator. -/
def augmentation : diagram k B M ⟶ cotangentDiagram k B M ⋙ ChainComplex.single₀ (ModuleCat.{max u v w} k) :=
  simplicialAugmentation k B M (resolution k B)

/-- For a commutative ℚ-algebra `k`, a commutative `k`-algebra `B`, and `p : ℕ`,
this is the carrier of the `p`th iterated polynomial-power object of `B`. It is
the generator type presenting degree `p` of the canonical polynomial resolution. -/
abbrev polynomialVariables (p : ℕ) : Type (max u v) := (CommAlgCat.polynomialPower k p).obj B

-- Legacy spelling for the same generator carrier.
abbrev «variables» (p : ℕ) : Type (max u v) := polynomialVariables k B p

/-- The canonical degree isomorphism earns every original column comparison. -/
theorem augmentation_column_quasiIso (p : ℕ) :
    _root_.QuasiIso ((augmentation k B M).app (op ⦋p⦌)) :=
  simplicialAugmentation_app_quasiIso_of_polynomialPresentation k B M (resolution k B)
    (op ⦋p⦌) (polynomialVariables k B p) (CommAlgCat.polynomialResolutionObjIso k B p)

/-- The nonnegative bicomplex of original shifted proper quotient columns. -/
def bicomplex : HomologicalComplex₂ (ModuleCat.{max u v w} k) (.down ℕ) (.down ℕ) :=
  simplicialBicomplex k B M (resolution k B)

/-- The nonnegative bicomplex of the original single-zero coefficient cotangent columns. -/
def cotangentBicomplex : HomologicalComplex₂ (ModuleCat.{max u v w} k) (.down ℕ) (.down ℕ) :=
  simplicialCotangentBicomplex k B M (resolution k B)

/-- Native alternating faces transport the original augmentation to the bicomplex map. -/
def bicomplexMap : bicomplex k B M ⟶ cotangentBicomplex k B M :=
  simplicialBicomplexMap k B M (resolution k B)

/-- Every outer component is precisely the original all-degree polynomial augmentation. -/
theorem bicomplexMap_f (p : ℕ) :
    (bicomplexMap k B M).f p = (augmentation k B M).app (op ⦋p⦌) := rfl

/-- The original direct-sum total of the shifted proper quotient bicomplex. -/
abbrev totalComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ := (bicomplex k B M).total (.down ℕ)

/-- The original direct-sum total of the coefficient cotangent comparison target. -/
abbrev cotangentTotalComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ := (cotangentBicomplex k B M).total (.down ℕ)

/-- The signed direct-sum total comparison of the original polynomial diagrams. -/
def totalMap : totalComplex k B M ⟶ cotangentTotalComplex k B M :=
  simplicialTotalMap k B M (resolution k B)

/-- The polynomial column quasi-isomorphisms prove the full total comparison,
without any supplied total or column quasi-isomorphism hypothesis. -/
instance totalMap_quasiIso : _root_.QuasiIso (totalMap k B M) := by
  exact simplicialTotalMap_quasiIso_of_polynomialPresentations k B M (resolution k B)
    («variables» k B) (fun p => CommAlgCat.polynomialResolutionObjIso k B p)

/-- The original total homology comparison is homology of the constructed total map. -/
def totalHomologyIso (n : ℕ) :
    (totalComplex k B M).homology n ≅ (cotangentTotalComplex k B M).homology n :=
  _root_.isoOfQuasiIsoAt (totalMap k B M) n

/-- The original total homology isomorphism retains the constructed comparison as its forward map. -/
theorem totalHomologyIso_hom (n : ℕ) :
    (totalHomologyIso k B M n).hom = HomologicalComplex.homologyMap (totalMap k B M) n := rfl

end ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle.Canonical
