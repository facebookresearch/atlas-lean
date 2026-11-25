/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Colimit.DirectLimit
public import MathlibExt.Algebra.Lie.OfNonUnitalAssociative
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.MatrixCyclicStabilization
public import MathlibExt.LinearAlgebra.Matrix.Stable

/-!
# Chevalley–Eilenberg complexes of stable matrix Lie algebras

Let `k` be a commutative ring and `A` a unital `k`-algebra. Finite square
matrices, equipped with the commutator bracket, map into their stable matrix
direct limit by top-left zero extension. These Lie algebra maps induce a
cocone of Chevalley–Eilenberg chain complexes and a comparison from its
colimit to the Chevalley–Eilenberg complex of the stable matrix Lie algebra.
The comparison is specified by its finite-stage inclusions.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v

namespace ChevalleyEilenberg

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]

/-- The stable matrix carrier formed by top-left zero extension. -/
abbrev canonicalStableMatrixAlgebra : Type v :=
  Matrix.Stable k A

/-- The commutator Lie bracket on stable matrices. -/
instance canonicalStableMatrixLieRing : LieRing (canonicalStableMatrixAlgebra k A) :=
  LieRing.ofNonUnitalAssociativeRing

/-- The k-Lie algebra structure on stable matrices induced by the commutator bracket. -/
instance canonicalStableMatrixLieAlgebra : LieAlgebra k (canonicalStableMatrixAlgebra k A) :=
  LieAlgebra.ofNonUnitalAssociativeAlgebra

/-- The inclusion of a finite matrix stage into the stable matrix algebra. -/
def canonicalStableMatrixInclusion (m : ℕ) :
    Matrix (Fin m) (Fin m) A →ₙₐ[k] canonicalStableMatrixAlgebra k A :=
  Matrix.Stable.ofFinite k A m

/-- The Lie algebra homomorphism induced by a finite-stage inclusion. -/
def canonicalStableMatrixLieInclusion (m : ℕ) :
    Matrix (Fin m) (Fin m) A →ₗ⁅k⁆ canonicalStableMatrixAlgebra k A :=
  (canonicalStableMatrixInclusion k A m).toLieHom

/-- Finite-stage inclusions commute with top-left zero extension. -/
theorem canonicalStableMatrixInclusion_zeroCorner {m n : ℕ} (h : m ≤ n) :
    (canonicalStableMatrixInclusion k A n).comp (Matrix.zeroExtendAlgHom (k := k) (A := A) h) =
      canonicalStableMatrixInclusion k A m := by
  ext x
  exact Matrix.Stable.ofFinite_zeroExtend k A h x

/-- The finite-stage Lie algebra inclusions commute with top-left zero extension. -/
theorem canonicalStableMatrixLieInclusion_zeroCorner {m n : ℕ} (h : m ≤ n) :
    (canonicalStableMatrixLieInclusion k A n).comp (Matrix.zeroExtendLieHom k A h) =
      canonicalStableMatrixLieInclusion k A m := by
  ext x
  change Matrix.Stable.ofFinite k A n (Matrix.zeroExtend h x) =
    Matrix.Stable.ofFinite k A m x
  exact Matrix.Stable.ofFinite_zeroExtend k A h x

/-- The Chevalley–Eilenberg complex of the stable matrix Lie algebra. -/
abbrev canonicalStableMatrixCEComplex : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  (canonicalChainData k (canonicalStableMatrixAlgebra k A)).complex

/-- The Chevalley–Eilenberg chain map induced by a finite matrix inclusion. -/
def canonicalStableMatrixCEInclusion (m : ℕ) :
    matrixComplex k A m ⟶ canonicalStableMatrixCEComplex k A :=
  nativeComplexMap k (Matrix (Fin m) (Fin m) A) (canonicalStableMatrixLieInclusion k A m)

/-- The cocone from finite matrix Chevalley–Eilenberg complexes to the stable matrix
Chevalley–Eilenberg complex. -/
def canonicalStableMatrixCECocone : Cocone (matrixComplexFunctor k A) where
  pt := canonicalStableMatrixCEComplex k A
  ι :=
    { app := canonicalStableMatrixCEInclusion k A
      naturality m n h := by
        change matrixZeroCornerMap k A (leOfHom h) ≫ canonicalStableMatrixCEInclusion k A n =
          canonicalStableMatrixCEInclusion k A m ≫ 𝟙 _
        rw [matrixZeroCornerMap, canonicalStableMatrixCEInclusion, canonicalStableMatrixCEInclusion,
          nativeComplexMap_comp, canonicalStableMatrixLieInclusion_zeroCorner, Category.comp_id] }

/-- The chain map from the colimit of finite matrix Chevalley–Eilenberg complexes to the
Chevalley–Eilenberg complex of stable matrices. -/
def colimitToCanonicalStableMatrixCE : stableMatrixCEComplex k A ⟶ canonicalStableMatrixCEComplex k A :=
  colimit.desc (matrixComplexFunctor k A) (canonicalStableMatrixCECocone k A)

/-- The colimit comparison restricts to the Chevalley–Eilenberg map of each finite-stage
inclusion. -/
@[reassoc]
theorem colimitToCanonicalStableMatrixCE_ι (m : ℕ) :
    colimit.ι (matrixComplexFunctor k A) m ≫ colimitToCanonicalStableMatrixCE k A =
      canonicalStableMatrixCEInclusion k A m :=
  colimit.ι_desc (canonicalStableMatrixCECocone k A) m

end ChevalleyEilenberg
