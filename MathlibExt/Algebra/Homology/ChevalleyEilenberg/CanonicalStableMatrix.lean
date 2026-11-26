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
# Chevalley–Eilenberg chains of the stable matrix Lie algebra

Let k be a commutative ring and A an associative unital k-algebra.
The stable nonunital matrix algebra Mat_∞(A) is the directed limit of
Mat_m(A), m ∈ ℕ, under top-left zero extension. Its commutator bracket
[X,Y] = XY−YX makes it a k-Lie algebra. The finite-stage inclusions
i_m are both nonunital algebra maps and Lie maps.

The Chevalley–Eilenberg complex has terms C_n = ⋀_k^n Mat_∞(A).
For n ≥ 1 its differential is
d(X₀∧⋯∧X_(n−1)) =
∑_(i<j) (−1)^(i+j) [X_i,X_j] ∧ X₀∧⋯∧X̂_i∧⋯∧X̂_j∧⋯∧X_(n−1),
with the remaining factors in their given order. In particular d₂ = −[−,−].

Exterior powers of i_m give a cocone from the finite matrix CE
complexes to this complex. The induced map from their colimit is
characterized by these finite-stage maps. The ring and algebra worlds
u,v are independent, and the chain category is ModuleCat^max(u,v)(k).
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v

namespace ChevalleyEilenberg

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]

/-- For a commutative ring k and an associative unital
k-algebra A, Mat_∞(A) is the directed limit of the finite square
matrix algebras Mat_m(A) under top-left zero extension.
Its carrier has the world v of A; its multiplication and k-action
are induced from the finite stages. -/
abbrev canonicalStableMatrixAlgebra : Type v :=
  Matrix.Stable k A

/-- For a commutative ring k and an associative unital
k-algebra A, the stable nonunital matrix algebra is a Lie ring
with bracket [X,Y] = XY−YX. -/
instance canonicalStableMatrixLieRing : LieRing (canonicalStableMatrixAlgebra k A) :=
  LieRing.ofNonUnitalAssociativeRing

/-- For a commutative ring k and an associative unital
k-algebra A, the commutator on Mat_∞(A) is k-bilinear and
defines a k-Lie algebra structure on its directed-limit carrier. -/
instance canonicalStableMatrixLieAlgebra : LieAlgebra k (canonicalStableMatrixAlgebra k A) :=
  LieAlgebra.ofNonUnitalAssociativeAlgebra

/-- For a commutative ring k, an associative unital k-algebra A
and m ≥ 0, the finite-stage map i_m : Mat_m(A) → Mat_∞(A)
is a nonunital k-algebra homomorphism representing a matrix in
the top-left m×m stage of the direct limit. -/
def canonicalStableMatrixInclusion (m : ℕ) :
    Matrix (Fin m) (Fin m) A →ₙₐ[k] canonicalStableMatrixAlgebra k A :=
  Matrix.Stable.ofFinite k A m

/-- For a commutative ring k, an associative unital k-algebra A
and m ≥ 0, the finite-stage inclusion i_m : Mat_m(A) → Mat_∞(A)
preserves commutator brackets and is a k-Lie homomorphism. -/
def canonicalStableMatrixLieInclusion (m : ℕ) :
    Matrix (Fin m) (Fin m) A →ₗ⁅k⁆ canonicalStableMatrixAlgebra k A :=
  (canonicalStableMatrixInclusion k A m).toLieHom

/-- For a commutative ring k, an associative unital k-algebra A
and m ≤ n, the stable inclusions satisfy i_n ∘ Z_(m,n) = i_m
as nonunital k-algebra maps. Here Z_(m,n) extends a matrix by
zero to the top-left n×n block. -/
theorem canonicalStableMatrixInclusion_zeroCorner {m n : ℕ} (h : m ≤ n) :
    (canonicalStableMatrixInclusion k A n).comp (Matrix.zeroExtendAlgHom (k := k) (A := A) h) =
      canonicalStableMatrixInclusion k A m := by
  ext x
  exact Matrix.Stable.ofFinite_zeroExtend k A h x

/-- For a commutative ring k, an associative unital k-algebra A
and m ≤ n, the commutator Lie maps satisfy i_n ∘ Z_(m,n) = i_m
from Mat_m(A) to Mat_∞(A), with Z_(m,n) the top-left zero
extension viewed as a Lie map. -/
theorem canonicalStableMatrixLieInclusion_zeroCorner {m n : ℕ} (h : m ≤ n) :
    (canonicalStableMatrixLieInclusion k A n).comp (Matrix.zeroExtendLieHom k A h) =
      canonicalStableMatrixLieInclusion k A m := by
  ext x
  change Matrix.Stable.ofFinite k A n (Matrix.zeroExtend h x) =
    Matrix.Stable.ofFinite k A m x
  exact Matrix.Stable.ofFinite_zeroExtend k A h x

/-- For a commutative ring k and an associative unital
k-algebra A, the canonical stable CE complex has degree-n term
⋀_k^n Mat_∞(A) and the bracket differential with pair sign
(−1)^(i+j). It lies in ModuleCat^max(u,v)(k), and d₂(X∧Y) = −[X,Y]. -/
abbrev canonicalStableMatrixCEComplex : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  (canonicalChainData k (canonicalStableMatrixAlgebra k A)).complex

/-- For a commutative ring k, an associative unital k-algebra A
and m ≥ 0, the Lie inclusion Mat_m(A) → Mat_∞(A) induces the
CE chain map whose degree-n component is its nth exterior power.
It applies i_m to every factor of a pure wedge. -/
def canonicalStableMatrixCEInclusion (m : ℕ) :
    matrixComplex k A m ⟶ canonicalStableMatrixCEComplex k A :=
  nativeComplexMap k (Matrix (Fin m) (Fin m) A) (canonicalStableMatrixLieInclusion k A m)

/-- For a commutative ring k and an associative unital
k-algebra A, the finite CE complexes C_*(Mat_m(A)) form a diagram
over ℕ by zero-extension maps. Their CE inclusion maps to
C_*(Mat_∞(A)) form a cocone, with components ⋀^n i_m in degree n. -/
def canonicalStableMatrixCECocone : Cocone (matrixComplexFunctor k A) where
  pt := canonicalStableMatrixCEComplex k A
  ι :=
    { app := canonicalStableMatrixCEInclusion k A
      naturality m n h := by
        change matrixZeroCornerMap k A (leOfHom h) ≫ canonicalStableMatrixCEInclusion k A n =
          canonicalStableMatrixCEInclusion k A m ≫ 𝟙 _
        rw [matrixZeroCornerMap, canonicalStableMatrixCEInclusion, canonicalStableMatrixCEInclusion,
          nativeComplexMap_comp, canonicalStableMatrixLieInclusion_zeroCorner, Category.comp_id] }

/-- For a commutative ring k and an associative unital
k-algebra A, the finite-inclusion cocone defines the chain map
colim_m C_*(Mat_m(A)) → C_*(Mat_∞(A)).
Its composite with each colimit leg is the CE map induced by i_m. -/
def colimitToCanonicalStableMatrixCE : stableMatrixCEComplex k A ⟶ canonicalStableMatrixCEComplex k A :=
  colimit.desc (matrixComplexFunctor k A) (canonicalStableMatrixCECocone k A)

/-- For a commutative ring k, an associative unital k-algebra A
and m ≥ 0, the finite-to-stable comparison T satisfies
T ∘ ι_m = C_*(i_m), where ι_m is the mth colimit leg.
This is an equality of chain maps from the finite matrix CE complex. -/
@[reassoc]
theorem colimitToCanonicalStableMatrixCE_ι (m : ℕ) :
    colimit.ι (matrixComplexFunctor k A) m ≫ colimitToCanonicalStableMatrixCE k A =
      canonicalStableMatrixCEInclusion k A m :=
  colimit.ι_desc (canonicalStableMatrixCECocone k A) m

end ChevalleyEilenberg
