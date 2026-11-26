/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.Matrix
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.AdjointCoinvariantNaturality

/-!
# Scalar special-linear coinvariants of matrix CE chains

Let `k` be a commutative ring and `A` a unital `k`-algebra. The scalar special-linear Lie
algebra over `k` acts on `⋀ⁿ[k] gl_m(A)` through its entrywise scalar inclusion. Its right
action replaces each wedge factor `X_i` by `[X_i,s]` and sums over all positions.

Quotienting by the span of this action gives the matrix coinvariant chain complex. The CE
coaugmentation, counit, and coproduct descend to it. Top-left zero extension and coefficient
algebra maps induce quotient chain maps, preserve projected wedges, and commute with the
quotient projections and with each other.
-/

@[expose] public section

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory

universe u v

namespace ChevalleyEilenberg

variable (k : Type u) [CommRing k]
variable (A : Type v) [Ring A] [Algebra k A]

/-- The scalar special-linear coinvariant matrix CE complex.

Take coinvariants of the matrix CE complex under the adjoint action of scalar special-linear
matrices. -/
abbrev matrixCoinvariantComplex (m : ℕ) :=
  adjointCoinvariantComplex k (Matrix (Fin m) (Fin m) A) (Matrix.scalarLieHom k A m)

/-- The projection to scalar-adjoint matrix coinvariants.

The canonical matrix CE complex maps to its scalar special-linear adjoint coinvariant
quotient. -/
abbrev matrixCoinvariantProjection (m : ℕ) :=
  adjointCoinvariantProjection k (Matrix (Fin m) (Fin m) A) (Matrix.scalarLieHom k A m)

/-- The degree module of scalar-adjoint matrix coinvariants.

In exterior degree `n`, quotient the matrix exterior module by the span of scalar special-
linear adjoint-action values. -/
abbrev matrixCoinvariantModule (m n : ℕ) :=
  adjointCoinvariantModule k (Matrix (Fin m) (Fin m) A) (Matrix.scalarLieHom k A m) n

/-- The degreewise quotient coordinates of matrix coinvariant chains.

Identify a coinvariant chain term with its scalar-adjoint exterior-module quotient. -/
abbrev matrixCoinvariantCoordinateIso (m n : ℕ) :=
  adjointCoinvariantCoordinateIso k (Matrix (Fin m) (Fin m) A) (Matrix.scalarLieHom k A m) n

/-- The endomorphism-valued scalar right-adjoint action on matrix wedges.

A scalar special-linear matrix acts in degree `n` by replacing each wedge factor `X_i` with
`[X_i,s]` and summing. -/
abbrev matrixRightAdjointAction (m n : ℕ) :=
  rightDegreeAdjointAction k (Matrix (Fin m) (Fin m) A) (Matrix.scalarLieHom k A m) n

/-- The opposite-endomorphism Lie map of scalar matrix adjoint action.

The right-adjoint action gives a Lie homomorphism to the opposite endomorphism algebra of the
exterior matrix module. -/
abbrev matrixRightAdjointLieHom (m n : ℕ) :=
  rightDegreeAdjointLieHom k (Matrix (Fin m) (Fin m) A) (Matrix.scalarLieHom k A m) n

/-- The pure-wedge sum for scalar matrix right-adjoint action.

For a scalar special-linear matrix `s`, sum the wedges obtained by replacing factor `X_i` with
`[X_i,s]`. -/
def matrixAdjointPure (m n : ℕ) (s : Matrix.ScalarSpecialLinear k m)
    (v : Fin n → Matrix (Fin m) (Fin m) A) : ⋀[k]^n (Matrix (Fin m) (Fin m) A) :=
  ∑ i : Fin n, exteriorPower.ιMulti k n
    (Function.update v i ⁅v i, Matrix.scalarLieHom k A m s⁆)

/-- The right-adjoint action formula on a matrix exterior wedge.

The endomorphism-valued scalar action on a pure wedge equals the sum of its single-factor
commutator replacements. -/
theorem matrixRightAdjointAction_pure (m n : ℕ) (s : Matrix.ScalarSpecialLinear k m)
    (v : Fin n → Matrix (Fin m) (Fin m) A) :
    matrixRightAdjointAction k A m n s (exteriorPower.ιMulti k n v) =
      matrixAdjointPure k A m n s v :=
  rightDegreeAdjointAction_pure k (Matrix (Fin m) (Fin m) A) (Matrix.scalarLieHom k A m) n s v

/-- The action-span kernel of the matrix coinvariant projection.

In degree `n`, the kernel is the ground span of all right-adjoint action values of scalar
special-linear matrices. -/
theorem matrixCoinvariantProjection_ker (m n : ℕ) :
    LinearMap.ker ((matrixCoinvariantProjection k A m).f n).hom =
      Submodule.span k {y | ∃ (s : Matrix.ScalarSpecialLinear k m)
        (a : ⋀[k]^n (Matrix (Fin m) (Fin m) A)), y = matrixRightAdjointAction k A m n s a} :=
  adjointCoinvariantProjection_ker_right k (Matrix (Fin m) (Fin m) A) (Matrix.scalarLieHom k A m) n

/-- The descended coalgebra complex on matrix adjoint coinvariants.

The scalar-adjoint quotient carries the coaugmented CE coalgebra structure. -/
abbrev matrixCoinvariantCoalgebra (m : ℕ) :=
  adjointCoinvariantCoalgebra k (Matrix (Fin m) (Fin m) A) (Matrix.scalarLieHom k A m)

/-- The coaugmentation of matrix adjoint coinvariants.

The CE coaugmentation descends through the matrix coinvariant projection. -/
abbrev matrixCoinvariantCoaug (m : ℕ) :=
  adjointCoinvariantCoaug k (Matrix (Fin m) (Fin m) A) (Matrix.scalarLieHom k A m)

/-- The counit of matrix adjoint coinvariants.

The CE counit descends to the scalar-adjoint quotient complex. -/
abbrev matrixCoinvariantCounit (m : ℕ) :=
  adjointCoinvariantCounit k (Matrix (Fin m) (Fin m) A) (Matrix.scalarLieHom k A m)

/-- The coproduct of matrix adjoint coinvariants.

The CE exterior coproduct descends to the tensor total of the coinvariant complex. -/
abbrev matrixCoinvariantComul (m : ℕ) :=
  adjointCoinvariantComul k (Matrix (Fin m) (Fin m) A) (Matrix.scalarLieHom k A m)

/-- The zero-extension map of matrix adjoint coinvariant complexes.

The compatible zero extensions of matrix and scalar special-linear Lie algebras induce a map
of coinvariant chain complexes. -/
def matrixCoinvariantZeroCornerMap {m n : ℕ} (h : m ≤ n) :
    matrixCoinvariantComplex k A m ⟶ matrixCoinvariantComplex k A n :=
  adjointCoinvariantMap k (Matrix (Fin m) (Fin m) A)
    (Matrix.scalarLieHom k A m) (Matrix.scalarLieHom k A n)
    (Matrix.zeroExtendLieHom k A h) (Matrix.scalarZeroExtendLieHom k h)
    (Matrix.scalarLieHom_zeroExtend k A h)

/-- The quotient square for matrix coinvariant zero extension.

The quotient projection followed by the coinvariant size map equals the ordinary size map
followed by the target quotient projection. -/
@[reassoc]
theorem matrixCoinvariantZeroCornerMap_projection {m n : ℕ} (h : m ≤ n) :
    matrixCoinvariantProjection k A m ≫ matrixCoinvariantZeroCornerMap k A h =
      matrixZeroCornerMap k A h ≫ matrixCoinvariantProjection k A n :=
  adjointCoinvariantMap_projection k (Matrix (Fin m) (Fin m) A)
    (Matrix.scalarLieHom k A m) (Matrix.scalarLieHom k A n)
    (Matrix.zeroExtendLieHom k A h) (Matrix.scalarZeroExtendLieHom k h)
    (Matrix.scalarLieHom_zeroExtend k A h)

/-- The projected-wedge formula for matrix coinvariant zero extension.

The quotient class of a matrix wedge maps to the quotient class of its top-left zero
extensions. -/
theorem matrixCoinvariantZeroCornerMap_pure {m n : ℕ} (h : m ≤ n) (d : ℕ)
    (v : Fin d → Matrix (Fin m) (Fin m) A) :
    ((matrixCoinvariantZeroCornerMap k A h).f d).hom
        (((matrixCoinvariantProjection k A m).f d).hom (exteriorPower.ιMulti k d v)) =
      ((matrixCoinvariantProjection k A n).f d).hom
        (exteriorPower.ιMulti k d (fun i => Matrix.zeroExtend h (v i))) := by
  simpa only [matrixCoinvariantZeroCornerMap, Function.comp_def, Matrix.zeroExtendLieHom_apply] using
    adjointCoinvariantMap_pure k (Matrix (Fin m) (Fin m) A)
      (Matrix.scalarLieHom k A m) (Matrix.scalarLieHom k A n)
      (Matrix.zeroExtendLieHom k A h) (Matrix.scalarZeroExtendLieHom k h)
      (Matrix.scalarLieHom_zeroExtend k A h) d v

/-- The identity map of matrix coinvariants at equal sizes.

The equal-size zero-extension map is the identity on the coinvariant complex. -/
@[simp]
theorem matrixCoinvariantZeroCornerMap_id (m : ℕ) :
    matrixCoinvariantZeroCornerMap k A (le_rfl : m ≤ m) = 𝟙 _ := by
  apply (cancel_epi (matrixCoinvariantProjection k A m)).mp
  rw [matrixCoinvariantZeroCornerMap_projection, matrixZeroCornerMap_id,
    Category.id_comp, Category.comp_id]

/-- Composition of matrix coinvariant size maps.

The quotient chain maps for successive size inclusions compose to the quotient map of the
composite size inclusion. -/
theorem matrixCoinvariantZeroCornerMap_comp {m n p : ℕ} (h : m ≤ n) (h' : n ≤ p) :
    matrixCoinvariantZeroCornerMap k A h ≫ matrixCoinvariantZeroCornerMap k A h' =
      matrixCoinvariantZeroCornerMap k A (h.trans h') := by
  apply (cancel_epi (matrixCoinvariantProjection k A m)).mp
  rw [← Category.assoc, matrixCoinvariantZeroCornerMap_projection, Category.assoc,
    matrixCoinvariantZeroCornerMap_projection, ← Category.assoc, matrixZeroCornerMap_comp,
    matrixCoinvariantZeroCornerMap_projection]

/-- The size functor of scalar-adjoint matrix coinvariant complexes.

The coinvariant matrix complexes form a natural-number-indexed functor under top-left zero
extension. -/
def matrixCoinvariantFunctor : ℕ ⥤ ChainComplex (ModuleCat.{max u v} k) ℕ where
  obj m := matrixCoinvariantComplex k A m
  map h := matrixCoinvariantZeroCornerMap k A (leOfHom h)
  map_id m := matrixCoinvariantZeroCornerMap_id k A m
  map_comp h h' := (matrixCoinvariantZeroCornerMap_comp k A (leOfHom h) (leOfHom h')).symm

/-- Comonoid compatibility of matrix coinvariant size maps.

Zero-extension maps preserve the descended coinvariant coproduct and counit. -/
abbrev matrixCoinvariantZeroCornerMapIsComonHom {m n : ℕ} (h : m ≤ n) :=
  adjointCoinvariantMapIsComonHom k (Matrix (Fin m) (Fin m) A)
    (Matrix.scalarLieHom k A m) (Matrix.scalarLieHom k A n)
    (Matrix.zeroExtendLieHom k A h) (Matrix.scalarZeroExtendLieHom k h)
    (Matrix.scalarLieHom_zeroExtend k A h)

section Coefficients

variable {B : Type v} [Ring B] [Algebra k B]

/-- The coefficient map of matrix adjoint coinvariant complexes.

An entry-algebra homomorphism commutes with scalar inclusion and induces a chain map on
scalar-adjoint coinvariants. -/
def matrixCoinvariantCoefficientMap (f : A →ₐ[k] B) (m : ℕ) :
    matrixCoinvariantComplex k A m ⟶ matrixCoinvariantComplex k B m :=
  adjointCoinvariantMap k (Matrix (Fin m) (Fin m) A)
    (Matrix.scalarLieHom k A m) (Matrix.scalarLieHom k B m)
    (Matrix.coefficientLieHom k A f m) LieHom.id
    (by simpa only [LieHom.comp_id] using Matrix.scalarLieHom_coefficient k A f m)

/-- The quotient square for matrix coinvariant coefficient maps.

The quotient projection followed by the coefficient quotient map equals the ordinary
coefficient map followed by the target projection. -/
@[reassoc]
theorem matrixCoinvariantCoefficientMap_projection (f : A →ₐ[k] B) (m : ℕ) :
    matrixCoinvariantProjection k A m ≫ matrixCoinvariantCoefficientMap k A f m =
      matrixCoefficientMap k A f m ≫ matrixCoinvariantProjection k B m :=
  adjointCoinvariantMap_projection k (Matrix (Fin m) (Fin m) A)
    (Matrix.scalarLieHom k A m) (Matrix.scalarLieHom k B m)
    (Matrix.coefficientLieHom k A f m) LieHom.id
    (by simpa only [LieHom.comp_id] using Matrix.scalarLieHom_coefficient k A f m)

/-- The projected-wedge formula for matrix coinvariant coefficients.

The coefficient quotient map sends a projected matrix wedge to the projected wedge of its
entrywise coefficient images. -/
theorem matrixCoinvariantCoefficientMap_pure (f : A →ₐ[k] B) (m d : ℕ)
    (v : Fin d → Matrix (Fin m) (Fin m) A) :
    ((matrixCoinvariantCoefficientMap k A f m).f d).hom
        (((matrixCoinvariantProjection k A m).f d).hom (exteriorPower.ιMulti k d v)) =
      ((matrixCoinvariantProjection k B m).f d).hom
        (exteriorPower.ιMulti k d (fun i => (v i).map f)) :=
  adjointCoinvariantMap_pure k (Matrix (Fin m) (Fin m) A)
    (Matrix.scalarLieHom k A m) (Matrix.scalarLieHom k B m)
    (Matrix.coefficientLieHom k A f m) LieHom.id
    (by simpa only [LieHom.comp_id] using Matrix.scalarLieHom_coefficient k A f m) d v

/-- Size naturality of matrix coinvariant coefficient maps.

Coefficient quotient maps commute with the quotient maps induced by top-left zero extension. -/
theorem matrixCoinvariantCoefficientMap_naturality (f : A →ₐ[k] B) {m n : ℕ} (h : m ≤ n) :
    matrixCoinvariantZeroCornerMap k A h ≫ matrixCoinvariantCoefficientMap k A f n =
      matrixCoinvariantCoefficientMap k A f m ≫ matrixCoinvariantZeroCornerMap k B h := by
  apply (cancel_epi (matrixCoinvariantProjection k A m)).mp
  rw [← Category.assoc, matrixCoinvariantZeroCornerMap_projection, Category.assoc,
    matrixCoinvariantCoefficientMap_projection, ← Category.assoc, matrixCoefficientMap_naturality,
    Category.assoc, ← matrixCoinvariantZeroCornerMap_projection,
    ← Category.assoc]
  have hp := matrixCoinvariantCoefficientMap_projection k A f m
  exact ((congrArg (fun z => z ≫ matrixCoinvariantZeroCornerMap k B h) hp).trans
    (Category.assoc _ _ _)).symm

/-- The coefficient natural transformation of matrix coinvariant systems.

The fixed-size coefficient quotient maps form a natural transformation of the matrix
coinvariant size functors. -/
def matrixCoinvariantCoefficientNatTrans (f : A →ₐ[k] B) :
    matrixCoinvariantFunctor k A ⟶ matrixCoinvariantFunctor k B where
  app m := matrixCoinvariantCoefficientMap k A f m
  naturality m n h := matrixCoinvariantCoefficientMap_naturality k A f (leOfHom h)

/-- Comonoid compatibility of matrix coinvariant coefficient maps.

Entry-algebra quotient maps preserve the descended coinvariant comultiplication and counit. -/
abbrev matrixCoinvariantCoefficientMapIsComonHom (f : A →ₐ[k] B) (m : ℕ) :=
  adjointCoinvariantMapIsComonHom k (Matrix (Fin m) (Fin m) A)
    (Matrix.scalarLieHom k A m) (Matrix.scalarLieHom k B m)
    (Matrix.coefficientLieHom k A f m) LieHom.id
    (by simpa only [LieHom.comp_id] using Matrix.scalarLieHom_coefficient k A f m)

end Coefficients

/-- The homology of a matrix scalar-adjoint coinvariant complex.

Take degree-`d` homology of the matrix coinvariant complex at size `m`. -/
abbrev matrixCoinvariantHomology (m d : ℕ) := (matrixCoinvariantComplex k A m).homology d

/-- The matrix coinvariant homology map of zero extension.

Take the degree-`d` homology map of a coinvariant size-inclusion chain map. -/
def matrixCoinvariantZeroCornerHomologyMap {m n : ℕ} (h : m ≤ n) (d : ℕ) :
    matrixCoinvariantHomology k A m d ⟶ matrixCoinvariantHomology k A n d :=
  HomologicalComplex.homologyMap (matrixCoinvariantZeroCornerMap k A h) d

end ChevalleyEilenberg
