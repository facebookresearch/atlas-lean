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
# Scalar-adjoint coinvariants of matrix chains

The scalar special-linear Lie algebra acts on exterior matrix chains through the entrywise
scalar inclusion. Taking coinvariants gives a quotient Chevalley–Eilenberg complex, its
coordinate quotient, coaugmentation, and coalgebra maps.

The right adjoint action is a Lie homomorphism to the opposite endomorphism algebra. Top-left
zero extension and coefficient maps descend to these quotients and preserve projected pure
wedges.
-/

@[expose] public section

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory

universe u v

namespace ChevalleyEilenberg

variable (k : Type u) [CommRing k]
variable (A : Type v) [Ring A] [Algebra k A]

/-- The finite-matrix scalar-action CE cokernel. -/
abbrev matrixCoinvariantComplex (m : ℕ) :=
  adjointCoinvariantComplex k (Matrix (Fin m) (Fin m) A) (Matrix.scalarLieHom k A m)

/-- Its projection from the canonical matrix CE complex. -/
abbrev matrixCoinvariantProjection (m : ℕ) :=
  adjointCoinvariantProjection k (Matrix (Fin m) (Fin m) A) (Matrix.scalarLieHom k A m)

/-- The finite-matrix coinvariant degree module. -/
abbrev matrixCoinvariantModule (m n : ℕ) :=
  adjointCoinvariantModule k (Matrix (Fin m) (Fin m) A) (Matrix.scalarLieHom k A m) n

/-- The degree coordinates of the matrix coinvariant complex. -/
abbrev matrixCoinvariantCoordinateIso (m n : ℕ) :=
  adjointCoinvariantCoordinateIso k (Matrix (Fin m) (Fin m) A) (Matrix.scalarLieHom k A m) n

/-- The right-adjoint endomorphism-valued action, with its linear type. -/
abbrev matrixRightAdjointAction (m n : ℕ) :=
  rightDegreeAdjointAction k (Matrix (Fin m) (Fin m) A) (Matrix.scalarLieHom k A m) n

/-- The same right-adjoint action as an Lie map into the opposite endomorphism algebra. -/
abbrev matrixRightAdjointLieHom (m n : ℕ) :=
  rightDegreeAdjointLieHom k (Matrix (Fin m) (Fin m) A) (Matrix.scalarLieHom k A m) n

/-- The alternating formula for the scalar right-adjoint action. -/
def matrixAdjointPure (m n : ℕ) (s : Matrix.ScalarSpecialLinear k m)
    (v : Fin n → Matrix (Fin m) (Fin m) A) : ⋀[k]^n (Matrix (Fin m) (Fin m) A) :=
  ∑ i : Fin n, exteriorPower.ιMulti k n
    (Function.update v i ⁅v i, Matrix.scalarLieHom k A m s⁆)

theorem matrixRightAdjointAction_pure (m n : ℕ) (s : Matrix.ScalarSpecialLinear k m)
    (v : Fin n → Matrix (Fin m) (Fin m) A) :
    matrixRightAdjointAction k A m n s (exteriorPower.ιMulti k n v) =
      matrixAdjointPure k A m n s v :=
  rightDegreeAdjointAction_pure k (Matrix (Fin m) (Fin m) A) (Matrix.scalarLieHom k A m) n s v

/-- The projection has exactly the source's action-span kernel. -/
theorem matrixCoinvariantProjection_ker (m n : ℕ) :
    LinearMap.ker ((matrixCoinvariantProjection k A m).f n).hom =
      Submodule.span k {y | ∃ (s : Matrix.ScalarSpecialLinear k m)
        (a : ⋀[k]^n (Matrix (Fin m) (Fin m) A)), y = matrixRightAdjointAction k A m n s a} :=
  adjointCoinvariantProjection_ker_right k (Matrix (Fin m) (Fin m) A) (Matrix.scalarLieHom k A m) n

/-- The lawful coaugmented coinvariant coalgebra is a map of the cokernel. -/
abbrev matrixCoinvariantCoalgebra (m : ℕ) :=
  adjointCoinvariantCoalgebra k (Matrix (Fin m) (Fin m) A) (Matrix.scalarLieHom k A m)

/-- The canonical coaugmentation of the finite-matrix coinvariant complex. -/
abbrev matrixCoinvariantCoaug (m : ℕ) :=
  adjointCoinvariantCoaug k (Matrix (Fin m) (Fin m) A) (Matrix.scalarLieHom k A m)

/-- The descended counit on finite-matrix coinvariants. -/
abbrev matrixCoinvariantCounit (m : ℕ) :=
  adjointCoinvariantCounit k (Matrix (Fin m) (Fin m) A) (Matrix.scalarLieHom k A m)

/-- The descended coproduct on finite-matrix coinvariants. -/
abbrev matrixCoinvariantComul (m : ℕ) :=
  adjointCoinvariantComul k (Matrix (Fin m) (Fin m) A) (Matrix.scalarLieHom k A m)

/-- Every zero corner induces the coinvariant chain map. -/
def matrixCoinvariantZeroCornerMap {m n : ℕ} (h : m ≤ n) :
    matrixCoinvariantComplex k A m ⟶ matrixCoinvariantComplex k A n :=
  adjointCoinvariantMap k (Matrix (Fin m) (Fin m) A)
    (Matrix.scalarLieHom k A m) (Matrix.scalarLieHom k A n)
    (Matrix.zeroExtendLieHom k A h) (Matrix.scalarZeroExtendLieHom k h)
    (Matrix.scalarLieHom_zeroExtend k A h)

@[reassoc]
theorem matrixCoinvariantZeroCornerMap_projection {m n : ℕ} (h : m ≤ n) :
    matrixCoinvariantProjection k A m ≫ matrixCoinvariantZeroCornerMap k A h =
      matrixZeroCornerMap k A h ≫ matrixCoinvariantProjection k A n :=
  adjointCoinvariantMap_projection k (Matrix (Fin m) (Fin m) A)
    (Matrix.scalarLieHom k A m) (Matrix.scalarLieHom k A n)
    (Matrix.zeroExtendLieHom k A h) (Matrix.scalarZeroExtendLieHom k h)
    (Matrix.scalarLieHom_zeroExtend k A h)

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

@[simp]
theorem matrixCoinvariantZeroCornerMap_id (m : ℕ) :
    matrixCoinvariantZeroCornerMap k A (le_rfl : m ≤ m) = 𝟙 _ := by
  apply (cancel_epi (matrixCoinvariantProjection k A m)).mp
  rw [matrixCoinvariantZeroCornerMap_projection, matrixZeroCornerMap_id,
    Category.id_comp, Category.comp_id]

theorem matrixCoinvariantZeroCornerMap_comp {m n p : ℕ} (h : m ≤ n) (h' : n ≤ p) :
    matrixCoinvariantZeroCornerMap k A h ≫ matrixCoinvariantZeroCornerMap k A h' =
      matrixCoinvariantZeroCornerMap k A (h.trans h') := by
  apply (cancel_epi (matrixCoinvariantProjection k A m)).mp
  rw [← Category.assoc, matrixCoinvariantZeroCornerMap_projection, Category.assoc,
    matrixCoinvariantZeroCornerMap_projection, ← Category.assoc, matrixZeroCornerMap_comp,
    matrixCoinvariantZeroCornerMap_projection]

/-- Finite matrix coinvariant complexes form a functor. -/
def matrixCoinvariantFunctor : ℕ ⥤ ChainComplex (ModuleCat.{max u v} k) ℕ where
  obj m := matrixCoinvariantComplex k A m
  map h := matrixCoinvariantZeroCornerMap k A (leOfHom h)
  map_id m := matrixCoinvariantZeroCornerMap_id k A m
  map_comp h h' := (matrixCoinvariantZeroCornerMap_comp k A (leOfHom h) (leOfHom h')).symm

/-- The zero-corner map has coinvariant coalgebra compatibility. -/
abbrev matrixCoinvariantZeroCornerMapIsComonHom {m n : ℕ} (h : m ≤ n) :=
  adjointCoinvariantMapIsComonHom k (Matrix (Fin m) (Fin m) A)
    (Matrix.scalarLieHom k A m) (Matrix.scalarLieHom k A n)
    (Matrix.zeroExtendLieHom k A h) (Matrix.scalarZeroExtendLieHom k h)
    (Matrix.scalarLieHom_zeroExtend k A h)

section Coefficients

variable {B : Type v} [Ring B] [Algebra k B]

/-- Coefficient algebra maps descend through the matrix coinvariant cokernels. -/
def matrixCoinvariantCoefficientMap (f : A →ₐ[k] B) (m : ℕ) :
    matrixCoinvariantComplex k A m ⟶ matrixCoinvariantComplex k B m :=
  adjointCoinvariantMap k (Matrix (Fin m) (Fin m) A)
    (Matrix.scalarLieHom k A m) (Matrix.scalarLieHom k B m)
    (Matrix.coefficientLieHom k A f m) LieHom.id
    (by simpa only [LieHom.comp_id] using Matrix.scalarLieHom_coefficient k A f m)

@[reassoc]
theorem matrixCoinvariantCoefficientMap_projection (f : A →ₐ[k] B) (m : ℕ) :
    matrixCoinvariantProjection k A m ≫ matrixCoinvariantCoefficientMap k A f m =
      matrixCoefficientMap k A f m ≫ matrixCoinvariantProjection k B m :=
  adjointCoinvariantMap_projection k (Matrix (Fin m) (Fin m) A)
    (Matrix.scalarLieHom k A m) (Matrix.scalarLieHom k B m)
    (Matrix.coefficientLieHom k A f m) LieHom.id
    (by simpa only [LieHom.comp_id] using Matrix.scalarLieHom_coefficient k A f m)

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

/-- Size and coefficient naturality of the matrix coinvariant maps. -/
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

/-- Coefficient maps are natural transformations of finite coinvariant systems. -/
def matrixCoinvariantCoefficientNatTrans (f : A →ₐ[k] B) :
    matrixCoinvariantFunctor k A ⟶ matrixCoinvariantFunctor k B where
  app m := matrixCoinvariantCoefficientMap k A f m
  naturality m n h := matrixCoinvariantCoefficientMap_naturality k A f (leOfHom h)

/-- The coefficient map has coalgebra compatibility. -/
abbrev matrixCoinvariantCoefficientMapIsComonHom (f : A →ₐ[k] B) (m : ℕ) :=
  adjointCoinvariantMapIsComonHom k (Matrix (Fin m) (Fin m) A)
    (Matrix.scalarLieHom k A m) (Matrix.scalarLieHom k B m)
    (Matrix.coefficientLieHom k A f m) LieHom.id
    (by simpa only [LieHom.comp_id] using Matrix.scalarLieHom_coefficient k A f m)

end Coefficients

/-- The quotient homology module, with no stored homology data. -/
abbrev matrixCoinvariantHomology (m d : ℕ) := (matrixCoinvariantComplex k A m).homology d

/-- The quotient homology map of a zero corner. -/
def matrixCoinvariantZeroCornerHomologyMap {m n : ℕ} (h : m ≤ n) (d : ℕ) :
    matrixCoinvariantHomology k A m d ⟶ matrixCoinvariantHomology k A n d :=
  HomologicalComplex.homologyMap (matrixCoinvariantZeroCornerMap k A h) d

end ChevalleyEilenberg
