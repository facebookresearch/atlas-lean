/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.LinearAlgebra.Matrix.Module
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Algebra.Opposite
public import MathlibExt.Algebra.Homology.Hochschild.Basic

/-!
# Matrix coefficient bimodules

Row matrix actions, additive transpose and the opposite
matrix-ring equivalence define the matrix bimodule.
The pointwise ground action and commuting scalar
towers give its coefficient Hochschild complex, with
independent algebra, coefficient and index universes.

Reference: Weibel, Homological Algebra, §9.5.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped BigOperators TensorProduct

namespace ModuleCat.Algebra.Hochschild.Matrix.Coefficients

universe u v w z

variable (A : Type v) [Ring A] (M : Type w) [AddCommGroup M]
  (ι : Type z) [Fintype ι] [DecidableEq ι]

/-- The left action is the native matrix module on a vector of rows. -/
def leftModule [Module A M] : Module (Matrix ι ι A) (Matrix ι ι M) :=
  Matrix.Module.matrixModule

/-- The right action is native row action over the opposite ring,
transported by transpose and the native opposite matrix-ring equivalence. -/
def rightModule [Module Aᵐᵒᵖ M] : Module (Matrix ι ι A)ᵐᵒᵖ (Matrix ι ι M) := by
  letI rows : Module (Matrix ι ι Aᵐᵒᵖ) (Matrix ι ι M) := Matrix.Module.matrixModule
  letI transposed : Module (Matrix ι ι Aᵐᵒᵖ) (Matrix ι ι M) :=
    (Matrix.transposeAddEquiv ι ι M).module _
  exact Module.compHom _ (RingEquiv.mopMatrix.symm.toRingHom)

theorem left_smul_apply [Module A M] (B : Matrix ι ι A) (X : Matrix ι ι M)
    (i j : ι) :
    letI : Module (Matrix ι ι A) (Matrix ι ι M) := leftModule A M ι
    (B • X) i j = ∑ p : ι, B i p • X p j := by
  let : Module (Matrix ι ι A) (Matrix ι ι M) := leftModule A M ι
  change (∑ p : ι, B i p • X p) j = ∑ p : ι, B i p • X p j
  simp only [Finset.sum_apply, Pi.smul_apply]

theorem right_smul_apply [Module Aᵐᵒᵖ M]
    (B : (Matrix ι ι A)ᵐᵒᵖ) (X : Matrix ι ι M) (i j : ι) :
    letI : Module (Matrix ι ι A)ᵐᵒᵖ (Matrix ι ι M) := rightModule A M ι
    (B • X) i j = ∑ q : ι, MulOpposite.op (B.unop q j) • X i q := by
  let : Module (Matrix ι ι A)ᵐᵒᵖ (Matrix ι ι M) := rightModule A M ι
  change (∑ q : ι, MulOpposite.op (B.unop q j) • (fun i' => X i' q)) i =
    ∑ q : ι, MulOpposite.op (B.unop q j) • X i q
  simp only [Finset.sum_apply, Pi.smul_apply]

/-- The computed left action on self coefficients is the regular matrix module. -/
theorem leftModule_self_eq :
    leftModule A A ι = (Semiring.toModule : Module (Matrix ι ι A) (Matrix ι ι A)) := by
  apply Module.ext'
  intro B X
  ext i j
  rw [left_smul_apply]
  change (∑ p : ι, B i p * X p j) = (B * X) i j
  exact Matrix.mul_apply.symm

/-- The computed right action on self coefficients is the regular right module. -/
theorem rightModule_self_eq :
    rightModule A A ι =
      (Semiring.toOppositeModule : Module (Matrix ι ι A)ᵐᵒᵖ (Matrix ι ι A)) := by
  apply Module.ext'
  intro B X
  ext i j
  rw [right_smul_apply]
  change (∑ q : ι, X i q * B.unop q j) = (X * B.unop) i j
  exact Matrix.mul_apply.symm

/-- Commutation of the computed matrix actions follows from that on M. -/
theorem commute [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M] :
    letI : Module (Matrix ι ι A) (Matrix ι ι M) := leftModule A M ι
    letI : Module (Matrix ι ι A)ᵐᵒᵖ (Matrix ι ι M) := rightModule A M ι
    SMulCommClass (Matrix ι ι A) (Matrix ι ι A)ᵐᵒᵖ (Matrix ι ι M) := by
  let : Module (Matrix ι ι A) (Matrix ι ι M) := leftModule A M ι
  let : Module (Matrix ι ι A)ᵐᵒᵖ (Matrix ι ι M) := rightModule A M ι
  constructor
  intro B C X
  ext i j
  calc
    (B • (C • X)) i j =
        ∑ p : ι, ∑ q : ι, B i p • (MulOpposite.op (C.unop q j) • X p q) := by
      rw [left_smul_apply]
      apply Finset.sum_congr rfl
      intro p _
      rw [right_smul_apply, Finset.smul_sum]
    _ = ∑ q : ι, ∑ p : ι, MulOpposite.op (C.unop q j) • (B i p • X p q) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro p _
      exact smul_comm _ _ _
    _ = (C • (B • X)) i j := by
      rw [right_smul_apply]
      apply Finset.sum_congr rfl
      intro q _
      rw [left_smul_apply, Finset.smul_sum]

variable (k : Type u) [CommRing k] [Algebra k A] [Module k M]

/-- Scalar diagonal matrices act through the original ground module. -/
theorem leftTower [Module A M] [IsScalarTower k A M] :
    letI : Module (Matrix ι ι A) (Matrix ι ι M) := leftModule A M ι
    IsScalarTower k (Matrix ι ι A) (Matrix ι ι M) := by
  let : Module (Matrix ι ι A) (Matrix ι ι M) := leftModule A M ι
  apply IsScalarTower.of_algebraMap_smul
  intro c X
  ext i j
  rw [left_smul_apply]
  simp [Matrix.algebraMap_matrix_apply,
    IsScalarTower.algebraMap_smul A]

/-- The opposite scalar diagonal has the same given ground action on M. -/
theorem rightTower [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M] :
    letI : Module (Matrix ι ι A)ᵐᵒᵖ (Matrix ι ι M) := rightModule A M ι
    IsScalarTower k (Matrix ι ι A)ᵐᵒᵖ (Matrix ι ι M) := by
  let : Module (Matrix ι ι A)ᵐᵒᵖ (Matrix ι ι M) := rightModule A M ι
  apply IsScalarTower.of_algebraMap_smul
  intro c X
  ext i j
  rw [right_smul_apply]
  have hc (m : M) : MulOpposite.op (algebraMap k A c) • m = c • m := by
    simpa only [MulOpposite.algebraMap_apply] using
      (IsScalarTower.algebraMap_smul Aᵐᵒᵖ c m)
  simp [MulOpposite.algebraMap_apply, Matrix.algebraMap_matrix_apply, apply_ite,
    hc]

section CanonicalBar

variable [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]

-- Keep the given pointwise k-module separate from both computed matrix modules.
/-- The original pointwise ground module, captured before the matrix algebra actions. -/
local instance groundMatrixModule : Module k (Matrix ι ι M) := inferInstance
/-- The native left matrix-algebra action on the original coefficient matrix. -/
local instance actorLeftModule : Module (Matrix ι ι A) (Matrix ι ι M) := leftModule A M ι
/-- The native right matrix-algebra action, with the original coefficient carrier. -/
local instance actorRightModule : Module (Matrix ι ι A)ᵐᵒᵖ (Matrix ι ι M) := rightModule A M ι
local instance : SMulCommClass (Matrix ι ι A) (Matrix ι ι A)ᵐᵒᵖ (Matrix ι ι M) :=
  commute A M ι
local instance : IsScalarTower k (Matrix ι ι A) (Matrix ι ι M) := leftTower A M ι k
local instance : IsScalarTower k (Matrix ι ι A)ᵐᵒᵖ (Matrix ι ι M) := rightTower A M ι k

/-- The canonical coefficient bar on the computed matrix bimodule. -/
def bar : SimplicialObject (ModuleCat.{max u v w z} k) :=
  ModuleCat.Algebra.Hochschild.coefficientBar k (Matrix ι ι A) (Matrix ι ι M)

/-- The canonical matrix coefficient complex. -/
def complex : ChainComplex (ModuleCat.{max u v w z} k) ℕ :=
  ModuleCat.Algebra.Hochschild.chainComplex k (Matrix ι ι A) (Matrix ι ι M)

/-- The bar coordinates keep the original pointwise ground module. -/
def objIso (n : ℕ) :
    (bar A M ι k).obj (Opposite.op (SimplexCategory.mk n)) ≅
      ModuleCat.of k (Matrix ι ι M ⊗[k] TensorPower k n (Matrix ι ι A)) :=
  ModuleCat.Algebra.Hochschild.coefficientBarObjIso k (Matrix ι ι A) (Matrix ι ι M) n

/-- The canonical face map on the matrix coefficient tensor level. -/
def face (n : ℕ) (i : Fin (n + 2)) :
    ModuleCat.of k (Matrix ι ι M ⊗[k] TensorPower k (n + 1) (Matrix ι ι A)) ⟶
      ModuleCat.of k (Matrix ι ι M ⊗[k] TensorPower k n (Matrix ι ι A)) :=
  ModuleCat.Algebra.Hochschild.face k (Matrix ι ι A) (Matrix ι ι M) n i

/-- The first matrix face is the given right matrix action. -/
theorem face_first_tprod (n : ℕ) (X : Matrix ι ι M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    (face A M ι k n 0).hom (X ⊗ₜ[k] PiTensorProduct.tprod k a) =
      (fun i j => ∑ q : ι, MulOpposite.op (a 0 q j) • X i q) ⊗ₜ[k]
        PiTensorProduct.tprod k (ModuleCat.Algebra.Hochschild.hochschildDropFirst a) := by
  change (ModuleCat.Algebra.Hochschild.face k (Matrix ι ι A) (Matrix ι ι M) n 0).hom
    (X ⊗ₜ[k] PiTensorProduct.tprod k a) = _
  rw [ModuleCat.Algebra.Hochschild.face_first_tprod]
  apply congrArg (fun Y : Matrix ι ι M => Y ⊗ₜ[k]
    PiTensorProduct.tprod k (ModuleCat.Algebra.Hochschild.hochschildDropFirst a))
  funext i j
  exact right_smul_apply A M ι (MulOpposite.op (a 0)) X i j

/-- Every interior matrix face keeps the source matrix product order. -/
theorem face_inner_tprod (n : ℕ) (i : Fin n) (X : Matrix ι ι M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    (face A M ι k n i.castSucc.succ).hom (X ⊗ₜ[k] PiTensorProduct.tprod k a) =
      X ⊗ₜ[k] PiTensorProduct.tprod k
        (ModuleCat.Algebra.Hochschild.hochschildMulAdjacent i a) :=
  ModuleCat.Algebra.Hochschild.face_inner_tprod k (Matrix ι ι A) (Matrix ι ι M) n i X a

/-- The last matrix face is the given left matrix action. -/
theorem face_last_tprod (n : ℕ) (X : Matrix ι ι M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    (face A M ι k n (Fin.last (n + 1))).hom (X ⊗ₜ[k] PiTensorProduct.tprod k a) =
      (fun i j => ∑ p : ι, a (Fin.last n) i p • X p j) ⊗ₜ[k]
        PiTensorProduct.tprod k (ModuleCat.Algebra.Hochschild.hochschildDropLast a) := by
  change (ModuleCat.Algebra.Hochschild.face k (Matrix ι ι A) (Matrix ι ι M)
    n (Fin.last (n + 1))).hom (X ⊗ₜ[k] PiTensorProduct.tprod k a) = _
  rw [ModuleCat.Algebra.Hochschild.face_last_tprod]
  apply congrArg (fun Y : Matrix ι ι M => Y ⊗ₜ[k]
    PiTensorProduct.tprod k (ModuleCat.Algebra.Hochschild.hochschildDropLast a))
  funext i j
  exact left_smul_apply A M ι (a (Fin.last n)) X i j

end CanonicalBar

end ModuleCat.Algebra.Hochschild.Matrix.Coefficients
