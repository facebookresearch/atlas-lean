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
# Left and right actions on matrix coefficients

Let A be an associative unital ring, M an A-bimodule with commuting
actions, and ι a finite index type with decidable equality.
The coefficient matrix module Mat_ι(M) has actions
(BX)_{ij}=∑_p B_{ip}•X_{pj},
(XB)_{ij}=∑_q op(B_{qj}) • X_{iq}.
The right action is represented over Mat_ι(A)ᵐᵒᵖ.
For M=A these are the regular matrix multiplications.

With k commutative, A a k-algebra and the coefficient actions
k-compatible, these give the matrix coefficient Hochschild bar and
chain complex. Their degree-n term is
Mat_ι(M)⊗[k]Mat_ι(A)^{⊗n}.
The first face acts on the right, the interior faces multiply adjacent
matrices, and the last acts on the left. Scalar, algebra, coefficient
and index universes are independent, in height max{u,v,w,z}.

Reference: C. A. Weibel, An Introduction to Homological Algebra, §9.5.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped BigOperators TensorProduct Matrix.Module

namespace ModuleCat.Algebra.Hochschild.Matrix.Coefficients

universe u v w z

variable (A : Type v) [Ring A] (M : Type w) [AddCommGroup M]
  (ι : Type z) [Fintype ι] [DecidableEq ι]

/-- Let A be a ring, M a left A-module and ι finite with
decidable equality. The left Mat_ι(A)-action on Mat_ι(M) is
(B•X)_{ij}=∑_p B_{ip}•X_{pj}. -/
@[instance_reducible]
def leftModule [Module A M] : Module (Matrix ι ι A) (Matrix ι ι M) :=
  Matrix.Module.matrixModule

/-- Let A be a ring, M a right A-module and ι finite with
decidable equality. The Mat_ι(A)ᵐᵒᵖ-action is
(op B•X)_{ij}=∑_q op(B_{qj}) • X_{iq}, using the right A-action. -/
@[instance_reducible]
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

/-- For a ring A and finite ι with decidable equality, the
left matrix module on Mat_ι(A) is regular multiplication: B•X=BX. -/
theorem leftModule_self_eq :
    leftModule A A ι = (Semiring.toModule : Module (Matrix ι ι A) (Matrix ι ι A)) := by
  apply Module.ext'
  intro B X
  ext i j
  rw [left_smul_apply]
  change (∑ p : ι, B i p * X p j) = (B * X) i j
  exact Matrix.mul_apply.symm

/-- For a ring A and finite ι with decidable equality, the
right matrix module on Mat_ι(A) is regular multiplication: op B•X=XB. -/
theorem rightModule_self_eq :
    rightModule A A ι =
      (Semiring.toOppositeModule : Module (Matrix ι ι A)ᵐᵒᵖ (Matrix ι ι A)) := by
  apply Module.ext'
  intro B X
  ext i j
  rw [right_smul_apply]
  change (∑ q : ι, X i q * B.unop q j) = (X * B.unop) i j
  exact Matrix.mul_apply.symm

/-- Let A be an associative unital ring, M an A-bimodule with
commuting left and right actions, and ι a finite type with decidable
equality.
The matrix actions commute:
B•(op D•X)=op D•(B•X), by entrywise commutation of the
left and right A-actions. -/
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

/-- Let k be commutative, A a k-algebra and M a left A-module
with compatible k-action. For finite ι with decidable equality,
the scalar diagonal algMap_k(λ) acts on Mat_ι(M) entrywise by λ. -/
theorem leftTower [Module A M] [IsScalarTower k A M] :
    letI : Module (Matrix ι ι A) (Matrix ι ι M) := leftModule A M ι
    IsScalarTower k (Matrix ι ι A) (Matrix ι ι M) := by
  let : Module (Matrix ι ι A) (Matrix ι ι M) := leftModule A M ι
  infer_instance

/-- Let k be commutative, A a k-algebra and M a right A-module
with compatible k-action. For finite ι with decidable equality,
the opposite scalar diagonal acts entrywise by the same λ∈k. -/
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
/-- For k commutative, a k-module M and any matrix index ι,
the ground action on coefficient matrices is pointwise:
(λ•X)_{ij}=λ•X_{ij}. -/
scoped instance groundMatrixModule : Module k (Matrix ι ι M) := inferInstance
/-- Let A be an associative unital ring, M an A-bimodule with
commuting left and right actions, and ι a finite type with decidable
equality.
Let k be commutative, A a k-algebra and the two actions on M
compatible with its k-module structure.
The left matrix actor is the row-product module
(B•X)_{ij}=∑_p B_{ip}•X_{pj}. -/
scoped instance actorLeftModule : Module (Matrix ι ι A) (Matrix ι ι M) := leftModule A M ι
/-- Let A be an associative unital ring, M an A-bimodule with
commuting left and right actions, and ι a finite type with decidable
equality.
Let k be commutative, A a k-algebra and the two actions on M
compatible with its k-module structure.
The right matrix actor uses
(op B•X)_{ij}=∑_q op(B_{qj})•X_{iq}. -/
scoped instance actorRightModule : Module (Matrix ι ι A)ᵐᵒᵖ (Matrix ι ι M) := rightModule A M ι
scoped instance actorCommute :
    SMulCommClass (Matrix ι ι A) (Matrix ι ι A)ᵐᵒᵖ (Matrix ι ι M) :=
  commute A M ι
scoped instance actorLeftTower : IsScalarTower k (Matrix ι ι A) (Matrix ι ι M) :=
  leftTower A M ι k
scoped instance actorRightTower : IsScalarTower k (Matrix ι ι A)ᵐᵒᵖ (Matrix ι ι M) :=
  rightTower A M ι k

open scoped ModuleCat.Algebra.Hochschild.Matrix.Coefficients

/-- Let A be an associative unital ring, M an A-bimodule with
commuting left and right actions, and ι a finite type with decidable
equality.
Let k be commutative, A a k-algebra and the two actions on M
compatible with its k-module structure.
The coefficient simplicial bar of Mat_ι(A) with Mat_ι(M)
uses the two matrix actions and the pointwise ground k-module. -/
def bar : SimplicialObject (ModuleCat.{max u v w z} k) :=
  ModuleCat.Algebra.Hochschild.coefficientBar k (Matrix ι ι A) (Matrix ι ι M)

/-- Let A be an associative unital ring, M an A-bimodule with
commuting left and right actions, and ι a finite type with decidable
equality.
Let k be commutative, A a k-algebra and the two actions on M
compatible with its k-module structure.
The matrix coefficient Hochschild complex has terms
Mat_ι(M)⊗[k]Mat_ι(A)^{⊗n} with the alternating face boundary. -/
def complex : ChainComplex (ModuleCat.{max u v w z} k) ℕ :=
  ModuleCat.Algebra.Hochschild.chainComplex k (Matrix ι ι A) (Matrix ι ι M)

/-- Let A be an associative unital ring, M an A-bimodule with
commuting left and right actions, and ι a finite type with decidable
equality.
Let k be commutative, A a k-algebra and the two actions on M
compatible with its k-module structure.
The degree-n bar object is canonically isomorphic to
Mat_ι(M)⊗[k]Mat_ι(A)^{⊗n} as a k-module. -/
def objIso (n : ℕ) :
    (bar A M ι k).obj (Opposite.op (SimplexCategory.mk n)) ≅
      ModuleCat.of k (Matrix ι ι M ⊗[k] TensorPower k n (Matrix ι ι A)) :=
  ModuleCat.Algebra.Hochschild.coefficientBarObjIso k (Matrix ι ι A) (Matrix ι ι M) n

/-- Let A be an associative unital ring, M an A-bimodule with
commuting left and right actions, and ι a finite type with decidable
equality.
Let k be commutative, A a k-algebra and the two actions on M
compatible with its k-module structure.
The matrix coefficient faces use right action first, ordered
adjacent matrix multiplication in the interior, and left action last. -/
def face (n : ℕ) (i : Fin (n + 2)) :
    ModuleCat.of k (Matrix ι ι M ⊗[k] TensorPower k (n + 1) (Matrix ι ι A)) ⟶
      ModuleCat.of k (Matrix ι ι M ⊗[k] TensorPower k n (Matrix ι ι A)) :=
  ModuleCat.Algebra.Hochschild.face k (Matrix ι ι A) (Matrix ι ι M) n i

/-- Let A be an associative unital ring, M an A-bimodule with
commuting left and right actions, and ι a finite type with decidable
equality.
Let k be commutative, A a k-algebra and the two actions on M
compatible with its k-module structure.
The first face sends X⊗B_1⊗⋯⊗B_{n+1} to
(XB_1)⊗B_2⊗⋯⊗B_{n+1}, where
(XB_1)_{ij}=∑_q op((B_1)_{qj}) • X_{iq}. -/
theorem face_first_tprod (n : ℕ) (X : Matrix ι ι M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    (face A M ι k n 0).hom (X ⊗ₜ[k] PiTensorProduct.tprod k a) =
      (Matrix.of fun i j => ∑ q : ι, MulOpposite.op (a 0 q j) • X i q) ⊗ₜ[k]
        PiTensorProduct.tprod k (ModuleCat.Algebra.Hochschild.hochschildDropFirst a) := by
  change (ModuleCat.Algebra.Hochschild.face k (Matrix ι ι A) (Matrix ι ι M) n 0).hom
    (X ⊗ₜ[k] PiTensorProduct.tprod k a) = _
  rw [ModuleCat.Algebra.Hochschild.face_first_tprod]
  apply congrArg (fun Y : Matrix ι ι M => Y ⊗ₜ[k]
    PiTensorProduct.tprod k (ModuleCat.Algebra.Hochschild.hochschildDropFirst a))
  funext i j
  exact right_smul_apply A M ι (MulOpposite.op (a 0)) X i j

/-- Let A be an associative unital ring, M an A-bimodule with
commuting left and right actions, and ι a finite type with decidable
equality.
Let k be commutative, A a k-algebra and the two actions on M
compatible with its k-module structure.
An interior face leaves X fixed and replaces B_i,B_{i+1}
by their ordered matrix product B_iB_{i+1}. -/
theorem face_inner_tprod (n : ℕ) (i : Fin n) (X : Matrix ι ι M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    (face A M ι k n i.castSucc.succ).hom (X ⊗ₜ[k] PiTensorProduct.tprod k a) =
      X ⊗ₜ[k] PiTensorProduct.tprod k
        (ModuleCat.Algebra.Hochschild.hochschildMulAdjacent i a) :=
  ModuleCat.Algebra.Hochschild.face_inner_tprod k (Matrix ι ι A) (Matrix ι ι M) n i X a

/-- Let A be an associative unital ring, M an A-bimodule with
commuting left and right actions, and ι a finite type with decidable
equality.
Let k be commutative, A a k-algebra and the two actions on M
compatible with its k-module structure.
The last face sends X⊗B_1⊗⋯⊗B_{n+1} to
(B_{n+1}X)⊗B_1⊗⋯⊗B_n, using entries
∑_p(B_{n+1})_{ip}•X_{pj}. -/
theorem face_last_tprod (n : ℕ) (X : Matrix ι ι M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    (face A M ι k n (Fin.last (n + 1))).hom (X ⊗ₜ[k] PiTensorProduct.tprod k a) =
      (Matrix.of fun i j => ∑ p : ι, a (Fin.last n) i p • X p j) ⊗ₜ[k]
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
