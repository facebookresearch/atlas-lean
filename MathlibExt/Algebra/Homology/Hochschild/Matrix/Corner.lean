/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.Matrix.GeneralizedTrace
public import MathlibExt.Algebra.Homology.Hochschild.Matrix.Coefficients
public import MathlibExt.Algebra.Homology.Hochschild.Maps
public import Mathlib.Data.Matrix.Basis

/-!
# Nonunital matrix corners on Hochschild chains

Let k be a commutative ring, A an associative unital k-algebra, and M an
A-bimodule whose commuting left and right actions are k-linear. For a finite
index type ι and b ∈ ι, write E_bb(x) for the matrix with x in its (b,b)
entry and zero elsewhere. The multiplicative k-linear map a ↦ E_bb(a)
and the coefficient map m ↦ E_bb(m) intertwine both A-actions.

The induced map on C_n(A,M) = M ⊗[k] A^⊗n applies E_bb to every factor.
It commutes with each Hochschild face, including the first right action and
the last left action. Lifting both coefficient modules to height
H = max(u,v,w,z), where k, A, M and ι have independent universes u, v, w
and z, gives a chain map between the corresponding Hochschild complexes.
The algebra map sends 1 to E_bb(1); no unit-preservation premise is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped BigOperators TensorProduct

namespace ModuleCat.Algebra.Hochschild.Matrix

attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

universe u v w z

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M]
  [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
  (ι : Type z) [Fintype ι] [DecidableEq ι]

/-- For a commutative ring k, an associative unital k-algebra A, a finite
matrix index type ι and b ∈ ι, the nonunital k-algebra homomorphism
a ↦ E_bb(a) has entry a at (b,b) and zero at every other entry.
It preserves multiplication and sends 1 to E_bb(1). -/
def cornerAlgHom (b : ι) : A →ₙₐ[k] Matrix ι ι A where
  toFun := cornerLinear k ι b
  map_zero' := (cornerLinear k ι b).map_zero
  map_add' := (cornerLinear k ι b).map_add
  map_mul' a a' := by
    have h (x : A) : cornerLinear k ι b x = Matrix.single b b x := by
      ext i j
      simp only [cornerLinear_apply, Matrix.single_apply, (eq_comm : b = i ↔ i = b),
        (eq_comm : b = j ↔ j = b), ite_and]
      split_ifs <;> rfl
    rw [h, h, h]
    exact (Matrix.single_mul_single_same a b b b a').symm
  map_smul' := (cornerLinear k ι b).map_smul

@[simp]
theorem cornerAlgHom_apply (b : ι) (a : A) :
    cornerAlgHom k A ι b a = cornerLinear k ι b a := rfl

-- Capture the given pointwise k-module before installing either matrix action.
/-- For a k-module M and a matrix index type ι, coefficient matrices
form a k-module by (λ • X)ᵢⱼ = λ • Xᵢⱼ. -/
local instance groundMatrixModule : Module k (Matrix ι ι M) := inferInstance
/-- For a left A-module M and finite ι, matrices over A act on
coefficient matrices by (B • X)ᵢⱼ = ∑ₚ Bᵢₚ • Xₚⱼ. -/
local instance cornerActorLeftModule : Module (Matrix ι ι A) (Matrix ι ι M) :=
  Coefficients.leftModule A M ι
/-- For a right A-module M and finite ι, the opposite matrix algebra
acts on coefficient matrices by (op B • X)ᵢⱼ = ∑ₚ op(Bₚⱼ) • Xᵢₚ. -/
local instance cornerActorRightModule : Module (Matrix ι ι A)ᵐᵒᵖ (Matrix ι ι M) :=
  Coefficients.rightModule A M ι
local instance : SMulCommClass (Matrix ι ι A) (Matrix ι ι A)ᵐᵒᵖ (Matrix ι ι M) :=
  Coefficients.commute A M ι
local instance : IsScalarTower k (Matrix ι ι A) (Matrix ι ι M) :=
  Coefficients.leftTower A M ι k
local instance : IsScalarTower k (Matrix ι ι A)ᵐᵒᵖ (Matrix ι ι M) :=
  Coefficients.rightTower A M ι k

omit [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M] [IsScalarTower k A M]
  [IsScalarTower k Aᵐᵒᵖ M] in
/-- For a left A-module M, a ∈ A, m ∈ M and b ∈ ι, the coefficient
corner satisfies E_bb(a • m) = E_bb(a) • E_bb(m), with the left matrix
action on the right-hand side. No right action on M is needed for this
identity. -/
theorem corner_left (b : ι) (a : A) (m : M) :
    cornerLinear k ι b (a • m) = cornerAlgHom k A ι b a • cornerLinear k ι b m := by
  ext i j
  rw [Coefficients.left_smul_apply]
  by_cases hi : i = b <;> by_cases hj : j = b <;>
    simp [cornerAlgHom_apply, cornerLinear_apply, hi, hj]

omit [Module A M] [SMulCommClass A Aᵐᵒᵖ M] [IsScalarTower k A M]
  [IsScalarTower k Aᵐᵒᵖ M] in
/-- For a right A-module M, a ∈ A, m ∈ M and b ∈ ι, the coefficient
corner satisfies E_bb(op(a) • m) = op(E_bb(a)) • E_bb(m), with the right
matrix action on the right-hand side. No left action on M is needed for
this identity. -/
theorem corner_right (b : ι) (a : A) (m : M) :
    cornerLinear k ι b (MulOpposite.op a • m) =
      MulOpposite.op (cornerAlgHom k A ι b a) • cornerLinear k ι b m := by
  ext i j
  rw [Coefficients.right_smul_apply]
  by_cases hi : i = b <;> by_cases hj : j = b <;>
    simp [cornerAlgHom_apply, cornerLinear_apply, hi, hj, apply_ite]

omit [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M] [IsScalarTower k A M]
  [IsScalarTower k Aᵐᵒᵖ M] in
/-- For k-modules M and A with A a k-algebra, the degree-n tensor
map induced by a ↦ E_bb(a) and m ↦ E_bb(m) is the corner tensor map:
m ⊗ a₁ ⊗ ⋯ ⊗ aₙ ↦ E_bb(m) ⊗ E_bb(a₁) ⊗ ⋯ ⊗ E_bb(aₙ).
This equality of k-linear maps does not require coefficient A-actions. -/
theorem corner_linearMap (b : ι) (n : ℕ) :
    ModuleCat.Algebra.Hochschild.linearMap (cornerAlgHom k A ι b)
      (cornerLinear k ι b : M →ₗ[k] Matrix ι ι M) n = cornerTensor k ι b n := by
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  simp only [ModuleCat.Algebra.Hochschild.linearMap_tprod, cornerTensor_tmul_tprod,
    cornerAlgHom_apply]

/-- Let M be an A-bimodule with commuting k-linear actions. For
every n ≥ 0 and face i ∈ {0,…,n+1}, the corner maps K_n satisfy
δᵢ^Mat ∘ K_(n+1) = K_n ∘ δᵢ^A from C_(n+1)(A,M) to
C_n(Mat_ι(A),Mat_ι(M)). The first and last faces use the right and left
coefficient actions, respectively. -/
theorem corner_face_comm (b : ι) (n : ℕ) (i : Fin (n + 2)) :
    (Coefficients.face A M ι k n i).hom.comp (cornerTensor k ι b (n + 1)) =
      (cornerTensor k ι b n).comp (ModuleCat.Algebra.Hochschild.face k A M n i).hom := by
  have h := ModuleCat.Algebra.Hochschild.linearMap_face_comm
    (k := k) (A := A) (B := Matrix ι ι A) (M := M) (N := Matrix ι ι M)
    (cornerAlgHom k A ι b) (cornerLinear k ι b : M →ₗ[k] Matrix ι ι M)
    (corner_left k A M ι b) (corner_right k A M ι b) n i
  simpa only [corner_linearMap, Coefficients.face] using h

/-- For a k-algebra A and an A-bimodule M with commuting k-linear
actions, the diagonal corner at b ∈ ι defines
C_*(A,ULift^H M) → C_*(Mat_ι(A),ULift^H Mat_ι(M)), where
H = max(u,v,w,z) for the independent worlds of k, A, M and ι.
Its degree maps apply E_bb to the coefficient and all algebra factors. -/
def cornerChainMap (b : ι) :
    ModuleCat.Algebra.Hochschild.chainComplex k A (ULift.{max u v w z} M) ⟶
      ModuleCat.Algebra.Hochschild.chainComplex k (Matrix ι ι A)
        (ULift.{max u v w z} (Matrix ι ι M)) :=
  ModuleCat.Algebra.Hochschild.liftedMap
    (cornerAlgHom k A ι b) (cornerLinear k ι b)
    (corner_left k A M ι b) (corner_right k A M ι b)

/-- For the diagonal-corner chain map at b ∈ ι, its degree-n
component sends up(m) ⊗ a₁ ⊗ ⋯ ⊗ aₙ to
up(E_bb(m)) ⊗ E_bb(a₁) ⊗ ⋯ ⊗ E_bb(aₙ).
Here both coefficient modules are lifted to H = max(u,v,w,z), and M is
an A-bimodule with commuting k-linear actions. -/
theorem cornerChainMap_f_tprod (b : ι) (n : ℕ) (m : M) (a : Fin n → A) :
    ((cornerChainMap k A M ι b).f n).hom
      (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      ULift.up (cornerLinear k ι b m) ⊗ₜ[k]
        PiTensorProduct.tprod k (fun j => cornerLinear k ι b (a j)) := by
  simpa only [cornerChainMap, cornerAlgHom_apply] using
    (ModuleCat.Algebra.Hochschild.liftedMap_f_tprod
      (cornerAlgHom k A ι b) (cornerLinear k ι b)
      (corner_left k A M ι b) (corner_right k A M ι b) n m a)

end ModuleCat.Algebra.Hochschild.Matrix
