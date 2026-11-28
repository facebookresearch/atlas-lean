/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Lie.TensorProduct
public import Mathlib.LinearAlgebra.BilinearMap
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.Exterior
import Mathlib.Tactic.Abel

/-!
# The exterior boundary with left Lie coefficients

Let R be a commutative ring, L an R-Lie algebra and M a compatible
left Lie module. On P=ExteriorAlgebra_R(L)⊗M, define the diagonal
Lie action T_x=ad_x⊗id+id⊗[x,−] and insertion c_x(a⊗m)=ι(x)a⊗m.
The coefficient boundary D is determined by
D(r⊗m)=0 for exterior scalars and D c_x=−T_x−c_xD.

The diagonal representation satisfies its commutator law and
T_x c_y=c_{[x,y]}+c_y T_x. The exterior quadratic relation gives c_x²=0.
Together these identities yield DT_x=T_xD and D²=0.
On a single exterior generator the boundary is
D(ι(x)⊗m)=−1⊗[x,m].

The scalar, Lie-carrier and coefficient universes are independent;
M is any compatible left Lie module.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]
variable (M : Type w) [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M]

local notation "E" => ExteriorAlgebra R L
local notation "P" => E ⊗[R] M
local notation "F" => M →ₗ[R] P

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
Put E=ExteriorAlgebra_R(L), P=E⊗_R M,
T_x=ad_x⊗id+id⊗[x,−], and c_x(a⊗m)=ι(x)a⊗m.
The diagonal representation L→End_R(P) has value
T_x(a⊗m)=ad_x(a)⊗m+a⊗[x,m]. -/
def coefficientDiagonalAction : L →ₗ⁅R⁆ Module.End R P := by
  letI : LieRingModule L E := LieRingModule.compLieHom E (adjointAction R L)
  letI : LieModule R L E := LieModule.compLieHom E (adjointAction R L)
  exact LieModule.toEnd R L P

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
Put E=ExteriorAlgebra_R(L), P=E⊗_R M,
T_x=ad_x⊗id+id⊗[x,−], and c_x(a⊗m)=ι(x)a⊗m.
On a pure tensor, T_x(a⊗m)=ad_x(a)⊗m+a⊗[x,m]. -/
@[simp]
theorem coefficientDiagonalAction_tmul (x : L) (a : E) (m : M) :
    coefficientDiagonalAction R L M x (a ⊗ₜ[R] m) =
      adjointAction R L x a ⊗ₜ[R] m + a ⊗ₜ[R] ⁅x, m⁆ := by
  let _ : LieRingModule L E := LieRingModule.compLieHom E (adjointAction R L)
  let _ : LieModule R L E := LieModule.compLieHom E (adjointAction R L)
  change ⁅x, a ⊗ₜ[R] m⁆ = _
  rw [TensorProduct.LieModule.lie_tmul_right]
  rfl

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
Put E=ExteriorAlgebra_R(L), P=E⊗_R M,
T_x=ad_x⊗id+id⊗[x,−], and c_x(a⊗m)=ι(x)a⊗m.
On exterior scalars, the adjoint term is zero:
T_x(r⊗m)=r⊗[x,m] for r∈R. -/
theorem coefficientDiagonalAction_algebraMap_tmul (x : L) (r : R) (m : M) :
    coefficientDiagonalAction R L M x ((algebraMap R E r) ⊗ₜ[R] m) =
      (algebraMap R E r) ⊗ₜ[R] ⁅x, m⁆ := by
  rw [coefficientDiagonalAction_tmul, adjointAction_algebraMap,
    TensorProduct.zero_tmul, zero_add]

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
Put E=ExteriorAlgebra_R(L), P=E⊗_R M,
T_x=ad_x⊗id+id⊗[x,−], and c_x(a⊗m)=ι(x)a⊗m.
The empty exterior word has diagonal action
T_x(1⊗m)=1⊗[x,m]. -/
theorem coefficientDiagonalAction_one_tmul (x : L) (m : M) :
    coefficientDiagonalAction R L M x ((1 : E) ⊗ₜ[R] m) =
      (1 : E) ⊗ₜ[R] ⁅x, m⁆ := by
  simpa only [map_one] using coefficientDiagonalAction_algebraMap_tmul R L M x 1 m

/-- Let R be commutative, L an R-Lie algebra and M an R-module.
Put E=ExteriorAlgebra_R(L) and P=E⊗_R M.
Insertion is the R-linear operator c_x:P→P, x∈L,
with c_x(a⊗m)=ι(x)a⊗m. -/
def coefficientInsertion : L →ₗ[R] Module.End R P :=
  (LinearMap.rTensorHom M).comp
    ((Algebra.lmul R E).toLinearMap.comp (ExteriorAlgebra.ι R))

omit [LieRingModule L M] [LieModule R L M] in
/-- Let R be commutative, L an R-Lie algebra and M an R-module.
Put E=ExteriorAlgebra_R(L) and P=E⊗_R M.
The insertion operator has pure-tensor value
c_x(a⊗m)=ι(x)a⊗m, leaving the coefficient unchanged. -/
@[simp]
theorem coefficientInsertion_tmul (x : L) (a : E) (m : M) :
    coefficientInsertion R L M x (a ⊗ₜ[R] m) =
      (ExteriorAlgebra.ι R x * a) ⊗ₜ[R] m :=
  rfl

omit [LieRingModule L M] [LieModule R L M] in
/-- Let R be commutative, L an R-Lie algebra and M an R-module.
Put E=ExteriorAlgebra_R(L) and P=E⊗_R M.
For every x∈L, insertion twice gives c_x²=0,
since ι(x)²=0 in E. -/
theorem coefficientInsertion_comp_self (x : L) :
    (coefficientInsertion R L M x).comp (coefficientInsertion R L M x) = 0 := by
  apply TensorProduct.ext'
  intro a m
  change (ExteriorAlgebra.ι R x * (ExteriorAlgebra.ι R x * a)) ⊗ₜ[R] m = 0
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul, TensorProduct.zero_tmul]

omit [LieRingModule L M] [LieModule R L M] in
/-- Let R be commutative, L an R-Lie algebra and M an R-module.
Put E=ExteriorAlgebra_R(L) and P=E⊗_R M.
For every p∈P, inserting x twice gives c_x(c_x(p))=0. -/
theorem coefficientInsertion_squared (x : L) (p : P) :
    coefficientInsertion R L M x (coefficientInsertion R L M x p) = 0 :=
  LinearMap.congr_fun (coefficientInsertion_comp_self R L M x) p

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
Put E=ExteriorAlgebra_R(L), P=E⊗_R M,
T_x=ad_x⊗id+id⊗[x,−], and c_x(a⊗m)=ι(x)a⊗m.
The diagonal action is a Lie representation:
T_{[x,y]}=T_xT_y−T_yT_x as R-linear operators on P. -/
theorem coefficientDiagonalAction_commutator (x y : L) :
    coefficientDiagonalAction R L M ⁅x, y⁆ =
      (coefficientDiagonalAction R L M x).comp (coefficientDiagonalAction R L M y) -
        (coefficientDiagonalAction R L M y).comp (coefficientDiagonalAction R L M x) :=
  LieHom.map_lie (coefficientDiagonalAction R L M) x y

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
Put E=ExteriorAlgebra_R(L), P=E⊗_R M,
T_x=ad_x⊗id+id⊗[x,−], and c_x(a⊗m)=ι(x)a⊗m.
For p∈P, T_{[x,y]}p=T_x(T_y p)−T_y(T_x p). -/
theorem coefficientDiagonalAction_commutator_apply (x y : L) (p : P) :
    coefficientDiagonalAction R L M ⁅x, y⁆ p =
      coefficientDiagonalAction R L M x (coefficientDiagonalAction R L M y p) -
        coefficientDiagonalAction R L M y (coefficientDiagonalAction R L M x p) :=
  LinearMap.congr_fun (coefficientDiagonalAction_commutator R L M x y) p

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
Put E=ExteriorAlgebra_R(L), P=E⊗_R M,
T_x=ad_x⊗id+id⊗[x,−], and c_x(a⊗m)=ι(x)a⊗m.
The diagonal action differentiates insertion:
T_x c_y=c_{[x,y]}+c_y T_x. -/
theorem coefficientDiagonalAction_comp_insertion (x y : L) :
    (coefficientDiagonalAction R L M x).comp (coefficientInsertion R L M y) =
      coefficientInsertion R L M ⁅x, y⁆ +
        (coefficientInsertion R L M y).comp (coefficientDiagonalAction R L M x) := by
  apply TensorProduct.ext'
  intro a m
  change coefficientDiagonalAction R L M x
      (coefficientInsertion R L M y (a ⊗ₜ[R] m)) =
    coefficientInsertion R L M ⁅x, y⁆ (a ⊗ₜ[R] m) +
      coefficientInsertion R L M y
        (coefficientDiagonalAction R L M x (a ⊗ₜ[R] m))
  simp only [coefficientInsertion_tmul, coefficientDiagonalAction_tmul,
    adjointAction_ι_mul, TensorProduct.add_tmul, map_add]
  abel

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
Put E=ExteriorAlgebra_R(L), P=E⊗_R M,
T_x=ad_x⊗id+id⊗[x,−], and c_x(a⊗m)=ι(x)a⊗m.
For p∈P, T_x(c_y p)=c_{[x,y]}p+c_y(T_x p). -/
theorem coefficientDiagonalAction_insertion (x y : L) (p : P) :
    coefficientDiagonalAction R L M x (coefficientInsertion R L M y p) =
      coefficientInsertion R L M ⁅x, y⁆ p +
        coefficientInsertion R L M y (coefficientDiagonalAction R L M x p) :=
  LinearMap.congr_fun (coefficientDiagonalAction_comp_insertion R L M x y) p

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
Put E=ExteriorAlgebra_R(L), P=E⊗_R M,
T_x=ad_x⊗id+id⊗[x,−], and c_x(a⊗m)=ι(x)a⊗m.
For the same generator x, T_x c_x=c_x T_x because [x,x]=0. -/
theorem coefficientDiagonalAction_comp_insertion_self (x : L) :
    (coefficientDiagonalAction R L M x).comp (coefficientInsertion R L M x) =
      (coefficientInsertion R L M x).comp (coefficientDiagonalAction R L M x) := by
  simpa only [lie_self, map_zero, zero_add] using
    coefficientDiagonalAction_comp_insertion R L M x x

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
Put E=ExteriorAlgebra_R(L), P=E⊗_R M,
T_x=ad_x⊗id+id⊗[x,−], and c_x(a⊗m)=ι(x)a⊗m.
For p∈P, T_x(c_x p)=c_x(T_x p). -/
theorem coefficientDiagonalAction_insertion_self (x : L) (p : P) :
    coefficientDiagonalAction R L M x (coefficientInsertion R L M x p) =
      coefficientInsertion R L M x (coefficientDiagonalAction R L M x p) :=
  LinearMap.congr_fun (coefficientDiagonalAction_comp_insertion_self R L M x) p

private def coefficientBoundaryStep : L →ₗ[R] (E × F) →ₗ[R] F :=
  (-1 : R) • ((((LinearMap.llcomp R M P P).comp
      (coefficientDiagonalAction R L M).toLinearMap).compl₂
    ((TensorProduct.mk R E M).comp (LinearMap.fst R E F))) +
    (((LinearMap.llcomp R M P P).comp (coefficientInsertion R L M)).compl₂
      (LinearMap.snd R E F)))

private theorem coefficientBoundaryStep_apply (x : L) (a : E) (g : F) (m : M) :
    coefficientBoundaryStep R L M x (a, g) m =
      -coefficientDiagonalAction R L M x (a ⊗ₜ[R] m) -
        coefficientInsertion R L M x (g m) := by
  change (-1 : R) • (coefficientDiagonalAction R L M x (a ⊗ₜ[R] m) +
    coefficientInsertion R L M x (g m)) = _
  simp only [neg_one_smul, neg_add, sub_eq_add_neg]

private theorem coefficientBoundaryStep_relation (x : L) (a : E) (g : F) :
    coefficientBoundaryStep R L M x
        (ExteriorAlgebra.ι R x * a, coefficientBoundaryStep R L M x (a, g)) =
      (0 : QuadraticForm R L) x • g := by
  have hz : (0 : QuadraticForm R L) x • g = (0 : F) := by simp
  rw [hz]
  apply LinearMap.ext
  intro m
  rw [coefficientBoundaryStep_apply, coefficientBoundaryStep_apply]
  change -coefficientDiagonalAction R L M x
      ((ExteriorAlgebra.ι R x * a) ⊗ₜ[R] m) -
    coefficientInsertion R L M x
      (-coefficientDiagonalAction R L M x (a ⊗ₜ[R] m) -
        coefficientInsertion R L M x (g m)) = 0
  rw [← coefficientInsertion_tmul]
  rw [coefficientDiagonalAction_insertion_self, map_sub, map_neg,
    coefficientInsertion_squared]
  abel

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
Put E=ExteriorAlgebra_R(L), P=E⊗_R M,
T_x=ad_x⊗id+id⊗[x,−], and c_x(a⊗m)=ι(x)a⊗m.
The R-linear coefficient boundary D:P→P vanishes on
exterior scalars and satisfies D c_x=−T_x−c_xD. -/
def coefficientBoundary : Module.End R P :=
  private_decl% (TensorProduct.lift
    (CliffordAlgebra.foldr' (0 : QuadraticForm R L)
      (coefficientBoundaryStep R L M) (coefficientBoundaryStep_relation R L M) (0 : F)))

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
Put E=ExteriorAlgebra_R(L), P=E⊗_R M,
T_x=ad_x⊗id+id⊗[x,−], and c_x(a⊗m)=ι(x)a⊗m.
The coefficient boundary vanishes on exterior scalar tensors:
D(r⊗m)=0 for r∈R and m∈M. -/
@[simp]
theorem coefficientBoundary_algebraMap_tmul (r : R) (m : M) :
    coefficientBoundary R L M ((algebraMap R E r) ⊗ₜ[R] m) = 0 := by
  change (CliffordAlgebra.foldr' (0 : QuadraticForm R L)
      (coefficientBoundaryStep R L M) (coefficientBoundaryStep_relation R L M)
      (0 : F) (algebraMap R E r)) m = 0
  rw [CliffordAlgebra.foldr'_algebraMap, smul_zero, LinearMap.zero_apply]

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
Put E=ExteriorAlgebra_R(L), P=E⊗_R M,
T_x=ad_x⊗id+id⊗[x,−], and c_x(a⊗m)=ι(x)a⊗m.
The empty exterior word has coefficient boundary D(1⊗m)=0. -/
@[simp]
theorem coefficientBoundary_one_tmul (m : M) :
    coefficientBoundary R L M ((1 : E) ⊗ₜ[R] m) = 0 := by
  simpa only [map_one] using coefficientBoundary_algebraMap_tmul R L M 1 m

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
Put E=ExteriorAlgebra_R(L), P=E⊗_R M,
T_x=ad_x⊗id+id⊗[x,−], and c_x(a⊗m)=ι(x)a⊗m.
The generator recursion is
D(ι(x)a⊗m)=−T_x(a⊗m)−c_x D(a⊗m). -/
@[simp]
theorem coefficientBoundary_ι_mul_tmul (x : L) (a : E) (m : M) :
    coefficientBoundary R L M ((ExteriorAlgebra.ι R x * a) ⊗ₜ[R] m) =
      -coefficientDiagonalAction R L M x (a ⊗ₜ[R] m) -
        coefficientInsertion R L M x (coefficientBoundary R L M (a ⊗ₜ[R] m)) := by
  change (CliffordAlgebra.foldr' (0 : QuadraticForm R L)
      (coefficientBoundaryStep R L M) (coefficientBoundaryStep_relation R L M)
      (0 : F) (ExteriorAlgebra.ι R x * a)) m = _
  rw [CliffordAlgebra.foldr'_ι_mul]
  rw [coefficientBoundaryStep_apply]
  rfl

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
Put E=ExteriorAlgebra_R(L), P=E⊗_R M,
T_x=ad_x⊗id+id⊗[x,−], and c_x(a⊗m)=ι(x)a⊗m.
As R-linear operators, D c_x=−T_x−c_xD for every x∈L. -/
theorem coefficientBoundary_comp_insertion (x : L) :
    (coefficientBoundary R L M).comp (coefficientInsertion R L M x) =
      -coefficientDiagonalAction R L M x -
        (coefficientInsertion R L M x).comp (coefficientBoundary R L M) := by
  apply TensorProduct.ext'
  intro a m
  change coefficientBoundary R L M (coefficientInsertion R L M x (a ⊗ₜ[R] m)) =
    -coefficientDiagonalAction R L M x (a ⊗ₜ[R] m) -
      coefficientInsertion R L M x (coefficientBoundary R L M (a ⊗ₜ[R] m))
  rw [coefficientInsertion_tmul]
  exact coefficientBoundary_ι_mul_tmul R L M x a m

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
Put E=ExteriorAlgebra_R(L), P=E⊗_R M,
T_x=ad_x⊗id+id⊗[x,−], and c_x(a⊗m)=ι(x)a⊗m.
For every p∈P, D(c_x p)=−T_x p−c_x(Dp). -/
theorem coefficientBoundary_insertion (x : L) (p : P) :
    coefficientBoundary R L M (coefficientInsertion R L M x p) =
      -coefficientDiagonalAction R L M x p -
        coefficientInsertion R L M x (coefficientBoundary R L M p) :=
  LinearMap.congr_fun (coefficientBoundary_comp_insertion R L M x) p

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
Put E=ExteriorAlgebra_R(L), P=E⊗_R M,
T_x=ad_x⊗id+id⊗[x,−], and c_x(a⊗m)=ι(x)a⊗m.
A single exterior generator has coefficient boundary
D(ι(x)⊗m)=−1⊗[x,m]. -/
@[simp]
theorem coefficientBoundary_ι_tmul (x : L) (m : M) :
    coefficientBoundary R L M ((ExteriorAlgebra.ι R x) ⊗ₜ[R] m) =
      -((1 : E) ⊗ₜ[R] ⁅x, m⁆) := by
  simpa only [mul_one, coefficientDiagonalAction_one_tmul, coefficientBoundary_one_tmul,
    map_zero, sub_zero] using coefficientBoundary_ι_mul_tmul R L M x 1 m

private theorem coefficientBoundary_diagonalAction_tmul (x : L) (a : E) :
    ∀ m : M,
      coefficientBoundary R L M (coefficientDiagonalAction R L M x (a ⊗ₜ[R] m)) =
        coefficientDiagonalAction R L M x (coefficientBoundary R L M (a ⊗ₜ[R] m)) := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
      intro m
      rw [coefficientDiagonalAction_algebraMap_tmul, coefficientBoundary_algebraMap_tmul,
        coefficientBoundary_algebraMap_tmul, map_zero]
  | add a b ha hb =>
      intro m
      simp only [TensorProduct.add_tmul, map_add, ha, hb]
  | ι_mul a y ha =>
      intro m
      let p : P := a ⊗ₜ[R] m
      have hax : coefficientBoundary R L M (coefficientDiagonalAction R L M x p) =
          coefficientDiagonalAction R L M x (coefficientBoundary R L M p) := ha m
      change coefficientBoundary R L M
          (coefficientDiagonalAction R L M x (coefficientInsertion R L M y p)) =
        coefficientDiagonalAction R L M x
          (coefficientBoundary R L M (coefficientInsertion R L M y p))
      rw [coefficientDiagonalAction_insertion, map_add, coefficientBoundary_insertion,
        coefficientBoundary_insertion, coefficientBoundary_insertion, hax,
        map_sub, map_neg, coefficientDiagonalAction_insertion,
        coefficientDiagonalAction_commutator_apply]
      abel

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
Put E=ExteriorAlgebra_R(L), P=E⊗_R M,
T_x=ad_x⊗id+id⊗[x,−], and c_x(a⊗m)=ι(x)a⊗m.
The coefficient boundary is equivariant for the diagonal action:
DT_x=T_xD on P. -/
theorem coefficientBoundary_comp_diagonalAction (x : L) :
    (coefficientBoundary R L M).comp (coefficientDiagonalAction R L M x) =
      (coefficientDiagonalAction R L M x).comp (coefficientBoundary R L M) := by
  apply TensorProduct.ext'
  intro a m
  exact coefficientBoundary_diagonalAction_tmul R L M x a m

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
Put E=ExteriorAlgebra_R(L), P=E⊗_R M,
T_x=ad_x⊗id+id⊗[x,−], and c_x(a⊗m)=ι(x)a⊗m.
For p∈P, D(T_x p)=T_x(Dp). -/
theorem coefficientBoundary_diagonalAction (x : L) (p : P) :
    coefficientBoundary R L M (coefficientDiagonalAction R L M x p) =
      coefficientDiagonalAction R L M x (coefficientBoundary R L M p) :=
  LinearMap.congr_fun (coefficientBoundary_comp_diagonalAction R L M x) p

private theorem coefficientBoundary_squared_tmul (a : E) :
    ∀ m : M,
      coefficientBoundary R L M (coefficientBoundary R L M (a ⊗ₜ[R] m)) = 0 := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
      intro m
      rw [coefficientBoundary_algebraMap_tmul, map_zero]
  | add a b ha hb =>
      intro m
      simp only [TensorProduct.add_tmul, map_add, ha, hb, add_zero]
  | ι_mul a x ha =>
      intro m
      let p : P := a ⊗ₜ[R] m
      have hp : coefficientBoundary R L M (coefficientBoundary R L M p) = 0 := ha m
      change coefficientBoundary R L M
        (coefficientBoundary R L M (coefficientInsertion R L M x p)) = 0
      rw [coefficientBoundary_insertion, map_sub, map_neg, coefficientBoundary_diagonalAction,
        coefficientBoundary_insertion, hp, map_zero]
      abel

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
Put E=ExteriorAlgebra_R(L), P=E⊗_R M,
T_x=ad_x⊗id+id⊗[x,−], and c_x(a⊗m)=ι(x)a⊗m.
The canonical coefficient boundary satisfies D²=0 as an
R-linear endomorphism of P. -/
theorem coefficientBoundary_comp_self :
    (coefficientBoundary R L M).comp (coefficientBoundary R L M) = 0 := by
  apply TensorProduct.ext'
  intro a m
  exact coefficientBoundary_squared_tmul R L M a m

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
Put E=ExteriorAlgebra_R(L), P=E⊗_R M,
T_x=ad_x⊗id+id⊗[x,−], and c_x(a⊗m)=ι(x)a⊗m.
For every p∈P, D(Dp)=0. -/
theorem coefficientBoundary_squared (p : P) :
    coefficientBoundary R L M (coefficientBoundary R L M p) = 0 :=
  LinearMap.congr_fun (coefficientBoundary_comp_self R L M) p

end ChevalleyEilenberg
