/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorLeft
public import MathlibExt.Algebra.Category.ModuleCat.ProjectiveFlatTargetTensor
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-!
# Right exactness of commutative balanced tensor functors

For a commutative acting ring, compatible left and right coefficient actions
identify the balanced tensor with the ordinary acting-ring tensor. The
comparison is natural on balanced representatives. Tensor right exactness
and exact restriction of scalars give finite-colimit preservation for the
ground-valued balanced functor.

The coefficient module need not be flat, projective or small. Its two actions
are retained, with their displayed compatibility.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits MulOpposite
open scoped TensorProduct

universe u v w z

namespace ModuleCat.BalancedTensor

variable (k : Type u) (R : Type v) [CommRing k] [CommRing R] [Algebra k R]
  (M : Type w) [AddCommGroup M] [Module k M] [Module R M] [Module Rᵐᵒᵖ M]
  [SMulCommClass k R M] [IsScalarTower k R M]
  (hOp : ∀ (r : R) (m : M), op r • m = r • m)

local instance actingGroundComm : SMulCommClass R k M := SMulCommClass.symm k R M
/-- Original compatible left and right actions commute over the commutative acting ring. -/
theorem actingOppositeComm {R : Type v} [CommRing R]
    {M : Type w} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    (hOp : ∀ (r : R) (m : M), op r • m = r • m) : SMulCommClass R Rᵐᵒᵖ M where
  smul_comm r s m := by
    rw [← op_unop s, hOp, hOp]
    exact smul_comm r s.unop m

/-- The ordinary acting-ring tensor is the actual balanced quotient with its native outer action. -/
def commutativeCoefficientTensorEquiv (N : ModuleCat.{max u v z} R) :
    letI := actingOppositeComm (R := R) (M := M) hOp
    Left.obj k R R M N ≃ₗ[R] M ⊗[R] N := by
  let := actingOppositeComm (R := R) (M := M) hOp
  letI : Module k N := Module.compHom N (algebraMap k R)
  letI : IsScalarTower k R N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let B := TensorProduct.Balanced k R M N
  let P := M ⊗[R] N
  letI : Module R B := TensorProduct.Balanced.leftModule k R R M N
  letI : Module k P :=
    TensorProduct.leftModule (R := R) (R'' := k) (M := M) (N := N)
  letI : IsScalarTower k R P := IsScalarTower.of_algebraMap_smul (fun a x => by
    induction x using TensorProduct.inductionOn with
    | tmul m n =>
        change ((algebraMap k R a) • m) ⊗ₜ[R] n = (a • m) ⊗ₜ[R] n
        rw [IsScalarTower.algebraMap_smul R a m]
    | add x y hx hy => simp only [smul_add, hx, hy])
  let p : M →ₗ[k] N →ₗ[k] P :=
    (LinearMap.restrictScalarsₗ (S := R) (M := N) (N := P) (R := k) (R₁ := k)).comp
      ((TensorProduct.mk R M N).restrictScalars k)
  have hp : ∀ (r : R) (m : M) (n : N), p (op r • m) n = p m (r • n) := by
    intro r m n
    change (op r • m) ⊗ₜ[R] n = m ⊗ₜ[R] (r • n)
    rw [hOp, TensorProduct.smul_tmul]
  let f : B →ₗ[k] P := TensorProduct.Balanced.lift p hp
  have hf (m : M) (n : N) : f (TensorProduct.Balanced.mk k R M N m n) = m ⊗ₜ[R] n :=
    TensorProduct.Balanced.lift_mk p hp m n
  let fR : B →ₗ[R] P :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro r x
        have he : f.comp (TensorProduct.Balanced.leftAction k R R M N r) =
            (Algebra.lsmul k k P r).comp f := by
          apply TensorProduct.Balanced.hom_ext
          intro m n
          rw [LinearMap.comp_apply, TensorProduct.Balanced.leftAction_mk, hf,
            LinearMap.comp_apply, hf]
          change (r • m) ⊗ₜ[R] n = r • (m ⊗ₜ[R] n)
          exact (TensorProduct.smul_tmul' r m n).symm
        exact LinearMap.congr_fun he x }
  let q : M →ₗ[R] N →ₗ[R] B := LinearMap.mk₂ R
    (fun m n => TensorProduct.Balanced.mk k R M N m n)
    (by intro m m' n; exact LinearMap.congr_fun ((TensorProduct.Balanced.mk k R M N).map_add m m') n)
    (by intro r m n; exact (TensorProduct.Balanced.leftModule_smul_mk k R R M N r m n).symm)
    (by intro m n n'; exact (TensorProduct.Balanced.mk k R M N m).map_add n n')
    (by
      intro r m n
      rw [← TensorProduct.Balanced.balance k R M N r m n, hOp]
      exact (TensorProduct.Balanced.leftModule_smul_mk k R R M N r m n).symm)
  let g : P →ₗ[R] B := TensorProduct.lift q
  refine LinearEquiv.ofLinearMap fR g ?_ ?_
  · apply TensorProduct.ext
    apply LinearMap.ext
    intro m
    apply LinearMap.ext
    intro n
    change f (g (m ⊗ₜ[R] n)) = m ⊗ₜ[R] n
    rw [TensorProduct.lift.tmul]
    exact hf m n
  · apply LinearMap.toAddMonoidHom_injective
    apply TensorProduct.Balanced.addHom_ext k R M N
    intro m n
    change g (f (TensorProduct.Balanced.mk k R M N m n)) =
      TensorProduct.Balanced.mk k R M N m n
    rw [hf, TensorProduct.lift.tmul]
    rfl

/-- Every actual balanced representative retains its original two factors. -/
theorem commutativeCoefficientTensorEquiv_mk (N : ModuleCat.{max u v z} R) (m : M) (n : N) :
    letI := actingOppositeComm (R := R) (M := M) hOp
    letI : Module k N := Module.compHom N (algebraMap k R)
    commutativeCoefficientTensorEquiv k R M hOp N
      (TensorProduct.Balanced.mk k R M N m n) = m ⊗ₜ[R] n := by
  let := actingOppositeComm (R := R) (M := M) hOp
  let : Module k N := Module.compHom N (algebraMap k R)
  exact TensorProduct.Balanced.lift_mk _ (by
    intro r m n
    change (op r • m) ⊗ₜ[R] n = m ⊗ₜ[R] (r • n)
    rw [hOp, TensorProduct.smul_tmul]) m n

/-- The comparison is an actual natural isomorphism of the original coefficient functors. -/
def commutativeCoefficientTensorNatIso :
    letI := actingOppositeComm (R := R) (M := M) hOp
    Left.functor k R R M ≅
      (ModuleCat.tensorBifunctorAt.{v, w, max u v z} R).obj (ModuleCat.of R M) := by
  let := actingOppositeComm (R := R) (M := M) hOp
  exact NatIso.ofComponents (fun N => by
    let A : ModuleCat.{max u v w z} R := (Left.functor k R R M).obj N
    let B : ModuleCat.{max u v w z} R :=
      ((ModuleCat.tensorBifunctorAt.{v, w, max u v z} R).obj (ModuleCat.of R M)).obj N
    let e : A ≃ₗ[R] B := commutativeCoefficientTensorEquiv k R M hOp N
    exact (show A ≅ B from e.toModuleIso
      (g₁ := A.isAddCommGroup) (g₂ := B.isAddCommGroup)
      (m₁ := A.isModule) (m₂ := B.isModule))) (by
    intro N N' f
    let : Module k N := Module.compHom N (algebraMap k R)
    let : Module k N' := Module.compHom N' (algebraMap k R)
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply TensorProduct.Balanced.addHom_ext k R M N
    intro m n
    change commutativeCoefficientTensorEquiv k R M hOp N'
        ((Left.map k R R M f).hom (TensorProduct.Balanced.mk k R M N m n)) =
      TensorProduct.map LinearMap.id f.hom
        (commutativeCoefficientTensorEquiv k R M hOp N
          (TensorProduct.Balanced.mk k R M N m n))
    rw [Left.map_mk, commutativeCoefficientTensorEquiv_mk,
      commutativeCoefficientTensorEquiv_mk, TensorProduct.map_tmul, LinearMap.id_apply])

include hOp in
/-- Finite-colimit preservation is earned from the ordinary tensor and actual scalar-restriction comparison. -/
theorem functor_preservesFiniteColimits_of_commutative :
    PreservesFiniteColimits
      (functor k R M : ModuleCat.{max u v z} R ⥤ ModuleCat.{max u v w z} k) := by
  let := actingOppositeComm (R := R) (M := M) hOp
  let T := (ModuleCat.tensorBifunctorAt.{v, w, max u v z} R).obj (ModuleCat.of R M)
  let F : ModuleCat.{max u v z} R ⥤ ModuleCat.{max u v w z} R := Left.functor k R R M
  let U : ModuleCat.{max u v w z} R ⥤ ModuleCat.{max u v w z} k :=
    ModuleCat.restrictScalars (algebraMap k R)
  let : PreservesFiniteColimits T :=
    ModuleCat.projectiveCoefficientTensor_preservesFiniteColimits.{v, w, max u z} R (ModuleCat.of R M)
  let : PreservesFiniteColimits F :=
    preservesFiniteColimits_of_natIso (commutativeCoefficientTensorNatIso k R M hOp).symm
  let : PreservesFiniteColimits U := inferInstance
  let : PreservesFiniteColimits (F ⋙ U) := inferInstance
  exact preservesFiniteColimits_of_natIso (Left.groundIso k R R M)

end ModuleCat.BalancedTensor
