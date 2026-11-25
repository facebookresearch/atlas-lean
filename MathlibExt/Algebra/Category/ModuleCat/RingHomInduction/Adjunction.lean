/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import MathlibExt.Algebra.Category.ModuleCat.RingHomInduction.Basic

/-!
# Induction and restriction of scalars

The semilinear map extension `r ⊗ m ↦ r • f m` is inverse to evaluation on `1 ⊗ m`. Naturality
gives the induction–restriction adjunction in a module universe containing both scalar rings.
-/

@[expose] public section

open CategoryTheory MulOpposite

universe u v w z t

namespace ModuleCat.RingHomInduction

variable {k : Type u} {R : Type v} [Ring k] [Ring R] (φ : k →+* R)
variable {M : Type w} {N : Type z}
  [AddCommGroup M] [AddCommGroup N] [Module k M] [Module R N]

/-- The scalar evaluation as an integer-bilinear map. -/
def evaluationBilinear (f : M →ₛₗ[φ] N) : R →ₗ[ℤ] M →ₗ[ℤ] N :=
  ({ toFun := fun r =>
      ({ toFun := fun m => r • f m
         map_zero' := by rw [map_zero, smul_zero]
         map_add' := by intro m n; rw [f.map_add, smul_add] } : M →+ N).toIntLinearMap
     map_zero' := by
       apply LinearMap.ext
       intro m
       exact zero_smul R (f m)
     map_add' := by
       intro r s
       apply LinearMap.ext
       intro m
       exact add_smul r s (f m) } : R →+ (M →ₗ[ℤ] N)).toIntLinearMap

/-- The public bilinear evaluation has the scalar value on every pair. -/
theorem evaluationBilinear_apply (f : M →ₛₗ[φ] N) (r : R) (m : M) :
    evaluationBilinear φ f r m = r • f m := rfl

/-- The semilinear evaluation respects the balancing action. -/
theorem evaluation_balanced (f : M →ₛₗ[φ] N) :
    letI := rightModule φ
    ∀ (a : k) (r : R) (m : M),
      evaluationBilinear φ f (op a • r) m = evaluationBilinear φ f r (a • m) := by
  let := rightModule φ
  intro a r m
  change (r * φ a) • f m = r • f (a • m)
  rw [f.map_smulₛₗ, mul_smul]

/-- Integer-linear evaluation on the induced module, constructed through its balancing quotient. -/
def descent (f : M →ₛₗ[φ] N) : Carrier φ M →ₗ[ℤ] N := by
  letI := rightModule φ
  exact TensorProduct.Balanced.lift (evaluationBilinear φ f) (evaluation_balanced φ f)

/-- The descended integer-linear evaluation retains the pure tensor value. -/
theorem descent_tensor (f : M →ₛₗ[φ] N) (r : R) (m : M) :
    descent φ f (tensor φ M r m) = r • f m := rfl

/-- The quotient evaluation intertwines the outer R-action. -/
theorem descent_smul (f : M →ₛₗ[φ] N) (s : R) (x : Carrier φ M) :
    descent φ f (s • x) = s • descent φ f x := by
  let := rightModule φ
  let l := descent φ f
  let a : Carrier φ M →+ N :=
    { toFun := fun y => l (s • y)
      map_zero' := by rw [smul_zero, map_zero]
      map_add' := by intro y z; rw [smul_add, l.map_add] }
  let b : Carrier φ M →+ N :=
    { toFun := fun y => s • l y
      map_zero' := by rw [map_zero, smul_zero]
      map_add' := by intro y z; rw [l.map_add, smul_add] }
  have h : a = b := TensorProduct.Balanced.addHom_ext ℤ k R M (by
    intro r m
    change descent φ f (s • tensor φ M r m) =
      s • descent φ f (tensor φ M r m)
    rw [smul_tensor, descent_tensor, descent_tensor, mul_smul])
  exact congrArg (fun q : Carrier φ M →+ N => q x) h

/-- Extend an semilinear map to the induced `R`-module. -/
def extendHom (f : M →ₛₗ[φ] N) : Carrier φ M →ₗ[R] N where
  toFun := descent φ f
  map_add' := (descent φ f).map_add
  map_smul' := descent_smul φ f

theorem extendHom_tensor (f : M →ₛₗ[φ] N) (r : R) (m : M) :
    extendHom φ f (tensor φ M r m) = r • f m := rfl

/-- Restriction of the induced-module map is evaluation on the unit tensor. -/
def restrictHom (g : Carrier φ M →ₗ[R] N) : M →ₛₗ[φ] N where
  toFun m := g (tensor φ M 1 m)
  map_add' m n := by rw [tensor_add_right, g.map_add]
  map_smul' a m := by rw [tensor_one_smul, g.map_smul]

theorem restrictHom_apply (g : Carrier φ M →ₗ[R] N) (m : M) :
    restrictHom φ g m = g (tensor φ M 1 m) := rfl

theorem restrict_extend (f : M →ₛₗ[φ] N) : restrictHom φ (extendHom φ f) = f := by
  apply LinearMap.ext
  intro m
  change extendHom φ f (tensor φ M 1 m) = f m
  rw [extendHom_tensor, one_smul]

theorem extend_restrict (g : Carrier φ M →ₗ[R] N) : extendHom φ (restrictHom φ g) = g := by
  apply hom_ext φ M
  intro r m
  rw [extendHom_tensor, restrictHom_apply]
  calc
    r • g (tensor φ M 1 m) = g (r • tensor φ M 1 m) := (g.map_smul r _).symm
    _ = g (tensor φ M r m) := congrArg g (by rw [smul_tensor, mul_one])

/-- The additive Hom equivalence for independent coefficient universes. -/
def homAddEquiv (M : Type w) (N : Type z)
    [AddCommGroup M] [AddCommGroup N] [Module k M] [Module R N] :
    (Carrier φ M →ₗ[R] N) ≃+ (M →ₛₗ[φ] N) where
  toFun := restrictHom φ
  invFun := extendHom φ
  left_inv := extend_restrict φ
  right_inv := restrict_extend φ
  map_add' f g := by
    apply LinearMap.ext
    intro m
    rfl

/-- The ring homomorphism itself is the semilinear regular-module map. -/
def ringHomSemilinear : k →ₛₗ[φ] R where
  toFun := φ
  map_add' := φ.map_add
  map_smul' := φ.map_mul

/-- Evaluate the induction of the regular `k`-module. -/
def regularEval : Carrier φ k →ₗ[R] R := extendHom φ (ringHomSemilinear φ)

theorem regularEval_tensor (r : R) (a : k) :
    regularEval φ (tensor φ k r a) = r * φ a := rfl

/-- Insert the unit to recover a regular `R`-element. -/
def regularInsert : R →ₗ[R] Carrier φ k where
  toFun r := tensor φ k r 1
  map_add' r s := tensor_add_left φ k r s 1
  map_smul' r s := (smul_tensor φ k r s 1).symm

theorem regularEval_insert : (regularEval φ).comp (regularInsert φ) = LinearMap.id := by
  apply LinearMap.ext
  intro r
  change regularEval φ (tensor φ k r 1) = r
  rw [regularEval_tensor, φ.map_one, mul_one]

theorem regularInsert_eval : (regularInsert φ).comp (regularEval φ) = LinearMap.id := by
  apply hom_ext φ k
  intro r a
  change tensor φ k (regularEval φ (tensor φ k r a)) 1 = tensor φ k r a
  rw [regularEval_tensor, tensor_balance]
  change tensor φ k r (a * 1) = tensor φ k r a
  rw [mul_one]

/-- Induction of the regular scalar module is isomorphic to the target ring. -/
def regularEquiv : Carrier φ k ≃ₗ[R] R :=
  LinearEquiv.ofLinearMap (regularEval φ) (regularInsert φ)
    (regularEval_insert φ) (regularInsert_eval φ)

theorem regularEquiv_tensor (r : R) (a : k) :
    regularEquiv φ (tensor φ k r a) = r * φ a := rfl

theorem regularEquiv_symm (r : R) :
    (regularEquiv φ).symm r = tensor φ k r 1 := rfl

end ModuleCat.RingHomInduction

namespace ModuleCat

variable {k : Type u} {R : Type v} [Ring k] [Ring R] (φ : k →+* R)

/-- Induction on the joint maximum universe containing both scalar rings and the coefficient universe. -/
def induceScalars : ModuleCat.{max u v w} k ⥤ ModuleCat.{max u v w} R where
  obj M := ModuleCat.of R (RingHomInduction.Carrier φ M)
  map f := ModuleCat.ofHom (RingHomInduction.map φ f.hom)
  map_id M := by
    apply ModuleCat.hom_ext
    exact RingHomInduction.map_id φ (M := M)
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact RingHomInduction.map_comp φ f.hom g.hom

theorem induceScalars_map_tensor {M N : ModuleCat.{max u v w} k}
    (f : M ⟶ N) (r : R) (m : M) :
    (induceScalars.{u, v, w} φ).map f (RingHomInduction.tensor φ M r m) =
      RingHomInduction.tensor φ N r (f m) :=
  RingHomInduction.map_tensor φ f.hom r m

instance induceScalars_additive : (induceScalars.{u, v, w} φ).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    exact RingHomInduction.map_add φ f.hom g.hom

namespace RingHomInduction

/-- The Hom equivalence between induction and restriction of scalars. -/
noncomputable def homEquiv (M : ModuleCat.{max u v w} k) (N : ModuleCat.{max u v w} R) :
    ((induceScalars.{u, v, w} φ).obj M ⟶ N) ≃
      (M ⟶ (restrictScalars.{max u v w} φ).obj N) :=
  (ModuleCat.homEquiv :
      ((induceScalars.{u, v, w} φ).obj M ⟶ N) ≃ (Carrier φ M →ₗ[R] N)).trans
    ((homAddEquiv φ M N).toEquiv.trans (ModuleCat.semilinearMapAddEquiv φ M N).toEquiv)

theorem homEquiv_apply (M : ModuleCat.{max u v w} k) (N : ModuleCat.{max u v w} R)
    (f : (induceScalars.{u, v, w} φ).obj M ⟶ N) (m : M) :
    homEquiv φ M N f m = f (tensor φ M 1 m) := rfl

theorem homEquiv_symm_tensor (M : ModuleCat.{max u v w} k) (N : ModuleCat.{max u v w} R)
    (g : M ⟶ (restrictScalars.{max u v w} φ).obj N) (r : R) (m : M) :
    (homEquiv φ M N).symm g (tensor φ M r m) = r • (show N from g m) := by
  change extendHom φ ((ModuleCat.semilinearMapAddEquiv φ M N).symm g)
    (tensor φ M r m) = _
  exact extendHom_tensor φ _ r m

/-- The Hom equivalence is natural in both module variables. -/
noncomputable def homCore : Adjunction.CoreHomEquiv (induceScalars.{u, v, w} φ)
    (restrictScalars.{max u v w} φ) where
  homEquiv := homEquiv φ
  homEquiv_naturality_left_symm := by
    intro M' M N f g
    apply ModuleCat.hom_ext
    apply RingHomInduction.hom_ext φ M'
    intro r m
    change (homEquiv φ M' N).symm (f ≫ g) (tensor φ M' r m) =
      (homEquiv φ M N).symm g
        ((induceScalars.{u, v, w} φ).map f (tensor φ M' r m))
    rw [homEquiv_symm_tensor, induceScalars_map_tensor, homEquiv_symm_tensor]
    rfl
  homEquiv_naturality_right := by
    intro M N N' f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change g (f (tensor φ M 1 m)) = g (f (tensor φ M 1 m))
    rfl

end RingHomInduction

/-- The adjunction is constructed from the natural tensor/restriction equivalence. -/
noncomputable def induceRestrictScalarsAdj :
    induceScalars.{u, v, w} φ ⊣ restrictScalars.{max u v w} φ :=
  Adjunction.mkOfHomEquiv (RingHomInduction.homCore φ)

theorem induceRestrictScalarsAdj_unit (M : ModuleCat.{max u v w} k) (m : M) :
    (induceRestrictScalarsAdj.{u, v, w} φ).unit.app M m =
      RingHomInduction.tensor φ M 1 m := rfl

theorem induceRestrictScalarsAdj_counit (N : ModuleCat.{max u v w} R) (r : R) (n : N) :
    (induceRestrictScalarsAdj.{u, v, w} φ).counit.app N
        (RingHomInduction.tensor φ ((restrictScalars.{max u v w} φ).obj N) r n) = r • n := by
  let M : ModuleCat.{max u v w} k := (restrictScalars.{max u v w} φ).obj N
  let m : M := n
  exact RingHomInduction.homEquiv_symm_tensor φ M N (𝟙 M) r m

end ModuleCat
