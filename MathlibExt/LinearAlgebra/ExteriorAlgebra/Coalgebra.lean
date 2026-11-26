/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Fold
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.Coalgebra.Primitive
import Mathlib.Tactic.Abel

/-!
# The exterior coproduct and its counit

For a commutative ring `R` and an `R`-module `M`, the exterior coproduct is the linear map `Δ
: E → E ⊗[R] E`, `E=ExteriorAlgebra R M`, with `Δ(1)=1⊗1` and `Δ(ι(x))=1⊗ι(x)+ι(x)⊗1`.

Its recursion uses `D_x(a⊗b)=ι(x)a⊗b+γ(a)⊗ι(x)b`, where `γ` is the grade involution. These
insertion operators square to zero. The augmentation `ε : E → R` kills generators and supplies
the counit. Coassociativity uses the tensor associator, and the counit identities identify the
outputs with `1⊗a` and `a⊗1`.

These maps define an ordinary coalgebra. The coproduct commutes with the grade involution and
with exterior maps induced by linear maps.

References: Bourbaki, *Algebra*, Chapter III; Sweedler, *Hopf Algebras*, Chapter 1.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w

namespace ExteriorAlgebra

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

local notation "E" => ExteriorAlgebra R M
local notation "γ" => (CliffordAlgebra.involute : E →ₐ[R] E)

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. For `x : M`, `signedInsertion R M x` is the endomorphism `a⊗b ↦ ι(x)*a ⊗ b
+ γ(a) ⊗ ι(x)*b`. The assignment `x ↦ signedInsertion x` is `R`-linear. -/
def signedInsertion : M →ₗ[R] Module.End R (E ⊗[R] E) where
  toFun x := ((Algebra.lmul R E) (ι R x)).rTensor E +
    TensorProduct.map (CliffordAlgebra.involute : E →ₐ[R] E).toLinearMap ((Algebra.lmul R E) (ι R x))
  map_add' x y := by
    apply TensorProduct.ext'
    intro a b
    change (ι R (x + y) * a) ⊗ₜ[R] b + γ a ⊗ₜ[R] (ι R (x + y) * b) =
      ((ι R x * a) ⊗ₜ[R] b + γ a ⊗ₜ[R] (ι R x * b)) +
        ((ι R y * a) ⊗ₜ[R] b + γ a ⊗ₜ[R] (ι R y * b))
    simp only [map_add, add_mul, TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  map_smul' r x := by
    apply TensorProduct.ext'
    intro a b
    change (ι R (r • x) * a) ⊗ₜ[R] b + γ a ⊗ₜ[R] (ι R (r • x) * b) =
      r • ((ι R x * a) ⊗ₜ[R] b + γ a ⊗ₜ[R] (ι R x * b))
    simp only [map_smul, smul_mul_assoc, TensorProduct.smul_tmul',
      TensorProduct.tmul_smul, smul_add]

@[simp]
theorem signedInsertion_tmul (x : M) (a b : E) :
    signedInsertion R M x (a ⊗ₜ[R] b) =
      (ι R x * a) ⊗ₜ[R] b + γ a ⊗ₜ[R] (ι R x * b) := by
  simp only [signedInsertion, LinearMap.add_apply, LinearMap.rTensor_tmul,
    TensorProduct.map_tmul, AlgHom.toLinearMap_apply]
  rfl

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. For every `x : M`, `D_x ∘ D_x=0` on `E ⊗[R] E`, where
`D_x(a⊗b)=ι(x)a⊗b+γ(a)⊗ι(x)b`. -/
theorem signedInsertion_comp_self (x : M) :
    (signedInsertion R M x).comp (signedInsertion R M x) = 0 := by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.comp_apply, signedInsertion_tmul, map_add,
    map_mul, CliffordAlgebra.involute_ι, CliffordAlgebra.involute_involute,
    neg_mul, ← mul_assoc, ι_sq_zero, zero_mul, TensorProduct.zero_tmul,
    TensorProduct.tmul_zero, TensorProduct.neg_tmul, LinearMap.zero_apply]
  abel

theorem signedInsertion_squared (x : M) (p : E ⊗[R] E) :
    signedInsertion R M x (signedInsertion R M x p) = 0 :=
  LinearMap.congr_fun (signedInsertion_comp_self R M x) p

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. The coproduct is determined by `Δ(1)=1⊗1` and `Δ(ι(x)*a)=D_x(Δ a)`, where
`D_x(a⊗b)=ι(x)a⊗b+γ(a)⊗ι(x)b`. In particular its generators have coproduct `1⊗ι(x)+ι(x)⊗1`. -/
def coproduct : E →ₗ[R] E ⊗[R] E :=
  CliffordAlgebra.foldr (0 : QuadraticForm R M) (signedInsertion R M)
    (fun x p => by simpa using signedInsertion_squared R M x p)
    ((1 : E) ⊗ₜ[R] (1 : E))

@[simp]
theorem coproduct_one : coproduct R M (1 : E) = (1 : E) ⊗ₜ[R] (1 : E) := by
  apply CliffordAlgebra.foldr_one

@[simp]
theorem coproduct_algebraMap (r : R) :
    coproduct R M (algebraMap R E r) = r • ((1 : E) ⊗ₜ[R] (1 : E)) := by
  apply CliffordAlgebra.foldr_algebraMap

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. For `x : M` and `a : E`, `Δ(ι(x)*a)=signedInsertion R M x (Δ a)`. -/
@[simp]
theorem coproduct_ι_mul (x : M) (a : E) :
    coproduct R M (ι R x * a) = signedInsertion R M x (coproduct R M a) := by
  unfold coproduct
  rw [CliffordAlgebra.foldr_mul, CliffordAlgebra.foldr_ι]

@[simp]
theorem coproduct_ι (x : M) :
    coproduct R M (ι R x) = (1 : E) ⊗ₜ[R] ι R x + ι R x ⊗ₜ[R] (1 : E) := by
  simpa only [mul_one, coproduct_one, signedInsertion_tmul, map_one, add_comm] using
    coproduct_ι_mul R M x (1 : E)

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. `augmentation R M : E →ₐ[R] R` fixes coefficient scalars and sends every
generator `ι(x)` to zero. Its underlying linear map is the counit. -/
def augmentation : E →ₐ[R] R :=
  lift R ⟨(0 : M →ₗ[R] R), fun x => by simp only [LinearMap.zero_apply, zero_mul]⟩

@[simp]
theorem augmentation_ι (x : M) : augmentation R M (ι R x) = 0 := by
  simp only [augmentation, lift_ι_apply, LinearMap.zero_apply]

@[simp]
theorem augmentation_involute (a : E) : augmentation R M (γ a) = augmentation R M a := by
  have h : (augmentation R M).comp γ = augmentation R M := by
    apply ExteriorAlgebra.hom_ext
    apply LinearMap.ext
    intro x
    change augmentation R M (γ (ι R x)) = augmentation R M (ι R x)
    rw [CliffordAlgebra.involute_ι, map_neg, augmentation_ι, neg_zero]
  exact AlgHom.congr_fun h a

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. `tensorParity R M` is the endomorphism `γ ⊗ γ` of `E ⊗[R] E`, sending
`a⊗b` to `γ(a)⊗γ(b)`. -/
def tensorParity : Module.End R (E ⊗[R] E) := TensorProduct.map (CliffordAlgebra.involute : E →ₐ[R] E).toLinearMap
  (CliffordAlgebra.involute : E →ₐ[R] E).toLinearMap

@[simp]
theorem tensorParity_tmul (a b : E) : tensorParity R M (a ⊗ₜ[R] b) = γ a ⊗ₜ[R] γ b := by
  simp only [tensorParity, TensorProduct.map_tmul, AlgHom.toLinearMap_apply]

theorem tensorParity_signedInsertion (x : M) (p : E ⊗[R] E) :
    tensorParity R M (signedInsertion R M x p) =
      -signedInsertion R M x (tensorParity R M p) := by
  have h : (tensorParity R M).comp (signedInsertion R M x) =
      -(signedInsertion R M x).comp (tensorParity R M) := by
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, signedInsertion_tmul, tensorParity_tmul, map_add,
      map_mul, CliffordAlgebra.involute_ι, CliffordAlgebra.involute_involute,
      neg_mul, TensorProduct.neg_tmul, TensorProduct.tmul_neg,
      LinearMap.neg_apply, neg_add]
  exact LinearMap.congr_fun h p

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. For every `a : E`, `Δ(γ a)=(γ ⊗ γ)(Δ a)`. -/
theorem coproduct_involute (a : E) :
    coproduct R M (γ a) = tensorParity R M (coproduct R M a) := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp only [AlgHom.commutes, coproduct_algebraMap, map_smul, tensorParity_tmul, map_one]
  | add a b ha hb => simp only [map_add, ha, hb]
  | ι_mul a x ha =>
      simp only [map_mul, CliffordAlgebra.involute_ι, neg_mul, map_neg,
        coproduct_ι_mul, ha]
      exact (tensorParity_signedInsertion R M x (coproduct R M a)).symm

private def tripleInsertion (x : M) : Module.End R (E ⊗[R] (E ⊗[R] E)) :=
  ((Algebra.lmul R E) (ι R x)).rTensor (E ⊗[R] E) +
    TensorProduct.map (CliffordAlgebra.involute : E →ₐ[R] E).toLinearMap (signedInsertion R M x)

private theorem tripleInsertion_tmul (x : M) (a : E) (p : E ⊗[R] E) :
    tripleInsertion R M x (a ⊗ₜ[R] p) =
      (ι R x * a) ⊗ₜ[R] p + γ a ⊗ₜ[R] signedInsertion R M x p := by
  simp only [tripleInsertion, LinearMap.add_apply, LinearMap.rTensor_tmul,
    TensorProduct.map_tmul, AlgHom.toLinearMap_apply]
  rfl

private theorem assoc_signedInsertion (x : M) (p : E ⊗[R] E) (c : E) :
    TensorProduct.assoc R E E E
        (signedInsertion R M x p ⊗ₜ[R] c + tensorParity R M p ⊗ₜ[R] (ι R x * c)) =
      tripleInsertion R M x (TensorProduct.assoc R E E E (p ⊗ₜ[R] c)) := by
  induction p using TensorProduct.inductionOn with
  | tmul a b =>
      simp only [signedInsertion_tmul, tensorParity_tmul, TensorProduct.add_tmul, map_add,
        TensorProduct.assoc_tmul, tripleInsertion_tmul, TensorProduct.tmul_add, add_assoc]
  | add p q hp hq =>
      simp only [map_add, TensorProduct.add_tmul]
      rw [← hp, ← hq]
      simp only [map_add]
      abel

private theorem iteratedLeft_insertion (x : M) (p : E ⊗[R] E) :
    TensorProduct.assoc R E E E
        ((coproduct R M).rTensor E (signedInsertion R M x p)) =
      tripleInsertion R M x
        (TensorProduct.assoc R E E E ((coproduct R M).rTensor E p)) := by
  induction p using TensorProduct.inductionOn with
  | tmul a b =>
      simp only [signedInsertion_tmul, map_add, LinearMap.rTensor_tmul,
        coproduct_ι_mul, coproduct_involute]
      exact assoc_signedInsertion R M x (coproduct R M a) b
  | add p q hp hq => simp only [map_add, hp, hq]

private theorem iteratedRight_insertion (x : M) (p : E ⊗[R] E) :
    (coproduct R M).lTensor E (signedInsertion R M x p) =
      tripleInsertion R M x ((coproduct R M).lTensor E p) := by
  induction p using TensorProduct.inductionOn with
  | tmul a b =>
      simp only [signedInsertion_tmul, map_add, LinearMap.lTensor_tmul,
        coproduct_ι_mul, tripleInsertion_tmul]
  | add p q hp hq => simp only [map_add, hp, hq]

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. For `a : E`, `α((Δ ⊗ id_E)(Δ a))=(id_E ⊗ Δ)(Δ a)`, where `α : (E⊗E)⊗E ≃
E⊗(E⊗E)` is the tensor associator. -/
theorem coproduct_coassoc_apply (a : E) :
    TensorProduct.assoc R E E E ((coproduct R M).rTensor E (coproduct R M a)) =
      (coproduct R M).lTensor E (coproduct R M a) := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp only [coproduct_algebraMap, map_smul, LinearMap.rTensor_tmul,
        LinearMap.lTensor_tmul, coproduct_one, TensorProduct.assoc_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]
  | ι_mul a x ha =>
      rw [coproduct_ι_mul, iteratedLeft_insertion, iteratedRight_insertion, ha]

theorem coproduct_coassoc :
    (TensorProduct.assoc R E E E).toLinearMap.comp
        (((coproduct R M).rTensor E).comp (coproduct R M)) =
      ((coproduct R M).lTensor E).comp (coproduct R M) :=
  LinearMap.ext (coproduct_coassoc_apply R M)

private theorem augmentation_left_insertion (x : M) (p : E ⊗[R] E) :
    (augmentation R M).toLinearMap.rTensor E (signedInsertion R M x p) =
      ((Algebra.lmul R E) (ι R x)).lTensor R
        ((augmentation R M).toLinearMap.rTensor E p) := by
  have h : ((augmentation R M).toLinearMap.rTensor E).comp (signedInsertion R M x) =
      (((Algebra.lmul R E) (ι R x)).lTensor R).comp
        ((augmentation R M).toLinearMap.rTensor E) := by
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, signedInsertion_tmul, map_add,
      LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply,
      map_mul, augmentation_ι, zero_mul, TensorProduct.zero_tmul, zero_add,
      augmentation_involute]
    rfl
  exact LinearMap.congr_fun h p

private theorem augmentation_right_insertion (x : M) (p : E ⊗[R] E) :
    (augmentation R M).toLinearMap.lTensor E (signedInsertion R M x p) =
      ((Algebra.lmul R E) (ι R x)).rTensor R
        ((augmentation R M).toLinearMap.lTensor E p) := by
  have h : ((augmentation R M).toLinearMap.lTensor E).comp (signedInsertion R M x) =
      (((Algebra.lmul R E) (ι R x)).rTensor R).comp
        ((augmentation R M).toLinearMap.lTensor E) := by
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, signedInsertion_tmul, map_add,
      LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply,
      map_mul, augmentation_ι, zero_mul, TensorProduct.tmul_zero, add_zero]
    rfl
  exact LinearMap.congr_fun h p

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. For `a : E` and `ε=augmentation R M`, `(ε ⊗ id_E)(Δ a)=1⊗a` in `R ⊗[R] E`. -/
theorem augmentation_rTensor_coproduct (a : E) :
    (augmentation R M).toLinearMap.rTensor E (coproduct R M a) = (1 : R) ⊗ₜ[R] a := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp only [coproduct_algebraMap, map_smul, LinearMap.rTensor_tmul,
        AlgHom.toLinearMap_apply, map_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.tmul_smul, coproduct_one, map_one]
  | add a b ha hb => simp only [map_add, ha, hb, TensorProduct.tmul_add]
  | ι_mul a x ha =>
      rw [coproduct_ι_mul, augmentation_left_insertion, ha, LinearMap.lTensor_tmul]
      rfl

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. For `a : E` and `ε=augmentation R M`, `(id_E ⊗ ε)(Δ a)=a⊗1` in `E ⊗[R] R`. -/
theorem augmentation_lTensor_coproduct (a : E) :
    (augmentation R M).toLinearMap.lTensor E (coproduct R M a) = a ⊗ₜ[R] (1 : R) := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp only [coproduct_algebraMap, map_smul, LinearMap.lTensor_tmul,
        AlgHom.toLinearMap_apply, map_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul', coproduct_one, map_one]
  | add a b ha hb => simp only [map_add, ha, hb, TensorProduct.add_tmul]
  | ι_mul a x ha =>
      rw [coproduct_ι_mul, augmentation_right_insertion, ha, LinearMap.rTensor_tmul]
      rfl

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. The coassociative coproduct `Δ` and counit `(augmentation R
M).toLinearMap` define `Coalgebra R E`, with the associator and both counit laws. -/
instance instCoalgebra : Coalgebra R E where
  comul := coproduct R M
  counit := (augmentation R M).toLinearMap
  coassoc := coproduct_coassoc R M
  rTensor_counit_comp_comul := LinearMap.ext (augmentation_rTensor_coproduct R M)
  lTensor_counit_comp_comul := LinearMap.ext (augmentation_lTensor_coproduct R M)

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. For every `x : M`, `ι(x)` is `(1,1)`-skew primitive: its counit is zero
and `Δ(ι(x))=1⊗ι(x)+ι(x)⊗1`. -/
theorem ι_isPrimitive (x : M) :
    Coalgebra.IsSkewPrimitiveElem R (1 : E) (1 : E) (ι R x) where
  counit_eq_zero := augmentation_ι R M x
  comul_eq_tmul_add_tmul := coproduct_ι R M x

section Naturality

variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. For an `R`-module `N`, `f : M →ₗ[R] N`, and `a : E`,
`γ_N(ExteriorAlgebra.map f a)=ExteriorAlgebra.map f (γ_M a)`. -/
theorem involute_map_apply (f : M →ₗ[R] N) (a : E) :
    CliffordAlgebra.involute (map f a) = map f (γ a) := by
  have h : (CliffordAlgebra.involute : ExteriorAlgebra R N →ₐ[R] ExteriorAlgebra R N).comp
      (map f) = (map f).comp γ := by
    apply ExteriorAlgebra.hom_ext
    apply LinearMap.ext
    intro x
    change CliffordAlgebra.involute (map f (ι R x)) = map f (γ (ι R x))
    rw [map_apply_ι, CliffordAlgebra.involute_ι, CliffordAlgebra.involute_ι, map_neg, map_apply_ι]
  exact AlgHom.congr_fun h a

theorem signedInsertion_naturality (f : M →ₗ[R] N) (x : M) (p : E ⊗[R] E) :
    TensorProduct.map (map f).toLinearMap (map f).toLinearMap (signedInsertion R M x p) =
      signedInsertion R N (f x)
        (TensorProduct.map (map f).toLinearMap (map f).toLinearMap p) := by
  have h : (TensorProduct.map (map f).toLinearMap (map f).toLinearMap).comp
      (signedInsertion R M x) =
    (signedInsertion R N (f x)).comp
      (TensorProduct.map (map f).toLinearMap (map f).toLinearMap) := by
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, signedInsertion_tmul, map_add,
      TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_mul, map_apply_ι,
      involute_map_apply]
  exact LinearMap.congr_fun h p

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. For an `R`-module `N`, `f : M →ₗ[R] N`, and `a : E`, `(Λf ⊗ Λf)(Δ_M
a)=Δ_N(Λf a)`, where `Λf=ExteriorAlgebra.map f`. -/
theorem coproduct_naturality (f : M →ₗ[R] N) (a : E) :
    TensorProduct.map (map f).toLinearMap (map f).toLinearMap (coproduct R M a) =
      coproduct R N (map f a) := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp only [AlgHom.commutes, coproduct_algebraMap, map_smul,
        TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one]
  | add a b ha hb => simp only [map_add, ha, hb]
  | ι_mul a x ha =>
      rw [coproduct_ι_mul, signedInsertion_naturality, ha, map_mul, map_apply_ι,
        coproduct_ι_mul]

@[simp]
theorem augmentation_map (f : M →ₗ[R] N) (a : E) :
    augmentation R N (map f a) = augmentation R M a := by
  have h : (augmentation R N).comp (map f) = augmentation R M := by
    apply ExteriorAlgebra.hom_ext
    apply LinearMap.ext
    intro x
    change augmentation R N (map f (ι R x)) = augmentation R M (ι R x)
    exact (congrArg (augmentation R N) (map_apply_ι f x)).trans
      ((augmentation_ι R N (f x)).trans (augmentation_ι R M x).symm)
  exact AlgHom.congr_fun h a

end Naturality

end ExteriorAlgebra
