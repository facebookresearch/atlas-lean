/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.UnitizationWords
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.Kernels

/-!
# Reduced normalized unitization coordinates

The positive degrees decompose using k ⊕ A, tensor distribution
over products and the quotient-tail equivalence. The bottom
degree is the kernel of scalar projection, identified with
the second coordinate.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex
open scoped TensorProduct

universe u v

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The degree-zero original regular tensor level is its coefficient module. -/
def unitizationOriginalZeroEquiv : chainLevel k A A 0 ≃ₗ[k] A :=
  TensorProduct.congr (LinearEquiv.refl k A) (TensorPower.zeroEquiv k A) ≪≫ₗ
    TensorProduct.rid k A

omit [IsScalarTower k A A] [SMulCommClass k A A] in
private theorem unitizationOriginalZeroEquiv_tprod (m : A) (a : Fin 0 → A) :
    unitizationOriginalZeroEquiv k A (m ⊗ₜ[k] PiTensorProduct.tprod k a) = m := by
  change (TensorProduct.rid k A)
    ((TensorProduct.congr (LinearEquiv.refl k A) (PiTensorProduct.isEmptyEquiv (Fin 0)))
      (m ⊗ₜ[k] PiTensorProduct.tprod k a)) = m
  rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    PiTensorProduct.isEmptyEquiv_apply_tprod, TensorProduct.rid_tmul, one_smul]

/-- The normalized bottom level has the same original unitization coefficient. -/
def unitizationNormalizedZeroEquiv :
    (normalizedBComplex k (Unitization k A)).X 0 ≃ₗ[k] Unitization k A :=
  TensorProduct.congr (LinearEquiv.refl k (Unitization k A))
      (TensorPower.zeroEquiv k
        (ModuleCat.Algebra.Hochschild.quotientCarrier k (Unitization k A))) ≪≫ₗ
    TensorProduct.rid k (Unitization k A)

private theorem unitizationNormalizedZeroEquiv_tprod (m : Unitization k A)
    (a : Fin 0 → ModuleCat.Algebra.Hochschild.quotientCarrier k (Unitization k A)) :
    unitizationNormalizedZeroEquiv k A (m ⊗ₜ[k] PiTensorProduct.tprod k a) = m := by
  change (TensorProduct.rid k (Unitization k A))
    ((TensorProduct.congr (LinearEquiv.refl k (Unitization k A))
      (PiTensorProduct.isEmptyEquiv (Fin 0))) (m ⊗ₜ[k] PiTensorProduct.tprod k a)) = m
  rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    PiTensorProduct.isEmptyEquiv_apply_tprod, TensorProduct.rid_tmul, one_smul]

/-- The bottom normalized projector is precisely scalar projection in the original coefficient. -/
theorem unitizationNormalizedZeroEquiv_projector
    (x : (normalizedBComplex k (Unitization k A)).X 0) :
    unitizationNormalizedZeroEquiv k A ((unitizationNormalizedScalarProjector k A).f 0 x) =
      unitizationScalarProjector k A (unitizationNormalizedZeroEquiv k A x) := by
  let L := (unitizationNormalizedZeroEquiv k A).toLinearMap.comp
    ((unitizationNormalizedScalarProjector k A).f 0).hom
  let R := (unitizationScalarProjector k A).toLinearMap.comp
    (unitizationNormalizedZeroEquiv k A).toLinearMap
  have h : L = R := by
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro m a
    change unitizationNormalizedZeroEquiv k A
      (ModuleCat.Algebra.Hochschild.normalizedLevelLinearMap
        (unitizationScalarProjector k A).toLinearMap
        (unitizationScalarProjector k A).toLinearMap
        (unitizationScalarProjector k A).map_one 0
        (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      unitizationScalarProjector k A
        (unitizationNormalizedZeroEquiv k A (m ⊗ₜ[k] PiTensorProduct.tprod k a))
    dsimp only [ModuleCat.Algebra.Hochschild.normalizedLevelLinearMap]
    rw [TensorProduct.map_tmul, PiTensorProduct.map_tprod,
      unitizationNormalizedZeroEquiv_tprod, unitizationNormalizedZeroEquiv_tprod]
    rfl
  exact DFunLike.congr_fun h x

/-- The degree-zero reduced kernel is the original nonunital coefficient tensor level. -/
def unitizationReducedZeroLinearEquiv :
    LinearMap.ker ((unitizationNormalizedScalarProjector k A).f 0).hom ≃ₗ[k]
      chainLevel k A A 0 where
  toLinearMap := (unitizationOriginalZeroEquiv k A).symm.toLinearMap.comp
    ((Unitization.sndHom k k A).comp
      ((unitizationNormalizedZeroEquiv k A).toLinearMap.comp
        (LinearMap.ker ((unitizationNormalizedScalarProjector k A).f 0).hom).subtype))
  invFun x := ⟨(unitizationNormalizedZeroEquiv k A).symm
    (Unitization.inr (unitizationOriginalZeroEquiv k A x)), by
      apply (unitizationNormalizedZeroEquiv k A).injective
      rw [unitizationNormalizedZeroEquiv_projector, LinearEquiv.apply_symm_apply,
        unitizationScalarProjector_apply, Unitization.fst_inr, Unitization.inl_zero, map_zero]⟩
  left_inv x := by
    apply Subtype.ext
    apply (unitizationNormalizedZeroEquiv k A).injective
    have hx := congrArg (unitizationNormalizedZeroEquiv k A) x.property
    rw [unitizationNormalizedZeroEquiv_projector, map_zero] at hx
    have hf := congrArg (fun y : Unitization k A => y.fst) hx
    simp only [unitizationScalarProjector_apply, Unitization.fst_inl,
      Unitization.fst_zero] at hf
    change unitizationNormalizedZeroEquiv k A
      ((unitizationNormalizedZeroEquiv k A).symm
        (Unitization.inr (unitizationOriginalZeroEquiv k A
          ((unitizationOriginalZeroEquiv k A).symm
            ((unitizationNormalizedZeroEquiv k A x).snd))))) = _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    simpa only [hf, Unitization.inl_zero, zero_add] using
      Unitization.inl_fst_add_inr_snd_eq (unitizationNormalizedZeroEquiv k A x)
  right_inv x := by
    change (unitizationOriginalZeroEquiv k A).symm
      ((unitizationNormalizedZeroEquiv k A
        ((unitizationNormalizedZeroEquiv k A).symm
          (Unitization.inr (unitizationOriginalZeroEquiv k A x)))).snd) = x
    rw [LinearEquiv.apply_symm_apply, Unitization.snd_inr, LinearEquiv.symm_apply_apply]

/-- Native preservation of this kernel by evaluation computes its original degree module. -/
def unitizationReducedKernelLevelIso (n : ℕ) :
    (unitizationReducedNormalizedComplex k A).X n ≅
      ModuleCat.of k (LinearMap.ker ((unitizationNormalizedScalarProjector k A).f n).hom) :=
  PreservesKernel.iso (HomologicalComplex.eval (ModuleCat.{max u v} k) (ComplexShape.down ℕ) n)
      (unitizationNormalizedScalarProjector k A) ≪≫
    ModuleCat.kernelIsoKer ((unitizationNormalizedScalarProjector k A).f n)

/-- The computed degree-kernel comparison retains the original inclusion. -/
@[reassoc]
theorem unitizationReducedKernelLevelIso_hom_subtype (n : ℕ) :
    (unitizationReducedKernelLevelIso k A n).hom ≫
        ModuleCat.ofHom (LinearMap.ker ((unitizationNormalizedScalarProjector k A).f n).hom).subtype =
      (kernel.ι (unitizationNormalizedScalarProjector k A)).f n := by
  rw [unitizationReducedKernelLevelIso, Iso.trans_hom, Category.assoc,
    ModuleCat.kernelIsoKer_hom_ker_subtype, PreservesKernel.iso_hom]
  exact kernelComparison_comp_ι _ _

/-- The original reduced bottom coefficient is from its kernel. -/
def unitizationReducedZeroIso :
    (unitizationReducedNormalizedComplex k A).X 0 ≅ chainLevel k A A 0 :=
  unitizationReducedKernelLevelIso k A 0 ≪≫
    (unitizationReducedZeroLinearEquiv k A).toModuleIso

/-- In positive degrees the reduced inclusion is an isomorphism, since this projector is zero. -/
instance unitizationReducedInclusion_succ_isIso (n : ℕ) :
    IsIso ((kernel.ι (unitizationNormalizedScalarProjector k A)).f (n + 1)) := by
  let E := HomologicalComplex.eval (ModuleCat.{max u v} k) (ComplexShape.down ℕ) (n + 1)
  have : IsIso (kernel.ι (E.map (unitizationNormalizedScalarProjector k A))) :=
    kernel.ι_of_zero (unitizationNormalizedScalarProjector_f_succ k A n)
  change IsIso (E.map (kernel.ι (unitizationNormalizedScalarProjector k A)))
  rw [← kernelComparison_comp_ι]
  infer_instance

/-- The positive reduced comparison is exactly its original kernel inclusion. -/
def unitizationReducedPositiveIso (n : ℕ) :
    (unitizationReducedNormalizedComplex k A).X (n + 1) ≅
      (normalizedBComplex k (Unitization k A)).X (n + 1) :=
  asIso ((kernel.ι (unitizationNormalizedScalarProjector k A)).f (n + 1))

/-- The bottom inverse really is the original even word, without a scalar summand. -/
@[reassoc]
theorem unitizationReducedZeroIso_inv_inclusion :
    (unitizationReducedZeroIso k A).inv ≫
        (kernel.ι (unitizationNormalizedScalarProjector k A)).f 0 =
      unitizationEvenWord k A 0 := by
  rw [← unitizationReducedKernelLevelIso_hom_subtype]
  simp only [unitizationReducedZeroIso, Iso.trans_inv, Category.assoc,
    Iso.inv_hom_id_assoc]
  apply ModuleCat.hom_ext
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [unitizationEvenWord_tprod]
  apply (unitizationNormalizedZeroEquiv k A).injective
  change unitizationNormalizedZeroEquiv k A
    ((unitizationNormalizedZeroEquiv k A).symm
      (Unitization.inr (unitizationOriginalZeroEquiv k A
        (m ⊗ₜ[k] PiTensorProduct.tprod k a)))) =
      unitizationNormalizedZeroEquiv k A
        (Unitization.inr m ⊗ₜ[k] PiTensorProduct.tprod k
          (fun i => originalToUnitizationQuotient k A (a i)))
  rw [LinearEquiv.apply_symm_apply, unitizationOriginalZeroEquiv_tprod,
    unitizationNormalizedZeroEquiv_tprod]

/-- The literal positive normalized tensor level has its original even and odd word coordinates. -/
def unitizationNormalizedPositiveEquiv (n : ℕ) :
    (normalizedBComplex k (Unitization k A)).X (n + 1) ≃ₗ[k]
      chainLevel k A A (n + 1) × chainLevel k A A n :=
  TensorProduct.congr (Unitization.linearEquiv k k A)
      (PiTensorProduct.congr (fun _ : Fin (n + 1) => unitizationQuotientEquiv k A)) ≪≫ₗ
    TensorProduct.prodLeft k k k A (TensorPower k (n + 1) A) ≪≫ₗ
    (TensorProduct.lid k (TensorPower k (n + 1) A)).prodCongr
      (LinearEquiv.refl k (chainLevel k A A (n + 1))) ≪≫ₗ
    LinearEquiv.prodComm k (TensorPower k (n + 1) A) (chainLevel k A A (n + 1)) ≪≫ₗ
    (LinearEquiv.refl k (chainLevel k A A (n + 1))).prodCongr (TensorPower.consEquiv k A n).symm

private theorem unitizationNormalizedPositiveEquiv_tprod (n : ℕ) (m : Unitization k A)
    (a : Fin (n + 1) → A) :
    unitizationNormalizedPositiveEquiv k A n
      (m ⊗ₜ[k] PiTensorProduct.tprod k (fun i => originalToUnitizationQuotient k A (a i))) =
        (m.snd ⊗ₜ[k] PiTensorProduct.tprod k a,
          (TensorPower.consEquiv k A n).symm (m.fst • PiTensorProduct.tprod k a)) := by
  change ((LinearEquiv.refl k (chainLevel k A A (n + 1))).prodCongr
    (TensorPower.consEquiv k A n).symm)
    ((LinearEquiv.prodComm k (TensorPower k (n + 1) A) (chainLevel k A A (n + 1)))
      (((TensorProduct.lid k (TensorPower k (n + 1) A)).prodCongr
        (LinearEquiv.refl k (chainLevel k A A (n + 1))))
        ((TensorProduct.prodLeft k k k A (TensorPower k (n + 1) A))
          ((TensorProduct.congr (Unitization.linearEquiv k k A)
            (PiTensorProduct.congr (fun _ : Fin (n + 1) => unitizationQuotientEquiv k A)))
            (m ⊗ₜ[k] PiTensorProduct.tprod k
              (fun i => originalToUnitizationQuotient k A (a i))))))) = _
  rw [TensorProduct.congr_tmul, PiTensorProduct.congr_tprod]
  have hQ (x : A) : unitizationQuotientEquiv k A (originalToUnitizationQuotient k A x) = x := rfl
  simp only [Unitization.linearEquiv_apply, hQ]
  rw [TensorProduct.prodLeft_tmul]
  rfl

/-- The even coordinate gives precisely the original word in the first product factor. -/
theorem unitizationNormalizedPositiveEquiv_even (n : ℕ) (x : chainLevel k A A (n + 1)) :
    unitizationNormalizedPositiveEquiv k A n ((unitizationEvenWord k A (n + 1)).hom x) = (x, 0) := by
  let L := (unitizationNormalizedPositiveEquiv k A n).toLinearMap.comp
    (unitizationEvenWord k A (n + 1)).hom
  have h : L = LinearMap.inl k _ _ := by
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro m a
    change unitizationNormalizedPositiveEquiv k A n
      ((unitizationEvenWord k A (n + 1)).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
        (m ⊗ₜ[k] PiTensorProduct.tprod k a, 0)
    erw [unitizationEvenWord_tprod]
    rw [unitizationNormalizedPositiveEquiv_tprod]
    simp only [Unitization.snd_inr, Unitization.fst_inr, zero_smul, map_zero]
  exact DFunLike.congr_fun h x

/-- The odd coordinate gives precisely the same original word in the second product factor. -/
theorem unitizationNormalizedPositiveEquiv_odd (n : ℕ) (x : chainLevel k A A n) :
    unitizationNormalizedPositiveEquiv k A n ((unitizationOddWord k A n).hom x) = (0, x) := by
  let L := (unitizationNormalizedPositiveEquiv k A n).toLinearMap.comp
    (unitizationOddWord k A n).hom
  have h : L = LinearMap.inr k _ _ := by
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro m a
    change unitizationNormalizedPositiveEquiv k A n
      ((unitizationOddWord k A n).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
        (0, m ⊗ₜ[k] PiTensorProduct.tprod k a)
    erw [unitizationOddWord_tprod]
    rw [unitizationNormalizedPositiveEquiv_tprod]
    change ((0 : A) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.cons m a : Fin (n + 1) → A),
      (TensorPower.consEquiv k A n).symm
        ((1 : k) • PiTensorProduct.tprod k (Fin.cons m a : Fin (n + 1) → A))) = _
    rw [TensorProduct.zero_tmul, one_smul, ← TensorPower.consEquiv_tmul,
      LinearEquiv.symm_apply_apply]
  exact DFunLike.congr_fun h x

end ModuleCat.Algebra.Hochschild.NonUnital
