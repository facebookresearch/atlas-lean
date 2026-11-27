/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.Basic
public import MathlibExt.Algebra.Category.ModuleCat.HomologyZero
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Degree-zero Hochschild homology of a bimodule

The Hochschild boundary sends m ⊗ a to ma - am. Its image is the
ground-ring submodule spanned by the commutators am - ma, so degree-zero
homology is the corresponding module quotient. The comparison uses the
tensor coordinates and the homology class map.

References: Loday, Cyclic Homology, §1.1; Weibel, Homological Algebra, §9.1.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild

section Coordinates

variable (k : Type u) [CommRing k] (A : Type v) [AddCommGroup A] [Module k A]
  (M : Type w) [AddCommGroup M] [Module k M]

/-- The empty tensor degree is the coefficient module. -/
def zeroEquiv : M ⊗[k] TensorPower k 0 A ≃ₗ[k] M :=
  (TensorProduct.congr (LinearEquiv.refl k M)
    (PiTensorProduct.isEmptyEquiv (R := k) (s := fun _ : Fin 0 => A) (Fin 0))).trans
      (TensorProduct.rid k M)

@[simp]
theorem zeroEquiv_tprod (m : M) (a : Fin 0 → A) :
    zeroEquiv k A M (m ⊗ₜ[k] PiTensorProduct.tprod k a) = m := by
  simp only [zeroEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, PiTensorProduct.isEmptyEquiv_apply_tprod,
    TensorProduct.rid_tmul, one_smul]

/-- The singleton tensor degree is `M ⊗ A`. -/
def oneEquiv : M ⊗[k] TensorPower k 1 A ≃ₗ[k] M ⊗[k] A :=
  TensorProduct.congr (LinearEquiv.refl k M)
    (PiTensorProduct.subsingletonEquiv (R := k) (s := fun _ : Fin 1 => A) (0 : Fin 1))

@[simp]
theorem oneEquiv_symm_tmul (m : M) (a : A) :
    (oneEquiv k A M).symm (m ⊗ₜ[k] a) =
      m ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => a) := by
  rw [oneEquiv, TensorProduct.congr_symm_tmul,
    PiTensorProduct.subsingletonEquiv_symm_apply']
  rfl

end Coordinates

section Bimodule

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M] [Module Aᵐᵒᵖ M]
  [SMulCommClass A Aᵐᵒᵖ M] [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]

/-- The ground-ring submodule spanned by the bimodule commutators `am - ma`. -/
def commutatorSubmodule : Submodule k M :=
  Submodule.span k (Set.range (fun p : A × M => p.1 • p.2 - MulOpposite.op p.1 • p.2))

/-- The coefficient module quotient by bimodule commutators. -/
abbrev coinvariants := M ⧸ commutatorSubmodule k A M

omit [Algebra k A] [SMulCommClass A Aᵐᵒᵖ M] [SMulCommClass k A M]
  [SMulCommClass k Aᵐᵒᵖ M] [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M] in
theorem commutator_mem (a : A) (m : M) :
    a • m - MulOpposite.op a • m ∈ commutatorSubmodule k A M :=
  Submodule.subset_span ⟨(a, m), rfl⟩

/-- Return the degree-one boundary to the coefficient module. -/
def boundaryToCoefficient : M ⊗[k] TensorPower k 1 A →ₗ[k] M :=
  (zeroEquiv k A M).toLinearMap.comp (boundary k A M 0).hom

@[simp]
theorem boundaryToCoefficient_tprod (m : M) (a : Fin 1 → A) :
    boundaryToCoefficient k A M (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      MulOpposite.op (a 0) • m - a 0 • m := by
  change zeroEquiv k A M
      ((boundary k A M 0).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a)) = _
  rw [boundary_one_tprod, map_sub, zeroEquiv_tprod, zeroEquiv_tprod]

/-- The `b₁ : M ⊗ A → M`, using the native singleton coordinates. -/
def boundaryLinearMap : M ⊗[k] A →ₗ[k] M :=
  (boundaryToCoefficient k A M).comp (oneEquiv k A M).symm.toLinearMap

@[simp]
theorem boundaryLinearMap_tmul (m : M) (a : A) :
    boundaryLinearMap k A M (m ⊗ₜ[k] a) = MulOpposite.op a • m - a • m := by
  change boundaryToCoefficient k A M ((oneEquiv k A M).symm (m ⊗ₜ[k] a)) = _
  exact (congrArg (boundaryToCoefficient k A M) (oneEquiv_symm_tmul k A M m a)).trans
    (boundaryToCoefficient_tprod k A M m (fun _ : Fin 1 => a))

/-- The boundary image equals the commutator submodule; opposite
generator signs produce the same submodule by negation. -/
theorem range_boundaryLinearMap :
    LinearMap.range (boundaryLinearMap k A M) = commutatorSubmodule k A M := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    induction x using TensorProduct.inductionOn with
    | tmul m a =>
      rw [boundaryLinearMap_tmul]
      simpa only [neg_sub] using
        (commutatorSubmodule k A M).neg_mem (commutator_mem k A M a m)
    | add x y hx hy =>
      rw [map_add]
      exact (commutatorSubmodule k A M).add_mem hx hy
  · refine Submodule.span_le.mpr ?_
    rintro y ⟨⟨a, m⟩, rfl⟩
    change a • m - MulOpposite.op a • m ∈ LinearMap.range (boundaryLinearMap k A M)
    have h : MulOpposite.op a • m - a • m ∈ LinearMap.range (boundaryLinearMap k A M) :=
      ⟨m ⊗ₜ[k] a, boundaryLinearMap_tmul k A M m a⟩
    simpa only [neg_sub] using (LinearMap.range (boundaryLinearMap k A M)).neg_mem h

/-- The same image computation on the literal tensor-power chain degree. -/
theorem range_boundaryToCoefficient :
    LinearMap.range (boundaryToCoefficient k A M) = commutatorSubmodule k A M := by
  have h : LinearMap.range (boundaryLinearMap k A M) =
      LinearMap.range (boundaryToCoefficient k A M) := by
    exact LinearMap.range_comp_of_range_eq_top (boundaryToCoefficient k A M)
      (LinearMap.range_eq_top.mpr (oneEquiv k A M).symm.surjective)
  exact h.symm.trans (range_boundaryLinearMap k A M)

/-- Empty-degree coordinates send the differential image to the
ground-ring commutator submodule. -/
theorem map_range_boundary :
    (LinearMap.range (boundary k A M 0).hom).map (zeroEquiv k A M).toLinearMap =
      commutatorSubmodule k A M := by
  rw [← range_boundaryToCoefficient]
  exact (LinearMap.range_comp (boundary k A M 0).hom
    (zeroEquiv k A M).toLinearMap).symm

/-- The tensor-degree cokernel quotient in coefficient coordinates. -/
def zeroQuotientEquiv :
    ((chainComplex k A M).X 0 ⧸
        LinearMap.range ((chainComplex k A M).d 1 0).hom) ≃ₗ[k]
      coinvariants k A M :=
  Submodule.Quotient.equiv
    (LinearMap.range ((chainComplex k A M).d 1 0).hom) (commutatorSubmodule k A M)
    (show (chainComplex k A M).X 0 ≃ₗ[k] M from zeroEquiv k A M) (by
      rw [chainComplex_d]
      exact map_range_boundary k A M)

theorem zeroQuotientEquiv_mkQ (x : (chainComplex k A M).X 0) :
    zeroQuotientEquiv k A M
        ((LinearMap.range ((chainComplex k A M).d 1 0).hom).mkQ x) =
      (commutatorSubmodule k A M).mkQ (zeroEquiv k A M x) :=
  rfl

/-- The homology/cokernel comparison, assembled entirely through
native opcycles, cokernel uniqueness and the concrete module quotient. -/
def homologyZeroLinearEquiv : (homology k A M 0).carrier ≃ₗ[k] coinvariants k A M :=
  (ModuleCat.homologyZeroIsoRangeQuotient (chainComplex k A M)).toLinearEquiv.trans
    (zeroQuotientEquiv k A M)

/-- The comparison evaluates a native homology class by empty-tensor
coordinates followed by the commutator quotient projection. -/
theorem homologyZeroLinearEquiv_class (x : (chainComplex k A M).X 0) :
    homologyZeroLinearEquiv k A M
        ((chainComplex k A M).isoHomologyι₀.inv.hom
          (((chainComplex k A M).pOpcycles 0).hom x)) =
      (commutatorSubmodule k A M).mkQ (zeroEquiv k A M x) := by
  have hx : (ModuleCat.homologyZeroIsoRangeQuotient (chainComplex k A M)).hom.hom
      ((chainComplex k A M).isoHomologyι₀.inv.hom
        (((chainComplex k A M).pOpcycles 0).hom x)) =
      (LinearMap.range ((chainComplex k A M).d 1 0).hom).mkQ x := by
    simpa only [ChainComplex.homologyZeroClass, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_ofHom] using
      congrArg
        (fun f : (chainComplex k A M).X 0 ⟶
            ModuleCat.of k ((chainComplex k A M).X 0 ⧸
              LinearMap.range ((chainComplex k A M).d 1 0).hom) => f.hom x)
        (ModuleCat.homologyZeroIsoRangeQuotient_class (chainComplex k A M))
  change zeroQuotientEquiv k A M
      ((ModuleCat.homologyZeroIsoRangeQuotient (chainComplex k A M)).hom.hom
        ((chainComplex k A M).isoHomologyι₀.inv.hom
          (((chainComplex k A M).pOpcycles 0).hom x))) = _
  rw [hx, zeroQuotientEquiv_mkQ]

/-- A categorical version in the native tensor-degree universe. -/
def homologyZeroIso : homology k A M 0 ≅
    ModuleCat.of k (ULift.{max u v w} (coinvariants k A M)) :=
  ((homologyZeroLinearEquiv k A M).trans
    (ULift.moduleEquiv : ULift.{max u v w} (coinvariants k A M) ≃ₗ[k]
      coinvariants k A M).symm).toModuleIso

/-- The native class map on raw coefficients, through empty-tensor
coordinates, opcycles and the degree-zero homology isomorphism. -/
def zeroClassMap : M →ₗ[k] (homology k A M 0).carrier :=
  (chainComplex k A M).isoHomologyι₀.inv.hom.comp
    (((chainComplex k A M).pOpcycles 0).hom.comp (zeroEquiv k A M).symm.toLinearMap)

@[simp]
theorem homologyZeroLinearEquiv_zeroClassMap (m : M) :
    homologyZeroLinearEquiv k A M (zeroClassMap k A M m) =
      (commutatorSubmodule k A M).mkQ m := by
  let x : (chainComplex k A M).X 0 :=
    show (chainComplex k A M).X 0 from (zeroEquiv k A M).symm m
  have hx := homologyZeroLinearEquiv_class k A M x
  have he : zeroEquiv k A M x = m := LinearEquiv.apply_symm_apply (zeroEquiv k A M) m
  change homologyZeroLinearEquiv k A M
      ((chainComplex k A M).isoHomologyι₀.inv.hom
        (((chainComplex k A M).pOpcycles 0).hom x)) = _
  exact hx.trans (congrArg (commutatorSubmodule k A M).mkQ he)

theorem homologyZeroLinearEquiv_symm_mkQ (m : M) :
    (homologyZeroLinearEquiv k A M).symm ((commutatorSubmodule k A M).mkQ m) =
      zeroClassMap k A M m := by
  apply (homologyZeroLinearEquiv k A M).injective
  rw [LinearEquiv.apply_symm_apply, homologyZeroLinearEquiv_zeroClassMap]

theorem zeroClassMap_commutator (a : A) (m : M) :
    zeroClassMap k A M (a • m - MulOpposite.op a • m) = 0 := by
  apply (homologyZeroLinearEquiv k A M).injective
  rw [homologyZeroLinearEquiv_zeroClassMap, map_zero, Submodule.mkQ_apply]
  exact (Submodule.Quotient.mk_eq_zero (p := commutatorSubmodule k A M)
    (x := a • m - MulOpposite.op a • m)).mpr (commutator_mem k A M a m)

/-- The native class map kills precisely the commutator submodule. -/
theorem zeroClassMap_eq_zero_iff (m : M) :
    zeroClassMap k A M m = 0 ↔ m ∈ commutatorSubmodule k A M := by
  constructor
  · intro hm
    apply (Submodule.Quotient.mk_eq_zero (p := commutatorSubmodule k A M) (x := m)).mp
    change (commutatorSubmodule k A M).mkQ m = 0
    rw [← homologyZeroLinearEquiv_zeroClassMap, hm, map_zero]
  · intro hm
    apply (homologyZeroLinearEquiv k A M).injective
    rw [homologyZeroLinearEquiv_zeroClassMap, map_zero, Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero (p := commutatorSubmodule k A M) (x := m)).mpr hm

theorem ker_zeroClassMap :
    LinearMap.ker (zeroClassMap k A M) = commutatorSubmodule k A M := by
  ext m
  exact zeroClassMap_eq_zero_iff k A M m

/-- The left and right coefficient actions have the same class in the
actual degree-zero homology. -/
theorem zeroClassMap_left_eq_right (a : A) (m : M) :
    zeroClassMap k A M (a • m) = zeroClassMap k A M (MulOpposite.op a • m) := by
  have h := zeroClassMap_commutator k A M a m
  rw [map_sub] at h
  exact sub_eq_zero.mp h

theorem zeroClassMap_surjective : Function.Surjective (zeroClassMap k A M) := by
  intro h
  obtain ⟨m, hm⟩ := (commutatorSubmodule k A M).mkQ_surjective
    (homologyZeroLinearEquiv k A M h)
  refine ⟨m, (homologyZeroLinearEquiv k A M).injective ?_⟩
  rw [homologyZeroLinearEquiv_zeroClassMap, hm]

/-- The boundary and native coefficient class map form the printed
degree-zero exact quotient sequence. -/
theorem boundary_exact_zeroClassMap :
    Function.Exact (boundaryLinearMap k A M) (zeroClassMap k A M) :=
  LinearMap.exact_iff.mpr
    ((ker_zeroClassMap k A M).trans (range_boundaryLinearMap k A M).symm)

/-- A coefficient map killing all commutators descends through the degree-zero homology, using the native module quotient universal map. -/
def descZero {N : Type*} [AddCommGroup N] [Module k N]
    (f : M →ₗ[k] N) (hf : ∀ (a : A) (m : M), f (a • m - MulOpposite.op a • m) = 0) :
    (homology k A M 0).carrier →ₗ[k] N :=
  ((commutatorSubmodule k A M).liftQ f (Submodule.span_le.mpr (by
    rintro x ⟨⟨a, m⟩, rfl⟩
    exact hf a m))).comp (homologyZeroLinearEquiv k A M).toLinearMap

@[simp]
theorem descZero_zeroClassMap {N : Type*} [AddCommGroup N] [Module k N]
    (f : M →ₗ[k] N) (hf : ∀ (a : A) (m : M), f (a • m - MulOpposite.op a • m) = 0)
    (m : M) : descZero k A M f hf (zeroClassMap k A M m) = f m := by
  let hk : commutatorSubmodule k A M ≤ f.ker := Submodule.span_le.mpr (by
    rintro x ⟨⟨a, m⟩, rfl⟩
    exact hf a m)
  change (commutatorSubmodule k A M).liftQ f hk
      (homologyZeroLinearEquiv k A M (zeroClassMap k A M m)) = f m
  rw [homologyZeroLinearEquiv_zeroClassMap]
  simpa only [Submodule.mkQ_apply] using
    (Submodule.liftQ_apply (p := commutatorSubmodule k A M) f (h := hk) m)

theorem descZero_unique {N : Type*} [AddCommGroup N] [Module k N]
    (f : M →ₗ[k] N) (hf : ∀ (a : A) (m : M), f (a • m - MulOpposite.op a • m) = 0)
    (g : (homology k A M 0).carrier →ₗ[k] N)
    (hg : ∀ m : M, g (zeroClassMap k A M m) = f m) :
    g = descZero k A M f hf := by
  ext h
  obtain ⟨m, rfl⟩ := zeroClassMap_surjective k A M h
  rw [hg, descZero_zeroClassMap]

omit [Algebra k A] [SMulCommClass A Aᵐᵒᵖ M] [SMulCommClass k A M]
  [SMulCommClass k Aᵐᵒᵖ M] [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M] in
/-- Symmetric coefficient actions are a separate case in which the
commutator submodule vanishes. No symmetry is required for the general API. -/
theorem commutatorSubmodule_eq_bot
    (h : ∀ (a : A) (m : M), a • m = MulOpposite.op a • m) :
    commutatorSubmodule k A M = ⊥ := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨⟨a, m⟩, rfl⟩
    change a • m - MulOpposite.op a • m ∈ (⊥ : Submodule k M)
    rw [h, sub_self]
    exact Submodule.zero_mem _
  · exact bot_le

/-- With separately specified symmetric actions, the degree-zero
homology is the coefficient module itself. -/
def homologyZeroSymmetricEquiv
    (h : ∀ (a : A) (m : M), a • m = MulOpposite.op a • m) :
    (homology k A M 0).carrier ≃ₗ[k] M :=
  (homologyZeroLinearEquiv k A M).trans
    ((commutatorSubmodule k A M).quotEquivOfEqBot (commutatorSubmodule_eq_bot k A M h))

@[simp]
theorem homologyZeroSymmetricEquiv_zeroClassMap
    (h : ∀ (a : A) (m : M), a • m = MulOpposite.op a • m) (m : M) :
    homologyZeroSymmetricEquiv k A M h (zeroClassMap k A M m) = m := by
  simp only [homologyZeroSymmetricEquiv, LinearEquiv.trans_apply,
    homologyZeroLinearEquiv_zeroClassMap, Submodule.mkQ_apply,
    Submodule.quotEquivOfEqBot_apply_mk]

end Bimodule

end ModuleCat.Algebra.Hochschild
