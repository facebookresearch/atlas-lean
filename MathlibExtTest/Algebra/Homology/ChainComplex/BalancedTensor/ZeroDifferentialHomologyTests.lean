/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
Authors: @toskua, Codex
-/
module

import MathlibExt.Algebra.Homology.ChainComplex.BalancedTensor.ZeroDifferentialHomology
import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.ProjectiveExact
import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Unitors
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# An integral negative-degree tensor homology calculation

The right coefficient is the regular integer module in degree -1. The left
complex has multiplication by two from degree one to degree zero. Their
native tensor total has differential -2 and homology ZMod 2 in degree -1.
The canonical comparison carries the tensor of one and the class of one
to a nonzero homology class.
-/

noncomputable section

open CategoryTheory Limits HomologicalComplex ChainComplex.BalancedTensor

namespace MathlibExtTest.BalancedTensorZeroDifferentialHomology

private abbrev Z : ModuleCat.{0} ℤ := ModuleCat.of ℤ ℤ
private abbrev Z2 : ModuleCat.{0} ℤ := ModuleCat.of ℤ (ZMod 2)
private abbrev regularRight : ModuleCat.{0} ℤᵐᵒᵖ := ModuleCat.of ℤᵐᵒᵖ ℤ

private def regularRightEquiv : ℤᵐᵒᵖ ≃ₗ[ℤᵐᵒᵖ] ℤ where
  toFun := MulOpposite.unop
  invFun := MulOpposite.op
  left_inv := MulOpposite.op_unop
  right_inv := MulOpposite.unop_op
  map_add' _ _ := rfl
  map_smul' r x := by
    first
    | rfl
    | change x.unop * r.unop = r.unop * x.unop
      exact mul_comm _ _

private instance regularRight_projective : Projective regularRight :=
  ModuleCat.projective_of_free
    ((Basis.singleton PUnit ℤᵐᵒᵖ).map regularRightEquiv)

private def A (p : ℤ) : ModuleCat.{0} ℤᵐᵒᵖ :=
  if p = -1 then regularRight else 0

private instance A_projective (p : ℤ) : Projective (A p) := by
  classical
  by_cases hp : p = -1
  · simpa only [A, if_pos hp] using (inferInstance : Projective regularRight)
  · simpa only [A, if_neg hp] using
      (inferInstance : Projective (0 : ModuleCat.{0} ℤᵐᵒᵖ))

private instance A_exact (p : ℤ) :
    ((ModuleCat.BalancedTensor.groupBifunctor ℤ).obj (A p)).PreservesHomology :=
  ModuleCat.BalancedTensor.groupBifunctor_obj_preservesHomology_of_projective ℤ (A p)

private instance A_exact_family :
    ∀ p : ℤ, ((ModuleCat.BalancedTensor.groupBifunctor ℤ).obj (A p)).PreservesHomology :=
  fun p => inferInstance

private def two : Z ⟶ Z :=
  ModuleCat.ofHom ((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))

private def modTwo : Z ⟶ Z2 :=
  ModuleCat.ofHom (Int.castAddHom (ZMod 2)).toIntLinearMap

private lemma two_comp_modTwo : two ≫ modTwo = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp [two, modTwo, smul_eq_mul]

private instance two_mono : Mono two := by
  apply (ModuleCat.mono_iff_injective two).2
  intro x y h
  have hm : (2 : ℤ) * x = 2 * y := by simpa [two, smul_eq_mul] using h
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) hm

private instance modTwo_epi : Epi modTwo := by
  apply (ModuleCat.epi_iff_surjective modTwo).2
  intro x
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective x
  exact ⟨z, hz⟩

private def modTwoSequence : ShortComplex (ModuleCat.{0} ℤ) :=
  ShortComplex.mk two modTwo two_comp_modTwo

private lemma modTwoSequence_shortExact : modTwoSequence.ShortExact := by
  apply ShortComplex.ShortExact.mk'
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    apply Submodule.ext
    intro x
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    change (∃ z : ℤ, (2 : ℤ) • z = x) ↔ (x : ZMod 2) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, by simpa [smul_eq_mul] using hz.symm⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, by simpa [smul_eq_mul] using hz.symm⟩
  · infer_instance
  · infer_instance

private def X (i : ℤ) : ModuleCat.{0} ℤ :=
  if i = 0 ∨ i = 1 then Z else 0

private def d (i : ℤ) : X (i + 1) ⟶ X i :=
  if hi : i = 0 then by
    subst i
    exact two
  else 0

private lemma d_sq (i : ℤ) : d (i + 1) ≫ d i = 0 := by
  by_cases hi : i = 0
  · subst i
    rw [show d (0 + 1) = 0 by simp [d]]
    exact zero_comp
  · rw [show d i = 0 by simp [d, hi]]
    exact comp_zero

private def Q : ChainComplex (ModuleCat.{0} ℤ) ℤ := ChainComplex.of X d d_sq

private lemma Q_d_one_zero : Q.d 1 0 = two := by
  change ChainComplex.of.d X d (0 + 1) 0 = two
  rw [ChainComplex.of_d]
  simp [d]

private lemma Q_d_zero_negOne : Q.d 0 (-1) = 0 := by
  simp [Q, ChainComplex.of.d, d]

private def QIdKernel :
    IsLimit (KernelFork.ofι (𝟙 Z)
      (show (𝟙 Z) ≫ (Q.sc' 1 0 (-1)).g = 0 by simp [Q_d_zero_negOne])) where
  lift s := s.π.app WalkingParallelPair.zero
  fac s j := by
    cases j
    · change _ ≫ (𝟙 Z) = _
      exact Category.comp_id _
    · exact (isZero_zero (ModuleCat.{0} ℤ)).eq_of_tgt _ _
  uniq s m hm := by
    have h := hm WalkingParallelPair.zero
    change m ≫ (𝟙 Z) = _ at h
    simpa only [Category.comp_id] using h

private lemma QIdKernel_lift :
    QIdKernel.lift (KernelFork.ofι (Q.sc' 1 0 (-1)).f (Q.sc' 1 0 (-1)).zero) = two := by
  have h := QIdKernel.fac
    (KernelFork.ofι (Q.sc' 1 0 (-1)).f (Q.sc' 1 0 (-1)).zero) WalkingParallelPair.zero
  change _ ≫ (𝟙 Z) = Q.d 1 0 at h
  simpa only [Category.comp_id, Q_d_one_zero] using h

private def QHomologyData : (Q.sc' 1 0 (-1)).LeftHomologyData where
  K := Z
  H := Z2
  i := 𝟙 Z
  π := modTwo
  wi := by simp [Q_d_zero_negOne]
  hi := QIdKernel
  wπ := by rw [QIdKernel_lift]; exact two_comp_modTwo
  hπ := by simpa only [QIdKernel_lift] using modTwoSequence_shortExact.gIsCokernel

private def QH0Iso : Q.homology 0 ≅ Z2 :=
  ShortComplex.homologyMapIso
    (Q.isoSc' 1 0 (-1)
      ((ComplexShape.down ℤ).prev_eq' (by rfl))
      ((ComplexShape.down ℤ).next_eq' (by change (-1 : ℤ) + 1 = 0; norm_num))) ≪≫
    QHomologyData.homologyIso

private lemma QH0Iso_projection :
    Q.homologyπ 0 ≫ QH0Iso.hom = Q.iCycles 0 ≫ modTwo := by
  have hc := QHomologyData.cyclesIso_hom_comp_i
  change QHomologyData.cyclesIso.hom ≫ (𝟙 Z) = (Q.sc' 1 0 (-1)).iCycles at hc
  simp only [Category.comp_id] at hc
  change _ ≫ (ShortComplex.homologyMap _ ≫ QHomologyData.homologyIso.hom) = _
  rw [← Category.assoc, ShortComplex.homologyπ_naturality, Category.assoc,
    QHomologyData.homologyπ_comp_homologyIso_hom, hc]
  rw [ShortComplex.cyclesMap_i]
  change _ ≫ (𝟙 Z) ≫ modTwo = _
  simp only [Category.assoc, Category.id_comp]

private def oneCycle : Q.cycles 0 :=
  (Q.liftCycles (𝟙 Z) (-1)
    ((ComplexShape.down ℤ).next_eq' (by change (-1 : ℤ) + 1 = 0; norm_num))
    (by rw [Q_d_zero_negOne]; exact comp_zero)).hom 1

private lemma oneCycle_value : (Q.iCycles 0).hom oneCycle = 1 := by
  have h := congrArg (fun f => f.hom (1 : ℤ))
    (Q.liftCycles_i (𝟙 Z) (-1)
      ((ComplexShape.down ℤ).next_eq' (by change (-1 : ℤ) + 1 = 0; norm_num))
      (by rw [Q_d_zero_negOne]; exact comp_zero))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
    LinearMap.id_apply, oneCycle] using h

private lemma oneCycle_class_value : QH0Iso.hom.hom ((Q.homologyπ 0).hom oneCycle) = 1 := by
  have h := congrArg (fun f => f.hom oneCycle) QH0Iso_projection
  simpa [ModuleCat.hom_comp, LinearMap.comp_apply, oneCycle_value, modTwo] using h

private abbrev T := complex ℤ (zeroDifferentialComplex ℤ A) Q
private abbrev F := zeroDifferentialTensorHomologyFamily ℤ A Q (-1)
private def j : {pq : ℤ × ℤ // pq.1 + pq.2 = -1} := ⟨(-1, 0), by norm_num⟩

private lemma F_other_isZero (pq : {pq : ℤ × ℤ // pq.1 + pq.2 = -1}) (hpq : pq ≠ j) :
    IsZero (F pq) := by
  have hp : pq.val.1 ≠ -1 := by
    intro hp
    apply hpq
    apply Subtype.ext
    apply Prod.ext
    · exact hp
    · have h := pq.property
      change pq.val.2 = 0
      omega
  let G : ModuleCat.{0} ℤᵐᵒᵖ ⥤ AddCommGrpCat.{0} :=
    (ModuleCat.BalancedTensor.groupBifunctor ℤ).flip.obj (Q.homology pq.val.2)
  letI : G.Additive :=
    ⟨fun f g => congrArg (fun τ => τ.app (Q.homology pq.val.2))
      ((ModuleCat.BalancedTensor.groupBifunctor ℤ).map_add f g)⟩
  change IsZero (G.obj (A pq.val.1))
  apply G.map_isZero
  simpa only [A, if_neg hp] using (isZero_zero (ModuleCat.{0} ℤᵐᵒᵖ))

private def sourceIso : (∐ F) ≅ F j where
  hom := Sigma.desc (fun pq => if h : pq = j then eqToHom (congrArg F h) else 0)
  inv := Sigma.ι F j
  hom_inv_id := by
    apply Sigma.hom_ext
    intro pq
    by_cases hpq : pq = j
    · subst pq
      simp
    · exact (F_other_isZero pq hpq).eq_of_src _ _
  inv_hom_id := by simp

private def regularTensorIso (N : ModuleCat.{0} ℤ) :
    ((ModuleCat.BalancedTensor.groupBifunctor ℤ).obj regularRight).obj N ≅
      (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}).obj N := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ ℤ)
  let e := TensorProduct.Balanced.leftUnitor ℤ ℤ N
  exact
    { hom := AddCommGrpCat.ofHom e.toLinearMap.toAddMonoidHom
      inv := AddCommGrpCat.ofHom e.symm.toLinearMap.toAddMonoidHom
      hom_inv_id := by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro x
        exact e.symm_apply_apply x
      inv_hom_id := by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro x
        exact e.apply_symm_apply x }

private def totalHomologyIso : T.homology (-1) ≅ AddCommGrpCat.of (ZMod 2) :=
  (zeroDifferentialTensorHomologyIso ℤ A Q (-1)).symm ≪≫ sourceIso ≪≫
    regularTensorIso (Q.homology 0) ≪≫
      (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}).mapIso QH0Iso

private lemma total_generator :
    ∃ z : T.cycles (-1), totalHomologyIso.hom.hom ((T.homologyπ (-1)).hom z) = 1 := by
  obtain ⟨z, _, hz⟩ := zeroDifferentialTensorHomologyIso_mk ℤ A Q (-1) 0 (-1)
    (by norm_num) (1 : ℤ) oneCycle
  refine ⟨z, ?_⟩
  rw [← hz]
  change (Sigma.ι F j ≫ (zeroDifferentialTensorHomologyIso ℤ A Q (-1)).hom ≫
      totalHomologyIso.hom).hom
        (TensorProduct.Balanced.mk ℤ ℤ ℤ (Q.homology 0) 1
          ((Q.homologyπ 0).hom oneCycle)) = 1
  simp only [totalHomologyIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc, sourceIso, Sigma.ι_desc_assoc, dif_pos rfl,
    eqToHom_refl, Category.id_comp]
  change QH0Iso.hom.hom
    ((TensorProduct.Balanced.leftUnitor ℤ ℤ (Q.homology 0))
      (TensorProduct.Balanced.mk ℤ ℤ ℤ (Q.homology 0) 1
        ((Q.homologyπ 0).hom oneCycle))) = 1
  rw [TensorProduct.Balanced.leftUnitor_mk, one_smul]
  exact oneCycle_class_value

example : Q.X 1 = Z ∧ Q.X 0 = Z := by simp [Q, X]

example (i : ℤ) (h0 : i ≠ 0) (h1 : i ≠ 1) : IsZero (Q.X i) := by
  simpa only [Q, X, or_false, h0, h1, if_false] using isZero_zero (ModuleCat.{0} ℤ)

example : (Q.d 1 0).hom (1 : ℤ) = 2 := by
  rw [Q_d_one_zero]
  simp [two, smul_eq_mul]

example : (T.d 0 (-1)).hom (mk ℤ (zeroDifferentialComplex ℤ A) Q (-1) 1 0
      (by norm_num) (1 : ℤ) (1 : ℤ)) =
    (-2 : ℤ) • mk ℤ (zeroDifferentialComplex ℤ A) Q (-1) 0 (-1)
      (by norm_num) (1 : ℤ) (1 : ℤ) := by
  rw [d_mk]
  simp only [zeroDifferentialComplex, HomologicalComplex.zeroDifferentialFunctor_obj_d,
    ModuleCat.hom_zero, LinearMap.zero_apply, mk, LinearMap.map_zero,
    LinearMap.zero_apply, map_zero, zero_add, Q_d_one_zero, two,
    ModuleCat.hom_ofHom, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.map_smul, map_zsmul]
  change (-1 : ℤ) • ((2 : ℤ) • _) = (-2 : ℤ) • _
  rw [smul_smul]
  norm_num

example : Nonempty (T.homology (-1) ≅ AddCommGrpCat.of (ZMod 2)) := ⟨totalHomologyIso⟩

example : ∃ z : T.cycles (-1), totalHomologyIso.hom.hom ((T.homologyπ (-1)).hom z) = 1 :=
  total_generator

example : ∃ z : T.cycles (-1), (T.homologyπ (-1)).hom z ≠ 0 := by
  obtain ⟨z, hz⟩ := total_generator
  refine ⟨z, ?_⟩
  intro hzero
  rw [hzero, map_zero] at hz
  exact zero_ne_one hz

end MathlibExtTest.BalancedTensorZeroDifferentialHomology
