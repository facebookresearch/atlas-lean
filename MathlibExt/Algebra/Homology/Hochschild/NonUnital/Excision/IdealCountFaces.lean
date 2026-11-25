/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.WordFiltration

/-!
# Hochschild faces on ideal-count stages

Regular nonunital faces preserve the ideal-count
stages in first-factor tensor coordinates. The
last face uses the last-to-first rotation and
its ordered product. Quotient-kernel pullback
retains the original Hochschild boundary.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex
open scoped TensorProduct NonUnitalSubalgebra.Quotient

universe u v

namespace ModuleCat.Algebra.Hochschild.NonUnital

open ModuleCat.Algebra.Hochschild

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (I : NonUnitalSubalgebra k A) [I.IsTwoSided]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Reindexing the original entries does not change how many lie in the ideal. -/
theorem idealEntryCount_reindex {n : ℕ} (e : Equiv.Perm (Fin n)) (a : Fin n → A) :
    idealEntryCount k A I (fun i => a (e i)) = idealEntryCount k A I a := by
  classical
  unfold idealEntryCount
  refine Finset.card_bij (fun i _ => e i) ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ hij
    exact e.injective hij
  · intro j hj
    refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [e.apply_symm_apply] using (Finset.mem_filter.mp hj).2

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- The original last-to-first face loses at most one original ideal entry. -/
theorem idealEntryCount_mulCyclicLast {n : ℕ} (a : Fin (n + 2) → A) :
    idealEntryCount k A I a - 1 ≤
      idealEntryCount k A I
        (hochschildMulAdjacent (0 : Fin (n + 1))
          (fun i => a ((finRotate (n + 2)).symm i))) := by
  rw [← idealEntryCount_reindex k A I (finRotate (n + 2)).symm a]
  exact idealEntryCount_mulAdjacent k A I 0 _

/-- The regular face in the original full tensor-word coordinates. -/
def regularWordFace (n : ℕ) (i : Fin (n + 2)) :
    TensorPower k (n + 2) A →ₗ[k] TensorPower k (n + 1) A :=
  (TensorPower.consEquiv k A n).toLinearMap.comp
    ((regularFace k A n i).hom.comp
      (TensorPower.consEquiv k A (n + 1)).symm.toLinearMap)

/-- Every non-wrapping face is the original adjacent product, including the coefficient face. -/
theorem regularWordFace_castSucc_tprod (n : ℕ) (i : Fin (n + 1))
    (a : Fin (n + 2) → A) :
    regularWordFace k A n i.castSucc (PiTensorProduct.tprod k a) =
      PiTensorProduct.tprod k (hochschildMulAdjacent i a) := by
  change TensorPower.consEquiv k A n
      ((regularFace k A n i.castSucc).hom
        ((TensorPower.consEquiv k A (n + 1)).symm (PiTensorProduct.tprod k a))) = _
  rw [TensorPower.consEquiv_symm_tprod]
  simpa only [Fin.cons_self_tail] using
    regularFace_cons_tprod k A n i (a 0) (Fin.tail a)

/-- The wrapping face rotates the original last entry first and multiplies it on the left. -/
theorem regularWordFace_last_tprod (n : ℕ) (a : Fin (n + 2) → A) :
    regularWordFace k A n (Fin.last (n + 1)) (PiTensorProduct.tprod k a) =
      PiTensorProduct.tprod k
        (hochschildMulAdjacent (0 : Fin (n + 1))
          (fun i => a ((finRotate (n + 2)).symm i))) := by
  have hrotate : (fun i : Fin (n + 2) => a ((finRotate (n + 2)).symm i)) =
      Fin.cons (a (Fin.last (n + 1))) (Fin.init a) := by
    simpa only [Fin.snoc_init_self] using
      rotate_snoc (n + 1) (Fin.init a) (a (Fin.last (n + 1)))
  change TensorPower.consEquiv k A n
      ((regularFace k A n (Fin.last (n + 1))).hom
        ((TensorPower.consEquiv k A (n + 1)).symm (PiTensorProduct.tprod k a))) = _
  rw [TensorPower.consEquiv_symm_tprod, regularFace_last_tprod,
    TensorPower.consEquiv_tmul, hrotate, mulAdjacent_cons_zero]
  apply congrArg (PiTensorProduct.tprod k)
  funext j
  cases j using Fin.cases <;> rfl

/-- Every regular face sends an ideal-word stage to the stage with one fewer required entry. -/
theorem idealWordSpan_regularWordFace (n required : ℕ) (i : Fin (n + 2)) :
    (idealWordSpan k A I (n + 2) required).map (regularWordFace k A n i) ≤
      idealWordSpan k A I (n + 1) (required - 1) := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ha, rfl⟩
  change regularWordFace k A n i (PiTensorProduct.tprod k a) ∈
    idealWordSpan k A I (n + 1) (required - 1)
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [regularWordFace_last_tprod]
    apply Submodule.subset_span
    refine ⟨_, ?_, rfl⟩
    have hcount := idealEntryCount_mulCyclicLast k A I a
    omega
  · rw [regularWordFace_castSucc_tprod]
    apply Submodule.subset_span
    refine ⟨_, ?_, rfl⟩
    have hcount := idealEntryCount_mulAdjacent k A I j a
    omega

/-- The original full boundary through the original tensor coordinates. -/
def regularWordBoundary (n : ℕ) :
    TensorPower k (n + 2) A →ₗ[k] TensorPower k (n + 1) A :=
  (TensorPower.consEquiv k A n).toLinearMap.comp
    (((bComplex k A).d (n + 1) n).hom.comp
      (TensorPower.consEquiv k A (n + 1)).symm.toLinearMap)

/-- The full original boundary retains all faces and their integer signs. -/
theorem regularWordBoundary_eq_sum (n : ℕ) :
    regularWordBoundary k A n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • regularWordFace k A n i := by
  unfold regularWordBoundary regularWordFace
  rw [bComplex_d]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  exact (map_zsmul
    (LinearMap.applyₗ (R := k) (M := TensorPower k (n + 2) A)
      (M₂ := TensorPower k (n + 1) A) x)
    ((-1 : ℤ) ^ i.val)
    ((TensorPower.consEquiv k A n).toLinearMap.comp
      ((regularFace k A n i).hom.comp
        (TensorPower.consEquiv k A (n + 1)).symm.toLinearMap))).symm

/-- The signed boundary preserves the original ideal-count thresholds. -/
theorem idealWordSpan_regularWordBoundary (n required : ℕ) :
    (idealWordSpan k A I (n + 2) required).map (regularWordBoundary k A n) ≤
      idealWordSpan k A I (n + 1) (required - 1) := by
  classical
  rw [Submodule.map_le_iff_le_comap]
  intro x hx
  change regularWordBoundary k A n x ∈ idealWordSpan k A I (n + 1) (required - 1)
  rw [regularWordBoundary_eq_sum, LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro i _
  have heval : (((-1 : ℤ) ^ i.val) • regularWordFace k A n i) x =
      ((-1 : ℤ) ^ i.val) • regularWordFace k A n i x :=
    map_zsmul
      (LinearMap.applyₗ (R := k) (M := TensorPower k (n + 2) A)
        (M₂ := TensorPower k (n + 1) A) x)
      ((-1 : ℤ) ^ i.val) (regularWordFace k A n i)
  rw [heval]
  exact (idealWordSpan k A I (n + 1) (required - 1)).toAddSubgroup.zsmul_mem
    ((Submodule.map_le_iff_le_comap.mp
      (idealWordSpan_regularWordFace k A I n required i)) hx) ((-1 : ℤ) ^ i.val)

/-- The original kernel-word map commutes with the full Hochschild boundary. -/
theorem relativeNaiveWordMap_d (n : ℕ) (x : (relativeNaiveComplex k A I).X (n + 1)) :
    relativeNaiveWordMap k A I n (((relativeNaiveComplex k A I).d (n + 1) n).hom x) =
      regularWordBoundary k A n (relativeNaiveWordMap k A I (n + 1) x) := by
  have hcomm := (kernel.ι (cyclicBComplexHom I.quotientMap)).comm (n + 1) n
  have hvalue := congrArg
    (fun f : (relativeNaiveComplex k A I).X (n + 1) ⟶ (bComplex k A).X n => f.hom x) hcomm
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hvalue
  change TensorPower.consEquiv k A n
      (((kernel.ι (cyclicBComplexHom I.quotientMap)).f n).hom
        (((relativeNaiveComplex k A I).d (n + 1) n).hom x)) =
    TensorPower.consEquiv k A n
      (((bComplex k A).d (n + 1) n).hom
        ((TensorPower.consEquiv k A (n + 1)).symm
          (TensorPower.consEquiv k A (n + 1)
            (((kernel.ι (cyclicBComplexHom I.quotientMap)).f (n + 1)).hom x))))
  rw [LinearEquiv.symm_apply_apply]
  exact congrArg (TensorPower.consEquiv k A n) hvalue.symm

/-- Every original ideal-count stage of the relative naive complex is closed under its boundary. -/
theorem naiveWordFiltration_d (p n : ℕ) :
    (naiveWordFiltration k A I p (n + 1)).map
        ((relativeNaiveComplex k A I).d (n + 1) n).hom ≤
      naiveWordFiltration k A I p n := by
  rw [Submodule.map_le_iff_le_comap]
  intro x hx
  change relativeNaiveWordMap k A I (n + 1) x ∈
    idealWordSpan k A I (n + 2) (n + 2 - p) at hx
  change relativeNaiveWordMap k A I n
    (((relativeNaiveComplex k A I).d (n + 1) n).hom x) ∈
      idealWordSpan k A I (n + 1) (n + 1 - p)
  rw [relativeNaiveWordMap_d]
  have h := (Submodule.map_le_iff_le_comap.mp
    (idealWordSpan_regularWordBoundary k A I n (n + 2 - p))) hx
  change regularWordBoundary k A n (relativeNaiveWordMap k A I (n + 1) x) ∈
    idealWordSpan k A I (n + 1) (n + 2 - p - 1) at h
  have hthreshold : n + 2 - p - 1 = n + 1 - p := by omega
  simpa only [hthreshold] using h

end ModuleCat.Algebra.Hochschild.NonUnital
