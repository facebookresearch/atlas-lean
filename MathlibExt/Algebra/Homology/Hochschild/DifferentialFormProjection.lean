/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricCoefficients
public import MathlibExt.LinearAlgebra.ExteriorPower.BaseChange
public import Mathlib.RingTheory.Kaehler.Basic
public import MathlibExt.Algebra.Homology.ZeroDifferentialHomology

/-!
# Projection to coefficient differential forms

For a commutative k-algebra A and a symmetric coefficient module M,
the word m ⊗ a₁ ⊗ ⋯ ⊗ aₙ maps to m ⊗ (da₁ ∧ ⋯ ∧ daₙ).
The Hochschild boundary maps to zero, giving a chain map to the
zero-differential complex of coefficient forms. This construction
requires neither smoothness nor a polynomial presentation.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]

local notation "Ω" => KaehlerDifferential k A

/-- The alternating ground-linear word of universal differentials. -/
def differentialWord (n : ℕ) : A [⋀^Fin n]→ₗ[k] (⋀[A]^n Ω) :=
  ((exteriorPower.ιMulti A n).restrictScalars (R := k)).compLinearMap
    (KaehlerDifferential.D k A).toLinearMap

/-- The original pure input gives the exterior differential word. -/
theorem differentialWord_apply (n : ℕ) (a : Fin n → A) :
    differentialWord k A n a =
      exteriorPower.ιMulti A n (fun j => KaehlerDifferential.D k A (a j)) := rfl

/-- The tensor universal map to the original differential-form tail. -/
def differentialTailProjection (n : ℕ) : TensorPower k n A →ₗ[k] (⋀[A]^n Ω) :=
  PiTensorProduct.lift (differentialWord k A n).toMultilinearMap

/-- An original pure tensor maps to the wedge of its universal differentials. -/
theorem differentialTailProjection_tprod (n : ℕ) (a : Fin n → A) :
    differentialTailProjection k A n (PiTensorProduct.tprod k a) =
      exteriorPower.ιMulti A n (fun j => KaehlerDifferential.D k A (a j)) := by
  rw [differentialTailProjection, PiTensorProduct.lift.tprod]
  exact differentialWord_apply k A n a

variable (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- The original coefficient and tensor tail pair bilinearly into coefficient forms. -/
def coefficientFormPair (n : ℕ) :
    M →ₗ[k] TensorPower k n A →ₗ[k] M ⊗[A] (⋀[A]^n Ω) where
  toFun m := ((TensorProduct.mk A M (⋀[A]^n Ω) m).restrictScalars k).comp
    (differentialTailProjection k A n)
  map_add' m m' := by
    ext x
    exact TensorProduct.add_tmul _ _ _
  map_smul' c m := by
    ext x
    exact (TensorProduct.smul_tmul' c m _).symm

/-- The original coefficient-first tensor projection to differential forms. -/
def coefficientFormProjection (n : ℕ) :
    M ⊗[k] TensorPower k n A →ₗ[k] M ⊗[A] (⋀[A]^n Ω) :=
  TensorProduct.lift (coefficientFormPair k A M n)

omit [SMulCommClass k A M] in
/-- The projection retains the original coefficient and ordered differential word. -/
theorem coefficientFormProjection_tprod (n : ℕ) (m : M) (a : Fin n → A) :
    coefficientFormProjection k A M n (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      m ⊗ₜ[A] exteriorPower.ιMulti A n (fun j => KaehlerDifferential.D k A (a j)) := by
  rw [coefficientFormProjection, TensorProduct.lift.tmul]
  change m ⊗ₜ[A] differentialTailProjection k A n (PiTensorProduct.tprod k a) = _
  rw [differentialTailProjection_tprod]

variable {A}

private theorem mulAdjacent_delete_of_ne {n : ℕ} (i j : Fin n)
    (a : Fin (n + 1) → A) (hj : j ≠ i) :
    hochschildMulAdjacent i a j = a (i.castSucc.succAbove j) := by
  rw [hochschildMulAdjacent, if_neg hj]
  rcases lt_or_gt_of_ne hj with h | h
  · rw [Fin.succAbove_succ_of_le i j (le_of_lt h),
      Fin.succAbove_of_castSucc_lt i.castSucc j
        (by simpa only [Fin.lt_def, Fin.val_castSucc] using h)]
  · rw [Fin.succAbove_succ_of_lt i j h,
      Fin.succAbove_of_le_castSucc i.castSucc j
        (by simpa only [Fin.le_def, Fin.val_castSucc] using le_of_lt h)]

omit [CommRing A] in
private theorem delete_succ_update {n : ℕ} (i : Fin n) (a : Fin (n + 1) → A) :
    a ∘ i.succ.succAbove =
      Function.update (a ∘ i.castSucc.succAbove) i (a i.castSucc) := by
  classical
  ext j
  by_cases hj : j = i
  · subst j
    simp only [Function.comp_apply, Function.update_self]
    have hi : i.castSucc < i.succ := Fin.castSucc_lt_succ
    rw [Fin.succAbove_of_castSucc_lt i.succ i hi]
  · simp only [Function.comp_apply, Function.update_of_ne hj]
    rcases lt_or_gt_of_ne hj with h | h
    · have hji : j.val < i.val := h
      have hjs : j.castSucc < i.succ := by change j.val < i.val + 1; omega
      rw [Fin.succAbove_of_castSucc_lt i.succ j hjs,
        Fin.succAbove_of_castSucc_lt i.castSucc j
          (by simpa only [Fin.lt_def, Fin.val_castSucc] using h)]
    · have hij : i.val < j.val := h
      have his : i.succ ≤ j.castSucc := by change i.val + 1 ≤ j.val; omega
      rw [Fin.succAbove_of_le_castSucc i.succ j his,
        Fin.succAbove_of_le_castSucc i.castSucc j
          (by simpa only [Fin.le_def, Fin.val_castSucc] using le_of_lt h)]

private theorem differential_mulAdjacent_update {n : ℕ}
    (i : Fin n) (a : Fin (n + 1) → A) :
    (fun j => KaehlerDifferential.D k A (hochschildMulAdjacent i a j)) =
      Function.update (fun j => KaehlerDifferential.D k A (a (i.castSucc.succAbove j))) i
        (a i.castSucc • KaehlerDifferential.D k A (a i.succ) +
          a i.succ • KaehlerDifferential.D k A (a i.castSucc)) := by
  classical
  ext j
  by_cases hj : j = i
  · subst j
    rw [hochschildMulAdjacent, if_pos rfl, Derivation.leibniz, Function.update_self]
  · rw [mulAdjacent_delete_of_ne i j a hj, Function.update_of_ne hj]

variable (A)

/-- The merged differential word is the sum of its two original deletion words
with the coefficients required by the differential Leibniz rule. -/
theorem differentialWord_mulAdjacent (n : ℕ) (i : Fin n) (a : Fin (n + 1) → A) :
    differentialWord k A n (hochschildMulAdjacent i a) =
      a i.castSucc • differentialWord k A n (a ∘ i.castSucc.succAbove) +
        a i.succ • differentialWord k A n (a ∘ i.succ.succAbove) := by
  classical
  rw [differentialWord_apply, differential_mulAdjacent_update]
  let e : MultilinearMap A (fun _ : Fin n => Ω) (⋀[A]^n Ω) :=
    (exteriorPower.ιMulti A n).toMultilinearMap
  let v : Fin n → KaehlerDifferential k A := fun j => KaehlerDifferential.D k A (a (i.castSucc.succAbove j))
  let x := KaehlerDifferential.D k A (a i.succ)
  let y := KaehlerDifferential.D k A (a i.castSucc)
  have hExpand : e (Function.update v i (a i.castSucc • x + a i.succ • y)) =
      a i.castSucc • e (Function.update v i x) + a i.succ • e (Function.update v i y) :=
    (e.map_update_add v i (a i.castSucc • x) (a i.succ • y)).trans
      (congrArg₂ (fun x y : ⋀[A]^n Ω => x + y)
        (e.map_update_smul v i (a i.castSucc) x) (e.map_update_smul v i (a i.succ) y))
  have hfirst : Function.update
      (fun j => KaehlerDifferential.D k A (a (i.castSucc.succAbove j))) i
        (KaehlerDifferential.D k A (a i.succ)) =
      fun j => KaehlerDifferential.D k A (a (i.castSucc.succAbove j)) := by
    ext j
    by_cases hj : j = i
    · subst j
      rw [Function.update_self, Fin.succAbove_of_le_castSucc i.castSucc i le_rfl]
    · rw [Function.update_of_ne hj]
  have hsecond : Function.update
      (fun j => KaehlerDifferential.D k A (a (i.castSucc.succAbove j))) i
        (KaehlerDifferential.D k A (a i.castSucc)) =
      fun j => KaehlerDifferential.D k A (a (i.succ.succAbove j)) := by
    change Function.update
      ((KaehlerDifferential.D k A) ∘ (a ∘ i.castSucc.succAbove)) i
        (KaehlerDifferential.D k A (a i.castSucc)) =
      (KaehlerDifferential.D k A) ∘ (a ∘ i.succ.succAbove)
    rw [delete_succ_update, Function.comp_update]
  have he₁ := congrArg e hfirst
  have he₂ := congrArg e hsecond
  have hd := hExpand.trans (congrArg₂ (fun x y : ⋀[A]^n Ω => x + y)
    (congrArg (fun x => a i.castSucc • x) he₁) (congrArg (fun y => a i.succ • y) he₂))
  simp only [differentialWord_apply] at ⊢
  exact hd

omit [SMulCommClass k A M] in
/-- The original coefficient merged tensor has its two adjacent deletion terms. -/
theorem coefficientFormProjection_mulAdjacent
    (n : ℕ) (i : Fin n) (m : M) (a : Fin (n + 1) → A) :
    coefficientFormProjection k A M n
      (m ⊗ₜ[k] PiTensorProduct.tprod k (hochschildMulAdjacent i a)) =
      (a i.castSucc • m) ⊗ₜ[A] differentialWord k A n (a ∘ i.castSucc.succAbove) +
        (a i.succ • m) ⊗ₜ[A] differentialWord k A n (a ∘ i.succ.succAbove) := by
  rw [coefficientFormProjection_tprod]
  change m ⊗ₜ[A] differentialWord k A n (hochschildMulAdjacent i a) = _
  rw [differentialWord_mulAdjacent, TensorProduct.tmul_add,
    TensorProduct.tmul_smul, TensorProduct.tmul_smul]
  exact congrArg₂ (fun x y : M ⊗[A] (⋀[A]^n Ω) => x + y)
    (TensorProduct.smul_tmul' (a i.castSucc) m (differentialWord k A n (a ∘ i.castSucc.succAbove)))
    (TensorProduct.smul_tmul' (a i.succ) m (differentialWord k A n (a ∘ i.succ.succAbove)))

private theorem alternating_adjacent_telescope {T : Type*} [AddCommGroup T]
    (n : ℕ) (f : Fin (n + 1) → T) :
    f 0 + (∑ i : Fin n, (-1 : ℤ) ^ (i.val + 1) • (f i.castSucc + f i.succ)) +
      (-1 : ℤ) ^ (n + 1) • f (Fin.last n) = 0 := by
  let g : Fin (n + 1) → T := fun i => (-1 : ℤ) ^ i.val • f i
  have hs (j : ℕ) (t : T) : (-1 : ℤ) ^ (j + 1) • t = -((-1 : ℤ) ^ j • t) := by
    rw [pow_succ, mul_smul, neg_one_smul, smul_neg]
  have htotal : g 0 + (∑ i : Fin n, g i.succ) =
      (∑ i : Fin n, g i.castSucc) + g (Fin.last n) :=
    (Fin.sum_univ_succ g).symm.trans (Fin.sum_univ_castSucc g)
  have hends : g 0 + (∑ i : Fin n, (g i.succ - g i.castSucc)) - g (Fin.last n) = 0 := by
    rw [Finset.sum_sub_distrib, ← add_sub_assoc, htotal, add_sub_cancel_left, sub_self]
  have hmid (i : Fin n) : (-1 : ℤ) ^ (i.val + 1) • (f i.castSucc + f i.succ) =
      g i.succ - g i.castSucc := by
    calc
     _ = (-1 : ℤ) ^ (i.val + 1) • f i.castSucc + (-1 : ℤ) ^ (i.val + 1) • f i.succ := smul_add _ _ _
     _ = -((-1 : ℤ) ^ i.val • f i.castSucc) + (-1 : ℤ) ^ (i.val + 1) • f i.succ :=
        congrArg (fun z : T => z + (-1 : ℤ) ^ (i.val + 1) • f i.succ) (hs i.val (f i.castSucc))
     _ = _ := by
        dsimp only [g]
        simp only [Fin.val_succ, Fin.val_castSucc]
        abel
  have h0 : f 0 = g 0 := by simp only [g, Fin.val_zero, pow_zero, one_smul]
  have hsum : (∑ i : Fin n, (-1 : ℤ) ^ (i.val + 1) • (f i.castSucc + f i.succ)) =
      ∑ i : Fin n, (g i.succ - g i.castSucc) := Finset.sum_congr rfl (fun i _ => hmid i)
  have hlast : (-1 : ℤ) ^ (n + 1) • f (Fin.last n) = -g (Fin.last n) := hs n (f (Fin.last n))
  calc
    _ = (g 0 + (∑ i : Fin n, (g i.succ - g i.castSucc))) + -g (Fin.last n) :=
      congrArg₂ (fun x y : T => x + y) (congrArg₂ (fun x y : T => x + y) h0 hsum) hlast
    _ = g 0 + (∑ i : Fin n, (g i.succ - g i.castSucc)) - g (Fin.last n) := (sub_eq_add_neg _ _).symm
    _ = 0 := hends

omit [CommRing A] in
private theorem dropFirst_eq_delete_zero (n : ℕ) (a : Fin (n + 1) → A) :
    hochschildDropFirst a = a ∘ (0 : Fin (n + 1)).succAbove := by
  ext j
  rw [Function.comp_apply, Fin.succAbove_of_le_castSucc 0 j (Fin.zero_le _)]
  rfl

omit [CommRing A] in
private theorem dropLast_eq_delete_last (n : ℕ) (a : Fin (n + 1) → A) :
    hochschildDropLast a = a ∘ (Fin.last n).succAbove := by
  ext j
  rw [Function.comp_apply, Fin.succAbove_of_castSucc_lt (Fin.last n) j
    (by simpa only [Fin.lt_def, Fin.val_last, Fin.val_castSucc] using j.isLt)]
  rfl

/-- The full original symmetric Hochschild boundary is killed by the coefficient differential-form projection in every degree. -/
theorem coefficientFormProjection_boundary (n : ℕ) :
    (coefficientFormProjection k A M n).comp ((chainComplex k A M).d (n + 1) n).hom = 0 := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  let d : M ⊗[k] TensorPower k (n + 1) A →ₗ[k] M ⊗[k] TensorPower k n A :=
    ((chainComplex k A M).d (n + 1) n).hom
  change (coefficientFormProjection k A M n).comp d = 0
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  change coefficientFormProjection k A M n (d (m ⊗ₜ[k] PiTensorProduct.tprod k a)) = 0
  have hd : d (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • faceValue k A M n i m a := by
    have h := congrArg
      (fun f : ModuleCat.Algebra.Hochschild.chainLevel k A M (n + 1) ⟶
        ModuleCat.Algebra.Hochschild.chainLevel k A M n =>
          f.hom (m ⊗ₜ[k] PiTensorProduct.tprod k a))
      (ModuleCat.Algebra.Hochschild.chainComplex_d k A M n)
    exact h.trans (ModuleCat.Algebra.Hochschild.boundary_tprod k A M n m a)
  rw [hd, map_sum]
  simp only [map_zsmul]
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [faceValue, Fin.cases_zero, Fin.cases_succ, Fin.lastCases_castSucc,
    Fin.lastCases_last, Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last,
    pow_zero, one_smul, opModule_smul, MulOpposite.unop_op,
    dropFirst_eq_delete_zero, dropLast_eq_delete_last]
  simp only [coefficientFormProjection_mulAdjacent]
  simp only [coefficientFormProjection_tprod]
  simpa only [differentialWord_apply, add_assoc] using
    (alternating_adjacent_telescope n (fun i =>
      (a i • m) ⊗ₜ[A] differentialWord k A n (a ∘ i.succAbove)))

/-- The original coefficient differential-form complex has zero differentials. -/
def coefficientDifferentialFormComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of k (ULift.{u} (M ⊗[A] (⋀[A]^n Ω))))
    (fun _ => 0) (by intro n; simp only [CategoryTheory.Limits.zero_comp])

omit [SMulCommClass k A M] in
/-- Every differential of the form complex is zero, also off the successor shape. -/
theorem coefficientDifferentialFormComplex_d_eq_zero (i j : ℕ) :
    (coefficientDifferentialFormComplex k A M).d i j = 0 := by
  by_cases h : (ComplexShape.down ℕ).Rel i j
  · change j + 1 = i at h
    subst i
    exact ChainComplex.of_d
      (fun n => ModuleCat.of k (ULift.{u} (M ⊗[A] (⋀[A]^n Ω)))) (fun _ => 0) j
  · exact (coefficientDifferentialFormComplex k A M).shape i j h

/-- The original tensor projection is a chain map, with no desired boundary law input. -/
def coefficientDifferentialFormChainMap : chainComplex k A M ⟶ coefficientDifferentialFormComplex k A M :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom
    ((ULift.moduleEquiv : ULift.{u} (M ⊗[A] (⋀[A]^n Ω)) ≃ₗ[k] M ⊗[A] (⋀[A]^n Ω)).symm.toLinearMap.comp
      (coefficientFormProjection k A M n))) (by
    intro n
    change ModuleCat.ofHom
      ((ULift.moduleEquiv : ULift.{u} (M ⊗[A] (⋀[A]^(n + 1) Ω)) ≃ₗ[k]
        M ⊗[A] (⋀[A]^(n + 1) Ω)).symm.toLinearMap.comp (coefficientFormProjection k A M (n + 1))) ≫
      (coefficientDifferentialFormComplex k A M).d (n + 1) n =
      (chainComplex k A M).d (n + 1) n ≫ ModuleCat.ofHom
        ((ULift.moduleEquiv : ULift.{u} (M ⊗[A] (⋀[A]^n Ω)) ≃ₗ[k] M ⊗[A] (⋀[A]^n Ω)).symm.toLinearMap.comp
          (coefficientFormProjection k A M n))
    erw [coefficientDifferentialFormComplex_d_eq_zero, CategoryTheory.Limits.comp_zero]
    apply ModuleCat.hom_ext
    have h := coefficientFormProjection_boundary k A M n
    have hp := congrArg (fun f =>
      (ULift.moduleEquiv : ULift.{u} (M ⊗[A] (⋀[A]^n Ω)) ≃ₗ[k] M ⊗[A] (⋀[A]^n Ω)).symm.toLinearMap.comp f) h
    simp only [LinearMap.comp_assoc, LinearMap.comp_zero] at hp
    exact hp.symm)

/-- The chain projection retains the coefficient and universal differential word. -/
theorem coefficientDifferentialFormChainMap_tprod
    (n : ℕ) (m : M) (a : Fin n → A) :
    ((coefficientDifferentialFormChainMap k A M).f n).hom
      (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      ULift.up (m ⊗ₜ[A] exteriorPower.ιMulti A n
        (fun j => KaehlerDifferential.D k A (a j))) :=
  congrArg ULift.up (coefficientFormProjection_tprod k A M n m a)

/-- Removing the canonical whole-module lift recovers the original coefficient differential word. -/
theorem coefficientDifferentialFormChainMap_tprod_down
    (n : ℕ) (m : M) (a : Fin n → A) :
    (((coefficientDifferentialFormChainMap k A M).f n).hom
      (m ⊗ₜ[k] PiTensorProduct.tprod k a)).down =
        m ⊗ₜ[A] exteriorPower.ιMulti A n (fun j => KaehlerDifferential.D k A (a j)) :=
  congrArg ULift.down (coefficientDifferentialFormChainMap_tprod k A M n m a)

/-- The induced Hochschild homology map to original coefficient differential forms. -/
def coefficientDifferentialFormHomologyMap (n : ℕ) :
    (chainComplex k A M).homology n ⟶ ModuleCat.of k (ULift.{u} (M ⊗[A] (⋀[A]^n Ω))) :=
  HomologicalComplex.homologyMap (coefficientDifferentialFormChainMap k A M) n ≫
    (HomologicalComplex.zeroDifferentialHomologyIso (coefficientDifferentialFormComplex k A M) n
      (coefficientDifferentialFormComplex_d_eq_zero k A M)).hom

/-- The raw ground-linear map uses the original form carrier after canonical lift removal. -/
def coefficientDifferentialFormHomologyLinearMap (n : ℕ) :
    (chainComplex k A M).homology n →ₗ[k] M ⊗[A] (⋀[A]^n Ω) :=
  (ULift.moduleEquiv : ULift.{u} (M ⊗[A] (⋀[A]^n Ω)) ≃ₗ[k] M ⊗[A] (⋀[A]^n Ω)).toLinearMap.comp
    (coefficientDifferentialFormHomologyMap k A M n).hom

end ModuleCat.Algebra.Hochschild.Symmetric
