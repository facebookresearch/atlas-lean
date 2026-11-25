/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.UnitizationRelative
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# The two original word coordinates in reduced unitization normalization

The even coordinate retains an original word in A. The odd coordinate
inserts the external unit before that same word. The b-prime contraction of the unital unitization and the last-face
decomposition give precisely b, 1-t and -b-prime on these coordinates.
The algebra A itself is not assumed to have a unit.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex
open scoped TensorProduct

universe u v

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The original ideal inclusion acts on the coefficient and every original tensor factor. -/
def unitizationRegularInclusion : bComplex k A ⟶ bComplex k (Unitization k A) :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom
    (TensorPower.consLevelMap (Unitization.inrHom k k A) n)) (fun n => by
      apply ModuleCat.hom_ext
      exact (bComplex_d_natural (Unitization.inrNonUnitalAlgHom k A) n).symm)

/-- The even word is the original ideal word followed by the quotient projection. -/
def unitizationEvenWord (n : ℕ) :
    chainLevel k A A n ⟶ (normalizedBComplex k (Unitization k A)).X n :=
  (unitizationRegularInclusion k A).f n ≫ (normalizedProjection k (Unitization k A)).f n

/-- The odd word inserts the external unit before the original ideal word. -/
def unitizationOddWord (n : ℕ) :
    chainLevel k A A n ⟶ (normalizedBComplex k (Unitization k A)).X (n + 1) :=
  (unitizationRegularInclusion k A).f n ≫
    extraDegeneracyWith k (Unitization k A) 1 n ≫
      (normalizedProjection k (Unitization k A)).f (n + 1)

/-- The even coordinate keeps the original nonunital coefficient and every original factor. -/
theorem unitizationEvenWord_tprod (n : ℕ) (m : A) (a : Fin n → A) :
    (unitizationEvenWord k A n).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      Unitization.inr m ⊗ₜ[k] PiTensorProduct.tprod k
        (fun i => originalToUnitizationQuotient k A (a i)) := by
  change ((normalizedProjection k (Unitization k A)).f n).hom
    (((unitizationRegularInclusion k A).f n).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a)) = _
  rw [normalizedProjection_f]
  change (ModuleCat.Algebra.Hochschild.normalizationLevelMap k (Unitization k A)
    (Unitization k A) n).hom
      (TensorPower.consLevelMap (Unitization.inrHom k k A) n
        (m ⊗ₜ[k] PiTensorProduct.tprod k a)) = _
  simp only [TensorPower.consLevelMap, TensorProduct.map_tmul, PiTensorProduct.map_tprod]
  erw [ModuleCat.Algebra.Hochschild.normalizationLevelMap_tmul_tprod]
  rfl

/-- The odd coordinate keeps the unit and original word, including its old coefficient. -/
theorem unitizationOddWord_tprod (n : ℕ) (m : A) (a : Fin n → A) :
    (unitizationOddWord k A n).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      (1 : Unitization k A) ⊗ₜ[k] PiTensorProduct.tprod k
        (fun i : Fin (n + 1) => originalToUnitizationQuotient k A
          ((Fin.cons m a : Fin (n + 1) → A) i)) := by
  change ((normalizedProjection k (Unitization k A)).f (n + 1)).hom
    ((extraDegeneracyWith k (Unitization k A) 1 n).hom
      (((unitizationRegularInclusion k A).f n).hom
        (m ⊗ₜ[k] PiTensorProduct.tprod k a))) = _
  rw [normalizedProjection_f]
  change (ModuleCat.Algebra.Hochschild.normalizationLevelMap k (Unitization k A)
    (Unitization k A) (n + 1)).hom
      ((extraDegeneracyWith k (Unitization k A) 1 n).hom
        (TensorPower.consLevelMap (Unitization.inrHom k k A) n
          (m ⊗ₜ[k] PiTensorProduct.tprod k a))) = _
  simp only [TensorPower.consLevelMap, TensorProduct.map_tmul, PiTensorProduct.map_tprod]
  erw [extraDegeneracyWith_tprod,
    ModuleCat.Algebra.Hochschild.normalizationLevelMap_tmul_tprod]
  congr 2
  funext i
  cases i using Fin.cases <;> rfl

/-- The scalar projector has zero quotient-tail map. -/
theorem unitizationScalarProjector_quotient_zero :
    (ModuleCat.Algebra.Hochschild.unitSubmodule k (Unitization k A)).mapQ
        (ModuleCat.Algebra.Hochschild.unitSubmodule k (Unitization k A))
        (unitizationScalarProjector k A).toLinearMap
        (ModuleCat.Algebra.Hochschild.unitSubmodule_le_comap
          (unitizationScalarProjector k A).toLinearMap
          (unitizationScalarProjector k A).map_one) = 0 := by
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on _ x ?_
  intro a
  rw [Submodule.mapQ_apply]
  change (ModuleCat.Algebra.Hochschild.unitSubmodule k (Unitization k A)).mkQ
    (unitizationScalarProjector k A a) = 0
  have h := unitizationQuotient_mkQ_eq_inr k A (unitizationScalarProjector k A a)
  simpa only [unitizationScalarProjector_apply, Unitization.snd_inl,
    Unitization.inr_zero, map_zero, LinearMap.zero_apply] using h

/-- In every positive degree the displayed normalized scalar projector is zero. -/
theorem unitizationNormalizedScalarProjector_f_succ (n : ℕ) :
    (unitizationNormalizedScalarProjector k A).f (n + 1) = 0 := by
  apply ModuleCat.hom_ext
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  change ModuleCat.Algebra.Hochschild.normalizedLevelLinearMap
      (unitizationScalarProjector k A).toLinearMap
      (unitizationScalarProjector k A).toLinearMap
      (unitizationScalarProjector k A).map_one (n + 1)
        (m ⊗ₜ[k] PiTensorProduct.tprod k a) = 0
  simp only [ModuleCat.Algebra.Hochschild.normalizedLevelLinearMap,
    TensorProduct.map_tmul, PiTensorProduct.map_tprod,
    unitizationScalarProjector_quotient_zero, LinearMap.zero_apply]
  rw [(PiTensorProduct.tprod k).map_coord_zero (0 : Fin (n + 1)) rfl,
    TensorProduct.tmul_zero]

/-- The even coordinate lies in the reduced kernel, including degree zero. -/
@[reassoc]
theorem unitizationEvenWord_projector (n : ℕ) :
    unitizationEvenWord k A n ≫ (unitizationNormalizedScalarProjector k A).f n = 0 := by
  cases n with
  | succ n => rw [unitizationNormalizedScalarProjector_f_succ, comp_zero]
  | zero =>
      apply ModuleCat.hom_ext
      apply ModuleCat.Algebra.Hochschild.tensorPower_ext
      intro m a
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, unitizationEvenWord_tprod]
      change ModuleCat.Algebra.Hochschild.normalizedLevelLinearMap
          (unitizationScalarProjector k A).toLinearMap
          (unitizationScalarProjector k A).toLinearMap
          (unitizationScalarProjector k A).map_one 0
            (Unitization.inr m ⊗ₜ[k] PiTensorProduct.tprod k
              (fun i => originalToUnitizationQuotient k A (a i))) = 0
      have hm : (unitizationScalarProjector k A).toLinearMap (Unitization.inr m) = 0 := rfl
      simp only [ModuleCat.Algebra.Hochschild.normalizedLevelLinearMap,
        TensorProduct.map_tmul, hm, TensorProduct.zero_tmul]

/-- The odd coordinate also lies in the reduced kernel. -/
@[reassoc]
theorem unitizationOddWord_projector (n : ℕ) :
    unitizationOddWord k A n ≫ (unitizationNormalizedScalarProjector k A).f (n + 1) = 0 := by
  rw [unitizationNormalizedScalarProjector_f_succ, comp_zero]

/-- The first column keeps precisely its original Hochschild differential. -/
@[reassoc]
theorem unitizationEvenWord_d (n : ℕ) :
    unitizationEvenWord k A (n + 1) ≫
        (normalizedBComplex k (Unitization k A)).d (n + 1) n =
      (bComplex k A).d (n + 1) n ≫ unitizationEvenWord k A n := by
  dsimp only [unitizationEvenWord]
  rw [Category.assoc, (normalizedProjection k (Unitization k A)).comm,
    ← Category.assoc, (unitizationRegularInclusion k A).comm, Category.assoc]

/-- The signed final face after insertion is the negative original rotation. -/
theorem unitizationInsertion_signed_last (n : ℕ) :
    extraDegeneracyWith k (Unitization k A) 1 n ≫
        ((-1 : ℤ) ^ (n + 1) •
          regularFace k (Unitization k A) n (Fin.last (n + 1))) =
      -cyclicMap k (Unitization k A) n := by
  apply ModuleCat.hom_ext
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  let b : Fin (n + 1) → Unitization k A := Fin.cons m a
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zsmul, ModuleCat.hom_neg,
    LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.neg_apply]
  rw [extraDegeneracyWith_tprod, regularFace_last_tprod, mul_one]
  have hC := TensorPower.consCyclicOperator_tmul k (Unitization k A) n b
  change TensorPower.consCyclicOperator k (Unitization k A) n
      (m ⊗ₜ[k] PiTensorProduct.tprod k a) = _ at hC
  change (-1 : ℤ) ^ (n + 1) •
      (b (Fin.last n) ⊗ₜ[k] PiTensorProduct.tprod k (fun i : Fin n => b i.castSucc)) =
    -TensorPower.consCyclicOperator k (Unitization k A) n
      (m ⊗ₜ[k] PiTensorProduct.tprod k a)
  rw [hC, ← Int.cast_smul_eq_zsmul k]
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one, pow_succ,
    mul_neg, mul_one, neg_smul]

/-- Native contraction of the unitization b-prime complex earns the original odd formula. -/
theorem unitizationInsertion_full_d_succ (n : ℕ) :
    extraDegeneracyWith k (Unitization k A) 1 (n + 1) ≫
        (bComplex k (Unitization k A)).d (n + 2) (n + 1) =
      (𝟙 _ - cyclicMap k (Unitization k A) (n + 1)) -
        ((bPrimeComplex k (Unitization k A)).d (n + 1) n ≫
          extraDegeneracyWith k (Unitization k A) 1 n :
            chainLevel k (Unitization k A) (Unitization k A) (n + 1) ⟶
              chainLevel k (Unitization k A) (Unitization k A) (n + 1)) := by
  let H := bPrimeContractionOfLeftUnit k (Unitization k A) 1 (fun a => one_mul a)
  have h := H.comm (n + 1)
  rw [HomologicalComplex.id_f, HomologicalComplex.zero_f_apply, add_zero,
    dNext_eq H.hom (by show (ComplexShape.down ℕ).Rel (n + 1) n; rfl),
    prevD_eq H.hom (by show (ComplexShape.down ℕ).Rel (n + 2) (n + 1); rfl),
    bPrimeContractionOfLeftUnit_hom, bPrimeContractionOfLeftUnit_hom] at h
  let d : chainLevel k (Unitization k A) (Unitization k A) (n + 2) ⟶
      chainLevel k (Unitization k A) (Unitization k A) (n + 1) :=
    (bComplex k (Unitization k A)).d (n + 2) (n + 1)
  let d' : chainLevel k (Unitization k A) (Unitization k A) (n + 2) ⟶
      chainLevel k (Unitization k A) (Unitization k A) (n + 1) :=
    (bPrimeComplex k (Unitization k A)).d (n + 2) (n + 1)
  let d₀ : chainLevel k (Unitization k A) (Unitization k A) (n + 1) ⟶
      chainLevel k (Unitization k A) (Unitization k A) n :=
    (bPrimeComplex k (Unitization k A)).d (n + 1) n
  have hLast : d = d' + (-1 : ℤ) ^ (n + 2) •
      regularFace k (Unitization k A) (n + 1) (Fin.last (n + 2)) :=
    bComplex_d_eq_bPrime_add_last k (Unitization k A) (n + 1)
  change 𝟙 (chainLevel k (Unitization k A) (Unitization k A) (n + 1)) =
    d₀ ≫ extraDegeneracyWith k (Unitization k A) 1 n +
      extraDegeneracyWith k (Unitization k A) 1 (n + 1) ≫ d' at h
  change extraDegeneracyWith k (Unitization k A) 1 (n + 1) ≫ d =
    (𝟙 _ - cyclicMap k (Unitization k A) (n + 1)) -
      d₀ ≫ extraDegeneracyWith k (Unitization k A) 1 n
  rw [hLast, Preadditive.comp_add, unitizationInsertion_signed_last, h]
  abel

/-- The source odd-column boundary is exactly 1-t into the even column and -b-prime into the odd. -/
@[reassoc]
theorem unitizationOddWord_d_succ (n : ℕ) :
    unitizationOddWord k A (n + 1) ≫
        (normalizedBComplex k (Unitization k A)).d (n + 2) (n + 1) =
      (𝟙 _ - cyclicMap k A (n + 1)) ≫ unitizationEvenWord k A (n + 1) -
        ((bPrimeComplex k A).d (n + 1) n ≫ unitizationOddWord k A n :
          chainLevel k A A (n + 1) ⟶ (normalizedBComplex k (Unitization k A)).X (n + 1)) := by
  let L := unitizationRegularInclusion k A
  let κ := normalizedProjection k (Unitization k A)
  let i₁ : chainLevel k A A (n + 1) →ₗ[k]
      chainLevel k (Unitization k A) (Unitization k A) (n + 1) := (L.f (n + 1)).hom
  let i₀ : chainLevel k A A n →ₗ[k]
      chainLevel k (Unitization k A) (Unitization k A) n := (L.f n).hom
  let s₁ := (extraDegeneracyWith k (Unitization k A) 1 (n + 1)).hom
  let s₀ := (extraDegeneracyWith k (Unitization k A) 1 n).hom
  let d : chainLevel k (Unitization k A) (Unitization k A) (n + 2) →ₗ[k]
      chainLevel k (Unitization k A) (Unitization k A) (n + 1) :=
    ((bComplex k (Unitization k A)).d (n + 2) (n + 1)).hom
  let d' : chainLevel k (Unitization k A) (Unitization k A) (n + 1) →ₗ[k]
      chainLevel k (Unitization k A) (Unitization k A) n :=
    ((bPrimeComplex k (Unitization k A)).d (n + 1) n).hom
  let d₀ : chainLevel k A A (n + 1) →ₗ[k] chainLevel k A A n :=
    ((bPrimeComplex k A).d (n + 1) n).hom
  let t := (cyclicMap k (Unitization k A) (n + 1)).hom
  let t₀ := (cyclicMap k A (n + 1)).hom
  let p₂ := (κ.f (n + 2)).hom
  let p₁ := (κ.f (n + 1)).hom
  let δ := ((normalizedBComplex k (Unitization k A)).d (n + 2) (n + 1)).hom
  have hPrime : d'.comp i₁ = i₀.comp d₀ :=
    (bPrimeComplex_d_natural (Unitization.inrNonUnitalAlgHom k A) n).symm
  have hCyclic : t.comp i₁ = i₁.comp t₀ :=
    (TensorPower.consCyclicOperator_natural (Unitization.inrHom k k A) (n + 1)).symm
  have hNorm : δ.comp p₂ = p₁.comp d := by
    have h := congrArg (fun f : chainLevel k (Unitization k A) (Unitization k A) (n + 2) ⟶
      (normalizedBComplex k (Unitization k A)).X (n + 1) => f.hom) (κ.comm (n + 2) (n + 1))
    exact h
  have hFull : d.comp s₁ = (LinearMap.id - t) - s₀.comp d' := by
    have h := congrArg (fun f : chainLevel k (Unitization k A) (Unitization k A) (n + 1) ⟶
      chainLevel k (Unitization k A) (Unitization k A) (n + 1) => f.hom)
      (unitizationInsertion_full_d_succ k A n)
    exact h
  refine ModuleCat.hom_ext (M := chainLevel k A A (n + 1))
    (N := (normalizedBComplex k (Unitization k A)).X (n + 1)) ?_
  dsimp only [unitizationOddWord, unitizationEvenWord]
  simp only [ModuleCat.hom_comp, ModuleCat.hom_sub, ModuleCat.hom_id]
  change δ.comp (p₂.comp (s₁.comp i₁)) =
    p₁.comp (i₁.comp (LinearMap.id - t₀)) - p₁.comp (s₀.comp (i₀.comp d₀))
  calc
    _ = p₁.comp ((d.comp s₁).comp i₁) := by
      rw [← LinearMap.comp_assoc, hNorm]
      rfl
    _ = p₁.comp (((LinearMap.id - t) - s₀.comp d').comp i₁) := by rw [hFull]
    _ = _ := by
      simp only [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp,
        LinearMap.comp_id, LinearMap.comp_assoc]
      rw [hPrime, hCyclic]

/-- There is no hidden shifted bottom term: the original odd word has zero boundary in degree one. -/
@[reassoc]
theorem unitizationOddWord_d_zero :
    unitizationOddWord k A 0 ≫ (normalizedBComplex k (Unitization k A)).d 1 0 = 0 := by
  let H := bPrimeContractionOfLeftUnit k (Unitization k A) 1 (fun a => one_mul a)
  have h := H.comm 0
  rw [HomologicalComplex.id_f, HomologicalComplex.zero_f_apply, add_zero,
    dNext_eq_zero H.hom 0 (by simp [ComplexShape.down_Rel]),
    prevD_eq H.hom (by show (ComplexShape.down ℕ).Rel 1 0; rfl),
    bPrimeContractionOfLeftUnit_hom, zero_add] at h
  let d : chainLevel k (Unitization k A) (Unitization k A) 1 ⟶
      chainLevel k (Unitization k A) (Unitization k A) 0 :=
    (bComplex k (Unitization k A)).d 1 0
  let d' : chainLevel k (Unitization k A) (Unitization k A) 1 ⟶
      chainLevel k (Unitization k A) (Unitization k A) 0 :=
    (bPrimeComplex k (Unitization k A)).d 1 0
  change 𝟙 (chainLevel k (Unitization k A) (Unitization k A) 0) =
    extraDegeneracyWith k (Unitization k A) 1 0 ≫ d' at h
  have hLast : d = d' + (-1 : ℤ) ^ 1 •
      regularFace k (Unitization k A) 0 (Fin.last 1) :=
    bComplex_d_eq_bPrime_add_last k (Unitization k A) 0
  have hCyclicZero : cyclicMap k (Unitization k A) 0 =
      𝟙 (chainLevel k (Unitization k A) (Unitization k A) 0) := by
    apply ModuleCat.hom_ext
    exact TensorPower.consCyclicOperator_zero k (Unitization k A)
  have hFull : extraDegeneracyWith k (Unitization k A) 1 0 ≫ d = 0 := by
    rw [hLast, Preadditive.comp_add, unitizationInsertion_signed_last, ← h, hCyclicZero]
    exact add_neg_cancel _
  let i : chainLevel k A A 0 ⟶ chainLevel k (Unitization k A) (Unitization k A) 0 :=
    (unitizationRegularInclusion k A).f 0
  let p₁ : chainLevel k (Unitization k A) (Unitization k A) 1 ⟶
      (normalizedBComplex k (Unitization k A)).X 1 :=
    (normalizedProjection k (Unitization k A)).f 1
  let p₀ : chainLevel k (Unitization k A) (Unitization k A) 0 ⟶
      (normalizedBComplex k (Unitization k A)).X 0 :=
    (normalizedProjection k (Unitization k A)).f 0
  let δ := (normalizedBComplex k (Unitization k A)).d 1 0
  have hNorm : p₁ ≫ δ = d ≫ p₀ := (normalizedProjection k (Unitization k A)).comm 1 0
  change ((i ≫ extraDegeneracyWith k (Unitization k A) 1 0) ≫ p₁) ≫ δ = 0
  rw [Category.assoc, Category.assoc, hNorm,
    ← Category.assoc (extraDegeneracyWith k (Unitization k A) 1 0) d p₀,
    hFull, zero_comp, comp_zero]

end ModuleCat.Algebra.Hochschild.NonUnital
