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
# Ideal-leading and unit-leading normalized words

Let `k` be a commutative ring and `A` a nonunital ground algebra. In normalized chains of `A⁺
= k ⊕ A`, the even word includes every entry in `A`, while the odd word puts the external unit
in the coefficient position and moves the whole `A`-word into the quotient tail.

Both word maps take values in the reduced scalar-projector kernel. The even differential is
the regular Hochschild boundary `b`. The odd differential has components `1-t` into the even
word and `-b′` into the odd word; its bottom boundary is zero. The formulas use the unit of
`A⁺` and apply to arbitrary nonunital `A`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex
open scoped TensorProduct

universe u v

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The regular Hochschild inclusion into a unitization.

The nonunital inclusion `A → A⁺` acts on the coefficient and every tail factor, giving a chain
map `b(A) → b(A⁺)`. -/
def unitizationRegularInclusion : bComplex k A ⟶ bComplex k (Unitization k A) :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom
    (TensorPower.consLevelMap (Unitization.inrHom k k A) n)) (fun n => by
      apply ModuleCat.hom_ext
      exact (bComplex_d_natural (Unitization.inrNonUnitalAlgHom k A) n).symm)

/-- The ideal-leading word in normalized unitization chains.

In degree `n`, include each `A`-entry into `A⁺` and apply normalized projection, retaining the
ideal coefficient in the leading position. -/
def unitizationEvenWord (n : ℕ) :
    chainLevel k A A n ⟶ (normalizedBComplex k (Unitization k A)).X n :=
  (unitizationRegularInclusion k A).f n ≫ (normalizedProjection k (Unitization k A)).f n

/-- The external-unit-leading word in normalized unitization chains.

For a word in degree `n`, include it into `A⁺`, insert the external unit as coefficient, and
normalize to obtain a word in degree `n+1`. -/
def unitizationOddWord (n : ℕ) :
    chainLevel k A A n ⟶ (normalizedBComplex k (Unitization k A)).X (n + 1) :=
  (unitizationRegularInclusion k A).f n ≫
    extraDegeneracyWith k (Unitization k A) 1 n ≫
      (normalizedProjection k (Unitization k A)).f (n + 1)

/-- The tensor formula for an ideal-leading normalized word.

The even word sends `m ⊗ ⊗ᵢ aᵢ` to `inr(m) ⊗ ⊗ᵢ [inr(aᵢ)]`, where brackets denote the ground-
module quotient by `k·1`. -/
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

/-- The tensor formula for an external-unit-leading normalized word.

The odd word sends `m ⊗ ⊗ᵢ aᵢ` to `1 ⊗ ([inr(m)] ⊗ ⊗ᵢ [inr(aᵢ)])`, placing the former
coefficient at the start of the quotient tail. -/
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

/-- The zero scalar-projector map on the reduced unitization tail.

The scalar projector induces the zero map on the ground quotient `A⁺ / k·1`, since its image
is contained in the scalar unit span. -/
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

/-- Vanishing of the normalized scalar projector in positive degrees.

In degree `n+1`, the scalar-projector map is zero because its induced map on every quotient-
tail factor is zero. -/
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

/-- The ideal-leading word lies in the reduced normalized kernel.

The even word followed by the normalized scalar projector is zero in every degree, including
degree zero. -/
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

/-- The external-unit-leading word lies in the reduced normalized kernel.

The odd word in degree `n+1` is killed by the normalized scalar projector. -/
@[reassoc]
theorem unitizationOddWord_projector (n : ℕ) :
    unitizationOddWord k A n ≫ (unitizationNormalizedScalarProjector k A).f (n + 1) = 0 := by
  rw [unitizationNormalizedScalarProjector_f_succ, comp_zero]

/-- The Hochschild boundary of an ideal-leading word.

The even word commutes with the regular boundary: `d(even(x)) = even(b(x))`. -/
@[reassoc]
theorem unitizationEvenWord_d (n : ℕ) :
    unitizationEvenWord k A (n + 1) ≫
        (normalizedBComplex k (Unitization k A)).d (n + 1) n =
      (bComplex k A).d (n + 1) n ≫ unitizationEvenWord k A n := by
  dsimp only [unitizationEvenWord]
  rw [Category.assoc, (normalizedProjection k (Unitization k A)).comm,
    ← Category.assoc, (unitizationRegularInclusion k A).comm, Category.assoc]

/-- The cyclic sign of the last face after unit insertion.

For insertion `s` of the external unit into degree `n`, the signed last face satisfies
`(-1)^(n+1) d_last ∘ s = -t_n`, where `t_n` is the signed cyclic map. -/
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

/-- The full boundary formula after external-unit insertion.

In degree `n+1`, the insertion map satisfies `b ∘ s = (1-t) - s ∘ b′`, with each differential
and insertion at its indicated successor degree. -/
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

/-- The signed differential of an external-unit-leading word.

For `x ∈ C_(n+1)(A)`, the odd word has boundary `even((1-t)x) - odd(b′x)`. The vertical odd-
column term has the negative sign. -/
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

/-- The zero bottom boundary of an external-unit-leading word.

The odd word of `C_0(A)` in normalized degree one has zero boundary in degree zero, since `t_0
= 1`. -/
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
