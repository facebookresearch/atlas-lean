/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.UnitizationTwoColumns

/-!
# nonunital-map naturality of unitization coordinates

Original nonunital algebra maps lift through the native unitization
property. Their normalized level maps preserve the even word and
unit-leading odd word for independent algebra carrier universes. In one
module carrier world these original maps restrict to the relative
and reduced complexes and commute with the two-column comparison.
No preservation of a unit in the original nonunital algebra is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

open ModuleCat.Algebra.Hochschild

variable {k : Type u} [CommRing k] {A : Type v} [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

section IndependentCarriers

variable {B : Type w} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- The original map acts on the regular coefficient and quotient tail, in independent worlds. -/
def unitizationNormalizedLevelMap (f : A →ₙₐ[k] B) (n : ℕ) :
    (normalizedBComplex k (Unitization k A)).X n →ₗ[k]
      (normalizedBComplex k (Unitization k B)).X n :=
  ModuleCat.Algebra.Hochschild.normalizedLevelLinearMap
    (unitizationMap k A f).toLinearMap (unitizationMap k A f).toLinearMap
    (unitizationMap k A f).map_one n

/-- The map preserves the even ideal word, with the original f on every factor. -/
theorem unitizationEvenWord_naturality (f : A →ₙₐ[k] B) (n : ℕ) :
    (unitizationNormalizedLevelMap f n).comp (unitizationEvenWord k A n).hom =
      (unitizationEvenWord k B n).hom.comp (TensorPower.consLevelMap (f : A →ₗ[k] B) n) := by
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  simp only [LinearMap.comp_apply, TensorPower.consLevelMap,
    TensorProduct.map_tmul, PiTensorProduct.map_tprod]
  erw [unitizationEvenWord_tprod, unitizationEvenWord_tprod]
  change ModuleCat.Algebra.Hochschild.normalizedLevelLinearMap
      (unitizationMap k A f).toLinearMap (unitizationMap k A f).toLinearMap
      (unitizationMap k A f).map_one n
        (Unitization.inr m ⊗ₜ[k] PiTensorProduct.tprod k
          (fun i => (ModuleCat.Algebra.Hochschild.unitSubmodule k (Unitization k A)).mkQ
            (Unitization.inr (a i)))) = _
  erw [ModuleCat.Algebra.Hochschild.normalizedLevelLinearMap_tmul_tprod]
  change unitizationMap k A f (Unitization.inr m) ⊗ₜ[k] PiTensorProduct.tprod k
    (fun i => (ModuleCat.Algebra.Hochschild.unitSubmodule k (Unitization k B)).mkQ
      (unitizationMap k A f (Unitization.inr (a i)))) = _
  simp only [unitizationMap_inr]
  rfl

/-- The map preserves the external unit and original odd ideal word. -/
theorem unitizationOddWord_naturality (f : A →ₙₐ[k] B) (n : ℕ) :
    (unitizationNormalizedLevelMap f (n + 1)).comp (unitizationOddWord k A n).hom =
      (unitizationOddWord k B n).hom.comp (TensorPower.consLevelMap (f : A →ₗ[k] B) n) := by
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  simp only [LinearMap.comp_apply, TensorPower.consLevelMap,
    TensorProduct.map_tmul, PiTensorProduct.map_tprod]
  erw [unitizationOddWord_tprod, unitizationOddWord_tprod]
  change ModuleCat.Algebra.Hochschild.normalizedLevelLinearMap
      (unitizationMap k A f).toLinearMap (unitizationMap k A f).toLinearMap
      (unitizationMap k A f).map_one (n + 1)
        ((1 : Unitization k A) ⊗ₜ[k] PiTensorProduct.tprod k
          (fun i => (ModuleCat.Algebra.Hochschild.unitSubmodule k (Unitization k A)).mkQ
            (Unitization.inr ((Fin.cons m a : Fin (n + 1) → A) i)))) = _
  erw [ModuleCat.Algebra.Hochschild.normalizedLevelLinearMap_tmul_tprod]
  change unitizationMap k A f (1 : Unitization k A) ⊗ₜ[k] PiTensorProduct.tprod k
    (fun i : Fin (n + 1) => (ModuleCat.Algebra.Hochschild.unitSubmodule k (Unitization k B)).mkQ
      (unitizationMap k A f (Unitization.inr ((Fin.cons m a : Fin (n + 1) → A) i)))) = _
  simp only [map_one, unitizationMap_inr]
  congr 2
  funext i
  cases i using Fin.cases <;> rfl

/-- The scalar projector commutes with the original lifted nonunital map. -/
theorem unitizationMap_scalarProjector (f : A →ₙₐ[k] B) :
    (unitizationMap k A f).comp (unitizationScalarProjector k A) =
      (unitizationScalarProjector k B).comp (unitizationMap k A f) := by
  apply AlgHom.ext
  intro x
  change unitizationMap k A f (Unitization.inl x.fst) =
    Unitization.inl (unitizationMap k A f x).fst
  rw [unitizationMap_inl, unitizationMap_apply]

end IndependentCarriers

section OneCarrierWorld

variable {B : Type v} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- The original unitization map gives the regular Hochschild chain map. -/
def unitizationRegularMap (f : A →ₙₐ[k] B) :
    bComplex k (Unitization k A) ⟶ bComplex k (Unitization k B) :=
  cyclicBComplexHom (unitizationMap k A f).toNonUnitalAlgHom

/-- The normalized chain map is the same native factor-quotient construction. -/
def unitizationNormalizedMap (f : A →ₙₐ[k] B) :
    normalizedBComplex k (Unitization k A) ⟶ normalizedBComplex k (Unitization k B) :=
  normalizedRegularUnitizationMap (unitizationMap k A f)

@[simp]
theorem unitizationNormalizedMap_f (f : A →ₙₐ[k] B) (n : ℕ) :
    (unitizationNormalizedMap f).f n = ModuleCat.ofHom (unitizationNormalizedLevelMap f n) := rfl

@[reassoc]
theorem unitizationRegularMap_projector (f : A →ₙₐ[k] B) :
    unitizationScalarComplexProjector k A ≫ unitizationRegularMap f =
      unitizationRegularMap f ≫ unitizationScalarComplexProjector k B := by
  dsimp only [unitizationScalarComplexProjector, unitizationRegularMap]
  rw [← cyclicBComplexHom_comp, ← cyclicBComplexHom_comp]
  exact congrArg cyclicBComplexHom
    (congrArg AlgHom.toNonUnitalAlgHom (unitizationMap_scalarProjector f))

@[reassoc]
theorem unitizationNormalizedMap_projection (f : A →ₙₐ[k] B) :
    normalizedProjection k (Unitization k A) ≫ unitizationNormalizedMap f =
      unitizationRegularMap f ≫ normalizedProjection k (Unitization k B) :=
  normalizedProjection_regularUnitizationMap (unitizationMap k A f)

@[reassoc]
theorem unitizationNormalizedMap_projector (f : A →ₙₐ[k] B) :
    unitizationNormalizedScalarProjector k A ≫ unitizationNormalizedMap f =
      unitizationNormalizedMap f ≫ unitizationNormalizedScalarProjector k B := by
  apply HomologicalComplex.hom_ext
  intro n
  let κA := normalizedProjection k (Unitization k A)
  let κB := normalizedProjection k (Unitization k B)
  have hA := HomologicalComplex.congr_hom
    (normalizedProjection_regularEndomorphism (unitizationScalarProjector k A)) n
  have hB := HomologicalComplex.congr_hom
    (normalizedProjection_regularEndomorphism (unitizationScalarProjector k B)) n
  have hf := HomologicalComplex.congr_hom (unitizationNormalizedMap_projection f) n
  have hp := HomologicalComplex.congr_hom (unitizationRegularMap_projector f) n
  simp only [HomologicalComplex.comp_f] at hA hB hf hp ⊢
  change κA.f n ≫ (unitizationNormalizedScalarProjector k A).f n =
    (unitizationScalarComplexProjector k A).f n ≫ κA.f n at hA
  change κB.f n ≫ (unitizationNormalizedScalarProjector k B).f n =
    (unitizationScalarComplexProjector k B).f n ≫ κB.f n at hB
  apply (cancel_epi (κA.f n)).1
  calc
    _ = (unitizationScalarComplexProjector k A).f n ≫
        (unitizationRegularMap f).f n ≫ κB.f n := by
      rw [← Category.assoc, hA, Category.assoc, hf, ← Category.assoc]
    _ = (unitizationRegularMap f).f n ≫
        (unitizationScalarComplexProjector k B).f n ≫ κB.f n := by
      simpa only [Category.assoc] using congrArg
        (fun g : (bComplex k (Unitization k A)).X n ⟶ (bComplex k (Unitization k B)).X n =>
          g ≫ κB.f n) hp
    _ = _ := by rw [← hB, ← Category.assoc, ← hf, Category.assoc]

/-- The original map restricts to the relative augmentation kernels. -/
def unitizationRelativeMap (f : A →ₙₐ[k] B) :
    unitizationRelativeComplex k A ⟶ unitizationRelativeComplex k B :=
  kernel.map _ _ (unitizationRegularMap f) (unitizationRegularMap f)
    (unitizationRegularMap_projector f)

/-- The same original map restricts to the reduced normalized kernels. -/
def unitizationReducedNormalizedMap (f : A →ₙₐ[k] B) :
    unitizationReducedNormalizedComplex k A ⟶ unitizationReducedNormalizedComplex k B :=
  kernel.map _ _ (unitizationNormalizedMap f) (unitizationNormalizedMap f)
    (unitizationNormalizedMap_projector f)

/-- Naturality retains the complete original restricted normalization map. -/
@[reassoc]
theorem unitizationRelativeNormalization_naturality (f : A →ₙₐ[k] B) :
    unitizationRelativeMap f ≫ unitizationRelativeNormalization k B =
      unitizationRelativeNormalization k A ≫ unitizationReducedNormalizedMap f := by
  have hr : unitizationRelativeMap f ≫ kernel.ι (unitizationScalarComplexProjector k B) =
      kernel.ι (unitizationScalarComplexProjector k A) ≫ unitizationRegularMap f :=
    kernel.lift_ι _ _ _
  have hn : unitizationReducedNormalizedMap f ≫
      kernel.ι (unitizationNormalizedScalarProjector k B) =
      kernel.ι (unitizationNormalizedScalarProjector k A) ≫ unitizationNormalizedMap f :=
    kernel.lift_ι _ _ _
  apply (cancel_mono (kernel.ι (unitizationNormalizedScalarProjector k B))).1
  rw [Category.assoc, unitizationRelativeNormalization_ι,
    ← Category.assoc, hr, Category.assoc, ← unitizationNormalizedMap_projection,
    ← Category.assoc, ← unitizationRelativeNormalization_ι, Category.assoc, ← hn]
  rw [Category.assoc]

/-- Original nonunital maps commute with the first-two-column unitization chain comparison. -/
@[reassoc]
theorem unitizationTwoColumnIso_naturality (f : A →ₙₐ[k] B) :
    (cyclicTwoColumnSequenceMap f).τ₁ ≫ (unitizationTwoColumnIso k B).hom =
      (unitizationTwoColumnIso k A).hom ≫ unitizationReducedNormalizedMap f := by
  apply (cancel_mono (kernel.ι (unitizationNormalizedScalarProjector k B))).1
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, Category.assoc]
  have hK₀ : unitizationReducedNormalizedMap f ≫
      kernel.ι (unitizationNormalizedScalarProjector k B) =
      kernel.ι (unitizationNormalizedScalarProjector k A) ≫ unitizationNormalizedMap f :=
    kernel.lift_ι _ _ _
  have hK := HomologicalComplex.congr_hom hK₀ n
  simp only [HomologicalComplex.comp_f] at hK
  apply unitizationRawDegree_hom_ext k A n
  · rw [← Category.assoc,
      cyclicFirstTwoColumnCell_naturality f (0 : Fin 2) n n (by change 0 + n = n; omega)]
    simp only [Category.assoc, unitizationTwoColumnIso_hom_f,
      unitizationTwoColumnCoordinateIso_even, unitizationTwoColumnCoordinateIso_even_assoc,
      hK, unitizationNormalizedMap_f]
    apply ModuleCat.hom_ext
    change (unitizationEvenWord k B n).hom.comp (TensorPower.consLevelMap (f : A →ₗ[k] B) n) =
      (unitizationNormalizedLevelMap f n).comp (unitizationEvenWord k A n).hom
    exact (unitizationEvenWord_naturality f n).symm
  · intro m hm
    subst n
    rw [← Category.assoc,
      cyclicFirstTwoColumnCell_naturality f (1 : Fin 2) m (m + 1) (by change 1 + m = m + 1; omega)]
    simp only [Category.assoc, unitizationTwoColumnIso_hom_f,
      unitizationTwoColumnCoordinateIso_odd, unitizationTwoColumnCoordinateIso_odd_assoc,
      hK, unitizationNormalizedMap_f]
    apply ModuleCat.hom_ext
    change (unitizationOddWord k B m).hom.comp (TensorPower.consLevelMap (f : A →ₗ[k] B) m) =
      (unitizationNormalizedLevelMap f (m + 1)).comp (unitizationOddWord k A m).hom
    exact (unitizationOddWord_naturality f m).symm

/-- The original scalar inclusion commutes with the original lifted nonunital map. -/
@[reassoc]
theorem unitizationScalarComplexInclusion_naturality (f : A →ₙₐ[k] B) :
    unitizationScalarComplexInclusion k A ≫ unitizationRegularMap f =
      unitizationScalarComplexInclusion k B := by
  dsimp only [unitizationScalarComplexInclusion, unitizationRegularMap]
  rw [← cyclicBComplexHom_comp]
  apply congrArg cyclicBComplexHom
  apply NonUnitalAlgHom.ext
  intro x
  change unitizationMap k A f (Unitization.inl x.down) = Unitization.inl x.down
  exact unitizationMap_inl k A f x.down

/-- The public source HH map is the cokernel map induced by the original unitization lift. -/
def unitizationHochschildMap (f : A →ₙₐ[k] B) (n : ℕ) :
    unitizationHochschildHomology k A n ⟶ unitizationHochschildHomology k B n :=
  cokernel.map _ _ (𝟙 _) (HomologicalComplex.homologyMap (unitizationRegularMap f) n) (by
    rw [Category.id_comp, ← HomologicalComplex.homologyMap_comp, unitizationScalarComplexInclusion_naturality])

/-- The source cokernel comparison is natural for the original nonunital algebra map. -/
@[reassoc]
theorem unitizationHochschildRelativeIso_naturality (f : A →ₙₐ[k] B) (n : ℕ) :
    unitizationHochschildMap f n ≫ (unitizationHochschildRelativeIso k B n).hom =
      (unitizationHochschildRelativeIso k A n).hom ≫ HomologicalComplex.homologyMap (unitizationRelativeMap f) n := by
  have hr := projectorKernelRetraction_naturality
    (unitizationScalarComplexProjector k A) (unitizationScalarComplexProjector_idempotent k A)
    (unitizationScalarComplexProjector k B) (unitizationScalarComplexProjector_idempotent k B)
    (unitizationRegularMap f) (unitizationRegularMap_projector f)
  apply (cancel_epi (cokernel.π (HomologicalComplex.homologyMap (unitizationScalarComplexInclusion k A) n))).1
  rw [← Category.assoc, unitizationHochschildMap, cokernel.π_desc,
    Category.assoc, unitizationHochschildRelativeIso_π_hom,
    ← Category.assoc, unitizationHochschildRelativeIso_π_hom,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun g => HomologicalComplex.homologyMap g n) hr

/-- The source HH comparison with the raw total commutes with its original map. -/
@[reassoc]
theorem unitizationHochschildTwoColumnIso_naturality (f : A →ₙₐ[k] B) (n : ℕ) :
    unitizationHochschildMap f n ≫ (unitizationHochschildTwoColumnIso k B n).hom =
      (unitizationHochschildTwoColumnIso k A n).hom ≫
        HomologicalComplex.homologyMap (cyclicTwoColumnSequenceMap f).τ₁ n := by
  have hN := congrArg (fun g => HomologicalComplex.homologyMap g n) (unitizationRelativeNormalization_naturality f)
  have hT := congrArg (fun g => HomologicalComplex.homologyMap g n) (unitizationTwoColumnIso_naturality f)
  simp only [HomologicalComplex.homologyMap_comp] at hN hT
  have hInv : HomologicalComplex.homologyMap (unitizationReducedNormalizedMap f) n ≫
      HomologicalComplex.homologyMap (unitizationTwoColumnIso k B).inv n =
      HomologicalComplex.homologyMap (unitizationTwoColumnIso k A).inv n ≫
        HomologicalComplex.homologyMap (cyclicTwoColumnSequenceMap f).τ₁ n := by
    apply (cancel_mono (HomologicalComplex.homologyMap (unitizationTwoColumnIso k B).hom n)).1
    rw [Category.assoc, ← HomologicalComplex.homologyMap_comp, Iso.inv_hom_id, HomologicalComplex.homologyMap_id,
      Category.comp_id, Category.assoc, hT, ← Category.assoc,
      ← HomologicalComplex.homologyMap_comp, Iso.inv_hom_id, HomologicalComplex.homologyMap_id, Category.id_comp]
  change unitizationHochschildMap f n ≫
    ((unitizationHochschildRelativeIso k B n).hom ≫
      (HomologicalComplex.homologyMap (unitizationRelativeNormalization k B) n ≫
        HomologicalComplex.homologyMap (unitizationTwoColumnIso k B).inv n)) =
    ((unitizationHochschildRelativeIso k A n).hom ≫
      (HomologicalComplex.homologyMap (unitizationRelativeNormalization k A) n ≫
        HomologicalComplex.homologyMap (unitizationTwoColumnIso k A).inv n)) ≫
      HomologicalComplex.homologyMap (cyclicTwoColumnSequenceMap f).τ₁ n
  rw [← Category.assoc, unitizationHochschildRelativeIso_naturality, Category.assoc]
  rw [← Category.assoc (HomologicalComplex.homologyMap (unitizationRelativeMap f) n), hN,
    Category.assoc, hInv]
  simp only [Category.assoc]

/-- An left unit earns the specialization to the original b-complex through its canonical inclusion. -/
def unitizationHochschildUnitalIso (hUnit : ∃ e : A, ∀ a : A, e * a = a) (n : ℕ) :
    unitizationHochschildHomology k A n ≅ (bComplex k A).homology n := by
  letI : _root_.QuasiIso (cyclicBToFirstTwo k A) := cyclicBToFirstTwo_quasiIso k A hUnit
  exact unitizationHochschildTwoColumnIso k A n ≪≫
    (asIso (HomologicalComplex.homologyMap (cyclicBToFirstTwo k A) n)).symm

/-- The unital specialization retains the canonical first-column inclusion. -/
@[reassoc]
theorem unitizationHochschildUnitalIso_inclusion
    (hUnit : ∃ e : A, ∀ a : A, e * a = a) (n : ℕ) :
    (unitizationHochschildUnitalIso hUnit n).hom ≫ HomologicalComplex.homologyMap (cyclicBToFirstTwo k A) n =
      (unitizationHochschildTwoColumnIso k A n).hom := by
  simp only [unitizationHochschildUnitalIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, asIso_inv, IsIso.inv_hom_id, Category.comp_id]

end OneCarrierWorld

end ModuleCat.Algebra.Hochschild.NonUnital
