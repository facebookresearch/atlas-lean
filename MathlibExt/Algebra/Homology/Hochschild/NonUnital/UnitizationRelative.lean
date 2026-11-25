/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.UnitizationCoordinates
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.UnitalSBI
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.NormalizedMixedBicomplex
public import MathlibExt.CategoryTheory.Preadditive.SplitProjector

/-!
# relative and reduced normalized unitization complexes

The relative complex is the kernel of the scalar projector on the
regular Hochschild complex of the native unitization. Its normalized
counterpart is the kernel of the same induced projector on the normalized quotient. The original normalization map restricts to a
quasi-isomorphism because its restricted arrow is an retract.

The scalar complex uses an explicit ULift of k in the unitization carrier
world. It does not require the original ring and algebra universes to agree.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex
open scoped TensorProduct

universe u v

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The original scalar inclusion, with only the explicit carrier lift added. -/
def unitizationGroundScalarSection :
    ULift.{v} k →ₐ[k] Unitization k A :=
  (unitizationScalarSection k A).comp (ULift.algEquiv (R := k) (A := k)).toAlgHom

/-- The original augmentation, into the explicitly lifted scalar carrier. -/
def unitizationGroundAugmentation :
    Unitization k A →ₐ[k] ULift.{v} k :=
  (ULift.algEquiv (R := k) (A := k)).symm.toAlgHom.comp (unitizationAugmentation k A)

@[simp]
theorem unitizationGroundScalarSection_apply (r : ULift.{v} k) :
    unitizationGroundScalarSection k A r = Unitization.inl r.down := rfl

@[simp]
theorem unitizationGroundAugmentation_apply (x : Unitization k A) :
    unitizationGroundAugmentation k A x = ULift.up x.fst := rfl

/-- The lifted augmentation retracts the original scalar inclusion. -/
theorem unitizationGroundScalarSection_augmentation :
    (unitizationGroundAugmentation k A).comp (unitizationGroundScalarSection k A) =
      AlgHom.id k (ULift.{v} k) := by
  ext x
  rfl

/-- The complementary composite is still the literal original scalar projector. -/
theorem unitizationGroundAugmentation_section :
    (unitizationGroundScalarSection k A).comp (unitizationGroundAugmentation k A) =
      unitizationScalarProjector k A := by
  apply AlgHom.ext
  intro x
  rfl

/-- The scalar inclusion acts on every original coefficient and tensor factor. -/
def unitizationScalarComplexInclusion :
    bComplex k (ULift.{v} k) ⟶ bComplex k (Unitization k A) :=
  ModuleCat.Algebra.Hochschild.cyclicBComplexHom
    (unitizationGroundScalarSection k A).toNonUnitalAlgHom

/-- The augmentation acts on the same original coefficient and tensor factors. -/
def unitizationScalarComplexAugmentation :
    bComplex k (Unitization k A) ⟶ bComplex k (ULift.{v} k) :=
  ModuleCat.Algebra.Hochschild.cyclicBComplexHom
    (unitizationGroundAugmentation k A).toNonUnitalAlgHom

/-- The chain-level scalar projector uses the original algebra endomorphism. -/
def unitizationScalarComplexProjector :
    bComplex k (Unitization k A) ⟶ bComplex k (Unitization k A) :=
  ModuleCat.Algebra.Hochschild.cyclicBComplexHom
    (unitizationScalarProjector k A).toNonUnitalAlgHom

/-- Both original split maps retain their chain-level identity. -/
@[reassoc]
theorem unitizationScalarComplexInclusion_augmentation :
    unitizationScalarComplexInclusion k A ≫ unitizationScalarComplexAugmentation k A = 𝟙 _ := by
  rw [unitizationScalarComplexInclusion, unitizationScalarComplexAugmentation,
    ← ModuleCat.Algebra.Hochschild.cyclicBComplexHom_comp]
  have h := congrArg AlgHom.toNonUnitalAlgHom
    (unitizationGroundScalarSection_augmentation k A)
  exact (congrArg ModuleCat.Algebra.Hochschild.cyclicBComplexHom h).trans
    (ModuleCat.Algebra.Hochschild.cyclicBComplexHom_id (k := k) (A := ULift.{v} k))

/-- The factorization of the projector is the original augmentation followed by scalar inclusion. -/
@[reassoc]
theorem unitizationScalarComplexAugmentation_inclusion :
    unitizationScalarComplexAugmentation k A ≫ unitizationScalarComplexInclusion k A =
      unitizationScalarComplexProjector k A := by
  rw [unitizationScalarComplexInclusion, unitizationScalarComplexAugmentation,
    unitizationScalarComplexProjector,
    ← ModuleCat.Algebra.Hochschild.cyclicBComplexHom_comp]
  exact congrArg ModuleCat.Algebra.Hochschild.cyclicBComplexHom
    (congrArg AlgHom.toNonUnitalAlgHom (unitizationGroundAugmentation_section k A))

theorem unitizationScalarComplexProjector_idempotent :
    unitizationScalarComplexProjector k A ≫ unitizationScalarComplexProjector k A =
      unitizationScalarComplexProjector k A := by
  rw [unitizationScalarComplexProjector,
    ← ModuleCat.Algebra.Hochschild.cyclicBComplexHom_comp]
  exact congrArg ModuleCat.Algebra.Hochschild.cyclicBComplexHom
    (congrArg AlgHom.toNonUnitalAlgHom (unitizationScalarProjector_idempotent k A))

section NormalizedEndomorphism

variable {k A} {B : Type v} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- A same-world unitization map uses the factor-quotient map.
Its chain law is from the original epic normalization projection. -/
def normalizedRegularUnitizationMap (f : Unitization k A →ₐ[k] Unitization k B) :
    normalizedBComplex k (Unitization k A) ⟶ normalizedBComplex k (Unitization k B) := by
  have hOne : f.toLinearMap (1 : Unitization k A) = (1 : Unitization k B) := f.map_one
  let g (n : ℕ) : (normalizedBComplex k (Unitization k A)).X n ⟶
      (normalizedBComplex k (Unitization k B)).X n :=
    ModuleCat.ofHom
      (ModuleCat.Algebra.Hochschild.normalizedLevelLinearMap
        f.toLinearMap f.toLinearMap hOne n)
  exact ChainComplex.ofHom g (fun n => by
      let a := ModuleCat.Algebra.Hochschild.cyclicBComplexHom f.toNonUnitalAlgHom
      let κA := normalizedProjection k (Unitization k A)
      let κB := normalizedProjection k (Unitization k B)
      have hs (r : ℕ) : κA.f r ≫ g r = a.f r ≫ κB.f r := by
        dsimp only [g]
        rw [normalizedProjection_f, normalizedProjection_f,
          ModuleCat.Algebra.Hochschild.cyclicBComplexHom_f]
        apply ModuleCat.hom_ext
        exact ModuleCat.Algebra.Hochschild.normalizationLevelMap_naturality
          f.toLinearMap f.toLinearMap hOne r
      apply (cancel_epi (κA.f (n + 1))).1
      calc
        _ = a.f (n + 1) ≫ κB.f (n + 1) ≫
            (normalizedBComplex k (Unitization k B)).d (n + 1) n := by
          exact (Category.assoc _ _ _).symm.trans
            ((congrArg (fun z => z ≫ (normalizedBComplex k (Unitization k B)).d (n + 1) n)
              (hs (n + 1))).trans (Category.assoc _ _ _))
        _ = a.f (n + 1) ≫ (bComplex k (Unitization k B)).d (n + 1) n ≫ κB.f n := by
          exact congrArg (fun z => a.f (n + 1) ≫ z) (κB.comm (n + 1) n)
        _ = (bComplex k (Unitization k A)).d (n + 1) n ≫ a.f n ≫ κB.f n := by
          exact (Category.assoc _ _ _).symm.trans
            ((congrArg (fun z => z ≫ κB.f n) (a.comm (n + 1) n)).trans
              (Category.assoc _ _ _))
        _ = _ := by
          exact (congrArg (fun z => (bComplex k (Unitization k A)).d (n + 1) n ≫ z)
            (hs n).symm).trans
              ((Category.assoc _ _ _).symm.trans
                ((congrArg (fun z => z ≫ g n) (κA.comm (n + 1) n).symm).trans
                  (Category.assoc _ _ _))))

/-- The complete original chain-map square is retained. -/
@[reassoc]
theorem normalizedProjection_regularUnitizationMap
    (f : Unitization k A →ₐ[k] Unitization k B) :
    normalizedProjection k (Unitization k A) ≫ normalizedRegularUnitizationMap f =
      ModuleCat.Algebra.Hochschild.cyclicBComplexHom f.toNonUnitalAlgHom ≫
        normalizedProjection k (Unitization k B) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    normalizedProjection_f, normalizedProjection_f,
    ModuleCat.Algebra.Hochschild.cyclicBComplexHom_f]
  apply ModuleCat.hom_ext
  exact ModuleCat.Algebra.Hochschild.normalizationLevelMap_naturality
    f.toLinearMap f.toLinearMap f.map_one n

/-- The endomorphism is the same normalized map, in its original coefficient world. -/
abbrev normalizedRegularEndomorphism (f : Unitization k A →ₐ[k] Unitization k A) :=
  normalizedRegularUnitizationMap f

/-- The original endomorphism square forwards the one quotient-map construction. -/
@[reassoc]
theorem normalizedProjection_regularEndomorphism
    (f : Unitization k A →ₐ[k] Unitization k A) :
    normalizedProjection k (Unitization k A) ≫ normalizedRegularEndomorphism f =
      ModuleCat.Algebra.Hochschild.cyclicBComplexHom f.toNonUnitalAlgHom ≫
        normalizedProjection k (Unitization k A) :=
  normalizedProjection_regularUnitizationMap f

end NormalizedEndomorphism

/-- The reduced normalized model uses the induced scalar projector. -/
def unitizationNormalizedScalarProjector :
    normalizedBComplex k (Unitization k A) ⟶ normalizedBComplex k (Unitization k A) :=
  normalizedRegularEndomorphism (unitizationScalarProjector k A)

theorem unitizationNormalizedScalarProjector_idempotent :
    unitizationNormalizedScalarProjector k A ≫ unitizationNormalizedScalarProjector k A =
      unitizationNormalizedScalarProjector k A := by
  apply HomologicalComplex.hom_ext
  intro n
  let κ := normalizedProjection k (Unitization k A)
  have hs₀ : κ ≫ unitizationNormalizedScalarProjector k A =
      unitizationScalarComplexProjector k A ≫ κ :=
    normalizedProjection_regularEndomorphism (unitizationScalarProjector k A)
  have hs := HomologicalComplex.congr_hom hs₀ n
  have hp := HomologicalComplex.congr_hom
    (unitizationScalarComplexProjector_idempotent k A) n
  simp only [HomologicalComplex.comp_f] at hs hp ⊢
  apply (cancel_epi (κ.f n)).1
  change κ.f n ≫ ((unitizationNormalizedScalarProjector k A).f n ≫
      (unitizationNormalizedScalarProjector k A).f n) =
    κ.f n ≫ (unitizationNormalizedScalarProjector k A).f n
  calc
    _ = ((unitizationScalarComplexProjector k A).f n ≫ κ.f n) ≫
        (unitizationNormalizedScalarProjector k A).f n := by
      rw [← Category.assoc, hs]
    _ = (unitizationScalarComplexProjector k A).f n ≫
        ((unitizationScalarComplexProjector k A).f n ≫ κ.f n) := by
      rw [Category.assoc, hs]
    _ = (unitizationScalarComplexProjector k A).f n ≫ κ.f n := by
      rw [← Category.assoc, hp]
    _ = _ := hs.symm

/-- The original relative Hochschild complex is the augmentation-projector kernel. -/
abbrev unitizationRelativeComplex : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  kernel (unitizationScalarComplexProjector k A)

/-- The original reduced normalized complex is the normalized scalar-projector kernel. -/
abbrev unitizationReducedNormalizedComplex : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  kernel (unitizationNormalizedScalarProjector k A)

/-- The original normalization projection restricts by the native kernel-map API. -/
def unitizationRelativeNormalization :
    unitizationRelativeComplex k A ⟶ unitizationReducedNormalizedComplex k A :=
  kernel.map _ _ (normalizedProjection k (Unitization k A))
    (normalizedProjection k (Unitization k A))
    (normalizedProjection_regularEndomorphism (unitizationScalarProjector k A)).symm

/-- The restricted map retains the complete original normalization projection. -/
@[reassoc]
theorem unitizationRelativeNormalization_ι :
    unitizationRelativeNormalization k A ≫ kernel.ι (unitizationNormalizedScalarProjector k A) =
      kernel.ι (unitizationScalarComplexProjector k A) ≫
        normalizedProjection k (Unitization k A) :=
  kernel.lift_ι _ _ _

/-- Native quasi-isomorphisms are closed under the computed arrow retract. -/
instance unitizationRelativeNormalization_quasiIso :
    _root_.QuasiIso (unitizationRelativeNormalization k A) :=
  quasiIso_of_retractArrow (projectorKernelMapRetractArrow
    (unitizationScalarComplexProjector k A) (unitizationScalarComplexProjector_idempotent k A)
    (unitizationNormalizedScalarProjector k A)
    (unitizationNormalizedScalarProjector_idempotent k A)
    (normalizedProjection k (Unitization k A))
    (normalizedProjection_regularEndomorphism (unitizationScalarProjector k A)).symm)

end ModuleCat.Algebra.Hochschild.NonUnital
