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
# Relative unitization chains and reduced normalization

Let `k` be a commutative ring and `A` a nonunital ground algebra. The scalar section and
augmentation of `A⁺ = k ⊕ A` act on every entry of the regular Hochschild complex. Their
composite is an idempotent scalar chain projector.

The relative complex is the kernel of this projector. The induced normalized scalar projector
has a corresponding reduced kernel, and normalization restricts to a chain map between the two
kernels. This restricted map is a quasi-isomorphism, obtained as an arrow retract of
unitization normalization. The scalar complex uses `ULift.{v} k` in the joint ring-algebra
carrier universe.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex
open scoped TensorProduct

universe u v

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The scalar section into a unitization with lifted scalar carrier.

The algebra map from `ULift.{v} k` to `A⁺` sends a lifted scalar to its scalar-coordinate
inclusion. -/
def unitizationGroundScalarSection :
    ULift.{v} k →ₐ[k] Unitization k A :=
  (unitizationScalarSection k A).comp (ULift.algEquiv (R := k) (A := k)).toAlgHom

/-- The unitization augmentation into a lifted scalar carrier.

The algebra map `A⁺ → ULift.{v} k` takes the first coordinate and lifts its value. -/
def unitizationGroundAugmentation :
    Unitization k A →ₐ[k] ULift.{v} k :=
  (ULift.algEquiv (R := k) (A := k)).symm.toAlgHom.comp (unitizationAugmentation k A)

/-- The value of the lifted unitization scalar section.

The scalar section sends `r : ULift.{v} k` to `Unitization.inl r.down`. -/
@[simp]
theorem unitizationGroundScalarSection_apply (r : ULift.{v} k) :
    unitizationGroundScalarSection k A r = Unitization.inl r.down := rfl

/-- The value of the lifted unitization augmentation.

The lifted augmentation sends `x ∈ A⁺` to `ULift.up x.fst`. -/
@[simp]
theorem unitizationGroundAugmentation_apply (x : Unitization k A) :
    unitizationGroundAugmentation k A x = ULift.up x.fst := rfl

/-- The retraction equation of the lifted unitization scalar section.

The lifted scalar section followed by the lifted augmentation is the identity on `ULift.{v}
k`. -/
theorem unitizationGroundScalarSection_augmentation :
    (unitizationGroundAugmentation k A).comp (unitizationGroundScalarSection k A) =
      AlgHom.id k (ULift.{v} k) := by
  ext x
  rfl

/-- The scalar projector from the lifted augmentation and section.

The lifted augmentation followed by the scalar section is the algebra projector `(r,a) ↦
(r,0)`. -/
theorem unitizationGroundAugmentation_section :
    (unitizationGroundScalarSection k A).comp (unitizationGroundAugmentation k A) =
      unitizationScalarProjector k A := by
  apply AlgHom.ext
  intro x
  rfl

/-- The lifted scalar inclusion on regular Hochschild complexes.

Apply the scalar section to the regular coefficient and each tail entry to obtain `b(ULift.{v}
k) → b(A⁺)`. -/
def unitizationScalarComplexInclusion :
    bComplex k (ULift.{v} k) ⟶ bComplex k (Unitization k A) :=
  ModuleCat.Algebra.Hochschild.cyclicBComplexHom
    (unitizationGroundScalarSection k A).toNonUnitalAlgHom

/-- The lifted scalar augmentation on regular Hochschild complexes.

Apply the lifted augmentation to each tensor entry to obtain `b(A⁺) → b(ULift.{v} k)`. -/
def unitizationScalarComplexAugmentation :
    bComplex k (Unitization k A) ⟶ bComplex k (ULift.{v} k) :=
  ModuleCat.Algebra.Hochschild.cyclicBComplexHom
    (unitizationGroundAugmentation k A).toNonUnitalAlgHom

/-- The scalar projector on regular unitization Hochschild chains.

The algebra projector `(r,a) ↦ (r,0)` acts on every tensor entry and defines a chain
endomorphism of `b(A⁺)`. -/
def unitizationScalarComplexProjector :
    bComplex k (Unitization k A) ⟶ bComplex k (Unitization k A) :=
  ModuleCat.Algebra.Hochschild.cyclicBComplexHom
    (unitizationScalarProjector k A).toNonUnitalAlgHom

/-- The chain retraction equation for lifted scalar inclusion.

The scalar chain inclusion followed by its augmentation is the identity on the lifted scalar
Hochschild complex. -/
@[reassoc]
theorem unitizationScalarComplexInclusion_augmentation :
    unitizationScalarComplexInclusion k A ≫ unitizationScalarComplexAugmentation k A = 𝟙 _ := by
  rw [unitizationScalarComplexInclusion, unitizationScalarComplexAugmentation,
    ← ModuleCat.Algebra.Hochschild.cyclicBComplexHom_comp]
  have h := congrArg AlgHom.toNonUnitalAlgHom
    (unitizationGroundScalarSection_augmentation k A)
  exact (congrArg ModuleCat.Algebra.Hochschild.cyclicBComplexHom h).trans
    (ModuleCat.Algebra.Hochschild.cyclicBComplexHom_id (k := k) (A := ULift.{v} k))

/-- The chain factorization of unitization scalar projection.

The scalar chain augmentation followed by its inclusion equals the scalar chain projector on
`b(A⁺)`. -/
@[reassoc]
theorem unitizationScalarComplexAugmentation_inclusion :
    unitizationScalarComplexAugmentation k A ≫ unitizationScalarComplexInclusion k A =
      unitizationScalarComplexProjector k A := by
  rw [unitizationScalarComplexInclusion, unitizationScalarComplexAugmentation,
    unitizationScalarComplexProjector,
    ← ModuleCat.Algebra.Hochschild.cyclicBComplexHom_comp]
  exact congrArg ModuleCat.Algebra.Hochschild.cyclicBComplexHom
    (congrArg AlgHom.toNonUnitalAlgHom (unitizationGroundAugmentation_section k A))

/-- Idempotence of the regular unitization scalar chain projector.

Composing the scalar chain projector with itself gives the same endomorphism. -/
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

/-- The normalized chain map of a unital map between unitizations.

A `k`-algebra homomorphism `A⁺ → B⁺` acts on the regular coefficient and quotient-tail
factors, inducing a map between their normalized Hochschild complexes. -/
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

/-- The normalization square for a map between unitizations.

The regular chain map induced by a unital homomorphism followed by normalization equals
normalization followed by the induced normalized chain map. -/
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

/-- The normalized endomorphism of a unitization algebra map.

A unital algebra endomorphism of `A⁺` induces the corresponding factorwise map on its
normalized Hochschild complex. -/
abbrev normalizedRegularEndomorphism (f : Unitization k A →ₐ[k] Unitization k A) :=
  normalizedRegularUnitizationMap f

/-- The normalization square for a unitization endomorphism.

The normalized projection commutes with the regular and normalized chain endomorphisms induced
by a unital map `A⁺ → A⁺`. -/
@[reassoc]
theorem normalizedProjection_regularEndomorphism
    (f : Unitization k A →ₐ[k] Unitization k A) :
    normalizedProjection k (Unitization k A) ≫ normalizedRegularEndomorphism f =
      ModuleCat.Algebra.Hochschild.cyclicBComplexHom f.toNonUnitalAlgHom ≫
        normalizedProjection k (Unitization k A) :=
  normalizedProjection_regularUnitizationMap f

end NormalizedEndomorphism

/-- The scalar projector on normalized unitization chains.

The unitization scalar algebra projector induces an endomorphism of the normalized regular
Hochschild complex. -/
def unitizationNormalizedScalarProjector :
    normalizedBComplex k (Unitization k A) ⟶ normalizedBComplex k (Unitization k A) :=
  normalizedRegularEndomorphism (unitizationScalarProjector k A)

/-- Idempotence of the normalized unitization scalar projector.

The normalized scalar chain projector is idempotent, as follows from the regular scalar
projector and its normalization square. -/
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

/-- The relative kernel of unitization Hochschild chains.

This chain complex is the kernel of the scalar projector on the regular Hochschild complex of
`A⁺`. -/
abbrev unitizationRelativeComplex : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  kernel (unitizationScalarComplexProjector k A)

/-- The reduced kernel of normalized unitization chains.

This chain complex is the kernel of the scalar projector on the normalized Hochschild complex
of `A⁺`. -/
abbrev unitizationReducedNormalizedComplex : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  kernel (unitizationNormalizedScalarProjector k A)

/-- Normalization restricted to relative unitization chains.

The normalization projection induces a chain map from the relative scalar-projector kernel to
the reduced normalized scalar-projector kernel. -/
def unitizationRelativeNormalization :
    unitizationRelativeComplex k A ⟶ unitizationReducedNormalizedComplex k A :=
  kernel.map _ _ (normalizedProjection k (Unitization k A))
    (normalizedProjection k (Unitization k A))
    (normalizedProjection_regularEndomorphism (unitizationScalarProjector k A)).symm

/-- The kernel-inclusion formula for relative normalization.

Relative normalization followed by the reduced kernel inclusion equals the relative kernel
inclusion followed by the full unitization normalization projection. -/
@[reassoc]
theorem unitizationRelativeNormalization_ι :
    unitizationRelativeNormalization k A ≫ kernel.ι (unitizationNormalizedScalarProjector k A) =
      kernel.ι (unitizationScalarComplexProjector k A) ≫
        normalizedProjection k (Unitization k A) :=
  kernel.lift_ι _ _ _

/-- The quasi-isomorphism of relative unitization normalization.

The restricted normalization map is a quasi-isomorphism, since the compatible idempotent
projectors exhibit it as an arrow retract of the full unitization normalization. -/
instance unitizationRelativeNormalization_quasiIso :
    _root_.QuasiIso (unitizationRelativeNormalization k A) :=
  quasiIso_of_retractArrow (projectorKernelMapRetractArrow
    (unitizationScalarComplexProjector k A) (unitizationScalarComplexProjector_idempotent k A)
    (unitizationNormalizedScalarProjector k A)
    (unitizationNormalizedScalarProjector_idempotent k A)
    (normalizedProjection k (Unitization k A))
    (normalizedProjection_regularEndomorphism (unitizationScalarProjector k A)).symm)

end ModuleCat.Algebra.Hochschild.NonUnital
