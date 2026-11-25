/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Lie.ProjectiveFreeCover
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.Variance
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Projective Lie modules and the enveloping augmentation

Under `Module.Projective R L`, a Lie algebra with free underlying module
covers `L` by a split Lie algebra map. Enveloping maps and exterior coefficient
maps give a retract of the two Chevalley–Eilenberg augmentations after scalar
restriction to the ground ring. Quasi-isomorphism stability under retracts
and reflection by scalar restriction prove that the augmentation for `L`
is a quasi-isomorphism.

Linear Lie-map formulas allow independent carrier universes. The free-cover
maps are bundled as chain maps in the common `max u v` module category.
-/

@[expose] public section

noncomputable section

universe u v v' v''

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace ChevalleyEilenberg

attribute [local implicit_reducible] coefficientComplex HomologicalComplex.homologyFunctor
attribute [local instance] LieRing.ofAssociativeRing rightRegularLieRingModule rightRegularLieModule

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

/-- Exact native restriction from the original enveloping modules to the
original ground ring. Its carrier universe is the original CE universe. -/
abbrev envelopingGroundRestriction : ModuleCat.{max u v} U ⥤ ModuleCat.{max u v} R :=
  ModuleCat.restrictScalars (algebraMap R U)

/-- The original enveloping CE complex with only its scalar ring restricted. -/
abbrev envelopingGroundComplex : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ((envelopingGroundRestriction R L).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (envelopingComplex R L)

/-- The original trivial enveloping module after the same exact restriction. -/
abbrev envelopingGroundTrivialObject : ModuleCat.{max u v} R :=
  (envelopingGroundRestriction R L).obj (envelopingTrivialObject R L)

/-- The mapped augmentation, including the native comparison with
the single-object complex. -/
def envelopingGroundAugmentation :
    envelopingGroundComplex R L ⟶
      (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj
        (envelopingGroundTrivialObject R L) :=
  Functor.mapChainAugmentation (envelopingGroundRestriction R L)
    (envelopingAugmentation R L)

@[simp]
theorem envelopingGroundAugmentation_f_zero :
    (envelopingGroundAugmentation R L).f 0 =
      (envelopingGroundRestriction R L).map ((envelopingAugmentation R L).f 0) :=
  Functor.mapChainAugmentation_f_zero (envelopingGroundRestriction R L)
    (envelopingAugmentation R L)

section LieMaps

variable {L' : Type v'} [LieRing L'] [LieAlgebra R L']
  (f : L →ₗ⁅R⁆ L')

/-- The existing semilinear CE map becomes ground linear using
the original scalar-map law of the native UEA map. Its source and target
carrier universes are independent; this is a linear map, without an
assumption that its two bundled complexes belong to one category. -/
def envelopingGroundLieTermMap (n : ℕ) :
    (envelopingGroundComplex R L).X n →ₗ[R] (envelopingGroundComplex R L').X n where
  toFun := envelopingLieTermMap R L f n
  map_add' := (envelopingLieTermMap R L f n).map_add
  map_smul' r z := by
    letI : Module U ((envelopingComplex R L).X n) := ((envelopingComplex R L).X n).isModule
    letI : Module (UniversalEnvelopingAlgebra R L') ((envelopingComplex R L').X n) :=
      ((envelopingComplex R L').X n).isModule
    change envelopingLieTermMap R L f n ((algebraMap R U) r • (show (envelopingComplex R L).X n from z)) =
      (algebraMap R (UniversalEnvelopingAlgebra R L')) r •
        envelopingLieTermMap R L f n z
    let z₀ : (envelopingComplex R L).X n := z
    have h := (envelopingLieTermMap R L f n).map_smulₛₗ ((algebraMap R U) r) z₀
    exact h.trans (congrArg (fun a : UniversalEnvelopingAlgebra R L' =>
      @SMul.smul (UniversalEnvelopingAlgebra R L') ((envelopingComplex R L').X n)
        ((envelopingComplex R L').X n).isModule.toDistribMulAction.toMulAction.toSMul
          a (envelopingLieTermMap R L f n z₀))
            ((UniversalEnvelopingAlgebra.map R f).commutes r))


theorem envelopingGroundLieTermMap_tmul (n : ℕ) (a : ⋀[R]^n L)
    (b : regularCoefficients R L) :
    envelopingGroundLieTermMap R L f n (a ⊗ₜ[R] b) =
      exteriorPower.map n f.toLinearMap a ⊗ₜ[R] UniversalEnvelopingAlgebra.map R f b :=
  envelopingLieTermMap_tmul R L f n a b

/-- Ground restriction keeps the original differential compatibility. -/
theorem envelopingGroundLieTermMap_d_apply (n : ℕ)
    (z : (envelopingGroundComplex R L).X (n + 1)) :
    envelopingGroundLieTermMap R L f n
        (((envelopingGroundComplex R L).d (n + 1) n).hom z) =
      ((envelopingGroundComplex R L').d (n + 1) n).hom
        (envelopingGroundLieTermMap R L f (n + 1) z) :=
  envelopingLieTermMap_d_apply R L f n z

/-- The ground CE degree maps preserve composition across
independently sized Lie carriers. -/
theorem envelopingGroundLieTermMap_comp_apply
    {L'' : Type v''} [LieRing L''] [LieAlgebra R L'']
    (g : L' →ₗ⁅R⁆ L'') (n : ℕ) (z : (envelopingGroundComplex R L).X n) :
    envelopingGroundLieTermMap R L' g n (envelopingGroundLieTermMap R L f n z) =
      envelopingGroundLieTermMap R L (g.comp f) n z := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' =>
      exact (congrArg (envelopingGroundLieTermMap R L' g n)
        ((envelopingGroundLieTermMap R L f n).map_add z z')).trans
          (((envelopingGroundLieTermMap R L' g n).map_add _ _).trans
            ((congrArg₂ (fun x y => x + y) hz hz').trans
              ((envelopingGroundLieTermMap R L (g.comp f) n).map_add z z').symm))
  | tmul a b =>
      rw [envelopingGroundLieTermMap_tmul, envelopingGroundLieTermMap_tmul,
        envelopingGroundLieTermMap_tmul, LieHom.toLinearMap_comp,
        exteriorPower.map_comp, LinearMap.comp_apply,
        UniversalEnvelopingAlgebra.map_comp, AlgHom.comp_apply]

end LieMaps

/-- The original ground CE degree map sends an identity Lie map to
the identity on every tensor. -/
theorem envelopingGroundLieTermMap_id_apply (n : ℕ)
    (z : (envelopingGroundComplex R L).X n) :
    envelopingGroundLieTermMap R L (LieHom.id : L →ₗ⁅R⁆ L) n z = z := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' =>
      exact ((envelopingGroundLieTermMap R L (LieHom.id : L →ₗ⁅R⁆ L) n).map_add z z').trans
        (congrArg₂ (fun x y => x + y) hz hz')
  | tmul a b =>
      rw [envelopingGroundLieTermMap_tmul, UniversalEnvelopingAlgebra.map_id]
      change exteriorPower.map n (LinearMap.id : L →ₗ[R] L) a ⊗ₜ[R] b = a ⊗ₜ[R] b
      rw [exteriorPower.map_id, LinearMap.id_apply]

/-- Ground restriction of the trivial enveloping action has its original scalar carrier and
ordinary scalar multiplication. -/
def envelopingGroundTrivialScalarIso :
    envelopingGroundTrivialObject R L ≅ ModuleCat.of R (ULift.{max u v} R) :=
  (show envelopingGroundTrivialObject R L ≃ₗ[R] ULift.{max u v} R from
    { toFun := fun z => ULift.up z.down
      invFun := fun z => ULift.up z.down
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' r z := by
        apply ULift.ext
        change UniversalEnvelopingAlgebra.augmentation R L ((algebraMap R U) r) * z.down =
          r * z.down
        rw [(UniversalEnvelopingAlgebra.augmentation R L).commutes]
        rfl }).toModuleIso

@[simp]
theorem envelopingGroundTrivialScalarIso_hom_apply
    (z : envelopingGroundTrivialObject R L) :
    (envelopingGroundTrivialScalarIso R L).hom z = ULift.up z.down := rfl

@[simp]
theorem envelopingGroundTrivialScalarIso_inv_apply (z : ULift.{max u v} R) :
    (envelopingGroundTrivialScalarIso R L).inv z = ULift.up z.down := rfl

section Projective

variable [Module.Projective R L]

local notation "F" => LieAlgebra.ProjectiveFreeCover R L
local notation "p" => LieAlgebra.projectiveCoverProjection R L

/-- The CE chain map of the Lie inclusion into the free cover.
Both complexes lie in the original `max u v` ground-module category: the
free cover has universe `max u v`, so its CE world normalizes to that same world. -/
def envelopingGroundCoverInclusion :
    envelopingGroundComplex R L ⟶ envelopingGroundComplex R F where
  f n := ModuleCat.ofHom
    (X := (envelopingGroundComplex R L).X n)
    (Y := (envelopingGroundComplex R F).X n)
    (envelopingGroundLieTermMap R L (LieAlgebra.projectiveCoverInclusion R L) n)
  comm' a b hab := by
    change b + 1 = a at hab
    subst a
    apply ModuleCat.hom_ext
    ext z
    change ((envelopingGroundComplex R F).d (b + 1) b).hom
        (envelopingGroundLieTermMap R L (LieAlgebra.projectiveCoverInclusion R L) (b + 1) z) =
      envelopingGroundLieTermMap R L (LieAlgebra.projectiveCoverInclusion R L) b
        (((envelopingGroundComplex R L).d (b + 1) b).hom z)
    exact (envelopingGroundLieTermMap_d_apply R L (LieAlgebra.projectiveCoverInclusion R L) b z).symm

/-- The CE chain map of the Lie projection from the free cover. -/
def envelopingGroundCoverProjection :
    envelopingGroundComplex R F ⟶ envelopingGroundComplex R L where
  f n := ModuleCat.ofHom
    (X := (envelopingGroundComplex R F).X n)
    (Y := (envelopingGroundComplex R L).X n)
    (envelopingGroundLieTermMap R F p n)
  comm' a b hab := by
    change b + 1 = a at hab
    subst a
    apply ModuleCat.hom_ext
    ext z
    change ((envelopingGroundComplex R L).d (b + 1) b).hom
        (envelopingGroundLieTermMap R F p (b + 1) z) =
      envelopingGroundLieTermMap R F p b
        (((envelopingGroundComplex R F).d (b + 1) b).hom z)
    exact (envelopingGroundLieTermMap_d_apply R F p b z).symm

theorem envelopingGroundCoverInclusion_f_apply (n : ℕ)
    (z : (envelopingGroundComplex R L).X n) :
    ((envelopingGroundCoverInclusion R L).f n).hom z =
      envelopingGroundLieTermMap R L (LieAlgebra.projectiveCoverInclusion R L) n z := rfl

theorem envelopingGroundCoverProjection_f_apply (n : ℕ)
    (z : (envelopingGroundComplex R F).X n) :
    ((envelopingGroundCoverProjection R L).f n).hom z =
      envelopingGroundLieTermMap R F p n z := rfl

/-- The original CE chain maps retain the original strict Lie retraction. -/
@[simp]
theorem envelopingGroundCoverInclusion_projection :
    envelopingGroundCoverInclusion R L ≫ envelopingGroundCoverProjection R L =
      𝟙 (envelopingGroundComplex R L) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext z
  change envelopingGroundLieTermMap R F p n
    (envelopingGroundLieTermMap R L (LieAlgebra.projectiveCoverInclusion R L) n z) = z
  rw [envelopingGroundLieTermMap_comp_apply,
    LieAlgebra.projectiveCoverProjection_comp_inclusion,
    envelopingGroundLieTermMap_id_apply]

/-- The original ground CE complex is a strict native retract
of the free-cover CE complex. -/
def envelopingGroundComplexRetract :
    Retract (envelopingGroundComplex R L) (envelopingGroundComplex R F) where
  i := envelopingGroundCoverInclusion R L
  r := envelopingGroundCoverProjection R L
  retract := envelopingGroundCoverInclusion_projection R L

/-- Both trivial objects have the same original lifted scalar carrier;
their ground linear identity is a native isomorphism. -/
def envelopingGroundTrivialCoverIso :
    envelopingGroundTrivialObject R L ≅ envelopingGroundTrivialObject R F :=
  (envelopingGroundTrivialScalarIso R L).trans
    (envelopingGroundTrivialScalarIso R F).symm

@[simp]
theorem envelopingGroundTrivialCoverIso_hom_apply
    (z : envelopingGroundTrivialObject R L) :
    (envelopingGroundTrivialCoverIso R L).hom z = ULift.up z.down := rfl

@[simp]
theorem envelopingGroundTrivialCoverIso_inv_apply
    (z : envelopingGroundTrivialObject R F) :
    (envelopingGroundTrivialCoverIso R L).inv z = ULift.up z.down := rfl

/-- The Lie inclusion preserves the original CE augmentation,
using the native exterior degree-zero map and UEA augmentation naturality. -/
theorem envelopingGroundCoverInclusion_augmentation :
    envelopingGroundCoverInclusion R L ≫ envelopingGroundAugmentation R F =
      envelopingGroundAugmentation R L ≫
        (ChainComplex.single₀ (ModuleCat.{max u v} R)).map
          (envelopingGroundTrivialCoverIso R L).hom := by
  apply (ChainComplex.toSingle₀Equiv (envelopingGroundComplex R L)
    (envelopingGroundTrivialObject R F)).injective
  apply Subtype.ext
  change (envelopingGroundCoverInclusion R L).f 0 ≫
      (envelopingGroundAugmentation R F).f 0 =
    (envelopingGroundAugmentation R L).f 0 ≫
      ((ChainComplex.single₀ (ModuleCat.{max u v} R)).map
        (envelopingGroundTrivialCoverIso R L).hom).f 0
  rw [envelopingGroundAugmentation_f_zero, envelopingGroundAugmentation_f_zero,
    ChainComplex.single₀_map_f_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let A := ((envelopingGroundCoverInclusion R L).f 0 ≫
    (envelopingGroundRestriction R F).map ((envelopingAugmentation R F).f 0)).hom
  let B := ((envelopingGroundRestriction R L).map ((envelopingAugmentation R L).f 0) ≫
    (envelopingGroundTrivialCoverIso R L).hom).hom
  change A z = B z
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' =>
      exact (A.map_add _ _).trans ((congrArg₂ (fun x y => x + y) hz hz').trans (B.map_add _ _).symm)
  | tmul a b =>
      change envelopingAugmentationComponent R F
          (envelopingGroundLieTermMap R L (LieAlgebra.projectiveCoverInclusion R L) 0 (a ⊗ₜ[R] b)) =
        ULift.up (envelopingAugmentationComponent R L (a ⊗ₜ[R] b)).down
      rw [envelopingGroundLieTermMap_tmul, envelopingAugmentationComponent_apply,
        envelopingAugmentationComponent_apply, envelopingZeroEquiv_tmul,
        envelopingZeroEquiv_tmul, exteriorZeroCoordinates_map]
      apply ULift.ext
      have h := congrArg (fun e : U →ₐ[R] R => e b)
        (UniversalEnvelopingAlgebra.augmentation_naturality R (LieAlgebra.projectiveCoverInclusion R L))
      change UniversalEnvelopingAlgebra.augmentation R F
        (UniversalEnvelopingAlgebra.map R (LieAlgebra.projectiveCoverInclusion R L) b) =
          UniversalEnvelopingAlgebra.augmentation R L b at h
      simp only [map_smul, h]

/-- The Lie projection preserves the original CE augmentation. -/
theorem envelopingGroundCoverProjection_augmentation :
    envelopingGroundCoverProjection R L ≫ envelopingGroundAugmentation R L =
      envelopingGroundAugmentation R F ≫
        (ChainComplex.single₀ (ModuleCat.{max u v} R)).map
          (envelopingGroundTrivialCoverIso R L).inv := by
  apply (ChainComplex.toSingle₀Equiv (envelopingGroundComplex R F)
    (envelopingGroundTrivialObject R L)).injective
  apply Subtype.ext
  change (envelopingGroundCoverProjection R L).f 0 ≫
      (envelopingGroundAugmentation R L).f 0 =
    (envelopingGroundAugmentation R F).f 0 ≫
      ((ChainComplex.single₀ (ModuleCat.{max u v} R)).map
        (envelopingGroundTrivialCoverIso R L).inv).f 0
  rw [envelopingGroundAugmentation_f_zero, envelopingGroundAugmentation_f_zero,
    ChainComplex.single₀_map_f_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let A := ((envelopingGroundCoverProjection R L).f 0 ≫
    (envelopingGroundRestriction R L).map ((envelopingAugmentation R L).f 0)).hom
  let B := ((envelopingGroundRestriction R F).map ((envelopingAugmentation R F).f 0) ≫
    (envelopingGroundTrivialCoverIso R L).inv).hom
  change A z = B z
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' =>
      exact (A.map_add _ _).trans ((congrArg₂ (fun x y => x + y) hz hz').trans (B.map_add _ _).symm)
  | tmul a b =>
      change envelopingAugmentationComponent R L
          (envelopingGroundLieTermMap R F p 0 (a ⊗ₜ[R] b)) =
        ULift.up (envelopingAugmentationComponent R F (a ⊗ₜ[R] b)).down
      rw [envelopingGroundLieTermMap_tmul, envelopingAugmentationComponent_apply,
        envelopingAugmentationComponent_apply, envelopingZeroEquiv_tmul,
        envelopingZeroEquiv_tmul, exteriorZeroCoordinates_map]
      apply ULift.ext
      have h := congrArg (fun e : UniversalEnvelopingAlgebra R F →ₐ[R] R => e b)
        (UniversalEnvelopingAlgebra.augmentation_naturality R p)
      change UniversalEnvelopingAlgebra.augmentation R L
        (UniversalEnvelopingAlgebra.map R p b) =
          UniversalEnvelopingAlgebra.augmentation R F b at h
      simp only [map_smul, h]

/-- The original mapped augmentation is a native arrow retract
of the free-cover augmentation. Every map is the previously constructed
Lie/UEA/CE map, and the scalar maps are the original lifted identities. -/
def envelopingGroundAugmentationRetract :
    RetractArrow (envelopingGroundAugmentation R L) (envelopingGroundAugmentation R F) where
  i := Arrow.homMk (envelopingGroundCoverInclusion R L)
    ((ChainComplex.single₀ (ModuleCat.{max u v} R)).map
      (envelopingGroundTrivialCoverIso R L).hom)
    (envelopingGroundCoverInclusion_augmentation R L)
  r := Arrow.homMk (envelopingGroundCoverProjection R L)
    ((ChainComplex.single₀ (ModuleCat.{max u v} R)).map
      (envelopingGroundTrivialCoverIso R L).inv)
    (envelopingGroundCoverProjection_augmentation R L)
  retract := by
    apply Arrow.hom_ext
    · exact envelopingGroundCoverInclusion_projection R L
    · change (ChainComplex.single₀ (ModuleCat.{max u v} R)).map
          (envelopingGroundTrivialCoverIso R L).hom ≫
        (ChainComplex.single₀ (ModuleCat.{max u v} R)).map
          (envelopingGroundTrivialCoverIso R L).inv = 𝟙 _
      rw [← Functor.map_comp, Iso.hom_inv_id]
      exact (ChainComplex.single₀ (ModuleCat.{max u v} R)).map_id _

/-- Exact ground restriction of the constructed free-cover augmentation
is a quasi-isomorphism. No free instance on the original Lie module is used. -/
theorem envelopingGroundFreeCoverAugmentation_quasiIso :
    QuasiIso (envelopingGroundAugmentation R F) := by
  letI : QuasiIso (envelopingAugmentation R F) :=
    envelopingAugmentation_quasiIso_of_free R F
  exact Functor.mapChainAugmentation_quasiIso (envelopingGroundRestriction R F)
    (envelopingAugmentation R F)

/-- Native stability under arrow retracts earns the original projective
Lie algebra's ground augmentation quasi-isomorphism. -/
theorem envelopingGroundAugmentation_quasiIso_of_projective :
    QuasiIso (envelopingGroundAugmentation R L) := by
  letI : QuasiIso (envelopingGroundAugmentation R F) :=
    envelopingGroundFreeCoverAugmentation_quasiIso R L
  exact quasiIso_of_retractArrow (envelopingGroundAugmentationRetract R L)

/-- Faithful exact restriction reflects the quasi-isomorphism
into the original enveloping module category. The conclusion concerns
the original CE augmentation. -/
theorem envelopingAugmentation_quasiIso_of_projective :
    QuasiIso (envelopingAugmentation R L) := by
  letI : QuasiIso (envelopingGroundAugmentation R L) :=
    envelopingGroundAugmentation_quasiIso_of_projective R L
  let α :=
    (HomologicalComplex.singleMapHomologicalComplex (envelopingGroundRestriction R L)
      (ComplexShape.down ℕ) 0).hom.app (envelopingTrivialObject R L)
  letI : QuasiIso
      (((envelopingGroundRestriction R L).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (envelopingAugmentation R L) ≫ α) := by
    change QuasiIso (envelopingGroundAugmentation R L)
    infer_instance
  letI : QuasiIso
      (((envelopingGroundRestriction R L).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (envelopingAugmentation R L)) :=
    quasiIso_of_comp_right _ α
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (envelopingAugmentation R L) (envelopingGroundRestriction R L)).mp inferInstance

end Projective

end ChevalleyEilenberg
