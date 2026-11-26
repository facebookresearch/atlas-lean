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
# Enveloping augmentation for projective Lie modules

Let `R` be a commutative ring and `L` an `R`-Lie algebra. Restriction along `R → U_R(L)` gives
a ground-module chain complex and augmentation. A Lie homomorphism acts on each ground term by
its exterior-power map and its induced enveloping-algebra map, with independent Lie-carrier
universes.

If the underlying `R`-module of `L` is projective, a Lie algebra `F` with free underlying
module has Lie maps `i : L → F` and `p : F → L` satisfying `p ∘ i = id`. Their chain maps and
the lifted-scalar trivial-module comparisons give an arrow retract of augmentations. The free-
cover augmentation is a quasi-isomorphism; retract stability and faithful exact scalar
restriction imply that the augmentation for `L` is also a quasi-isomorphism.

Reference: Weibel, *An Introduction to Homological Algebra*, Chapter 7.
-/

@[expose] public section

noncomputable section

universe u v v' v''

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace ChevalleyEilenberg

attribute [local implicit_reducible] coefficientComplex
attribute [local instance] LieRing.ofAssociativeRing rightRegularLieRingModule rightRegularLieModule

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

/-- Ground-scalar restriction of enveloping modules.

Restricting along `R → U_R(L)` sends enveloping modules in carrier universe `max u v` to
`R`-modules in the same universe. -/
abbrev envelopingGroundRestriction : ModuleCat.{max u v} U ⥤ ModuleCat.{max u v} R :=
  ModuleCat.restrictScalars (algebraMap R U)

/-- The enveloping chain complex over the ground ring.

This is the Chevalley–Eilenberg enveloping complex with its scalar action restricted along `R
→ U_R(L)` in each degree. -/
abbrev envelopingGroundComplex : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ((envelopingGroundRestriction R L).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (envelopingComplex R L)

/-- The ground module of trivial enveloping coefficients.

The trivial enveloping module is restricted to an `R`-module through the scalar inclusion. -/
abbrev envelopingGroundTrivialObject : ModuleCat.{max u v} R :=
  (envelopingGroundRestriction R L).obj (envelopingTrivialObject R L)

/-- The ground-scalar enveloping augmentation.

Applying scalar restriction to the enveloping augmentation, with the comparison to a single-
object complex, gives a chain map to the restricted trivial module concentrated in degree
zero. -/
def envelopingGroundAugmentation :
    envelopingGroundComplex R L ⟶
      (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj
        (envelopingGroundTrivialObject R L) :=
  Functor.mapChainAugmentation (envelopingGroundRestriction R L)
    (envelopingAugmentation R L)

/-- The degree-zero map of the ground enveloping augmentation.

The degree-zero component is scalar restriction of the degree-zero enveloping augmentation. -/
@[simp]
theorem envelopingGroundAugmentation_f_zero :
    (envelopingGroundAugmentation R L).f 0 =
      (envelopingGroundRestriction R L).map ((envelopingAugmentation R L).f 0) :=
  Functor.mapChainAugmentation_f_zero (envelopingGroundRestriction R L)
    (envelopingAugmentation R L)

section LieMaps

variable {L' : Type v'} [LieRing L'] [LieAlgebra R L']
  (f : L →ₗ⁅R⁆ L')

/-- The ground-linear chain-term map of a Lie homomorphism.

For `f : L → L'`, the enveloping semilinear term map restricts to an `R`-linear map between
the ground chain terms. The carrier universes of `L` and `L'` may differ. -/
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


/-- The tensor formula for a ground Lie-induced term map.

For `f : L → L'`, the degree-`n` map sends `a ⊗ b` to `⋀ⁿ(f)(a) ⊗ U(f)(b)`, retaining
exterior-first tensor order. -/
theorem envelopingGroundLieTermMap_tmul (n : ℕ) (a : ⋀[R]^n L)
    (b : regularCoefficients R L) :
    envelopingGroundLieTermMap R L f n (a ⊗ₜ[R] b) =
      exteriorPower.map n f.toLinearMap a ⊗ₜ[R] UniversalEnvelopingAlgebra.map R f b :=
  envelopingLieTermMap_tmul R L f n a b

/-- Differential compatibility of a ground Lie-induced term map.

The degreewise map induced by `f : L → L'` commutes with the successor enveloping chain
differentials after ground-scalar restriction. -/
theorem envelopingGroundLieTermMap_d_apply (n : ℕ)
    (z : (envelopingGroundComplex R L).X (n + 1)) :
    envelopingGroundLieTermMap R L f n
        (((envelopingGroundComplex R L).d (n + 1) n).hom z) =
      ((envelopingGroundComplex R L').d (n + 1) n).hom
        (envelopingGroundLieTermMap R L f (n + 1) z) :=
  envelopingLieTermMap_d_apply R L f n z

/-- Composition of ground Lie-induced term maps.

For `L → L' → L''`, composing the ground term maps equals the term map of the composite Lie
homomorphism, even when the three carrier universes differ. -/
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

/-- The ground term map of an identity Lie homomorphism.

The identity of `L` induces the identity on every ground enveloping chain term. -/
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

/-- The scalar coordinates of restricted trivial enveloping coefficients.

The ground restriction of the trivial enveloping module is isomorphic to the lifted regular
module `ULift.{max u v} R`. The isomorphism and its inverse retain the down value of a lifted
scalar. -/
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

/-- The forward scalar formula for restricted trivial coefficients.

The ground trivial-module comparison sends a lifted scalar `z` to `ULift.up z.down` in the
regular ground module. -/
@[simp]
theorem envelopingGroundTrivialScalarIso_hom_apply
    (z : envelopingGroundTrivialObject R L) :
    (envelopingGroundTrivialScalarIso R L).hom z = ULift.up z.down := rfl

/-- The inverse scalar formula for restricted trivial coefficients.

The inverse comparison sends a lifted ground scalar `z` to the trivial-module element
`ULift.up z.down`. -/
@[simp]
theorem envelopingGroundTrivialScalarIso_inv_apply (z : ULift.{max u v} R) :
    (envelopingGroundTrivialScalarIso R L).inv z = ULift.up z.down := rfl

section Projective

variable [Module.Projective R L]

local notation "F" => LieAlgebra.ProjectiveFreeCover R L
local notation "p" => LieAlgebra.projectiveCoverProjection R L

/-- The chain inclusion into a projective Lie free cover.

If `Module.Projective R L`, the Lie inclusion `L → F` into the free-module cover induces a
chain map of ground enveloping complexes in the common universe `max u v`. -/
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

/-- The chain projection from a projective Lie free cover.

For a projective underlying Lie module, the Lie projection `F → L` from the free-module cover
induces a chain map of ground enveloping complexes. -/
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

/-- The component formula for the free-cover chain inclusion.

The degree-`n` component is the ground term map of the Lie inclusion `L → F`. -/
theorem envelopingGroundCoverInclusion_f_apply (n : ℕ)
    (z : (envelopingGroundComplex R L).X n) :
    ((envelopingGroundCoverInclusion R L).f n).hom z =
      envelopingGroundLieTermMap R L (LieAlgebra.projectiveCoverInclusion R L) n z := rfl

/-- The component formula for the free-cover chain projection.

The degree-`n` component is the ground term map of the Lie projection `F → L`. -/
theorem envelopingGroundCoverProjection_f_apply (n : ℕ)
    (z : (envelopingGroundComplex R F).X n) :
    ((envelopingGroundCoverProjection R L).f n).hom z =
      envelopingGroundLieTermMap R F p n z := rfl

/-- The chain retraction equation for a projective Lie free cover.

The chain inclusion of `L` into `F` followed by the chain projection back to `L` is the
identity on the ground enveloping complex. -/
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

/-- The ground enveloping complex as a free-cover retract.

For `Module.Projective R L`, the Lie inclusion and projection exhibit the ground enveloping
complex of `L` as a retract of that of its free-module cover `F`. -/
def envelopingGroundComplexRetract :
    Retract (envelopingGroundComplex R L) (envelopingGroundComplex R F) where
  i := envelopingGroundCoverInclusion R L
  r := envelopingGroundCoverProjection R L
  retract := envelopingGroundCoverInclusion_projection R L

/-- The trivial-coefficient comparison for a projective Lie free cover.

The ground trivial modules of `L` and its free cover `F` are isomorphic through their common
lifted regular scalar module. -/
def envelopingGroundTrivialCoverIso :
    envelopingGroundTrivialObject R L ≅ envelopingGroundTrivialObject R F :=
  (envelopingGroundTrivialScalarIso R L).trans
    (envelopingGroundTrivialScalarIso R F).symm

/-- The forward scalar value in the free-cover trivial comparison.

The trivial-coefficient comparison from `L` to its free cover sends `z` to `ULift.up z.down`. -/
@[simp]
theorem envelopingGroundTrivialCoverIso_hom_apply
    (z : envelopingGroundTrivialObject R L) :
    (envelopingGroundTrivialCoverIso R L).hom z = ULift.up z.down := rfl

/-- The inverse scalar value in the free-cover trivial comparison.

The inverse trivial-coefficient comparison sends `z` to `ULift.up z.down`. -/
@[simp]
theorem envelopingGroundTrivialCoverIso_inv_apply
    (z : envelopingGroundTrivialObject R F) :
    (envelopingGroundTrivialCoverIso R L).inv z = ULift.up z.down := rfl

/-- Augmentation compatibility of the free-cover inclusion.

The chain inclusion into the free cover followed by its augmentation equals the augmentation
for `L` followed by the trivial-coefficient comparison in degree zero. -/
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

/-- Augmentation compatibility of the free-cover projection.

The chain projection from the free cover followed by the augmentation for `L` equals the free-
cover augmentation followed by the inverse trivial-coefficient comparison. -/
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

/-- The enveloping augmentation as a free-cover arrow retract.

For a projective underlying Lie module, the chain inclusion, chain projection, and trivial-
coefficient comparison exhibit the ground augmentation for `L` as an arrow retract of the
free-cover augmentation. -/
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

/-- The quasi-isomorphism of the ground free-cover augmentation.

For the free-module Lie cover of a projective `R`-module `L`, the ground-restricted enveloping
augmentation is a quasi-isomorphism. -/
theorem envelopingGroundFreeCoverAugmentation_quasiIso :
    QuasiIso (envelopingGroundAugmentation R F) := by
  letI : QuasiIso (envelopingAugmentation R F) :=
    envelopingAugmentation_quasiIso_of_free R F
  exact Functor.mapChainAugmentation_quasiIso (envelopingGroundRestriction R F)
    (envelopingAugmentation R F)

/-- The ground augmentation quasi-isomorphism for a projective Lie module.

If `Module.Projective R L`, the ground enveloping augmentation for `L` is a quasi-isomorphism,
as follows from its arrow retract of the free-cover augmentation. -/
theorem envelopingGroundAugmentation_quasiIso_of_projective :
    QuasiIso (envelopingGroundAugmentation R L) := by
  letI : QuasiIso (envelopingGroundAugmentation R F) :=
    envelopingGroundFreeCoverAugmentation_quasiIso R L
  exact quasiIso_of_retractArrow (envelopingGroundAugmentationRetract R L)

/-- The enveloping augmentation quasi-isomorphism for a projective Lie module.

If the underlying `R`-module of `L` is projective, the Chevalley–Eilenberg augmentation to the
trivial `U_R(L)`-module is a quasi-isomorphism in the enveloping-module category. -/
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
