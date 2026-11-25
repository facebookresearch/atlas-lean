/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Category.FGProjectiveCat.Basic
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.CategoryTheory.Equivalence

/-!
# Finite projective modules in independent universes

For a ring in `Type u`, finitely generated modules are `u`-small. Shrinking
finite projective modules therefore gives an equivalence from carrier universe
`max u v` to carrier universe `u`. Its inverse is `ULift`, and both functors
conjugate the original linear maps by the corresponding linear equivalences.
The unit and counit retain these same coordinates. Both functors are additive
and preserve the canonical split exact structures.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace FGProjectiveCat
namespace UniverseEquivalence

variable (R : Type u) [Ring R]

/-- The ring-universe copy of a finite projective module. -/
def shrinkObject (M : FGProjectiveCat.{max u v} R) : FGProjectiveCat.{u} R := by
  letI : Small.{u} M := Module.Finite.small R M
  exact FGProjectiveCat.of (R := R) (Shrink.{u} M)

/-- The linear equivalence from the shrunken module to its original carrier. -/
def shrinkLinearEquiv (M : FGProjectiveCat.{max u v} R) :
    shrinkObject.{u, v} R M ≃ₗ[R] M := by
  letI : Small.{u} M := Module.Finite.small R M
  change Shrink.{u} M ≃ₗ[R] M
  exact Shrink.linearEquiv R M

/-- Lift a ring-universe finite projective module to carrier universe `max u v`. -/
def liftObject (M : FGProjectiveCat.{u} R) : FGProjectiveCat.{max u v} R :=
  FGProjectiveCat.of (R := R) (ULift.{v} M)

/-- The linear equivalence given by `ULift.down` on the lifted module. -/
def liftLinearEquiv (M : FGProjectiveCat.{u} R) :
    liftObject.{u, v} R M ≃ₗ[R] M :=
  ULift.moduleEquiv

/-- Shrinking acts on each original linear map by conjugation. -/
def shrinkFunctor : FGProjectiveCat.{max u v} R ⥤ FGProjectiveCat.{u} R where
  obj := shrinkObject.{u, v} R
  map {M N} f := FGProjectiveCat.ofHom
    ((shrinkLinearEquiv.{u, v} R N).symm.toLinearMap.comp
      (f.hom.hom.comp (shrinkLinearEquiv.{u, v} R M).toLinearMap))
  map_id M := by
    apply FGProjectiveCat.hom_ext
    apply LinearMap.ext
    intro x
    change (shrinkLinearEquiv.{u, v} R M).symm (shrinkLinearEquiv.{u, v} R M x) = x
    exact (shrinkLinearEquiv.{u, v} R M).symm_apply_apply x
  map_comp {M N P} f g := by
    apply FGProjectiveCat.hom_ext
    apply LinearMap.ext
    intro x
    change
      (shrinkLinearEquiv.{u, v} R P).symm (g.hom.hom (f.hom.hom (shrinkLinearEquiv.{u, v} R M x))) =
        (shrinkLinearEquiv.{u, v} R P).symm (g.hom.hom
          (shrinkLinearEquiv.{u, v} R N ((shrinkLinearEquiv.{u, v} R N).symm
            (f.hom.hom (shrinkLinearEquiv.{u, v} R M x)))))
    rw [(shrinkLinearEquiv.{u, v} R N).apply_symm_apply]

/-- The whole linear-map formula for the shrinking functor. -/
@[simp]
theorem shrinkFunctor_map_apply {M N : FGProjectiveCat.{max u v} R}
    (f : M ⟶ N) (x : shrinkObject.{u, v} R M) :
    ((shrinkFunctor.{u, v} R).map f).hom.hom x =
      (shrinkLinearEquiv.{u, v} R N).symm (f.hom.hom (shrinkLinearEquiv.{u, v} R M x)) :=
  rfl

/-- The existing module universe-lift functor, restricted to finite projectives. -/
def liftFunctor : FGProjectiveCat.{u} R ⥤ FGProjectiveCat.{max u v} R :=
  ObjectProperty.lift (ModuleCat.isFGProjective.{max u v} R)
    ((ModuleCat.isFGProjective.{u} R).ι ⋙ ModuleCat.uliftFunctor.{v, u} R)
    (by
      intro M
      change Module.Finite R (ULift.{v} M) ∧ Module.Projective R (ULift.{v} M)
      exact ⟨inferInstance, inferInstance⟩)

/-- The whole linear-map formula for the lifting functor. -/
@[simp]
theorem liftFunctor_map_apply {M N : FGProjectiveCat.{u} R}
    (f : M ⟶ N) (x : liftObject.{u, v} R M) :
    ((liftFunctor.{u, v} R).map f).hom.hom x =
      (liftLinearEquiv.{u, v} R N).symm
        (f.hom.hom (liftLinearEquiv.{u, v} R M x)) :=
  rfl

/-- Shrinking preserves addition of original linear maps. -/
instance shrinkFunctor_additive : (shrinkFunctor.{u, v} R).Additive where
  map_add {M N} {f g} := by
    apply FGProjectiveCat.hom_ext
    apply LinearMap.ext
    intro x
    change
      (shrinkLinearEquiv.{u, v} R N).symm
          (f.hom.hom (shrinkLinearEquiv.{u, v} R M x) +
              g.hom.hom (shrinkLinearEquiv.{u, v} R M x)) =
        (shrinkLinearEquiv.{u, v} R N).symm (f.hom.hom (shrinkLinearEquiv.{u, v} R M x)) +
          (shrinkLinearEquiv.{u, v} R N).symm (g.hom.hom (shrinkLinearEquiv.{u, v} R M x))
    exact (shrinkLinearEquiv.{u, v} R N).symm.map_add _ _

/-- Lifting inherits additivity from the module lift and full-subcategory lift. -/
instance liftFunctor_additive : (liftFunctor.{u, v} R).Additive := by
  dsimp only [liftFunctor]
  infer_instance

/-- The actual shrink-then-lift unit, on the original module carriers. -/
def unitIso : 𝟭 (FGProjectiveCat.{max u v} R) ≅
    shrinkFunctor.{u, v} R ⋙ liftFunctor.{u, v} R :=
  NatIso.ofComponents
    (fun M => (ModuleCat.isFGProjective.{max u v} R).isoMk
      (_root_.LinearEquiv.toModuleIso
        ((shrinkLinearEquiv.{u, v} R M).symm.trans
          (liftLinearEquiv.{u, v} R (shrinkObject.{u, v} R M)).symm)))
    (by
      intro M N f
      apply FGProjectiveCat.hom_ext
      apply LinearMap.ext
      intro x
      change
        (liftLinearEquiv.{u, v} R (shrinkObject.{u, v} R N)).symm
            ((shrinkLinearEquiv.{u, v} R N).symm (f.hom.hom x)) =
          (liftLinearEquiv.{u, v} R (shrinkObject.{u, v} R N)).symm
            ((shrinkLinearEquiv.{u, v} R N).symm (f.hom.hom
              (shrinkLinearEquiv.{u, v} R M
                (liftLinearEquiv.{u, v} R (shrinkObject.{u, v} R M)
                  ((liftLinearEquiv.{u, v} R (shrinkObject.{u, v} R M)).symm
                    ((shrinkLinearEquiv.{u, v} R M).symm x))))))
      simp only [LinearEquiv.apply_symm_apply])

/-- The actual lift-then-shrink counit, on the original module carriers. -/
def counitIso : liftFunctor.{u, v} R ⋙ shrinkFunctor.{u, v} R ≅ 𝟭 (FGProjectiveCat.{u} R) :=
  NatIso.ofComponents
    (fun M => (ModuleCat.isFGProjective.{u} R).isoMk
      (_root_.LinearEquiv.toModuleIso
        ((shrinkLinearEquiv.{u, v} R (liftObject.{u, v} R M)).trans
          (liftLinearEquiv.{u, v} R M))))
    (by
      intro M N f
      apply FGProjectiveCat.hom_ext
      apply LinearMap.ext
      intro x
      change
        liftLinearEquiv.{u, v} R N
            (shrinkLinearEquiv.{u, v} R (liftObject.{u, v} R N)
              ((shrinkLinearEquiv.{u, v} R (liftObject.{u, v} R N)).symm
                ((liftLinearEquiv.{u, v} R N).symm
                  (f.hom.hom (liftLinearEquiv.{u, v} R M
                    (shrinkLinearEquiv.{u, v} R (liftObject.{u, v} R M) x)))))) =
          f.hom.hom (liftLinearEquiv.{u, v} R M
            (shrinkLinearEquiv.{u, v} R (liftObject.{u, v} R M) x))
      simp only [LinearEquiv.apply_symm_apply])

end UniverseEquivalence

variable (R : Type u) [Ring R]

/-- Exact equivalence from carrier universe `max u v` to the ring universe.

The regular module is present in the source as its `ULift` and in the target as
`R` itself. The forward functor shrinks every finite projective, and the inverse
lifts it back; neither direction changes the ring or the original linear maps. -/
def universeEquivalence : FGProjectiveCat.{max u v} R ≌ FGProjectiveCat.{u} R where
  functor := UniverseEquivalence.shrinkFunctor.{u, v} R
  inverse := UniverseEquivalence.liftFunctor.{u, v} R
  unitIso := UniverseEquivalence.unitIso.{u, v} R
  counitIso := UniverseEquivalence.counitIso.{u, v} R
  functor_unitIso_comp M := by
    apply FGProjectiveCat.hom_ext
    apply LinearMap.ext
    intro x
    change
      UniverseEquivalence.liftLinearEquiv.{u, v} R (UniverseEquivalence.shrinkObject.{u, v} R M)
          (UniverseEquivalence.shrinkLinearEquiv.{u, v} R
            (UniverseEquivalence.liftObject.{u, v} R (UniverseEquivalence.shrinkObject.{u, v} R M))
            ((UniverseEquivalence.shrinkLinearEquiv.{u, v} R
              (UniverseEquivalence.liftObject.{u, v} R
                  (UniverseEquivalence.shrinkObject.{u, v} R M))).symm
              ((UniverseEquivalence.liftLinearEquiv.{u, v} R
                (UniverseEquivalence.shrinkObject.{u, v} R M)).symm
                ((UniverseEquivalence.shrinkLinearEquiv.{u, v} R M).symm
                  (UniverseEquivalence.shrinkLinearEquiv.{u, v} R M x))))) = x
    simp only [LinearEquiv.apply_symm_apply]
    exact (UniverseEquivalence.shrinkLinearEquiv.{u, v} R M).symm_apply_apply x

/-- The forward direction of universe resizing is additive. -/
instance universeEquivalence_functor_additive :
    (universeEquivalence.{u, v} R).functor.Additive := by
  change (UniverseEquivalence.shrinkFunctor.{u, v} R).Additive
  infer_instance

/-- The inverse direction of universe resizing is additive. -/
instance universeEquivalence_inverse_additive :
    (universeEquivalence.{u, v} R).inverse.Additive := by
  change (UniverseEquivalence.liftFunctor.{u, v} R).Additive
  infer_instance

/-- The forward direction preserves the canonical split exact structure. -/
instance universeEquivalence_functor_isExact : (universeEquivalence.{u, v} R).functor.IsExact :=
  ExactCategory.isExact_splitSource _

/-- The inverse direction preserves the canonical split exact structure. -/
instance universeEquivalence_inverse_isExact : (universeEquivalence.{u, v} R).inverse.IsExact :=
  ExactCategory.isExact_splitSource _

/-- The unit sends every original element to its lifted shrink coordinate. -/
@[simp]
theorem universeEquivalence_unit_hom_apply
    (M : FGProjectiveCat.{max u v} R) (x : M) :
    DFunLike.coe (F := M →ₗ[R] (universeEquivalence.{u, v} R).inverse.obj
        ((universeEquivalence.{u, v} R).functor.obj M))
      (α := M) (β := fun _ => (universeEquivalence.{u, v} R).inverse.obj
          ((universeEquivalence.{u, v} R).functor.obj M))
      ((universeEquivalence.{u, v} R).unitIso.hom.app M).hom.hom x =
      (UniverseEquivalence.liftLinearEquiv.{u, v} R
        (UniverseEquivalence.shrinkObject.{u, v} R M)).symm
        ((UniverseEquivalence.shrinkLinearEquiv.{u, v} R M).symm x) :=
  rfl

/-- The inverse unit recovers every original element from its lifted shrink coordinate. -/
@[simp]
theorem universeEquivalence_unit_inv_apply (M : FGProjectiveCat.{max u v} R)
    (x : (universeEquivalence.{u, v} R).inverse.obj
      ((universeEquivalence.{u, v} R).functor.obj M)) :
    DFunLike.coe (F := (universeEquivalence.{u, v} R).inverse.obj
        ((universeEquivalence.{u, v} R).functor.obj M) →ₗ[R] M)
      (α := (universeEquivalence.{u, v} R).inverse.obj
          ((universeEquivalence.{u, v} R).functor.obj M)) (β := fun _ => M)
      ((universeEquivalence.{u, v} R).unitIso.inv.app M).hom.hom x =
      UniverseEquivalence.shrinkLinearEquiv.{u, v} R M
        (UniverseEquivalence.liftLinearEquiv.{u, v} R
          (UniverseEquivalence.shrinkObject.{u, v} R M) x) :=
  rfl

/-- The counit recovers the original small module from its shrunken lift. -/
@[simp]
theorem universeEquivalence_counit_hom_apply (M : FGProjectiveCat.{u} R)
    (x : (universeEquivalence.{u, v} R).functor.obj
      ((universeEquivalence.{u, v} R).inverse.obj M)) :
    DFunLike.coe (F := (universeEquivalence.{u, v} R).functor.obj
        ((universeEquivalence.{u, v} R).inverse.obj M) →ₗ[R] M)
      (α := (universeEquivalence.{u, v} R).functor.obj
          ((universeEquivalence.{u, v} R).inverse.obj M)) (β := fun _ => M)
      ((universeEquivalence.{u, v} R).counitIso.hom.app M).hom.hom x =
      UniverseEquivalence.liftLinearEquiv.{u, v} R M
        (UniverseEquivalence.shrinkLinearEquiv.{u, v} R
          (UniverseEquivalence.liftObject.{u, v} R M) x) :=
  rfl

/-- The inverse counit sends each original small element to its shrink-of-lift coordinate. -/
@[simp]
theorem universeEquivalence_counit_inv_apply (M : FGProjectiveCat.{u} R) (x : M) :
    DFunLike.coe (F := M →ₗ[R] (universeEquivalence.{u, v} R).functor.obj
        ((universeEquivalence.{u, v} R).inverse.obj M))
      (α := M) (β := fun _ => (universeEquivalence.{u, v} R).functor.obj
          ((universeEquivalence.{u, v} R).inverse.obj M))
      ((universeEquivalence.{u, v} R).counitIso.inv.app M).hom.hom x =
      (UniverseEquivalence.shrinkLinearEquiv.{u, v} R
        (UniverseEquivalence.liftObject.{u, v} R M)).symm
        ((UniverseEquivalence.liftLinearEquiv.{u, v} R M).symm x) :=
  rfl

end FGProjectiveCat
