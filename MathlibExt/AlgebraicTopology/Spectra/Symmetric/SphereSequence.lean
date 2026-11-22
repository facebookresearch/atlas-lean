/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Operad.FinBijTensorPower
public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.LaxBraidedMonoid
public import MathlibExt.CategoryTheory.Monoidal.PreservesColimits
public import MathlibExt.Topology.Category.PointedCGWH.SphereOne
public import MathlibExt.Topology.Category.PointedCGWH.Closed

/-!
# The commutative sphere sequence under Day convolution

The symmetric sphere sequence is the tensor-power functor on the one-sphere, with
bijections acting by permutations of smash factors. Its lax tensorator gives the
Day-convolution unit and multiplication, and the permutation compatibility proves
commutativity.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory
open CategoryTheory.MonoidalCategory
open CategoryTheory.Operad

universe u v

namespace PointedCGWH

/-- Symmetric sequences in pointed compactly generated weakly Hausdorff spaces. -/
abbrev SymmetricSequence :=
  CategoryTheory.MonoidalCategory.DayFunctor
    CategoryTheory.Operad.SmallFinBijGroupoid
    PointedCGWH.{u, v}

/-- The symmetric sphere sequence in pointed compactly generated weakly Hausdorff spaces. -/
noncomputable def sphereSequence : SymmetricSequence.{u, v} :=
  CategoryTheory.MonoidalCategory.DayFunctor.mk
    (CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctor
      PointedCGWH.sphereOne.{u, v})

/-- The value of the sphere sequence on a finite set is the corresponding smash power of
the circle. -/
theorem sphereSequence_obj
    (A : CategoryTheory.Operad.SmallFinBijGroupoid) :
    sphereSequence.{u, v}.functor.obj A =
      CategoryTheory.MonoidalCategory.TensorPower.tensorPowObj
        PointedCGWH.sphereOne.{u, v} A.of.len :=
  CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctor_obj _ _

/-- A bijection acts on the sphere sequence by the corresponding permutation of smash factors. -/
theorem sphereSequence_map
    {A B : CategoryTheory.Operad.SmallFinBijGroupoid} (f : A ⟶ B) :
    sphereSequence.{u, v}.functor.map f =
      (CategoryTheory.MonoidalCategory.SymmetricTensorPower.permutationIso
        PointedCGWH.sphereOne.{u, v}
        ((Equiv.ulift.symm : Fin A.of.len ≃ ULift (Fin A.of.len)).trans
          ((CategoryTheory.Operad.FinBijGroupoid.equivOfHom
            (CategoryTheory.Operad.smallFinBijEquivalence.functor.map f)).trans
              (Equiv.ulift :
                ULift (Fin B.of.len) ≃ Fin B.of.len)))).hom :=
  CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctor_map _ f

/-- The explicitly selected Day-convolution monoid structure on the sphere sequence. -/
@[instance_reducible]
noncomputable def sphereSequenceMonObj :
    MonObj sphereSequence.{u, v} := by
  let P := CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctor
    PointedCGWH.sphereOne.{u, v}
  let _ : P.Braided :=
    CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctorBraided
      PointedCGWH.sphereOne.{u, v}
  exact DayFunctor.monObjOfLaxMonoidal P

/-- The unit of the selected sphere-sequence monoid is the unit of the tensor-power functor. -/
theorem sphereSequence_one_app :
    let P := CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctor
      PointedCGWH.sphereOne.{u, v}
    letI : P.Braided :=
      CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctorBraided
        PointedCGWH.sphereOne.{u, v}
    DayFunctor.ν CategoryTheory.Operad.SmallFinBijGroupoid
          PointedCGWH.{u, v} ≫
        sphereSequenceMonObj.one.natTrans.app
          (𝟙_ CategoryTheory.Operad.SmallFinBijGroupoid) =
      Functor.LaxMonoidal.ε P := by
  let P := CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctor
    PointedCGWH.sphereOne.{u, v}
  let _ : P.Braided :=
    CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctorBraided
      PointedCGWH.sphereOne.{u, v}
  change DayFunctor.ν CategoryTheory.Operad.SmallFinBijGroupoid
        PointedCGWH.{u, v} ≫
      (DayFunctor.monObjOfLaxMonoidal P).one.natTrans.app
        (𝟙_ CategoryTheory.Operad.SmallFinBijGroupoid) =
    Functor.LaxMonoidal.ε P
  exact DayFunctor.monObjOfLaxMonoidal_one_app P

/-- The multiplication of the selected sphere-sequence monoid is induced by the tensor-power
functor's lax tensorator. -/
theorem sphereSequence_mul_app
    (A B : CategoryTheory.Operad.SmallFinBijGroupoid) :
    let P := CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctor
      PointedCGWH.sphereOne.{u, v}
    letI : P.Braided :=
      CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctorBraided
        PointedCGWH.sphereOne.{u, v}
    (DayFunctor.η sphereSequence sphereSequence).app (A, B) ≫
        sphereSequenceMonObj.mul.natTrans.app (A ⊗ B) =
      Functor.LaxMonoidal.μ P A B := by
  let P := CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctor
    PointedCGWH.sphereOne.{u, v}
  let _ : P.Braided :=
    CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctorBraided
      PointedCGWH.sphereOne.{u, v}
  change
    (DayFunctor.η (DayFunctor.mk P) (DayFunctor.mk P)).app (A, B) ≫
        (DayFunctor.monObjOfLaxMonoidal P).mul.natTrans.app (A ⊗ B) =
      Functor.LaxMonoidal.μ P A B
  exact DayFunctor.monObjOfLaxMonoidal_mul_app P A B

/-- The selected sphere-sequence monoid is commutative. -/
theorem sphereSequenceIsCommMonObj :
    @IsCommMonObj (SymmetricSequence.{u, v}) _ _ _
      sphereSequence sphereSequenceMonObj := by
  let P := CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctor
    PointedCGWH.sphereOne.{u, v}
  let _ : P.Braided :=
    CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctorBraided
      PointedCGWH.sphereOne.{u, v}
  change @IsCommMonObj (SymmetricSequence.{u, v}) _ _ _
    (DayFunctor.mk P) (DayFunctor.monObjOfLaxMonoidal P)
  exact DayFunctor.isCommMonObjOfLaxBraided P

/-- The sphere sequence bundled as a commutative monoid for Day convolution. -/
noncomputable def sphereSequenceCommMon :
    CommMon (SymmetricSequence.{u, v}) where
  X := sphereSequence
  mon := sphereSequenceMonObj
  comm := sphereSequenceIsCommMonObj

/-- Multiplication on the sphere sequence is invariant under the Day braiding. -/
theorem sphereSequence_mul_comm :
    (β_ sphereSequence.{u, v} sphereSequence).hom ≫
        sphereSequenceMonObj.mul =
      sphereSequenceMonObj.mul := by
  let P := CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctor
    PointedCGWH.sphereOne.{u, v}
  let _ : P.Braided :=
    CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctorBraided
      PointedCGWH.sphereOne.{u, v}
  change
    (β_ (DayFunctor.mk P) (DayFunctor.mk P)).hom ≫
        (DayFunctor.monObjOfLaxMonoidal P).mul =
      (DayFunctor.monObjOfLaxMonoidal P).mul
  exact DayFunctor.mul_comm P

/-- Componentwise sphere-sequence commutativity includes both the target braiding and the source
permutation. -/
theorem sphereSequence_mul_app_permutation
    (A B : CategoryTheory.Operad.SmallFinBijGroupoid) :
    let P := CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctor
      PointedCGWH.sphereOne.{u, v}
    letI : P.Braided :=
      CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctorBraided
        PointedCGWH.sphereOne.{u, v}
    (β_ (P.obj A) (P.obj B)).hom ≫
        Functor.LaxMonoidal.μ P B A ≫
        P.map (β_ B A).hom =
      Functor.LaxMonoidal.μ P A B := by
  let P := CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctor
    PointedCGWH.sphereOne.{u, v}
  let _ : P.Braided :=
    CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctorBraided
      PointedCGWH.sphereOne.{u, v}
  exact DayFunctor.mul_comm_app P A B

end PointedCGWH
