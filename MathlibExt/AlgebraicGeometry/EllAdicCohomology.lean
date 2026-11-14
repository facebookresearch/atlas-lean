/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The continuous coefficient sheaf and its pushforward are adapted from:

`Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean` (Mathlib):
Copyright (c) 2026 Christian Merten. All rights reserved.
Authors: Jiedong Jiang, Christian Merten.

`Mathlib/AlgebraicGeometry/Sites/ConstantSheaf.lean` (Mathlib):
Copyright (c) 2026 Christian Merten. All rights reserved.
Authors: Christian Merten.

These files are from leanprover-community/mathlib4 at commit
56a005855ea17e0b0958f73ec801ae140b0a1679 and are licensed under the Apache
License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).

The rational scalar-extension pattern is adapted from `Weil/Definitions.lean`
in `AxiomMath/Weil` at commit 27cdb2049be62ee2911429b47f54774078450e32,
distributed under the Apache License, Version 2.0. That file contains no
individual copyright or author notice.

Modification notice: generalized continuous coefficient maps, specified
integral scalar multiplication by the actual coefficient-induced cohomology
map, and used Mathlib's pro-étale cohomology carrier for rationalization.
-/

module

public import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

@[expose] public noncomputable section

universe u

/-!
# Coefficient maps and rational ℓ-adic cohomology

Mathlib's `Scheme.EllAdicCohomology` is ordinary pro-étale cohomology with
integral `ℤ_[ℓ]` coefficients. The coefficient action here starts with
pointwise multiplication on continuous maps, uses the pushforward from
`Scheme.ellAdicSheaf` and the lift from `Scheme.EllAdicCohomology`, and
applies `Sheaf.H.map`.

`CanonicalEllAdicModule` specifies a module structure whose scalar action
equals that coefficient-induced map on every element of the existing group.
With this explicit parameter, `RationalCohomology` is the tensor product
`ℚ_[ℓ] ⊗[ℤ_[ℓ]] X.EllAdicCohomology ℓ n`.

## References

* B. Bhatt and P. Scholze, *The pro-étale topology for schemes* (2015),
  §6.8; Definition 6.8.1 is the source cited by Mathlib's coefficient sheaf.
* The Mathlib and Axiom source interfaces are credited with exact revisions
  in the adaptation notice above.
-/

namespace MathlibExt.AlgebraicGeometry.EllAdicCohomology

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme
open scoped TensorProduct

section Coefficients

variable {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
  [AddCommGroup A] [AddCommGroup B]
  [IsTopologicalAddGroup A] [IsTopologicalAddGroup B]

/-- A continuous additive coefficient map acts pointwise on every scheme. -/
def coefficientPresheafMap (f : A →ₜ+ B) :
    continuousMapPresheafAb.{0, u} A ⟶ continuousMapPresheafAb.{0, u} B where
  app U := AddCommGrpCat.ofHom {
    toFun g := f.toContinuousMap.comp g
    map_zero' := by
      ext x
      exact map_zero f
    map_add' := by
      intro g h
      ext x
      exact map_add f _ _ }
  naturality := by
    intro U V g
    ext s
    rfl

/-- The sheaf of continuous coefficient-valued maps on the big
pro-étale site. -/
abbrev globalCoefficientSheaf (A : Type) [TopologicalSpace A]
    [AddCommGroup A] [IsTopologicalAddGroup A] :
    Sheaf proetaleTopology Ab.{u} :=
  ⟨continuousMapPresheafAb A,
    .of_le proetaleTopology_le_fpqcTopology
      (isSheaf_fpqcTopology_continuousMapPresheafAb A)⟩

/-- The pointwise coefficient map, viewed as a morphism of sheaves. -/
def globalCoefficientMap (f : A →ₜ+ B) :
    globalCoefficientSheaf.{u} A ⟶ globalCoefficientSheaf.{u} B :=
  ObjectProperty.homMk (coefficientPresheafMap f)

/-- The pushforward appearing in Mathlib's `Scheme.ellAdicSheaf`. -/
abbrev coefficientPushforward (X : Scheme.{u}) :
    Sheaf proetaleTopology Ab.{u} ⥤ Sheaf (ProEt.topology X) Ab.{u} :=
  (ProEt.forget X ⋙ Over.forget _).sheafPushforwardContinuous _ _
    proetaleTopology

/-- The coefficient pushforward preserves addition of sheaf morphisms. -/
instance coefficientPushforward_additive (X : Scheme.{u}) :
    (coefficientPushforward X).Additive where
  map_add := by
    intro F G f g
    rfl

/-- Continuous coefficients on the pro-étale site of the fixed scheme. -/
abbrev coefficientSheaf (X : Scheme.{u}) (A : Type) [TopologicalSpace A]
    [AddCommGroup A] [IsTopologicalAddGroup A] :
    Sheaf (ProEt.topology X) Ab.{u} :=
  (coefficientPushforward X).obj (globalCoefficientSheaf A)

/-- The coefficient-induced morphism on the pro-étale site of `X`. -/
def coefficientMap (X : Scheme.{u}) (f : A →ₜ+ B) :
    coefficientSheaf X A ⟶ coefficientSheaf X B :=
  (coefficientPushforward X).map (globalCoefficientMap f)

/-- The universe lift used in Mathlib's `Scheme.EllAdicCohomology`. -/
abbrev coefficientLift (X : Scheme.{u}) :
    Sheaf (ProEt.topology X) Ab.{u} ⥤
      Sheaf (ProEt.topology X) Ab.{u + 1} :=
  sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}

/-- Lifting coefficient groups preserves addition of sheaf morphisms. -/
instance coefficientLift_additive (X : Scheme.{u}) :
    (coefficientLift X).Additive where
  map_add := by
    intro F G f g
    rfl

end Coefficients

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Multiplication by a fixed integral coefficient is continuous
and additive. -/
def scalarCoefficient (a : ℤ_[ℓ]) : ℤ_[ℓ] →ₜ+ ℤ_[ℓ] where
  toFun x := a * x
  map_zero' := mul_zero a
  map_add' := mul_add a
  continuous_toFun := continuous_const.mul continuous_id

/-- Scalar multiplication on the global continuous-map sheaf. -/
def globalScalar (a : ℤ_[ℓ]) :
    globalCoefficientSheaf.{u} ℤ_[ℓ] ⟶ globalCoefficientSheaf.{u} ℤ_[ℓ] :=
  globalCoefficientMap (scalarCoefficient ℓ a)

/-- Scalar multiplication on the actual Mathlib integral coefficient sheaf. -/
def sheafScalar (X : Scheme.{u}) (a : ℤ_[ℓ]) :
    X.ellAdicSheaf ℓ ⟶ X.ellAdicSheaf ℓ :=
  (coefficientPushforward X).map (globalScalar ℓ a)

/-- Scalar multiplication after the same universe lift as integral
cohomology. -/
def liftedScalar (X : Scheme.{u}) (a : ℤ_[ℓ]) :
    (coefficientLift X).obj (X.ellAdicSheaf ℓ) ⟶
      (coefficientLift X).obj (X.ellAdicSheaf ℓ) :=
  (coefficientLift X).map (sheafScalar ℓ X a)

/-- The canonical scalar action induced by `Sheaf.H.map` on
Mathlib's carrier. -/
def cohomologyScalar (X : Scheme.{u}) (n : ℕ) (a : ℤ_[ℓ]) :
    X.EllAdicCohomology ℓ n →+ X.EllAdicCohomology ℓ n :=
  Sheaf.H.map (liftedScalar ℓ X a) n

/-- A module structure whose scalar action is fixed by the coefficient sheaf.
The equality specifies every scalar operation on the actual integral group. -/
class CanonicalEllAdicModule (X : Scheme.{u}) (n : ℕ) where
  /-- The module on the existing integral cohomology type. -/
  moduleStructure : Module ℤ_[ℓ] (X.EllAdicCohomology ℓ n)
  /-- Every scalar is induced by multiplication on the coefficient sheaf. -/
  smul_eq : ∀ (a : ℤ_[ℓ]) (x : X.EllAdicCohomology ℓ n),
    letI : Module ℤ_[ℓ] (X.EllAdicCohomology ℓ n) := moduleStructure
    a • x = cohomologyScalar ℓ X n a x

/-- Use the module supplied by the characterized coefficient action. -/
instance ellAdicModule (X : Scheme.{u}) (n : ℕ)
    [h : CanonicalEllAdicModule ℓ X n] :
    Module ℤ_[ℓ] (X.EllAdicCohomology ℓ n) := h.moduleStructure

/-- Rational cohomology is the actual scalar extension of the integral group. -/
abbrev RationalCohomology (X : Scheme.{u}) (n : ℕ)
    [CanonicalEllAdicModule ℓ X n] : Type (u + 1) :=
  ℚ_[ℓ] ⊗[ℤ_[ℓ]] X.EllAdicCohomology ℓ n

end MathlibExt.AlgebraicGeometry.EllAdicCohomology

namespace MathlibExt.AlgebraicGeometry.EllAdicCohomology
open CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
variable (ell : Nat) [Fact ell.Prime]

private theorem scalar_one : globalScalar.{u} ell 1 = 𝟙 _ := by
  ext U s
  change C(U.unop, ℤ_[ell]) at s
  change (scalarCoefficient ell 1).toContinuousMap.comp s = s
  apply ContinuousMap.ext
  intro x
  change (1 : ℤ_[ell]) * s x = s x
  exact one_mul _

private theorem scalar_zero : globalScalar.{u} ell 0 = 0 := by
  ext U s
  change C(U.unop, ℤ_[ell]) at s
  change (scalarCoefficient ell 0).toContinuousMap.comp s = 0
  apply ContinuousMap.ext
  intro x
  change (0 : ℤ_[ell]) * s x = 0
  exact zero_mul _

private theorem scalar_add (a b : ℤ_[ell]) :
    globalScalar.{u} ell (a + b) = globalScalar ell a + globalScalar ell b := by
  ext U s
  change C(U.unop, ℤ_[ell]) at s
  change (scalarCoefficient ell (a + b)).toContinuousMap.comp s =
    (scalarCoefficient ell a).toContinuousMap.comp s +
      (scalarCoefficient ell b).toContinuousMap.comp s
  apply ContinuousMap.ext
  intro x
  change (a + b) * s x = a * s x + b * s x
  exact add_mul a b _

private theorem scalar_mul (a b : ℤ_[ell]) :
    globalScalar.{u} ell (a * b) = globalScalar ell b ≫ globalScalar ell a := by
  ext U s
  change C(U.unop, ℤ_[ell]) at s
  change (scalarCoefficient ell (a * b)).toContinuousMap.comp s =
    (scalarCoefficient ell a).toContinuousMap.comp
      ((scalarCoefficient ell b).toContinuousMap.comp s)
  apply ContinuousMap.ext
  intro x
  change (a * b) * s x = a * (b * s x)
  exact mul_assoc a b _

private theorem lift_one (X : Scheme.{u}) : liftedScalar ell X 1 = 𝟙 _ := by
  change (coefficientLift X).map
    ((coefficientPushforward X).map (globalScalar ell 1)) =
      𝟙 ((coefficientLift X).obj
        ((coefficientPushforward X).obj (globalCoefficientSheaf ℤ_[ell])))
  rw [scalar_one, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]

private theorem lift_zero (X : Scheme.{u}) : liftedScalar ell X 0 = 0 := by
  change (coefficientLift X).map
    ((coefficientPushforward X).map (globalScalar ell 0)) =
      (0 : (coefficientLift X).obj
        ((coefficientPushforward X).obj (globalCoefficientSheaf ℤ_[ell])) ⟶ _)
  rw [scalar_zero, Functor.map_zero, Functor.map_zero]

private theorem lift_add (X : Scheme.{u}) (a b : ℤ_[ell]) :
    liftedScalar ell X (a + b) =
      liftedScalar ell X a + liftedScalar ell X b := by
  change (coefficientLift X).map
    ((coefficientPushforward X).map (globalScalar ell (a + b))) =
      (coefficientLift X).map
        ((coefficientPushforward X).map (globalScalar ell a)) +
      (coefficientLift X).map
        ((coefficientPushforward X).map (globalScalar ell b))
  rw [scalar_add, Functor.map_add, Functor.map_add]

private theorem lift_mul (X : Scheme.{u}) (a b : ℤ_[ell]) :
    liftedScalar ell X (a * b) =
      liftedScalar ell X b ≫ liftedScalar ell X a := by
  change (coefficientLift X).map
    ((coefficientPushforward X).map (globalScalar ell (a * b))) =
      (coefficientLift X).map
        ((coefficientPushforward X).map (globalScalar ell b)) ≫
      (coefficientLift X).map
        ((coefficientPushforward X).map (globalScalar ell a))
  rw [scalar_mul, Functor.map_comp, Functor.map_comp]

/-- Integral pro-étale cohomology has the module structure induced by scalar
multiplication on its continuous coefficient sheaf. -/
instance canonicalEllAdicModule (X : Scheme.{u}) (n : Nat) :
    CanonicalEllAdicModule ell X n where
  moduleStructure := {
    smul := fun a x => cohomologyScalar ell X n a x
    one_smul := by
      intro x
      change Sheaf.H.map (liftedScalar ell X 1) n x = x
      rw [lift_one]
      exact Sheaf.H.map_id_apply x
    mul_smul := by
      intro a b x
      change Sheaf.H.map (liftedScalar ell X (a * b)) n x =
        Sheaf.H.map (liftedScalar ell X a) n
          (Sheaf.H.map (liftedScalar ell X b) n x)
      rw [lift_mul]
      exact Sheaf.H.map_comp_apply _ _ x
    smul_add := by
      intro a x y
      exact (cohomologyScalar ell X n a).map_add x y
    smul_zero := by
      intro a
      exact (cohomologyScalar ell X n a).map_zero
    add_smul := by
      intro a b x
      change Sheaf.H.map (liftedScalar ell X (a + b)) n x =
        Sheaf.H.map (liftedScalar ell X a) n x +
          Sheaf.H.map (liftedScalar ell X b) n x
      rw [lift_add]
      exact Sheaf.H.map_add_apply _ _ x
    zero_smul := by
      intro x
      change Sheaf.H.map (liftedScalar ell X 0) n x = 0
      rw [lift_zero]
      change ((Sheaf.functorH _ n).map (0 : _ ⟶ _)).hom x = 0
      rw [Functor.map_zero]
      rfl }
  smul_eq := by intro a x; rfl

end MathlibExt.AlgebraicGeometry.EllAdicCohomology
