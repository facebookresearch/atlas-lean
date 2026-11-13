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
map, and used Mathlib’s pro-étale cohomology carrier for rationalization.
The finiteness and vanishing statements remain Wanted obligations with their
proper smooth hypotheses displayed explicitly.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

@[expose] public noncomputable section

universe u

/-!
# Integral and rational ℓ-adic cohomology

Mathlib’s `Scheme.EllAdicCohomology` is ordinary pro-étale cohomology with
integral `ℤ_[ℓ]` coefficients. The coefficient action here starts with
pointwise multiplication on continuous maps, uses the pushforward from
`Scheme.ellAdicSheaf` and the lift from `Scheme.EllAdicCohomology`, and
applies `Sheaf.H.map`.

`CanonicalEllAdicModule` requests the module laws with an equality fixing
its scalar action to that map on every element of the existing group.
`RationalCohomology` is the actual tensor product
`ℚ_[ℓ] ⊗[ℤ_[ℓ]] X.EllAdicCohomology ℓ n` using that characterized action.

The finiteness and degree bounds are deferred for a proper smooth scheme
of pure relative dimension `d` over an algebraically closed field, with
prime `ℓ` distinct from the field’s characteristic. Properness includes
finite type and separatedness. These entries concern ordinary cohomology
with constant coefficients, and the integral finiteness statement allows
torsion.

## References

* B. Bhatt and P. Scholze, *The pro-étale topology for schemes* (2015),
  §6.8; Definition 6.8.1 is the source cited by Mathlib’s coefficient sheaf.
* The Stacks Project, Tag 0F0W, and SGA 4, Exposé X, Corollary 4.3,
  for the finite-type torsion cohomological-dimension bound.
* The Mathlib and Axiom source interfaces are credited with exact revisions
  in the adaptation notice above.
-/

namespace WantedExt.AlgebraicGeometry.EllAdicCohomologyWanted

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

/-- The sheaf of continuous coefficient-valued maps on the big pro-étale site. -/
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

/-- The pushforward appearing in Mathlib’s `Scheme.ellAdicSheaf`. -/
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

/-- The universe lift used in Mathlib’s `Scheme.EllAdicCohomology`. -/
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

/-- Multiplication by a fixed integral coefficient is continuous and additive. -/
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

/-- Scalar multiplication after the same universe lift as integral cohomology. -/
def liftedScalar (X : Scheme.{u}) (a : ℤ_[ℓ]) :
    (coefficientLift X).obj (X.ellAdicSheaf ℓ) ⟶
      (coefficientLift X).obj (X.ellAdicSheaf ℓ) :=
  (coefficientLift X).map (sheafScalar ℓ X a)

/-- The canonical scalar action induced by `Sheaf.H.map` on Mathlib’s carrier. -/
def cohomologyScalar (X : Scheme.{u}) (n : ℕ) (a : ℤ_[ℓ]) :
    X.EllAdicCohomology ℓ n →+ X.EllAdicCohomology ℓ n :=
  Sheaf.H.map (liftedScalar ℓ X a) n

/-- A module structure whose scalar action is fixed by the coefficient sheaf.
The equality specifies every scalar operation on the actual integral group. -/
class CanonicalEllAdicModule (X : Scheme.{u}) (n : ℕ) where
  /-- The module on the existing integral cohomology type. -/
  moduleStructure : Module ℤ_[ℓ] (X.EllAdicCohomology ℓ n)
  /-- Every scalar is the map induced by multiplication on the coefficient sheaf. -/
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

/-- Construct the module with the scalar action induced by the coefficient sheaf.
Source: Bhatt–Scholze (2015), §6.8, and Mathlib’s coefficient construction. -/
public instance_wanted canonicalEllAdicModule (X : Scheme.{u}) (n : ℕ) :
  CanonicalEllAdicModule ℓ X n

/-- Integral cohomology is finitely generated over `ℤ_[ℓ]` in the proper smooth
algebraically closed setting. Torsion is permitted. -/
public theorem_wanted integralFinite
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Over (Spec (.of k))) (d n : ℕ)
    [IsProper X.hom] [SmoothOfRelativeDimension d X.hom]
    (hℓ : ℓ ≠ ringChar k) :
    Module.Finite ℤ_[ℓ] (X.left.EllAdicCohomology ℓ n)

/-- The actual rational scalar extension is finite-dimensional over `ℚ_[ℓ]`. -/
public theorem_wanted rationalFinite
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Over (Spec (.of k))) (d n : ℕ)
    [IsProper X.hom] [SmoothOfRelativeDimension d X.hom]
    (hℓ : ℓ ≠ ringChar k) :
    FiniteDimensional ℚ_[ℓ] (RationalCohomology ℓ X.left n)

/-- Integral cohomology vanishes above twice the pure relative dimension.
Source: the finite-type torsion cohomological-dimension bound and
Bhatt–Scholze (2015), §6.8. -/
public theorem_wanted integralVanish
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Over (Spec (.of k))) (d n : ℕ)
    [IsProper X.hom] [SmoothOfRelativeDimension d X.hom]
    (hℓ : ℓ ≠ ringChar k) (hn : 2 * d < n) :
    Subsingleton (X.left.EllAdicCohomology ℓ n)

/-- Rational cohomology vanishes above twice the pure relative dimension. -/
public theorem_wanted rationalVanish
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Over (Spec (.of k))) (d n : ℕ)
    [IsProper X.hom] [SmoothOfRelativeDimension d X.hom]
    (hℓ : ℓ ≠ ringChar k) (hn : 2 * d < n) :
    Subsingleton (RationalCohomology ℓ X.left n)

end WantedExt.AlgebraicGeometry.EllAdicCohomologyWanted
