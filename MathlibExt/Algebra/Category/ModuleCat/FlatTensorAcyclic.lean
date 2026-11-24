/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.ModuleCat.ProjectiveFlatTargetTensor
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.Logic.Small.Defs

/-!
# Tensor acyclicity of flat targets

Tensoring a projective resolution of a flat target with an arbitrary coefficient gives zero
homology in positive degrees. Comparison with left derivation gives the corresponding acyclicity
result in a source module universe containing the ring.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace ModuleCat.FlatTensorAcyclic

variable (R : Type u) [CommRing R]
  (M : ModuleCat.{v} R)

/-- The source category contains the original ring universe. -/
local instance ringSmall : Small.{max u w} R := small_max R
/-- The free-module presentation supplies enough projectives at this height. -/
local instance enoughProjectives : EnoughProjectives (ModuleCat.{max u w} R) :=
  ModuleCat.enoughProjectives
/-- Projective resolution existence follows from those presentations. -/
local instance hasProjectiveResolutions : HasProjectiveResolutions (ModuleCat.{max u w} R) :=
  inferInstance

/-- Any projective resolution of the original flat target proves positive derived vanishing. -/
theorem isZero_leftDerived_obj_of_projectiveResolution
    (X : ModuleCat.{max u w} R) [Module.Flat R X]
    (P : ProjectiveResolution X) (n : ℕ) :
    IsZero ((((tensorBifunctorAt.{u, v, max u w} R).obj M).leftDerived (n + 1)).obj X) := by
  have h : IsZero ((ModuleCat.projectiveCoefficientComplex R M P).homology (n + 1)) :=
    ModuleCat.projectiveCoefficientHomology_isZero_succ R M P n
  exact IsZero.of_iso h
    (P.isoLeftDerivedObj ((tensorBifunctorAt.{u, v, max u w} R).obj M) (n + 1))

/-- Every flat target has zero positive left-derived objects for the original coefficient tensor functor. -/
theorem isZero_leftDerived_obj (X : ModuleCat.{max u w} R) [Module.Flat R X] (n : ℕ) :
    IsZero ((((tensorBifunctorAt.{u, v, max u w} R).obj M).leftDerived (n + 1)).obj X) :=
  isZero_leftDerived_obj_of_projectiveResolution R M X (projectiveResolution X) n

/-- The complete acyclicity predicate is constructed for every original flat target. -/
theorem all_positive_isZero (X : ModuleCat.{max u w} R) [Module.Flat R X] :
    ∀ n : ℕ,
      IsZero ((((tensorBifunctorAt.{u, v, max u w} R).obj M).leftDerived (n + 1)).obj X) :=
  fun n => isZero_leftDerived_obj R M X n

/-- Termwise flat complexes supply the all-term/all-positive predicate of acyclic resolutions. -/
theorem termwise_all_positive_isZero (Q : ChainComplex (ModuleCat.{max u w} R) ℕ)
    [∀ q, Module.Flat R (Q.X q)] :
    ∀ q n : ℕ,
      IsZero ((((tensorBifunctorAt.{u, v, max u w} R).obj M).leftDerived (n + 1)).obj (Q.X q)) :=
  fun q n => isZero_leftDerived_obj R M (Q.X q) n

section OriginalCarriers

variable (M₀ : Type v) (X₀ : Type w)
  [AddCommGroup M₀] [AddCommGroup X₀] [Module R M₀] [Module R X₀]

/-- The original independently sized flat target is acyclic after its ring-height lift. -/
theorem originalCarrier_all_positive_isZero [Module.Flat R X₀] :
    ∀ n : ℕ,
      IsZero ((((tensorBifunctorAt.{u, v, max u w} R).obj (ModuleCat.of R M₀)).leftDerived
        (n + 1)).obj (ModuleCat.of R (ULift.{u} X₀))) := by
  let : Module.Flat R (ModuleCat.of R (ULift.{u} X₀)) :=
    Module.Flat.of_linearEquiv (ULift.moduleEquiv : ULift.{u} X₀ ≃ₗ[R] X₀)
  exact all_positive_isZero R (ModuleCat.of R M₀) (ModuleCat.of R (ULift.{u} X₀))

end OriginalCarriers

end ModuleCat.FlatTensorAcyclic
