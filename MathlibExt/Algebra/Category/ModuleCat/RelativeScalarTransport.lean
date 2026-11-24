/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Functor.RelativeProjectivityTransport
public import MathlibExt.Algebra.Category.ModuleCat.RingHomInduction.Composition
public import MathlibExt.Algebra.Category.ModuleCat.CoextendScalarsRelativeInjectivity

/-!
# Scalar transport of relative lifting properties

The general transport laws for relative projectivity and injectivity specialize to restriction of
scalars and module equivalences. The formulas retain the stated scalar morphisms, module actions,
and universe parameters.
-/

@[expose] public section

open CategoryTheory

universe u v s w

namespace ModuleCat.RelativeScalarTransport

variable {k : Type u} {R : Type v} {S : Type s}
  [Ring k] [Ring R] [Ring S]

/-- The full relative lifting predicate uses the restriction composition. -/
theorem isRelativeProjective_restrict_comp_iff (φ : k →+* R) (ψ : R →+* S)
    (P : ModuleCat.{w} S) :
    (ModuleCat.restrictScalars.{w} (ψ.comp φ)).IsRelativeProjective P ↔
      ((ModuleCat.restrictScalars.{w} ψ) ⋙
        (ModuleCat.restrictScalars.{w} φ)).IsRelativeProjective P :=
  Functor.isRelativeProjective_iff_of_natIso (ModuleCat.restrictScalarsComp' φ ψ (ψ.comp φ) rfl) P

/-- The full relative extension predicate uses the same original restriction comparison. -/
theorem isRelativeInjective_restrict_comp_iff (φ : k →+* R) (ψ : R →+* S)
    (P : ModuleCat.{w} S) :
    (ModuleCat.restrictScalars.{w} (ψ.comp φ)).IsRelativeInjective P ↔
      ((ModuleCat.restrictScalars.{w} ψ) ⋙
        (ModuleCat.restrictScalars.{w} φ)).IsRelativeInjective P :=
  Functor.isRelativeInjective_iff_of_natIso (ModuleCat.restrictScalarsComp' φ ψ (ψ.comp φ) rfl) P

/-- Splitting over the first scalar ring tests at least every intermediate split epimorphism. -/
theorem isRelativeProjective_restrict_of_comp (φ : k →+* R) (ψ : R →+* S)
    {P : ModuleCat.{w} S}
    (hP : (ModuleCat.restrictScalars.{w} (ψ.comp φ)).IsRelativeProjective P) :
    (ModuleCat.restrictScalars.{w} ψ).IsRelativeProjective P :=
  Functor.IsRelativeProjective.of_comp (ModuleCat.restrictScalars.{w} φ)
    ((isRelativeProjective_restrict_comp_iff φ ψ P).mp hP)

/-- The intermediate scalar-relative extension property follows from the original composite property. -/
theorem isRelativeInjective_restrict_of_comp (φ : k →+* R) (ψ : R →+* S)
    {P : ModuleCat.{w} S}
    (hP : (ModuleCat.restrictScalars.{w} (ψ.comp φ)).IsRelativeInjective P) :
    (ModuleCat.restrictScalars.{w} ψ).IsRelativeInjective P :=
  Functor.IsRelativeInjective.of_comp (ModuleCat.restrictScalars.{w} φ)
    ((isRelativeInjective_restrict_comp_iff φ ψ P).mp hP)

/-- The original induction counit splitting over ψ is forced by the full composite lifting property. -/
theorem counit_isSplitEpi_of_relativeProjective_comp (φ : k →+* R) (ψ : R →+* S)
    (P : ModuleCat.{max u v s w} S)
    (hP : (ModuleCat.restrictScalars.{max u v s w} (ψ.comp φ)).IsRelativeProjective P) :
    IsSplitEpi ((ModuleCat.induceRestrictScalarsAdj.{v, s, max u v s w} ψ).counit.app P) :=
  ((ModuleCat.induceRestrictScalarsAdj.{v, s, max u v s w} ψ).isRelativeProjective_iff_counit_isSplitEpi P).mp
    (isRelativeProjective_restrict_of_comp φ ψ hP)

/-- The restriction/coextension unit over ψ retracts for every composite-relative injective object. -/
theorem unit_isSplitMono_of_relativeInjective_comp (φ : k →+* R) (ψ : R →+* S)
    (P : ModuleCat.{max u v s w} S)
    (hP : (ModuleCat.restrictScalars.{max u v s w} (ψ.comp φ)).IsRelativeInjective P) :
    IsSplitMono ((ModuleCat.restrictCoextendScalarsAdj.{max u v s w} ψ).unit.app P) :=
  (ModuleCat.CoextendScalars.isRelativeInjective_iff_unit_isSplitMono.{v, s, max u v s w} ψ P).mp
    (isRelativeInjective_restrict_of_comp φ ψ hP)

/-- Congruence of the original ring homomorphism transports all relative lifts by the iso. -/
theorem isRelativeProjective_restrict_congr {φ φ' : k →+* R} (h : φ = φ')
    (P : ModuleCat.{w} R) :
    (ModuleCat.restrictScalars.{w} φ).IsRelativeProjective P ↔
      (ModuleCat.restrictScalars.{w} φ').IsRelativeProjective P :=
  Functor.isRelativeProjective_iff_of_natIso (ModuleCat.restrictScalarsCongr h) P

/-- The extension property uses the same congruence of restriction maps. -/
theorem isRelativeInjective_restrict_congr {φ φ' : k →+* R} (h : φ = φ')
    (P : ModuleCat.{w} R) :
    (ModuleCat.restrictScalars.{w} φ).IsRelativeInjective P ↔
      (ModuleCat.restrictScalars.{w} φ').IsRelativeInjective P :=
  Functor.isRelativeInjective_iff_of_natIso (ModuleCat.restrictScalarsCongr h) P

/-- Direct induction along the original composite is already projective relative to ψ. -/
theorem isRelativeProjective_induced_comp (φ : k →+* R) (ψ : R →+* S)
    (M : ModuleCat.{max u v s w} k) :
    (ModuleCat.restrictScalars.{max u v s w} ψ).IsRelativeProjective
      ((ModuleCat.induceScalars.{u, s, max u v s w} (ψ.comp φ)).obj M) :=
  isRelativeProjective_restrict_of_comp φ ψ
    ((ModuleCat.induceRestrictScalarsAdj.{u, s, max u v s w} (ψ.comp φ)).isRelativeProjective_obj M)

/-- The original iterated induced module inherits that intermediate property through the comparison. -/
theorem isRelativeProjective_iterated_induced (φ : k →+* R) (ψ : R →+* S)
    (M : ModuleCat.{max u v s w} k) :
    (ModuleCat.restrictScalars.{max u v s w} ψ).IsRelativeProjective
      (((ModuleCat.induceScalars.{u, v, max u v s w} φ) ⋙
        (ModuleCat.induceScalars.{v, s, max u v s w} ψ)).obj M) := by
  intro Y Z g s f
  let e : (((ModuleCat.induceScalars.{u, v, max u v s w} φ) ⋙
      (ModuleCat.induceScalars.{v, s, max u v s w} ψ)).obj M) ≅
      (ModuleCat.induceScalars.{u, s, max u v s w} (ψ.comp φ)).obj M :=
    (ModuleCat.RingHomInduction.compositionIso.{u, v, s, w} φ ψ).app M
  exact Functor.IsRelativeProjective.of_retract (isRelativeProjective_induced_comp φ ψ M)
    e.retract g s f

/-- Every retract of the iterated induced module keeps its intermediate relative lifts. -/
theorem isRelativeProjective_retract_iterated_induced (φ : k →+* R) (ψ : R →+* S)
    (M : ModuleCat.{max u v s w} k) (P : ModuleCat.{max u v s w} S)
    (r : Retract P (((ModuleCat.induceScalars.{u, v, max u v s w} φ) ⋙
      (ModuleCat.induceScalars.{v, s, max u v s w} ψ)).obj M)) :
    (ModuleCat.restrictScalars.{max u v s w} ψ).IsRelativeProjective P := by
  intro Y Z g s f
  exact Functor.IsRelativeProjective.of_retract
    (isRelativeProjective_iterated_induced φ ψ M) r g s f

/-- Direct coextension along the original composite earns the intermediate scalar extension property. -/
theorem isRelativeInjective_coextended_comp (φ : k →+* R) (ψ : R →+* S)
    (N : ModuleCat.{max u v s w} k) :
    (ModuleCat.restrictScalars.{max u v s w} ψ).IsRelativeInjective
      ((ModuleCat.coextendScalars.{u, s, max u v s w} (ψ.comp φ)).obj N) :=
  isRelativeInjective_restrict_of_comp φ ψ
    (ModuleCat.CoextendScalars.isRelativeInjective_obj.{u, s, max u v s w} (ψ.comp φ) N)

/-- Retract stability preserves the intermediate property of every coextended retract. -/
theorem isRelativeInjective_retract_coextended_comp (φ : k →+* R) (ψ : R →+* S)
    (N : ModuleCat.{max u v s w} k) (P : ModuleCat.{max u v s w} S)
    (r : Retract P ((ModuleCat.coextendScalars.{u, s, max u v s w} (ψ.comp φ)).obj N)) :
    (ModuleCat.restrictScalars.{max u v s w} ψ).IsRelativeInjective P := by
  intro X Y g s f
  exact Functor.IsRelativeInjective.of_retract
    (isRelativeInjective_coextended_comp φ ψ N) r g s f

end ModuleCat.RelativeScalarTransport
