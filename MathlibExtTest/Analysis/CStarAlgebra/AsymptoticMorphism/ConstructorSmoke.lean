/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Functoriality
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-!
# Nonunital asymptotic-morphism constructors and boundary consumers

Use the actual closed time ray starting at one. Constant star homomorphisms,
zero families, identity reparametrization and constant homotopies are tested
through public APIs. The universe test keeps domain and codomain independent.
-/

noncomputable section
open scoped ZeroAtInfty
open AsymptoticMorphism
namespace AsymptoticConstructorSmoke
universe u v

-- A continuous family factory works across independent coefficient universes.
example {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (ρ : A →⋆ₙₐ[ℂ] B) (t : AsymptoticTime) (a : A) :
    ofHomFamily (fun _ => ρ) (fun _ => continuous_const) t a = ρ a :=
  ofHomFamily_apply _ _ t a

private abbrev Coefficients := C₀(ℝ, ℂ)
private def initialTime : AsymptoticTime := ⟨1, le_rfl⟩

example (a : Coefficients) (t : AsymptoticTime) :
    ofHom (NonUnitalStarAlgHom.id ℂ Coefficients) t a = a :=
  ofHom_apply _ t a

example (a : Coefficients) (t : AsymptoticTime) :
    ‖ofHom (NonUnitalStarAlgHom.id ℂ Coefficients) t a‖ = ‖a‖ := by
  rw [ofHom_apply]
  rfl

-- The minimum allowed source time is exercised rather than introducing time zero.
example (a : Coefficients) :
    AsymptoticMorphism.zero (A := Coefficients) (B := Coefficients) initialTime a = 0 :=
  AsymptoticMorphism.zero_apply _ _

example (a : Coefficients) (t : AsymptoticTime) :
    ofHomFamily (fun _ => (0 : Coefficients →⋆ₙₐ[ℂ] Coefficients))
        (fun _ => continuous_const) t a = 0 := by
  rw [ofHomFamily_apply, NonUnitalStarAlgHom.zero_apply]

example (φ : AsymptoticMorphism Coefficients Coefficients) :
    reparam φ id continuous_id Filter.tendsto_id = φ := by
  apply AsymptoticMorphism.ext
  intro t a
  exact reparam_apply φ id continuous_id Filter.tendsto_id t a

example (φ : AsymptoticMorphism Coefficients Coefficients) (t : AsymptoticTime)
    (a : Coefficients) : (Homotopy.refl φ).family t a 0 = φ t a :=
  (Homotopy.refl φ).start t a

example (φ : AsymptoticMorphism Coefficients Coefficients) (t : AsymptoticTime)
    (a : Coefficients) : ((Homotopy.refl φ).trans (Homotopy.refl φ)).family t a 1 = φ t a :=
  ((Homotopy.refl φ).trans (Homotopy.refl φ)).finish t a

example (φ : AsymptoticMorphism Coefficients Coefficients) :
    precomp φ (NonUnitalStarAlgHom.id ℂ Coefficients) = φ :=
  precomp_id φ

example : postcomp (ofHom (NonUnitalStarAlgHom.id ℂ Coefficients))
    (0 : Coefficients →⋆ₙₐ[ℂ] Coefficients) = AsymptoticMorphism.zero := by
  apply AsymptoticMorphism.ext
  intro t a
  simp only [postcomp_apply, ofHom_apply, NonUnitalStarAlgHom.zero_apply,
    AsymptoticMorphism.zero_apply]

-- A general nonlinear slice is required to approach zero at the zero coefficient;
-- no exact pointwise-zero property is imposed on arbitrary asymptotic morphisms.
example (φ : AsymptoticMorphism Coefficients Coefficients) :
    Filter.Tendsto (fun t => φ t 0) Filter.atTop (nhds 0) := zero_tendsto φ

local instance : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
local instance : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ
private abbrev ZeroCoefficients := CStarMatrix (Fin 0) (Fin 0) ℂ

example (a : ZeroCoefficients) (t : AsymptoticTime) :
    ofHom (0 : ZeroCoefficients →⋆ₙₐ[ℂ] Coefficients) t a = 0 := by
  rw [ofHom_apply, NonUnitalStarAlgHom.zero_apply]

example (a : Coefficients) (t : AsymptoticTime) :
    ofHom (0 : Coefficients →⋆ₙₐ[ℂ] ZeroCoefficients) t a = 0 := by
  rw [ofHom_apply, NonUnitalStarAlgHom.zero_apply]

end AsymptoticConstructorSmoke
