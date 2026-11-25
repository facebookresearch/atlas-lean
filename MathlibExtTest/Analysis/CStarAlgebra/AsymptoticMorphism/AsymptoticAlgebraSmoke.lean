/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.AsymptoticAlgebraMap
import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Correspondence
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Nonunital asymptotic quotient, functor and strict-class consumers

Activate the public quotient C-star factory for functions vanishing at
infinity. Test actual quotient maps, constant classes, functor maps and the
strict-equivalence correspondence without specifying a lift or output model.
-/

noncomputable section
open scoped ZeroAtInfty BoundedContinuousFunction
namespace AsymptoticAlgebraSmoke

private abbrev Coefficients := C₀(ℝ, ℂ)
local instance : NonUnitalCStarAlgebra (AsymptoticAlgebra Coefficients) :=
  AsymptoticAlgebra.cStarAlgebra Coefficients

example : AsymptoticAlgebra.quotientMap Coefficients
    (0 : AsymptoticTime →ᵇ Coefficients) = 0 :=
  map_zero _

-- A genuinely vanishing time function has zero class in the actual quotient.
example (f : C₀(AsymptoticTime, Coefficients)) :
    AsymptoticAlgebra.quotientMap Coefficients f.toBCF = 0 :=
  AsymptoticAlgebra.quotientMap_toBCF f

example (f : AsymptoticTime →ᵇ Coefficients) :
    ‖AsymptoticAlgebra.quotientMap Coefficients f‖ ≤ ‖f‖ :=
  NonUnitalStarAlgHom.norm_apply_le (AsymptoticAlgebra.quotientMap Coefficients) f

-- Constant classes retain the coefficient algebra's exact zero criterion.
example (a : Coefficients) :
    AsymptoticAlgebra.constantHom Coefficients a = 0 ↔ a = 0 :=
  AsymptoticAlgebra.constantHom_eq_zero_iff Coefficients a

example (a : Coefficients) :
    ‖AsymptoticAlgebra.constantHom Coefficients a‖ ≤ ‖a‖ :=
  NonUnitalStarAlgHom.norm_apply_le (AsymptoticAlgebra.constantHom Coefficients) a

example (x : AsymptoticAlgebra Coefficients) :
    AsymptoticAlgebra.map (NonUnitalStarAlgHom.id ℂ Coefficients) x = x := by
  rw [AsymptoticAlgebra.map_id]
  rfl

example (x : AsymptoticAlgebra Coefficients) :
    AsymptoticAlgebra.map (0 : Coefficients →⋆ₙₐ[ℂ] Coefficients) x = 0 := by
  rw [AsymptoticAlgebra.map_zero, NonUnitalStarAlgHom.zero_apply]

-- Naturality is checked on actual coefficient classes, with no separate norm bound.
example (ρ : Coefficients →⋆ₙₐ[ℂ] Coefficients) (a : Coefficients) :
    AsymptoticAlgebra.map ρ (AsymptoticAlgebra.constantHom Coefficients a) =
      AsymptoticAlgebra.constantHom Coefficients (ρ a) :=
  DFunLike.congr_fun (AsymptoticAlgebra.map_comp_constantHom ρ) a

-- The genuine quotient-preimage factory maps back to its original homomorphism;
-- its chosen representatives need not be pointwise constant.
example : AsymptoticMorphism.toHom
    (AsymptoticAlgebra.ofHom (AsymptoticAlgebra.constantHom Coefficients)) =
      AsymptoticAlgebra.constantHom Coefficients :=
  AsymptoticMorphism.toHom_ofHom _

-- The actual strict-class equivalence has a genuine two-sided inverse.
example (q : Quotient (AsymptoticMorphism.strictSetoid Coefficients Coefficients)) :
    (AsymptoticMorphism.strictClassEquiv (A := Coefficients) (B := Coefficients)).symm
      ((AsymptoticMorphism.strictClassEquiv (A := Coefficients) (B := Coefficients)) q) = q :=
  Equiv.symm_apply_apply _ _

end AsymptoticAlgebraSmoke
