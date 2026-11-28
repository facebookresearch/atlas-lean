/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Normalization
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Star
import Mathlib.Topology.Algebra.MulAction

/-!
A concrete consumer of raw asymptotic morphisms and zero normalization. The family
φ_t(z) = z + exp(−t) has a nonzero zero orbit at every finite time, so none of its slices
is a star homomorphism. Its defects tend to zero in the ordinary complex norm.
Normalization removes this decaying translation exactly and leaves the identity family.
-/

set_option autoImplicit false

open Filter

namespace ConcreteAsymptoticNormalization

private def error (t : AsymptoticTime) : ℂ := Real.exp (-(t : ℝ))

private theorem error_continuous : Continuous error :=
  Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_subtype_val.neg)

private theorem error_tendsto : Tendsto error atTop (nhds 0) := by
  have h : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hray : Tendsto (fun t : AsymptoticTime => Real.exp (-(t : ℝ)))
      atTop (nhds 0) := (tendsto_comp_val_Ici_atTop (a := (1 : ℝ))).2 h
  simpa [error] using (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hray

private theorem orbit_tendsto (a : ℂ) :
    Tendsto (fun t : AsymptoticTime => a + error t) atTop (nhds a) := by
  simpa only [add_zero] using tendsto_const_nhds.add error_tendsto

private def translated : AsymptoticMorphism ℂ ℂ where
  toFun t a := a + error t
  continuous_orbit a := continuous_const.add error_continuous
  add_defect_tendsto a b := by
    simpa only [sub_self] using
      (orbit_tendsto (a + b)).sub ((orbit_tendsto a).add (orbit_tendsto b))
  smul_defect_tendsto c a := by
    simpa only [sub_self] using
      (orbit_tendsto (c • a)).sub ((orbit_tendsto a).const_smul c)
  mul_defect_tendsto a b := by
    simpa only [sub_self] using
      (orbit_tendsto (a * b)).sub ((orbit_tendsto a).mul (orbit_tendsto b))
  star_defect_tendsto a := by
    simpa only [sub_self] using
      (orbit_tendsto (star a)).sub ((orbit_tendsto a).star)

private theorem translated_zero_ne_zero (t : AsymptoticTime) : translated t 0 ≠ 0 := by
  intro h
  have hreal : Real.exp (-(t : ℝ)) = 0 := by
    simpa [translated, error] using congrArg Complex.re h
  exact Real.exp_ne_zero _ hreal

-- This exercises the actual norm and a nonzero zero orbit of a raw family.
example (t : AsymptoticTime) : 0 < ‖translated t 0‖ :=
  norm_pos_iff.mpr (translated_zero_ne_zero t)

example (t : AsymptoticTime) :
    ¬ ∃ f : ℂ →⋆ₙₐ[ℂ] ℂ, ∀ a, translated t a = f a := by
  rintro ⟨f, hf⟩
  exact translated_zero_ne_zero t ((hf 0).trans (map_zero f))

private theorem normalized_eq_identity :
    translated.normalize = AsymptoticMorphism.ofHom (NonUnitalStarAlgHom.id ℂ ℂ) := by
  apply AsymptoticMorphism.ext
  intro t a
  simp [AsymptoticMorphism.normalize_apply, translated]

example (t : AsymptoticTime) : translated.normalize t 0 = 0 :=
  AsymptoticMorphism.normalize_zero translated t

example (t : AsymptoticTime) : ‖translated.normalize t (1 : ℂ)‖ = 1 := by
  simp [normalized_eq_identity]

example : AsymptoticMorphism.StrictlyEquivalent translated.normalize translated :=
  AsymptoticMorphism.normalize_strictlyEquivalent translated

end ConcreteAsymptoticNormalization
