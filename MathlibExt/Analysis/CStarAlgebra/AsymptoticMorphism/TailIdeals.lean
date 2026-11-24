/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.AsymptoticAlgebra
public import Mathlib.Order.Directed
public import Mathlib.Topology.Order.OrderClosed

/-!
# Actual tail ideals and restriction quotients

The kernel J_n of restriction to the true closed tail gives the exact
vanishing-on-[n,infty) ideal in Cb([1,infty),B). Clamp-extension is a computed
right inverse, hence the restriction quotient is the actual tail algebra.
No ideal comparison, inverse, lifting output or alternate C-star model is input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter
open scoped ZeroAtInfty BoundedContinuousFunction

noncomputable section

namespace AsymptoticAlgebra

universe uB

variable {B : Type uB} [NonUnitalCStarAlgebra B]

attribute [local instance] cStarAlgebra

/-- The true source-domain tail; n=0,1 do not remove any source points. -/
abbrev TailTime (n : ℕ) := {t : AsymptoticTime // (n : ℝ) ≤ (t : ℝ)}

/-- Continuous inclusion of the actual tail in the original ray. -/
def tailInclusion (n : ℕ) : C(TailTime n, AsymptoticTime) :=
  ⟨Subtype.val, continuous_subtype_val⟩

@[simp]
theorem tailInclusion_apply (n : ℕ) (t : TailTime n) :
    tailInclusion n t = t.val := by
  rfl

/-- Actual continuous clamping, constant below the effective tail endpoint. -/
def tailClamp (n : ℕ) : C(AsymptoticTime, TailTime n) where
  toFun t :=
    ⟨⟨max (t : ℝ) (n : ℝ), t.property.trans (le_max_left _ _)⟩, le_max_right _ _⟩
  continuous_toFun := by
    have hmax : Continuous (fun t : AsymptoticTime => max (t : ℝ) (n : ℝ)) :=
      continuous_subtype_val.max
        (continuous_const : Continuous (fun _ : AsymptoticTime => (n : ℝ)))
    exact (hmax.subtype_mk
      (fun t : AsymptoticTime => t.property.trans (le_max_left (t : ℝ) (n : ℝ)))).subtype_mk
        (fun t : AsymptoticTime => le_max_right (t : ℝ) (n : ℝ))

@[simp]
theorem tailClamp_coe (n : ℕ) (t : AsymptoticTime) :
    ((tailClamp n t : AsymptoticTime) : ℝ) = max (t : ℝ) (n : ℝ) := by
  rfl

/-- Inclusion followed by clamp is the actual identity on the tail. -/
theorem tailClamp_inclusion (n : ℕ) (t : TailTime n) :
    tailClamp n (tailInclusion n t) = t := by
  apply Subtype.ext
  apply Subtype.ext
  exact max_eq_left t.property

/-- Restriction of the stock BCF algebra as a real nonunital star hom. -/
def tailRestriction (n : ℕ) (B : Type uB) [NonUnitalCStarAlgebra B] :
    (AsymptoticTime →ᵇ B) →⋆ₙₐ[ℂ] (TailTime n →ᵇ B) where
  toFun f := f.compContinuous (tailInclusion n)
  map_zero' := by
    ext t
    rfl
  map_add' := by
    intro f g
    ext t
    rfl
  map_smul' := by
    intro c f
    ext t
    rfl
  map_mul' := by
    intro f g
    ext t
    rfl
  map_star' := by
    intro f
    ext t
    rfl

@[simp]
theorem tailRestriction_apply (n : ℕ) (f : AsymptoticTime →ᵇ B) (t : TailTime n) :
    tailRestriction n B f t = f (tailInclusion n t) :=
  BoundedContinuousFunction.compContinuous_apply _ _ _

/-- The actual constant-below-endpoint extension along the computed clamp. -/
def tailExtension (n : ℕ) (B : Type uB) [NonUnitalCStarAlgebra B] :
    (TailTime n →ᵇ B) →⋆ₙₐ[ℂ] (AsymptoticTime →ᵇ B) where
  toFun f := f.compContinuous (tailClamp n)
  map_zero' := by
    ext t
    rfl
  map_add' := by
    intro f g
    ext t
    rfl
  map_smul' := by
    intro c f
    ext t
    rfl
  map_mul' := by
    intro f g
    ext t
    rfl
  map_star' := by
    intro f
    ext t
    rfl

@[simp]
theorem tailExtension_apply (n : ℕ) (f : TailTime n →ᵇ B) (t : AsymptoticTime) :
    tailExtension n B f t = f (tailClamp n t) :=
  BoundedContinuousFunction.compContinuous_apply _ _ _

/-- The two computed maps give an actual right-inverse identity. -/
theorem tailRestriction_extension (n : ℕ) (f : TailTime n →ᵇ B) :
    tailRestriction n B (tailExtension n B f) = f := by
  ext t
  rw [tailRestriction_apply, tailExtension_apply, tailClamp_inclusion]

theorem tailRestriction_surjective (n : ℕ) (B : Type uB) [NonUnitalCStarAlgebra B] :
    Function.Surjective (tailRestriction n B) :=
  fun f => ⟨tailExtension n B f, tailRestriction_extension n f⟩

/-- The source's exact tail ideal is a true closed kernel, not a model input. -/
def tailIdeal (n : ℕ) (B : Type uB) [NonUnitalCStarAlgebra B] :
    ClosedStarIdeal (AsymptoticTime →ᵇ B) :=
  ClosedStarIdeal.ker (tailRestriction n B)

/-- Exact printed membership: zero at every source time at least n. -/
theorem mem_tailIdeal_iff (n : ℕ) (f : AsymptoticTime →ᵇ B) :
    f ∈ tailIdeal n B ↔
      ∀ t : AsymptoticTime, (n : ℝ) ≤ (t : ℝ) → f t = 0 := by
  rw [tailIdeal, ClosedStarIdeal.mem_ker]
  constructor
  · intro h t ht
    have hv := DFunLike.congr_fun h (⟨t, ht⟩ : TailTime n)
    simpa only [tailRestriction_apply, tailInclusion_apply,
      BoundedContinuousFunction.coe_zero, Pi.zero_apply] using hv
  · intro h
    ext t
    simpa only [tailRestriction_apply, tailInclusion_apply,
      BoundedContinuousFunction.coe_zero, Pi.zero_apply] using h t.val t.property

/-- Monotonicity uses the literal nested-tail relation. -/
theorem tailIdeal_monotone (B : Type uB) [NonUnitalCStarAlgebra B] :
    Monotone (fun n : ℕ => tailIdeal n B) := by
  intro n m hnm f hf
  apply (mem_tailIdeal_iff m f).2
  intro t ht
  have hcast : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
  exact (mem_tailIdeal_iff n f).1 hf t (hcast.trans ht)

theorem tailIdeal_directed (B : Type uB) [NonUnitalCStarAlgebra B] :
    Directed (· ≤ ·) (fun n : ℕ => tailIdeal n B) :=
  (tailIdeal_monotone B).directed_le

/-- Exact eventual zero implies membership in the real C0 ideal. -/
theorem tailIdeal_le_vanishingIdeal (n : ℕ) (B : Type uB) [NonUnitalCStarAlgebra B] :
    tailIdeal n B ≤ BoundedContinuousFunction.vanishingIdeal AsymptoticTime B := by
  intro f hf
  apply (mem_vanishingIdeal_iff f).2
  have hzero : ∀ᶠ t : AsymptoticTime in atTop, f t = 0 := by
    let r : AsymptoticTime := ⟨max (n : ℝ) 1, le_max_right _ _⟩
    filter_upwards [eventually_ge_atTop r] with t ht
    exact (mem_tailIdeal_iff n f).1 hf t ((le_max_left _ _).trans ht)
  have hconst : Tendsto (fun _ : AsymptoticTime => (0 : B)) atTop (nhds (0 : B)) :=
    tendsto_const_nhds
  exact hconst.congr' (Filter.EventuallyEq.symm hzero)

/-- The actual restriction quotient is the actual tail BCF algebra. -/
def tailQuotientEquiv (n : ℕ) (B : Type uB) [NonUnitalCStarAlgebra B] :
    letI : NonUnitalCStarAlgebra (tailIdeal n B).Quotient :=
      (tailIdeal n B).quotientCStarAlgebra
    (tailIdeal n B).Quotient ≃⋆ₐ[ℂ] (TailTime n →ᵇ B) := by
  letI : NonUnitalCStarAlgebra (tailIdeal n B).Quotient :=
    (tailIdeal n B).quotientCStarAlgebra
  exact NonUnitalStarAlgHom.quotientKerEquivOfSurjective
    (tailRestriction n B) (tailRestriction_surjective n B)

/-- Its characteristic formula is restriction of the original representative. -/
theorem tailQuotientEquiv_quotientMap (n : ℕ) (f : AsymptoticTime →ᵇ B) :
    letI : NonUnitalCStarAlgebra (tailIdeal n B).Quotient :=
      (tailIdeal n B).quotientCStarAlgebra
    tailQuotientEquiv n B ((tailIdeal n B).quotientMap f) = tailRestriction n B f := by
  let : NonUnitalCStarAlgebra (tailIdeal n B).Quotient :=
    (tailIdeal n B).quotientCStarAlgebra
  exact NonUnitalStarAlgHom.quotientKerEquivOfSurjective_quotientMap
    (tailRestriction n B) (tailRestriction_surjective n B) f

/-- The genuine stage-to-asymptotic quotient map is induced by the proven inclusion. -/
def tailToAsymptotic (n : ℕ) (B : Type uB) [NonUnitalCStarAlgebra B] :
    letI : NonUnitalCStarAlgebra (tailIdeal n B).Quotient :=
      (tailIdeal n B).quotientCStarAlgebra
    (tailIdeal n B).Quotient →⋆ₙₐ[ℂ] AsymptoticAlgebra B := by
  letI : NonUnitalCStarAlgebra (tailIdeal n B).Quotient :=
    (tailIdeal n B).quotientCStarAlgebra
  exact ClosedStarIdeal.quotientMapOfLE
    (tailIdeal n B) (BoundedContinuousFunction.vanishingIdeal AsymptoticTime B)
    (tailIdeal_le_vanishingIdeal n B)

theorem tailToAsymptotic_quotientMap (n : ℕ) (f : AsymptoticTime →ᵇ B) :
    letI : NonUnitalCStarAlgebra (tailIdeal n B).Quotient :=
      (tailIdeal n B).quotientCStarAlgebra
    tailToAsymptotic n B ((tailIdeal n B).quotientMap f) = quotientMap B f := by
  let : NonUnitalCStarAlgebra (tailIdeal n B).Quotient :=
    (tailIdeal n B).quotientCStarAlgebra
  exact ClosedStarIdeal.quotientMapOfLE_quotientMap _ _
    (tailIdeal_le_vanishingIdeal n B) f

/-- The canonical stage transition uses the actual monotonicity proof. -/
def tailTransition {n m : ℕ} (hnm : n ≤ m)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    letI : NonUnitalCStarAlgebra (tailIdeal n B).Quotient :=
      (tailIdeal n B).quotientCStarAlgebra
    letI : NonUnitalCStarAlgebra (tailIdeal m B).Quotient :=
      (tailIdeal m B).quotientCStarAlgebra
    (tailIdeal n B).Quotient →⋆ₙₐ[ℂ] (tailIdeal m B).Quotient := by
  letI : NonUnitalCStarAlgebra (tailIdeal n B).Quotient :=
    (tailIdeal n B).quotientCStarAlgebra
  letI : NonUnitalCStarAlgebra (tailIdeal m B).Quotient :=
    (tailIdeal m B).quotientCStarAlgebra
  exact ClosedStarIdeal.quotientMapOfLE (tailIdeal n B) (tailIdeal m B)
    (tailIdeal_monotone B hnm)

theorem tailTransition_quotientMap {n m : ℕ} (hnm : n ≤ m)
    (f : AsymptoticTime →ᵇ B) :
    letI : NonUnitalCStarAlgebra (tailIdeal n B).Quotient :=
      (tailIdeal n B).quotientCStarAlgebra
    letI : NonUnitalCStarAlgebra (tailIdeal m B).Quotient :=
      (tailIdeal m B).quotientCStarAlgebra
    tailTransition hnm B ((tailIdeal n B).quotientMap f) =
      (tailIdeal m B).quotientMap f := by
  let : NonUnitalCStarAlgebra (tailIdeal n B).Quotient :=
    (tailIdeal n B).quotientCStarAlgebra
  let : NonUnitalCStarAlgebra (tailIdeal m B).Quotient :=
    (tailIdeal m B).quotientCStarAlgebra
  exact ClosedStarIdeal.quotientMapOfLE_quotientMap _ _ (tailIdeal_monotone B hnm) f

end AsymptoticAlgebra
