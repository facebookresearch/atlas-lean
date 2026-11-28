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
# Tail restriction ideals and their quotient algebras

Let B be a nonunital complex C-star algebra, T=[1,∞), n∈ℕ and T_n={t∈T:n≤t}=[max(1,n),∞). Let
J_n={f∈C_b(T,B):f(t)=0 for every t≥n}. This is the kernel of restriction
r_n:C_b(T,B)→C_b(T_n,B), and C_n=C_b(T,B)/J_n has its quotient C-star norm. For h∈C_b(T_n,B),
clamp extension h↦(t↦h(max(n,t))) is a right inverse of restriction, so C_n is star-isomorphic
to C_b(T_n,B). The ideals J_n increase with n and lie in C₀(T,B), giving maps
C_n→B∞=C_b(T,B)/C₀(T,B) and C_n→C_m for n≤m.
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

/-- **Closed tail of the asymptotic time ray.**

Let B be a nonunital complex C-star algebra, T=[1,∞), n∈ℕ and T_n={t∈T:n≤t}=[max(1,n),∞).
TailTime n is T_n; for n=0 or n=1 it is all of T.
-/
abbrev TailTime (n : ℕ) := {t : AsymptoticTime // (n : ℝ) ≤ (t : ℝ)}

/-- **Continuous inclusion of a closed time tail.**

Let B be a nonunital complex C-star algebra, T=[1,∞), n∈ℕ and T_n={t∈T:n≤t}=[max(1,n),∞). The
map tailInclusion n:T_n→T is the continuous inclusion t↦t.
-/
def tailInclusion (n : ℕ) : C(TailTime n, AsymptoticTime) :=
  ⟨Subtype.val, continuous_subtype_val⟩

@[simp]
theorem tailInclusion_apply (n : ℕ) (t : TailTime n) :
    tailInclusion n t = t.val := by
  rfl

/-- **Continuous clamping to a closed time tail.**

Let B be a nonunital complex C-star algebra, T=[1,∞), n∈ℕ and T_n={t∈T:n≤t}=[max(1,n),∞). The
map tailClamp n:T→T_n is t↦max(n,t); since t≥1, this is at least max(1,n). It is constant
below the tail endpoint and the identity on T_n.
-/
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

/-- **Clamping is the identity on the tail.**

Let B be a nonunital complex C-star algebra, T=[1,∞), n∈ℕ and T_n={t∈T:n≤t}=[max(1,n),∞). For
t∈T_n, tailClamp n (tailInclusion n t)=t.
-/
theorem tailClamp_inclusion (n : ℕ) (t : TailTime n) :
    tailClamp n (tailInclusion n t) = t := by
  apply Subtype.ext
  apply Subtype.ext
  exact max_eq_left t.property

/-- **Restriction homomorphism to the time tail.**

Let B be a nonunital complex C-star algebra, T=[1,∞), n∈ℕ and T_n={t∈T:n≤t}=[max(1,n),∞). The
nonunital complex star homomorphism tailRestriction n B:C_b(T,B)→C_b(T_n,B) sends f to its
restriction f|T_n.
-/
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

/-- **Clamp extension of a bounded tail function.**

Let B be a nonunital complex C-star algebra, T=[1,∞), n∈ℕ and T_n={t∈T:n≤t}=[max(1,n),∞). The
nonunital complex star homomorphism tailExtension n B:C_b(T_n,B)→C_b(T,B) sends f to
t↦f(max(n,t)).
-/
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

/-- **Tail restriction after clamp extension.**

Let B be a nonunital complex C-star algebra, T=[1,∞), n∈ℕ and T_n={t∈T:n≤t}=[max(1,n),∞). For
f∈C_b(T_n,B), tailRestriction n B (tailExtension n B f)=f.
-/
theorem tailRestriction_extension (n : ℕ) (f : TailTime n →ᵇ B) :
    tailRestriction n B (tailExtension n B f) = f := by
  ext t
  rw [tailRestriction_apply, tailExtension_apply, tailClamp_inclusion]

theorem tailRestriction_surjective (n : ℕ) (B : Type uB) [NonUnitalCStarAlgebra B] :
    Function.Surjective (tailRestriction n B) :=
  fun f => ⟨tailExtension n B f, tailRestriction_extension n f⟩

/-- **Ideal of functions vanishing on a time tail.**

Let B be a nonunital complex C-star algebra, T=[1,∞), n∈ℕ and T_n={t∈T:n≤t}=[max(1,n),∞). Let
J_n={f∈C_b(T,B):f(t)=0 for every t≥n}. This is the kernel of restriction
r_n:C_b(T,B)→C_b(T_n,B), and C_n=C_b(T,B)/J_n has its quotient C-star norm. The closed star
ideal tailIdeal n B is J_n.
-/
def tailIdeal (n : ℕ) (B : Type uB) [NonUnitalCStarAlgebra B] :
    ClosedStarIdeal (AsymptoticTime →ᵇ B) :=
  ClosedStarIdeal.ker (tailRestriction n B)

/-- **Membership in the tail-vanishing ideal.**

Let B be a nonunital complex C-star algebra, T=[1,∞), n∈ℕ and T_n={t∈T:n≤t}=[max(1,n),∞). For
f∈C_b(T,B), f∈tailIdeal n B if and only if f(t)=0 for every t∈T with n≤t.
-/
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

/-- **Monotonicity of tail-vanishing ideals.**

Let B be a nonunital complex C-star algebra, T=[1,∞), n∈ℕ and T_n={t∈T:n≤t}=[max(1,n),∞). For
J_n=tailIdeal n B, n≤m implies J_n⊆J_m, because vanishing on [max(1,n),∞) implies vanishing on
[max(1,m),∞).
-/
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

/-- **Tail-vanishing functions vanish at infinity.**

Let B be a nonunital complex C-star algebra, T=[1,∞), n∈ℕ and T_n={t∈T:n≤t}=[max(1,n),∞). For
J_n=tailIdeal n B, J_n⊆C₀(T,B): every bounded continuous function vanishing for t≥n tends to
zero at infinity.
-/
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

/-- **Tail restriction quotient is the tail function algebra.**

Let B be a nonunital complex C-star algebra, T=[1,∞), n∈ℕ and T_n={t∈T:n≤t}=[max(1,n),∞). Let
J_n={f∈C_b(T,B):f(t)=0 for every t≥n}. This is the kernel of restriction
r_n:C_b(T,B)→C_b(T_n,B), and C_n=C_b(T,B)/J_n has its quotient C-star norm. The complex
star-algebra equivalence tailQuotientEquiv n B:C_n≃⋆ₐ[ℂ]C_b(T_n,B) sends the quotient class of
f to f|T_n.
-/
def tailQuotientEquiv (n : ℕ) (B : Type uB) [NonUnitalCStarAlgebra B] :
    letI : NonUnitalCStarAlgebra (tailIdeal n B).Quotient :=
      (tailIdeal n B).quotientCStarAlgebra
    (tailIdeal n B).Quotient ≃⋆ₐ[ℂ] (TailTime n →ᵇ B) := by
  letI : NonUnitalCStarAlgebra (tailIdeal n B).Quotient :=
    (tailIdeal n B).quotientCStarAlgebra
  exact NonUnitalStarAlgHom.quotientKerEquivOfSurjective
    (tailRestriction n B) (tailRestriction_surjective n B)

/-- **Tail quotient equivalence on a function class.**

Let B be a nonunital complex C-star algebra, T=[1,∞), n∈ℕ and T_n={t∈T:n≤t}=[max(1,n),∞). Let
J_n={f∈C_b(T,B):f(t)=0 for every t≥n}. This is the kernel of restriction
r_n:C_b(T,B)→C_b(T_n,B), and C_n=C_b(T,B)/J_n has its quotient C-star norm. For f∈C_b(T,B),
tailQuotientEquiv n B ([f]_J_n)=tailRestriction n B f=f|T_n.
-/
theorem tailQuotientEquiv_quotientMap (n : ℕ) (f : AsymptoticTime →ᵇ B) :
    letI : NonUnitalCStarAlgebra (tailIdeal n B).Quotient :=
      (tailIdeal n B).quotientCStarAlgebra
    tailQuotientEquiv n B ((tailIdeal n B).quotientMap f) = tailRestriction n B f := by
  let : NonUnitalCStarAlgebra (tailIdeal n B).Quotient :=
    (tailIdeal n B).quotientCStarAlgebra
  exact NonUnitalStarAlgHom.quotientKerEquivOfSurjective_quotientMap
    (tailRestriction n B) (tailRestriction_surjective n B) f

/-- **Map from a tail quotient to the asymptotic algebra.**

Let B be a nonunital complex C-star algebra, T=[1,∞), n∈ℕ and T_n={t∈T:n≤t}=[max(1,n),∞). Let
J_n={f∈C_b(T,B):f(t)=0 for every t≥n}. This is the kernel of restriction
r_n:C_b(T,B)→C_b(T_n,B), and C_n=C_b(T,B)/J_n has its quotient C-star norm. The nonunital
complex star homomorphism tailToAsymptotic n B:C_n→B∞=C_b(T,B)/C₀(T,B) sends [f]_J_n to
[f]_C₀.
-/
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

/-- **Transition between tail quotient algebras.**

Let B be a nonunital complex C-star algebra, T=[1,∞), n∈ℕ and T_n={t∈T:n≤t}=[max(1,n),∞). Let
J_n={f∈C_b(T,B):f(t)=0 for every t≥n}. This is the kernel of restriction
r_n:C_b(T,B)→C_b(T_n,B), and C_n=C_b(T,B)/J_n has its quotient C-star norm. For n≤m, the
inclusion J_n⊆J_m gives tailTransition hnm B:C_n→C_m, the nonunital complex star homomorphism
[f]_J_n↦[f]_J_m.
-/
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
