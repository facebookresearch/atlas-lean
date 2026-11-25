/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.IdealQuotient
public import Mathlib.Analysis.CStarAlgebra.Multiplier
public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit

/-!
# Closed ideals under multiplier actions

For nonunital C-star `B`, a multiplier `m` has continuous linear components `L_m,R_m` with
`L_m(a*b) = L_m(a)*b` and `R_m(a*b) = a*R_m(b)`. Both maps preserve every closed two-sided star
ideal `I ⊆ B`.

An approximate unit of `I`, together with the centralizer identities and closedness of `I`,
proves `L_m(x),R_m(x) ∈ I` whenever `x ∈ I`. Thus multiplier actions can descend to the quotient
`B/I`.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Set
open scoped MultiplierAlgebra Topology
namespace DoubleCentralizer
universe uB
variable {B : Type uB} [NonUnitalCStarAlgebra B]

/-- **Left centralizer identity.** For nonunital C-star `B`, multiplier `m` and `a,b : B`, `m.fst
(a*b) = m.fst a * b`. -/
theorem fst_apply_mul (m : 𝓜(ℂ, B)) (a b : B) : m.fst (a * b) = m.fst a * b := by
  have h (x : B) : x * m.fst (a * b) = x * (m.fst a * b) := by
    calc
      x * m.fst (a * b) = m.snd x * (a * b) := (m.central x (a * b)).symm
      _ = (m.snd x * a) * b := (mul_assoc _ _ _).symm
      _ = (x * m.fst a) * b := congrArg (fun z : B => z * b) (m.central x a)
      _ = x * (m.fst a * b) := mul_assoc _ _ _
  let z := m.fst (a * b) - m.fst a * b
  have hz : star z * z = 0 := by
    dsimp only [z]
    rw [mul_sub, h, sub_self]
  exact sub_eq_zero.mp (star_mul_self_eq_zero.mp hz)

/-- **Right centralizer identity.** For nonunital C-star `B`, multiplier `m` and `a,b : B`, `m.snd
(a*b) = a * m.snd b`. -/
theorem snd_apply_mul (m : 𝓜(ℂ, B)) (a b : B) : m.snd (a * b) = a * m.snd b := by
  have h := fst_apply_mul (star m) (star b) (star a)
  have hs := congrArg (star : B → B) h
  simpa only [star_fst, star_mul, star_star] using hs

/-- **Left multiplier invariance of a closed ideal.** For a closed two-sided star ideal `I` of
nonunital C-star `B`, `m : M(B)` and `x ∈ I`, `m.fst x ∈ I`. -/
theorem fst_mem_closedStarIdeal (I : ClosedStarIdeal B) (m : 𝓜(ℂ, B)) {x : B} (hx : x ∈ I) :
    m.fst x ∈ I := by
  let : NonUnitalCStarAlgebra I.carrier := I.carrierCStarAlgebra
  let : PartialOrder I.carrier := CStarAlgebra.spectralOrder _
  let : StarOrderedRing I.carrier := CStarAlgebra.spectralOrderedRing _
  let l := CStarAlgebra.approximateUnit I.carrier
  have hl : l.IsApproximateUnit := (CStarAlgebra.increasingApproximateUnit I.carrier).toIsApproximateUnit
  let : NeBot l := hl.neBot
  let xi : I.carrier := ⟨x, hx⟩
  have hi : Tendsto (fun e : I.carrier => xi * e) l (𝓝 xi) := hl.tendsto_mul_left xi
  have hb := ((continuous_subtype_val : Continuous (fun y : I.carrier => (y : B))).tendsto xi).comp hi
  change Tendsto (fun e : I.carrier => x * (e : B)) l (𝓝 x) at hb
  refine I.isClosed.mem_of_tendsto ((m.fst.continuous.tendsto x).comp hb) (Eventually.of_forall ?_)
  intro e
  change m.fst (x * (e : B)) ∈ I.carrier
  rw [fst_apply_mul]
  exact I.isTwoSided.mul_mem_left (m.fst x) e.property

/-- **Right multiplier invariance of a closed ideal.** For a closed two-sided star ideal `I` of
nonunital C-star `B`, `m : M(B)` and `x ∈ I`, `m.snd x ∈ I`. -/
theorem snd_mem_closedStarIdeal (I : ClosedStarIdeal B) (m : 𝓜(ℂ, B)) {x : B} (hx : x ∈ I) :
    m.snd x ∈ I := by
  let : NonUnitalCStarAlgebra I.carrier := I.carrierCStarAlgebra
  let : PartialOrder I.carrier := CStarAlgebra.spectralOrder _
  let : StarOrderedRing I.carrier := CStarAlgebra.spectralOrderedRing _
  let l := CStarAlgebra.approximateUnit I.carrier
  have hl : l.IsApproximateUnit := (CStarAlgebra.increasingApproximateUnit I.carrier).toIsApproximateUnit
  let : NeBot l := hl.neBot
  let xi : I.carrier := ⟨x, hx⟩
  have hi : Tendsto (fun e : I.carrier => e * xi) l (𝓝 xi) := hl.tendsto_mul_right xi
  have hb := ((continuous_subtype_val : Continuous (fun y : I.carrier => (y : B))).tendsto xi).comp hi
  change Tendsto (fun e : I.carrier => (e : B) * x) l (𝓝 x) at hb
  refine I.isClosed.mem_of_tendsto ((m.snd.continuous.tendsto x).comp hb) (Eventually.of_forall ?_)
  intro e
  change m.snd ((e : B) * x) ∈ I.carrier
  rw [snd_apply_mul]
  exact I.isTwoSided.mul_mem_right e.property (m.snd x)

end DoubleCentralizer
