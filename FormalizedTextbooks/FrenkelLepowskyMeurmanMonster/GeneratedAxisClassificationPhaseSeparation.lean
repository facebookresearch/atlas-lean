/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationPhaseCharacters
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionOmegaClass

/-! A short class cannot equal the actual norm-eight Ω class. The proof uses
both integral half-sum vectors and the genuine lattice minimum. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Integral vectors of squared physical norms four and eight cannot have
the same genuine lattice class modulo twice the lattice. -/
theorem generatedAxis_short_norm_eight_class_ne (u v : leechIntegral)
    (hu : leechSquareSum u.val = 32) (hv : leechSquareSum v.val = 64) :
    leechReduction u ≠ leechReduction v := by
  intro he
  have hz : leechReduction (u - v) = 0 := by rw [map_sub, he, sub_self]
  have hm : u - v ∈ twiceLeechIntegral := (QuotientAddGroup.eq_zero_iff (u - v)).mp hz
  obtain ⟨w, hw⟩ := hm
  have hpoint (i : Fin 24) : 2 * w.val i = u.val i - v.val i := by
    have h := congrArg (fun x : leechIntegral => x.val i) hw
    simpa only [leechDouble, AddMonoidHom.coe_mk, ZeroHom.coe_mk, two_nsmul,
      Submodule.coe_add, Pi.add_apply, Submodule.coe_sub, Pi.sub_apply, ← two_mul] using h
  have hsum : 2 * (leechSquareSum w.val + leechSquareSum (w + v).val) = 96 := by
    have hp (i : Fin 24) :
        2 * (w.val i ^ 2 + (w.val i + v.val i) ^ 2) = u.val i ^ 2 + v.val i ^ 2 := by
      have hi : u.val i = 2 * w.val i + v.val i := by linarith [hpoint i]
      rw [hi]
      ring
    have h := congrArg (fun f : Fin 24 → ℤ => ∑ i, f i) (funext hp)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
    change 2 * (leechSquareSum w.val + leechSquareSum (w + v).val) =
      leechSquareSum u.val + leechSquareSum v.val at h
    rw [hu, hv] at h
    exact h
  have hw0 : w.val ≠ 0 := by
    intro h
    have huv : u.val = v.val := by
      funext i
      have hp := hpoint i
      simp only [h, Pi.zero_apply] at hp
      omega
    rw [huv, hv] at hu
    omega
  have hwv0 : (w + v).val ≠ 0 := by
    intro h
    have huv : u.val = -v.val := by
      funext i
      have hp := hpoint i
      have hn := congrFun h i
      change w.val i + v.val i = 0 at hn
      change u.val i = -v.val i
      omega
    have hneg : leechSquareSum u.val = leechSquareSum v.val := by
      rw [huv]
      simp [leechSquareSum]
    omega
  have ha := leechIntegral_minimum w.val w.property hw0
  have hb := leechIntegral_minimum (w + v).val (w + v).property hwv0
  omega

/-- Every actual preferred short lift has binary base different from Ω. -/
theorem generatedAxis_short_base_ne_omega (r : GriessShortIndex) :
    (griessShortQ r).base ≠ sourceOmegaQ.base := by
  intro he
  have h := congrArg toAdd he
  change leechHyperbolicCoordinates (griessShortClass r) =
    toAdd (qQuotHom sourceOmegaQ) at h
  rw [sourceOmegaQ_eq_frame_class] at h
  apply generatedAxis_short_norm_eight_class_ne (griessShortLatticeVector r)
    (leechCoordinateFrameLattice 0)
    (griessShortIntegral_squareSum r) (leechCoordinateFrameVector_square 0)
  exact leechHyperbolicCoordinates.injective h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
