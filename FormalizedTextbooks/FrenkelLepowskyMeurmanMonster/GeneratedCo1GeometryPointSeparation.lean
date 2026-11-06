/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCo1GeometryPoints
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationPhaseSeparation

/-! Actual short-vector classes cannot be norm-eight Conway geometry points. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual lattice minimum excludes zero reductions of norm-eight vectors. -/
theorem generatedCo1GeometryPoints_norm_eight_ne_zero (u : leechIntegral)
    (hu : leechSquareSum u.val = 64) : leechReduction u ≠ 0 := by
  intro hz
  obtain ⟨w, hw⟩ := (QuotientAddGroup.eq_zero_iff u).mp hz
  have hpoint (i : Fin 24) : u.val i = 2 * w.val i := by
    have hi := congrArg (fun x : leechIntegral => x.val i) hw
    simpa only [leechDouble, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      two_nsmul, Submodule.coe_add, Pi.add_apply, ← two_mul] using hi.symm
  have he : u.val = fun i => 2 * w.val i := funext hpoint
  have hs : leechSquareSum u.val = 4 * leechSquareSum w.val := by
    rw [he]
    simp only [leechSquareSum, mul_pow, show (2 : ℤ) ^ 2 = 4 by norm_num,
      Finset.mul_sum]
  rw [hu] at hs
  have hw0 : w.val ≠ 0 := by
    intro hzero
    have hs0 : leechSquareSum w.val = 0 := by simp [hzero, leechSquareSum]
    rw [hs0] at hs
    norm_num at hs
  have hm := leechIntegral_minimum w.val w.property hw0
  omega

/-- Every actual norm-eight Conway geometry point is a nonzero binary vector. -/
theorem generatedCo1GeometryPoints_ne_zero (v : Fin 24 → ZMod 2)
    (hv : v ∈ generatedCo1GeometryPoints) : v ≠ 0 := by
  obtain ⟨x, ⟨e, he⟩, rfl⟩ := hv
  intro hz
  have hx : x = 0 := leechHyperbolicCoordinates.injective (by simpa using hz)
  change leechReduction (leechIntegralAction e (leechCoordinateFrameLattice 0)) = x at he
  exact generatedCo1GeometryPoints_norm_eight_ne_zero
    (leechIntegralAction e (leechCoordinateFrameLattice 0))
    (by
      rw [leechIntegralAction_squareSum]
      exact leechCoordinateFrameVector_square 0) (he.trans hx)

/-- No genuine preferred short-vector class is a Conway norm-eight frame-class point. -/
theorem generatedCo1GeometryPoints_short_not_mem (r : GriessShortIndex) :
    leechHyperbolicCoordinates (griessShortClass r) ∉ generatedCo1GeometryPoints := by
  rintro ⟨x, ⟨e, he⟩, hx⟩
  change leechReduction (leechIntegralAction e (leechCoordinateFrameLattice 0)) = x at he
  have hc := leechHyperbolicCoordinates.injective hx
  have hn := generatedAxis_short_norm_eight_class_ne (griessShortLatticeVector r)
    (leechIntegralAction e (leechCoordinateFrameLattice 0))
    (griessShortIntegral_squareSum r)
    (by
      rw [leechIntegralAction_squareSum]
      exact leechCoordinateFrameVector_square 0)
  exact hn (he.trans hc).symm

/-- No genuine preferred Q short lift has binary base in the Conway norm-eight point set. -/
theorem generatedCo1GeometryPoints_short_base_not_mem (r : GriessShortIndex) :
    Multiplicative.toAdd (griessShortQ r).base ∉ generatedCo1GeometryPoints :=
  generatedCo1GeometryPoints_short_not_mem r

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
