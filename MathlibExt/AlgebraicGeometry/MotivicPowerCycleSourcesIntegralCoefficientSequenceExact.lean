/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicBocksteinModels

/-!
# Short exactness of the integral coefficient sequence

For a prime `ℓ`, the integral coefficient sequence
`0 → ℤ → ℤ → ℤ/ℓ → 0`, multiplication by `ℓ` followed by reduction modulo `ℓ`,
is short exact.

Source: Voevodsky, arXiv:math/0107109v1, Construction 5.3 and Sections 6/9.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MotivicPowerCycleSourcesWanted

open MathlibExt.AlgebraicGeometry.MotivicBocksteinModels

/-- For a prime ℓ, the sequence of $\mathbb{Z}$-modules
$0 \to \mathbb{Z} \to \mathbb{Z} \to \mathbb{Z}/\ell \to 0$, multiplication by ℓ followed by
reduction modulo ℓ, is short exact. -/
theorem integralCoefficientSequenceExact (ell : ℕ) [Fact ell.Prime] :
    (integralSequence ell).ShortExact := by
  have hp : ell.Prime := Fact.out
  have hne : (ell : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  refine ModuleCat.shortComplex_shortExact _ ?ex ?inj ?surj
  · intro y
    constructor
    · intro hy
      have hcast : ((y.down : ℤ) : ZMod ell) = 0 := ULift.up_inj.mp hy
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hcast
      obtain ⟨k, hk⟩ := hcast
      refine ⟨ULift.up k, ?_⟩
      change ULift.up ((ell : ℤ) * k) = y
      rw [← hk]
      exact ULift.up_down y
    · rintro ⟨x, rfl⟩
      apply ULift.ext
      change (((ell : ℤ) * x.down : ℤ) : ZMod ell) = 0
      simp
  · intro x y h
    change ULift.up ((ell : ℤ) * x.down) = ULift.up ((ell : ℤ) * y.down) at h
    have hdown : x.down = y.down := mul_left_cancel₀ hne (ULift.up_inj.mp h)
    exact ULift.ext hdown
  · intro z
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective z.down
    refine ⟨ULift.up a, ?_⟩
    change ULift.up ((a : ℤ) : ZMod ell) = z
    rw [ha]
    exact ULift.up_down z

end WantedExt.AlgebraicGeometry.MotivicPowerCycleSourcesWanted
