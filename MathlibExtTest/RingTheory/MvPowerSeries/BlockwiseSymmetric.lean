/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPowerSeries.BlockwiseSymmetric

@[expose] public section

universe u

/-- Consumer with the original binders: a commutative ring `k`, a finite
number `m` of blocks, and block sizes `rs : Fin m → ℕ`. -/
noncomputable example (k : Type u) [CommRing k] (m : ℕ) (rs : Fin m → ℕ) :
    letI := MvPowerSeries.blockPermMulSemiringAction k m rs
    letI := MvPowerSeries.blockPermSMulCommClass k m rs
    (FixedPoints.subalgebra k (MvPowerSeries (Fin (∑ j, rs j)) k)
        (∀ j, Equiv.Perm (Fin (rs j))))
      ≃ₐ[k] MvPowerSeries (Fin (∑ j, rs j)) k :=
  MvPowerSeries.mvPowerSeriesBlockFixedEquiv k m rs

/-- Higher-universe consumer. -/
noncomputable example (k : Type (u + 1)) [CommRing k] (m : ℕ) (rs : Fin m → ℕ) :
    letI := MvPowerSeries.blockPermMulSemiringAction k m rs
    letI := MvPowerSeries.blockPermSMulCommClass k m rs
    (FixedPoints.subalgebra k (MvPowerSeries (Fin (∑ j, rs j)) k)
        (∀ j, Equiv.Perm (Fin (rs j))))
      ≃ₐ[k] MvPowerSeries (Fin (∑ j, rs j)) k :=
  MvPowerSeries.mvPowerSeriesBlockFixedEquiv k m rs

/-- Boundary: with no blocks, the equivalence still applies. -/
noncomputable example (k : Type u) [CommRing k] (rs : Fin 0 → ℕ) :
    letI := MvPowerSeries.blockPermMulSemiringAction k 0 rs
    letI := MvPowerSeries.blockPermSMulCommClass k 0 rs
    (FixedPoints.subalgebra k (MvPowerSeries (Fin (∑ j, rs j)) k)
        (∀ j, Equiv.Perm (Fin (rs j))))
      ≃ₐ[k] MvPowerSeries (Fin (∑ j, rs j)) k :=
  MvPowerSeries.mvPowerSeriesBlockFixedEquiv k 0 rs
