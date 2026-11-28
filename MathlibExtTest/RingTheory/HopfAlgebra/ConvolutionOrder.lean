/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.HopfAlgebra.ConvolutionOrder
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

@[expose] public section

universe u v w

open WithConv

/-- The restated theorem applied with the original binders. -/
private theorem exactSource
    (R : Type u) [CommRing R]
    (H : Type v) [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
    [Module.Finite R H] [Module.Free R H]
    (T : Type w) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)) :
    f ^ Module.finrank R H = 1 :=
  HopfAlgebra.convPow_finrank_eq_one_of_isCocomm R H T f

/-- The sign character of the group ring `ℤ[ℤˣ]` of the cyclic group `ℤˣ = {1, -1}` of order
two, as a point of the convolution monoid: it sends the group element `u` to `u`. -/
private noncomputable def signPoint : WithConv (MonoidAlgebra ℤ ℤˣ →ₐ[ℤ] ℤ) :=
  toConv (MonoidAlgebra.lift ℤ ℤ ℤˣ (Units.coeHom ℤ))

/-- Rank two at a nonidentity point: `ℤ[ℤˣ]` is free of rank two over `ℤ`, so the theorem gives
`signPoint ^ 2 = 1`, while `signPoint ≠ 1` because it sends `-1` to `-1` and the identity point
sends it to its counit `1`. -/
example : signPoint ^ 2 = 1 ∧ signPoint ≠ 1 := by
  have : Module.Finite ℤ (MonoidAlgebra ℤ ℤˣ) := .of_basis (MonoidAlgebra.basis ℤˣ ℤ)
  have hrank : Module.finrank ℤ (MonoidAlgebra ℤ ℤˣ) = 2 := by
    rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis ℤˣ ℤ), Fintype.card_units_int]
  refine ⟨?_, fun h => ?_⟩
  · have h2 := HopfAlgebra.convPow_finrank_eq_one_of_isCocomm ℤ (MonoidAlgebra ℤ ℤˣ) ℤ signPoint
    rwa [hrank] at h2
  · have h1 := congrArg (fun f : WithConv (MonoidAlgebra ℤ ℤˣ →ₐ[ℤ] ℤ) =>
      f (MonoidAlgebra.single (-1 : ℤˣ) (1 : ℤ))) h
    simp [signPoint] at h1
