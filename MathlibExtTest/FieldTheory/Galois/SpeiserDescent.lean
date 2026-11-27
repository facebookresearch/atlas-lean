/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.FieldTheory.Galois.SpeiserDescent
import Mathlib.FieldTheory.Galois.IsGaloisGroup

/-! Tests for Speiser's lemma: fixed vectors linearly independent over the fixed ring are
linearly independent; for a group acting on a field through a finite quotient, the vectors fixed
by the kernel are combinations of fixed vectors; and, for the Galois group of a finite Galois
extension `L/K`, the natural map `L ⊗_K W^Gal → W` is an isomorphism and
`dim_K W^Gal = dim_L W`, with `W = L` as an example. -/

open scoped TensorProduct
open Module

variable {K L W : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup W] [Module L W]
  [Module K W] [IsScalarTower K L W]

-- Fixed vectors linearly independent over the ring of invariants are linearly independent,
-- for any group.
example {Γ : Type*} [Group Γ] [MulSemiringAction Γ L] [DistribMulAction Γ W]
    (hsl : ∀ (g : Γ) (a : L) (w : W), g • a • w = (g • a) • g • w) {ι : Type*} {v : ι → W}
    (hv : ∀ i (g : Γ), g • v i = v i) (hli : LinearIndependent (FixedPoints.subring L Γ) v) :
    LinearIndependent L v :=
  FixedPoints.linearIndependent_of_linearIndependent_subring (Field.toIsField L) hsl hv hli

-- For a group acting on `L` through a finite quotient, the vectors fixed by the kernel are
-- combinations of fixed vectors.
example {Γ : Type*} [Group Γ] [MulSemiringAction Γ L] [DistribMulAction Γ W]
    (hsl : ∀ (g : Γ) (a : L) (w : W), g • a • w = (g • a) • g • w) (N : Subgroup Γ)
    [N.FiniteIndex] (hNL : ∀ g : Γ, g ∈ N ↔ ∀ a : L, g • a = a) {w : W}
    (hw : ∀ g ∈ N, g • w = w) : w ∈ Submodule.span L (MulAction.fixedPoints Γ W) :=
  FixedPoints.mem_span_of_finiteIndex (Field.toIsField L) hsl N hNL hw

-- Invariant vectors linearly independent over `K` are linearly independent over `L`, for any
-- group whose fixed elements of `L` lie in the image of `K`.
example {Γ : Type*} [Group Γ] [MulSemiringAction Γ L] [Algebra.IsInvariant K L Γ]
    [DistribMulAction Γ W] [SMulCommClass Γ K W]
    (hsl : ∀ (g : Γ) (a : L) (w : W), g • a • w = (g • a) • g • w) {ι : Type*}
    {v : ι → (Representation.ofDistribMulAction K Γ W).invariants}
    (hv : LinearIndependent K v) : LinearIndependent L fun i => (v i : W) :=
  Algebra.IsInvariant.linearIndependent_invariants hsl hv

-- Speiser's lemma for the Galois group of a finite Galois extension: `L ⊗_K W^Gal ≃ W` and
-- `dim_K W^Gal = dim_L W`.
example [FiniteDimensional K L] [IsGalois K L] [DistribMulAction Gal(L/K) W]
    [SMulCommClass Gal(L/K) K W]
    (hsl : ∀ (g : Gal(L/K)) (a : L) (w : W), g • a • w = (g • a) • g • w) :
    Function.Bijective
        ((Representation.ofDistribMulAction K Gal(L/K) W).invariants.subtype.liftBaseChange L) ∧
      finrank K (Representation.ofDistribMulAction K Gal(L/K) W).invariants = finrank L W :=
  ⟨IsGaloisGroup.bijective_liftBaseChange_invariants hsl, IsGaloisGroup.finrank_invariants hsl⟩

-- The isomorphism maps `a ⊗ w` to `a • w`.
example [FiniteDimensional K L] [IsGalois K L] [DistribMulAction Gal(L/K) W]
    [SMulCommClass Gal(L/K) K W]
    (hsl : ∀ (g : Gal(L/K)) (a : L) (w : W), g • a • w = (g • a) • g • w) (a : L)
    (w : (Representation.ofDistribMulAction K Gal(L/K) W).invariants) :
    IsGaloisGroup.baseChangeInvariantsEquiv hsl (a ⊗ₜ w) = a • (w : W) := by
  simp

-- For `W = L` with the Galois action, `dim_K L^Gal = dim_L L = 1`.
example [FiniteDimensional K L] [IsGalois K L] :
    finrank K (Representation.ofDistribMulAction K Gal(L/K) L).invariants = 1 := by
  rw [IsGaloisGroup.finrank_invariants fun g a w => smul_mul' g a w, finrank_self]
