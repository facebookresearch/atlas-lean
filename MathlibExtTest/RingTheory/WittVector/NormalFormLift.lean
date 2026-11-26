/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.WittVector.NormalFormLift

@[expose] public section

open Polynomial

universe u v

private theorem exactSource
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [IsAlgClosed K] [CharP K p]
    (n : ℕ) (B : Type v) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra K[X] B] (b : Module.Basis (Fin (n + 1)) K[X] B) (d : Fin (n + 1) → ℕ)
    (hb0 : b 0 = 1) (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (hdeg : ∀ i j k, i ≠ 0 → j ≠ 0 →
      ((b.repr (b i * b j)) k).natDegree ≤ d i + d j - d k)
    (hinf : ∃ τ : Fin (n + 1) → Fin (n + 1) → K,
      IsUnit (Matrix.det (Matrix.of τ)) ∧
      (∀ j, τ j 0 = 1) ∧
      ∀ j i i', i ≠ 0 → i' ≠ 0 →
        τ j i * τ j i' = ∑ k, ((b.repr (b i * b i')) k).coeff (d i + d i' - d k) * τ j k) :
    ∃ (Bt : Type u) (_ : CommRing Bt) (_ : Algebra (WittVector p K)[X] Bt)
      (bt : Module.Basis (Fin (n + 1)) (WittVector p K)[X] Bt) (π : Bt →+* B),
      bt 0 = 1 ∧
      (∀ i j k, i ≠ 0 → j ≠ 0 → ((bt.repr (bt i * bt j)) k).natDegree ≤ d i + d j - d k) ∧
      (∀ f : (WittVector p K)[X],
        π (algebraMap (WittVector p K)[X] Bt f) =
          algebraMap K[X] B (f.map (WittVector.constantCoeff : WittVector p K →+* K))) ∧
      (∀ i, π (bt i) = b i) :=
  AlgebraicCurve.exists_wittVector_lift_of_normalFormOrder p K n B b d hb0 hd0 hd hdeg hinf

-- The same statement with both types in `Type 1`.
example
    (p : ℕ) [Fact p.Prime] (K : Type 1) [Field K] [IsAlgClosed K] [CharP K p]
    (n : ℕ) (B : Type 1) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra K[X] B] (b : Module.Basis (Fin (n + 1)) K[X] B) (d : Fin (n + 1) → ℕ)
    (hb0 : b 0 = 1) (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (hdeg : ∀ i j k, i ≠ 0 → j ≠ 0 →
      ((b.repr (b i * b j)) k).natDegree ≤ d i + d j - d k)
    (hinf : ∃ τ : Fin (n + 1) → Fin (n + 1) → K,
      IsUnit (Matrix.det (Matrix.of τ)) ∧
      (∀ j, τ j 0 = 1) ∧
      ∀ j i i', i ≠ 0 → i' ≠ 0 →
        τ j i * τ j i' = ∑ k, ((b.repr (b i * b i')) k).coeff (d i + d i' - d k) * τ j k) :
    ∃ (Bt : Type 1) (_ : CommRing Bt) (_ : Algebra (WittVector p K)[X] Bt)
      (bt : Module.Basis (Fin (n + 1)) (WittVector p K)[X] Bt) (π : Bt →+* B),
      bt 0 = 1 ∧
      (∀ i j k, i ≠ 0 → j ≠ 0 → ((bt.repr (bt i * bt j)) k).natDegree ≤ d i + d j - d k) ∧
      (∀ f : (WittVector p K)[X],
        π (algebraMap (WittVector p K)[X] Bt f) =
          algebraMap K[X] B (f.map (WittVector.constantCoeff : WittVector p K →+* K))) ∧
      (∀ i, π (bt i) = b i) :=
  AlgebraicCurve.exists_wittVector_lift_of_normalFormOrder p K n B b d hb0 hd0 hd hdeg hinf
