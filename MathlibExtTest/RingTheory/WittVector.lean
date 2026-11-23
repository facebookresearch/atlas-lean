/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.WittVector.Basic

@[expose] public section

universe u v

example {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime] (hp : (p : R) ∈ nonZeroDivisors R)
    (n : ℕ) (x y : WittVector p R)
    (h : ∀ k < n, WittVector.ghostComponent k x = WittVector.ghostComponent k y) :
    ∀ k < n, x.coeff k = y.coeff k :=
  WittVector.coeff_eq_coeff_of_forall_ghostComponent_eq p hp n x y h

example {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime] (σ : R →+* R)
    (hσ : ∀ a : R, σ a - a ^ p ∈ Ideal.span {(p : R)})
    (n : ℕ) (g : ℕ → R)
    (hg : ∀ k : ℕ, k + 1 < n → g (k + 1) - σ (g k) ∈ Ideal.span {(p : R) ^ (k + 1)}) :
    ∃ x : WittVector p R, ∀ k < n, WittVector.ghostComponent k x = g k :=
  WittVector.exists_forall_ghostComponent_eq_of_sub_frobeniusLift_mem p σ hσ n g hg

example (p : ℕ) [Fact p.Prime]
    {F : Type u} [Field F] [Finite F] [CharP F p]
    {k : Type v} [CommRing k] [CharP k p] [PerfectRing k p]
    (ι : WittVector p F →+* WittVector p k) (x : WittVector p F) :
    ι (WittVector.frobenius x) = WittVector.frobenius (ι x) :=
  WittVector.ringHom_map_frobenius_of_finite p ι x

example {S : Type u} [CommRing S] (p : ℕ) [Fact p.Prime] (hp : (p : S) ∈ nonZeroDivisors S)
    (hred : IsReduced (S ⧸ Ideal.span {(p : S)}))
    (z : WittVector p S) (N : ℕ)
    (hz : WittVector.ghostComponent (N - 1) z ∈ Ideal.span {(p : S) ^ N}) :
    ∀ j : ℕ, j < N → z.coeff j ∈ Ideal.span {(p : S)} :=
  WittVector.coeff_mem_span_of_ghostComponent_mem_span_pow_of_isReduced p hp hred z N hz
