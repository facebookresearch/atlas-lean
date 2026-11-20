/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPowerSeries.SpecialFibreCoordinates

@[expose] public section

open MvPowerSeries
open scoped TensorProduct

universe u v w

/-- Consumer with the original binders. -/
example
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (R₀ : ℕ → Type v) [∀ v, CommRing (R₀ v)] [∀ v, Algebra 𝓞 (R₀ v)]
    [∀ v, Module.Free 𝓞 (R₀ v)] [∀ v, Module.Finite 𝓞 (R₀ v)]
    (t₀ : ∀ v, R₀ (v + 1) →ₐ[𝓞] R₀ v)
    {σ : Type w} [Finite σ] (x : ∀ v, σ → R₀ v) (hxt : ∀ v i, t₀ v (x (v + 1) i) = x v i)
    (hxrad : ∀ v i, x v i ∈ (Ideal.span {(p : R₀ v)}).radical)
    (hxsurj : ∀ v, Function.Surjective
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i) :
        MvPolynomial σ (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R₀ v)))
    (hxker : ∀ N : ℕ, ∃ v, RingHom.ker
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i) :
        MvPolynomial σ (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R₀ v)) ≤
      (Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ (ZMod p)))) ^ N) :
    ∃ π : ∀ v, MvPowerSeries σ 𝓞 →ₐ[𝓞] R₀ v,
      (∀ v i, π v (X i) = x v i) ∧
      (∀ v, Function.Surjective (π v)) ∧
      (∀ v, (t₀ v).comp (π (v + 1)) = π v) ∧
      (∀ v i, π v (X i) ∈ (Ideal.span {(p : R₀ v)}).radical) ∧
      (∀ v G, π v G = MvPowerSeries.adicEval (Ideal.span {(p : R₀ v)}) (fun i => π v (X i)) G) ∧
      (∀ G, (∀ v, π v G = 0) → G = 0) ∧
      (∀ z : ∀ v, R₀ v, (∀ v, t₀ v (z (v + 1)) = z v) → ∃ G, ∀ v, π v G = z v) :=
  MvPowerSeries.exists_algHom_adicEval_forall_comp_eq_of_specialFibre_coordinates
    p hp hker R₀ t₀ x hxt hxrad hxsurj hxker

/-- Higher-universe consumer. -/
example
    {𝓞 : Type (u + 1)} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (R₀ : ℕ → Type (v + 1)) [∀ v, CommRing (R₀ v)] [∀ v, Algebra 𝓞 (R₀ v)]
    [∀ v, Module.Free 𝓞 (R₀ v)] [∀ v, Module.Finite 𝓞 (R₀ v)]
    (t₀ : ∀ v, R₀ (v + 1) →ₐ[𝓞] R₀ v)
    {σ : Type (w + 1)} [Finite σ] (x : ∀ v, σ → R₀ v) (hxt : ∀ v i, t₀ v (x (v + 1) i) = x v i)
    (hxrad : ∀ v i, x v i ∈ (Ideal.span {(p : R₀ v)}).radical)
    (hxsurj : ∀ v, Function.Surjective
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i) :
        MvPolynomial σ (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R₀ v)))
    (hxker : ∀ N : ℕ, ∃ v, RingHom.ker
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i) :
        MvPolynomial σ (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R₀ v)) ≤
      (Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ (ZMod p)))) ^ N) :
    ∃ π : ∀ v, MvPowerSeries σ 𝓞 →ₐ[𝓞] R₀ v,
      (∀ v i, π v (X i) = x v i) ∧
      (∀ v, Function.Surjective (π v)) ∧
      (∀ v, (t₀ v).comp (π (v + 1)) = π v) ∧
      (∀ v i, π v (X i) ∈ (Ideal.span {(p : R₀ v)}).radical) ∧
      (∀ v G, π v G = MvPowerSeries.adicEval (Ideal.span {(p : R₀ v)}) (fun i => π v (X i)) G) ∧
      (∀ G, (∀ v, π v G = 0) → G = 0) ∧
      (∀ z : ∀ v, R₀ v, (∀ v, t₀ v (z (v + 1)) = z v) → ∃ G, ∀ v, π v G = z v) :=
  MvPowerSeries.exists_algHom_adicEval_forall_comp_eq_of_specialFibre_coordinates
    p hp hker R₀ t₀ x hxt hxrad hxsurj hxker

/-- `adicEval` sends the variable `X s` to the coordinate `x s`. -/
example {R S σ : Type*} [CommRing R] [CommRing S] [Algebra R S] (J : Ideal S) (x : σ → S)
    (s : σ) : MvPowerSeries.adicEval J x (X s : MvPowerSeries σ R) = x s :=
  MvPowerSeries.adicEval_X J x s

/-- On polynomials, `adicEval` is polynomial evaluation, for any ideal. -/
example {R S σ : Type*} [CommRing R] [CommRing S] [Algebra R S] (J : Ideal S) (x : σ → S)
    (q : MvPolynomial σ R) :
    MvPowerSeries.adicEval J x (q : MvPowerSeries σ R) = MvPolynomial.aeval x q :=
  MvPowerSeries.adicEval_coe J x q

/-- An element of the radical of `J` is topologically nilpotent for the `J`-adic topology. -/
example {S : Type*} [CommRing S] (J : Ideal S) {a : S} (ha : a ∈ J.radical) :
    letI : TopologicalSpace S := J.adicTopology
    IsTopologicallyNilpotent a :=
  Ideal.isTopologicallyNilpotent_of_mem_radical J ha

/-- For a complete `S` and coordinates in the radical, `adicEval` is multiplicative. -/
example {R S σ : Type*} [CommRing R] [CommRing S] [Algebra R S] [Finite σ] (J : Ideal S)
    [IsAdicComplete J S] (x : σ → S) (hx : ∀ s, x s ∈ J.radical) (f g : MvPowerSeries σ R) :
    MvPowerSeries.adicEval J x (f * g) =
      MvPowerSeries.adicEval J x f * MvPowerSeries.adicEval J x g := by
  rw [← MvPowerSeries.coe_adicEvalAlgHom J hx, map_mul]
