/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CerednikDrinfeld_DrinfeldQuadruple.lean` and
`Definitions/Def_CerednikDrinfeld_DrinfeldQuadrupleRelations.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import MathlibExt.AlgebraicGeometry.FormalOmega.DeligneFunctor

@[expose] public section

noncomputable section

open scoped TensorProduct MatrixGroups Matrix
open LT.LatticeTree TensorProduct

namespace CerednikDrinfeld
namespace FormalOmega


section DetIndex

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]

def HasDetIndex (π : 𝒪) (N : Submodule 𝒪 (Fin 2 → K)) (e : ℤ) : Prop :=
  ∃ g : GL (Fin 2) K, latticeMap g (stdLattice 𝒪 K) = N ∧
    ∃ u : 𝒪ˣ, ((Matrix.GeneralLinearGroup.det g : Kˣ) : K) = algebraMap 𝒪 K u * algebraMap 𝒪 K π ^ e

end DetIndex

section Datum

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable (B : Type) [CommRing B] [Algebra 𝒪 B]

abbrev locRing (x : PrimeSpectrum B) : Type := Localization.AtPrime x.asIdeal

abbrev toLocRing (x : PrimeSpectrum B) : B →ₐ[𝒪] locRing B x :=
  IsScalarTower.toAlgHom 𝒪 B (locRing B x)

abbrev stalk (x : PrimeSpectrum B) (T : Type) [AddCommGroup T] [Module B T] : Type :=
  LocalizedModule x.asIdeal.primeCompl T

variable {B}

def smulInto {N N' : Submodule 𝒪 (Fin 2 → K)} (h : ∀ v ∈ N, algebraMap 𝒪 K π • v ∈ N') : ↥N →ₗ[𝒪]
  ↥N' :=
  (DistribSMul.toLinearMap 𝒪 (Fin 2 → K) (algebraMap 𝒪 K π)).restrict h

theorem coe_smulInto_apply {N N' : Submodule 𝒪 (Fin 2 → K)} (h : ∀ v ∈ N, algebraMap 𝒪 K π • v ∈
  N') (v : ↥N) :
    ((smulInto π h v : ↥N') : Fin 2 → K) = algebraMap 𝒪 K π • (v : Fin 2 → K) := rfl

variable (B) in
structure DrinfeldDatum : Type 1 where

  N₀ : PrimeSpectrum B → Submodule 𝒪 (Fin 2 → K)

  N₁ : PrimeSpectrum B → Submodule 𝒪 (Fin 2 → K)
  full₀ : ∀ x, Submodule.IsFullLattice K (N₀ x)
  full₁ : ∀ x, Submodule.IsFullLattice K (N₁ x)

  le : ∀ x, N₀ x ≤ N₁ x

  smul_le : ∀ x, ∀ v ∈ N₁ x, algebraMap 𝒪 K π • v ∈ N₀ x

  isOpen_setOf_mem₀ : ∀ v : Fin 2 → K, IsOpen {x : PrimeSpectrum B | v ∈ N₀ x}
  isOpen_setOf_mem₁ : ∀ v : Fin 2 → K, IsOpen {x : PrimeSpectrum B | v ∈ N₁ x}

  T₀ : Type
  T₁ : Type
  [addCommGroup₀ : AddCommGroup T₀]
  [module₀ : Module B T₀]
  [addCommGroup₁ : AddCommGroup T₁]
  [module₁ : Module B T₁]
  invertible₀ : Module.Invertible B T₀
  invertible₁ : Module.Invertible B T₁

  Pi₀ : T₀ →ₗ[B] T₁
  Pi₁ : T₁ →ₗ[B] T₀
  Pi₁_Pi₀ : ∀ t, Pi₁ (Pi₀ t) = algebraMap 𝒪 B π • t
  Pi₀_Pi₁ : ∀ t, Pi₀ (Pi₁ t) = algebraMap 𝒪 B π • t

  u₀ : ∀ x : PrimeSpectrum B,
    latticeBaseChange 𝒪 K (locRing B x) ⟨N₀ x, full₀ x⟩ →ₗ[locRing B x] stalk B x T₀

  u₁ : ∀ x : PrimeSpectrum B,
    latticeBaseChange 𝒪 K (locRing B x) ⟨N₁ x, full₁ x⟩ →ₗ[locRing B x] stalk B x T₁

  u₁_incl : ∀ x w, u₁ x (inclBaseChange (locRing B x) (M' := ⟨N₀ x, full₀ x⟩) (M := ⟨N₁ x, full₁
    x⟩) (le x) w) =
    LocalizedModule.map x.asIdeal.primeCompl Pi₀ (u₀ x w)

  u₀_smul : ∀ x w, u₀ x (((smulInto π (smul_le x)).baseChange (locRing B x) :
      latticeBaseChange 𝒪 K (locRing B x) ⟨N₁ x, full₁ x⟩ →ₗ[locRing B x] latticeBaseChange 𝒪 K
        (locRing B x) ⟨N₀ x, full₀ x⟩) w) =
    LocalizedModule.map x.asIdeal.primeCompl Pi₁ (u₁ x w)

  u₀_surjective : ∀ x, Function.Surjective (u₀ x)
  u₁_surjective : ∀ x, Function.Surjective (u₁ x)

  u₀_continuous : ∀ (x : PrimeSpectrum B) (v : Fin 2 → K), v ∈ N₀ x →
    ∃ (f : B) (t : T₀), f ∉ x.asIdeal ∧ ∀ (y : PrimeSpectrum B) (hy : f ∉ y.asIdeal),
      ∃ hv : v ∈ N₀ y, u₀ y ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(N₀ y))) = LocalizedModule.mk t
        ⟨f, hy⟩
  u₁_continuous : ∀ (x : PrimeSpectrum B) (v : Fin 2 → K), v ∈ N₁ x →
    ∃ (f : B) (t : T₁), f ∉ x.asIdeal ∧ ∀ (y : PrimeSpectrum B) (hy : f ∉ y.asIdeal),
      ∃ hv : v ∈ N₁ y, u₁ y ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(N₁ y))) = LocalizedModule.mk t
        ⟨f, hy⟩

  locallyConstant₀ : ∀ x : PrimeSpectrum B, LinearMap.range Pi₀ ≤ x.asIdeal • (⊤ : Submodule B T₁) →
    ∃ U : Set (PrimeSpectrum B), IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, LinearMap.range Pi₀ ≤ y.asIdeal • (⊤ : Submodule B T₁) → N₀ y = N₀ x

  locallyConstant₁ : ∀ x : PrimeSpectrum B, LinearMap.range Pi₁ ≤ x.asIdeal • (⊤ : Submodule B T₀) →
    ∃ U : Set (PrimeSpectrum B), IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, LinearMap.range Pi₁ ≤ y.asIdeal • (⊤ : Submodule B T₀) → N₁ y = N₁ x

  injective₀ : ∀ (x : PrimeSpectrum B) (v : ↥(N₀ x)),
    u₀ x ((1 : locRing B x) ⊗ₜ[𝒪] v) ∈
      (LinearMap.range (LocalizedModule.map x.asIdeal.primeCompl Pi₁)).restrictScalars B ⊔
        x.asIdeal • (⊤ : Submodule B (stalk B x T₀)) →
    ∃ w ∈ N₁ x, (v : Fin 2 → K) = algebraMap 𝒪 K π • w

  injective₁ : ∀ (x : PrimeSpectrum B) (v : ↥(N₁ x)),
    u₁ x ((1 : locRing B x) ⊗ₜ[𝒪] v) ∈
      (LinearMap.range (LocalizedModule.map x.asIdeal.primeCompl Pi₀)).restrictScalars B ⊔
        x.asIdeal • (⊤ : Submodule B (stalk B x T₁)) →
    (v : Fin 2 → K) ∈ N₀ x

  hasDetIndex₀ : ∀ x : PrimeSpectrum B, LinearMap.range Pi₀ ≤ x.asIdeal • (⊤ : Submodule B T₁) →
    HasDetIndex π (N₀ x) 0

  hasDetIndex₁ : ∀ x : PrimeSpectrum B, LinearMap.range Pi₁ ≤ x.asIdeal • (⊤ : Submodule B T₀) →
    HasDetIndex π (N₁ x) (-1)

attribute [instance] DrinfeldDatum.addCommGroup₀ DrinfeldDatum.module₀ DrinfeldDatum.addCommGroup₁
  DrinfeldDatum.module₁
  DrinfeldDatum.invertible₀ DrinfeldDatum.invertible₁

namespace DrinfeldDatum

variable {π}

abbrev L₀ (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) : FullLattice 𝒪 K := ⟨Q.N₀ x,
  Q.full₀ x⟩

abbrev L₁ (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) : FullLattice 𝒪 K := ⟨Q.N₁ x,
  Q.full₁ x⟩

def stratum₀ (Q : DrinfeldDatum (K := K) π B) : Set (PrimeSpectrum B) :=
  {x | LinearMap.range Q.Pi₀ ≤ x.asIdeal • (⊤ : Submodule B Q.T₁)}

def stratum₁ (Q : DrinfeldDatum (K := K) π B) : Set (PrimeSpectrum B) :=
  {x | LinearMap.range Q.Pi₁ ≤ x.asIdeal • (⊤ : Submodule B Q.T₀)}

structure Iso (Q Q' : DrinfeldDatum (K := K) π B) : Type where
  N₀_eq : ∀ x, Q.N₀ x = Q'.N₀ x
  N₁_eq : ∀ x, Q.N₁ x = Q'.N₁ x
  τ₀ : Q.T₀ ≃ₗ[B] Q'.T₀
  τ₁ : Q.T₁ ≃ₗ[B] Q'.T₁
  τ₁_Pi₀ : ∀ t, τ₁ (Q.Pi₀ t) = Q'.Pi₀ (τ₀ t)
  τ₀_Pi₁ : ∀ t, τ₀ (Q.Pi₁ t) = Q'.Pi₁ (τ₁ t)
  τ₀_u₀ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → K) (hv : v ∈ Q.N₀ x) (hv' : v ∈ Q'.N₀ x),
    Q'.u₀ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥(Q'.N₀ x))) =
      LocalizedModule.map x.asIdeal.primeCompl τ₀.toLinearMap (Q.u₀ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v,
        hv⟩ : ↥(Q.N₀ x))))
  τ₁_u₁ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → K) (hv : v ∈ Q.N₁ x) (hv' : v ∈ Q'.N₁ x),
    Q'.u₁ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥(Q'.N₁ x))) =
      LocalizedModule.map x.asIdeal.primeCompl τ₁.toLinearMap (Q.u₁ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v,
        hv⟩ : ↥(Q.N₁ x))))

def IsIsomorphic (Q Q' : DrinfeldDatum (K := K) π B) : Prop := Nonempty (Iso Q Q')

/-- A Drinfeld datum `Q` is a quadruple of the Deligne datum `d` if at every point `x` the edge
`Q.L₀ x ⊆ Q.L₁ x` is nondegenerate for `d` at `x`, and the kernels of the stalk maps `Q.u₀ x` and
`Q.u₁ x` are the lines of the base change of `d` to the local ring at `x`. -/
def IsQuadrupleOf (Q : DrinfeldDatum (K := K) π B) (d : DeligneDatum (K := K) π B) : Prop :=
  ∀ x : PrimeSpectrum B,
    d.EdgeNondegAt π x.asIdeal (Q.L₀ x) (Q.L₁ x) ∧
    LinearMap.ker (Q.u₀ x) = (d.map π (toLocRing B x)).line (Q.L₀ x) ∧
    LinearMap.ker (Q.u₁ x) = (d.map π (toLocRing B x)).line (Q.L₁ x)

theorem IsQuadrupleOf.edge_iff (Q : DrinfeldDatum (K := K) π B) (d : DeligneDatum (K := K) π B)
    (x : PrimeSpectrum B) :
    d.EdgeNondegAt π x.asIdeal (Q.L₀ x) (Q.L₁ x) ↔
    (Q.N₀ x ≤ Q.N₁ x ∧ (∀ v : ↥(Q.N₁ x), algebraMap 𝒪 K π • (v : Fin 2 → K) ∈ Q.N₀ x) ∧
      (∀ v : ↥(Q.N₁ x), (v : Fin 2 → K) ∉ Q.N₀ x →
        (1 : B) ⊗ₜ[𝒪] v ∉ d.line (Q.L₁ x) ⊔
          (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (Q.L₁ x)))) ∧
      (∀ v' : ↥(Q.N₀ x),
        (¬ ∃ w : ↥(Q.N₁ x), (v' : Fin 2 → K) = algebraMap 𝒪 K π • (w : Fin 2 → K)) →
        (1 : B) ⊗ₜ[𝒪] v' ∉ d.line (Q.L₀ x) ⊔
          (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (Q.L₀ x))))) :=
  Iff.rfl


end DrinfeldDatum

end Datum


namespace DrinfeldDatum


variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

section BaseChange

variable {B' : Type} [CommRing B'] [Algebra 𝒪 B']

abbrev pointUnder (f : B →ₐ[𝒪] B') (x' : PrimeSpectrum B') : PrimeSpectrum B :=
  PrimeSpectrum.comap (f : B →+* B') x'

structure BaseChangeAlong (f : B →ₐ[𝒪] B') (Q : DrinfeldDatum (K := K) π B) (Q' : DrinfeldDatum (K
  := K) π B') :
    Type where

  N₀_eq : ∀ x' : PrimeSpectrum B', Q'.N₀ x' = Q.N₀ (pointUnder f x')

  N₁_eq : ∀ x' : PrimeSpectrum B', Q'.N₁ x' = Q.N₁ (pointUnder f x')

  τ₀ : Q.T₀ →ₛₗ[(f : B →+* B')] Q'.T₀

  τ₁ : Q.T₁ →ₛₗ[(f : B →+* B')] Q'.T₁

  span_range_τ₀ : Submodule.span B' (Set.range τ₀) = ⊤

  span_range_τ₁ : Submodule.span B' (Set.range τ₁) = ⊤

  τ₁_Pi₀ : ∀ t, τ₁ (Q.Pi₀ t) = Q'.Pi₀ (τ₀ t)

  τ₀_Pi₁ : ∀ t, τ₀ (Q.Pi₁ t) = Q'.Pi₁ (τ₁ t)

  u₀_eq : ∀ (x' : PrimeSpectrum B') (v : Fin 2 → K) (hv : v ∈ Q.N₀ (pointUnder f x')) (hv' : v ∈
    Q'.N₀ x')
    (t : Q.T₀) (s : B) (hs : f s ∉ x'.asIdeal),
    Q.u₀ (pointUnder f x') ((1 : locRing B (pointUnder f x')) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(Q.N₀ (pointUnder f
      x')))) =
      LocalizedModule.mk t (⟨s, hs⟩ : (pointUnder f x').asIdeal.primeCompl) →
    Q'.u₀ x' ((1 : locRing B' x') ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥(Q'.N₀ x'))) =
      LocalizedModule.mk (τ₀ t) (⟨f s, hs⟩ : x'.asIdeal.primeCompl)

  u₁_eq : ∀ (x' : PrimeSpectrum B') (v : Fin 2 → K) (hv : v ∈ Q.N₁ (pointUnder f x')) (hv' : v ∈
    Q'.N₁ x')
    (t : Q.T₁) (s : B) (hs : f s ∉ x'.asIdeal),
    Q.u₁ (pointUnder f x') ((1 : locRing B (pointUnder f x')) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(Q.N₁ (pointUnder f
      x')))) =
      LocalizedModule.mk t (⟨s, hs⟩ : (pointUnder f x').asIdeal.primeCompl) →
    Q'.u₁ x' ((1 : locRing B' x') ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥(Q'.N₁ x'))) =
      LocalizedModule.mk (τ₁ t) (⟨f s, hs⟩ : x'.asIdeal.primeCompl)

def IsBaseChangeAlong (f : B →ₐ[𝒪] B') (Q : DrinfeldDatum (K := K) π B) (Q' : DrinfeldDatum (K :=
  K) π B') : Prop :=
  Nonempty (BaseChangeAlong f Q Q')

end BaseChange

section Translate

structure TranslateEven (g : GL (Fin 2) K) (c : Kˣ) (Q Q' : DrinfeldDatum (K := K) π B) : Type where

  N₀_eq : ∀ x : PrimeSpectrum B, Q'.N₀ x = latticeMap (scalarGL c * g⁻¹) (Q.N₀ x)

  N₁_eq : ∀ x : PrimeSpectrum B, Q'.N₁ x = latticeMap (scalarGL c * g⁻¹) (Q.N₁ x)

  τ₀ : Q.T₀ ≃ₗ[B] Q'.T₀

  τ₁ : Q.T₁ ≃ₗ[B] Q'.T₁
  τ₁_Pi₀ : ∀ t, τ₁ (Q.Pi₀ t) = Q'.Pi₀ (τ₀ t)
  τ₀_Pi₁ : ∀ t, τ₀ (Q.Pi₁ t) = Q'.Pi₁ (τ₁ t)

  τ₀_u₀ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → K) (hv : v ∈ Q.N₀ x)
    (hv' : ((scalarGL c * g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v ∈ Q'.N₀ x),
    Q'.u₀ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨_, hv'⟩ : ↥(Q'.N₀ x))) =
      LocalizedModule.map x.asIdeal.primeCompl τ₀.toLinearMap (Q.u₀ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v,
        hv⟩ : ↥(Q.N₀ x))))

  τ₁_u₁ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → K) (hv : v ∈ Q.N₁ x)
    (hv' : ((scalarGL c * g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v ∈ Q'.N₁ x),
    Q'.u₁ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨_, hv'⟩ : ↥(Q'.N₁ x))) =
      LocalizedModule.map x.asIdeal.primeCompl τ₁.toLinearMap (Q.u₁ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v,
        hv⟩ : ↥(Q.N₁ x))))

def IsTranslateEven (g : GL (Fin 2) K) (c : Kˣ) (Q Q' : DrinfeldDatum (K := K) π B) : Prop :=
  Nonempty (TranslateEven g c Q Q')

structure TranslateOdd (g : GL (Fin 2) K) (c₀ c₁ : Kˣ) (Q Q' : DrinfeldDatum (K := K) π B) : Type
  where

  c₀_eq : (c₀ : K) = algebraMap 𝒪 K π * c₁

  N₀_eq : ∀ x : PrimeSpectrum B, Q'.N₀ x = latticeMap (scalarGL c₀ * g⁻¹) (Q.N₁ x)

  N₁_eq : ∀ x : PrimeSpectrum B, Q'.N₁ x = latticeMap (scalarGL c₁ * g⁻¹) (Q.N₀ x)

  σ₀ : Q.T₁ ≃ₗ[B] Q'.T₀

  σ₁ : Q.T₀ ≃ₗ[B] Q'.T₁
  σ₁_Pi₁ : ∀ t, σ₁ (Q.Pi₁ t) = Q'.Pi₀ (σ₀ t)
  σ₀_Pi₀ : ∀ t, σ₀ (Q.Pi₀ t) = Q'.Pi₁ (σ₁ t)

  σ₀_u₀ : ∀ (x : PrimeSpectrum B) (w : Fin 2 → K) (hw : w ∈ Q.N₁ x)
    (hw' : ((scalarGL c₀ * g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w ∈ Q'.N₀ x),
    Q'.u₀ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨_, hw'⟩ : ↥(Q'.N₀ x))) =
      LocalizedModule.map x.asIdeal.primeCompl σ₀.toLinearMap (Q.u₁ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨w,
        hw⟩ : ↥(Q.N₁ x))))

  σ₁_u₁ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → K) (hv : v ∈ Q.N₀ x)
    (hv' : ((scalarGL c₁ * g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v ∈ Q'.N₁ x),
    Q'.u₁ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨_, hv'⟩ : ↥(Q'.N₁ x))) =
      LocalizedModule.map x.asIdeal.primeCompl σ₁.toLinearMap (Q.u₀ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v,
        hv⟩ : ↥(Q.N₀ x))))

def IsTranslateOdd (g : GL (Fin 2) K) (c₀ c₁ : Kˣ) (Q Q' : DrinfeldDatum (K := K) π B) : Prop :=
  Nonempty (TranslateOdd g c₀ c₁ Q Q')

def Iso.toTranslateEven {Q Q' : DrinfeldDatum (K := K) π B} (e : Iso Q Q') : TranslateEven 1 1 Q Q'
  where
  N₀_eq x := by rw [scalarGL_one, one_mul, inv_one, latticeMap_one]; exact (e.N₀_eq x).symm
  N₁_eq x := by rw [scalarGL_one, one_mul, inv_one, latticeMap_one]; exact (e.N₁_eq x).symm
  τ₀ := e.τ₀
  τ₁ := e.τ₁
  τ₁_Pi₀ := e.τ₁_Pi₀
  τ₀_Pi₁ := e.τ₀_Pi₁
  τ₀_u₀ x v hv hv' := by
    have h1 : ((scalarGL (1 : Kˣ) * (1 : GL (Fin 2) K)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2)
      K) *ᵥ v = v := by
      rw [scalarGL_one, one_mul, inv_one, Units.val_one, Matrix.one_mulVec]
    have hv'' : v ∈ Q'.N₀ x := by rw [← h1]; exact hv'
    have key := e.τ₀_u₀ x v hv hv''
    have hsub : (⟨_, hv'⟩ : ↥(Q'.N₀ x)) = ⟨v, hv''⟩ := Subtype.ext h1
    rw [hsub]; exact key
  τ₁_u₁ x v hv hv' := by
    have h1 : ((scalarGL (1 : Kˣ) * (1 : GL (Fin 2) K)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2)
      K) *ᵥ v = v := by
      rw [scalarGL_one, one_mul, inv_one, Units.val_one, Matrix.one_mulVec]
    have hv'' : v ∈ Q'.N₁ x := by rw [← h1]; exact hv'
    have key := e.τ₁_u₁ x v hv hv''
    have hsub : (⟨_, hv'⟩ : ↥(Q'.N₁ x)) = ⟨v, hv''⟩ := Subtype.ext h1
    rw [hsub]; exact key

end Translate


/-- Being a base change along `f` is exactly the existence of the
base-change data. -/
theorem isBaseChangeAlong_iff {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (f : B →ₐ[𝒪] B') (Q : DrinfeldDatum (K := K) π B)
    (Q' : DrinfeldDatum (K := K) π B') :
    IsBaseChangeAlong f Q Q' ↔ Nonempty (BaseChangeAlong f Q Q') :=
  Iff.rfl

/-- Being an even translate is exactly the existence of the translate data. -/
theorem isTranslateEven_iff (g : GL (Fin 2) K) (c : Kˣ)
    (Q Q' : DrinfeldDatum (K := K) π B) :
    IsTranslateEven g c Q Q' ↔ Nonempty (TranslateEven g c Q Q') :=
  Iff.rfl

/-- Being an odd translate is exactly the existence of the translate data. -/
theorem isTranslateOdd_iff (g : GL (Fin 2) K) (c₀ c₁ : Kˣ)
    (Q Q' : DrinfeldDatum (K := K) π B) :
    IsTranslateOdd g c₀ c₁ Q Q' ↔ Nonempty (TranslateOdd g c₀ c₁ Q Q') :=
  Iff.rfl

end DrinfeldDatum

end FormalOmega
end CerednikDrinfeld

end
