/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:

`TauCeti/NumberTheory/ClassFieldTheory/Brauer/Invariant.lean`
(TauCeti, revision `62bbc0596dc3539d488232e4e924a338548ea0a9`):
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Tau Ceti contributors.

Modifications: the arithmetic Frobenius and the primitive cyclic cocycle are specified on
native field, valuation-ring, residue-field and cocycle objects; the comparison with the
proved TauCeti invariant is an explicit construction request, not a claim that local class
field theory is missing.
-/
module

public import MathlibExt.AlgebraicGeometry.BrauerCorestriction
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Arithmetic Frobenius normalization of the local invariant

The invariant target is the actual `ℚ/ℤ`. An unramified cyclic layer is
normalized by the action of arithmetic Frobenius on its actual residue field.
The primitive class is the cocycle whose value is a base uniformizer exactly
when the two Frobenius exponents carry past the degree. Its invariant is
`1/[E:K]`, fixing the sign of the local invariant on the actual coefficient
object rather than on an arbitrary evaluation group.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.BrauerLocalInvariant

open BrauerCoefficients BrauerCorestriction
open ValuativeRel Valued.integer

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

section Layers

variable (E : IntermediateField K (SeparableClosure K))
  [FiniteDimensional K E] [IsGalois K E]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeExtension K E]

/-- A cyclic unramified layer, pinned to arithmetic Frobenius in the actual
residue field and to the original field automorphisms on its valuation ring. -/
structure FrobeniusLayer where
  unramified_value_group : Function.Surjective (ValuativeExtension.mapValueGroupWithZero K E)
  integersAction : Gal(E/K) →* (𝒪[E] ≃+* 𝒪[E])
  integersAction_normalized : ∀ (g : Gal(E/K)) (x : 𝒪[E]),
    (integersAction g x).val = g x.val
  frobenius : Gal(E/K)
  residue_frobenius : ∀ x : 𝒪[E],
    IsLocalRing.residue 𝒪[E] (integersAction frobenius x) =
      (IsLocalRing.residue 𝒪[E] x) ^ Nat.card 𝓀[K]
  exponents : Gal(E/K) ≃* Multiplicative (ZMod (Module.finrank K E))
  frobenius_exponent : (exponents frobenius).toAdd = 1

/-- Restriction to the finite layer, followed by its normalized Frobenius exponent. -/
def frobeniusExponent (F : FrobeniusLayer K E) (g : Field.absoluteGaloisGroup K) : ℕ :=
  (F.exponents ((AlgEquiv.restrictNormalHom E) g.separableClosure)).toAdd.val

/-- The primitive cyclic cocycle values on the actual separable-closure units.
A carry contributes the base uniformizer; otherwise it contributes the unit `1`. -/
def primitiveValue (F : FrobeniusLayer K E) (π : Kˣ)
    (g h : Field.absoluteGaloisGroup K) : SepUnits K :=
  if Module.finrank K E ≤ frobeniusExponent K E F g + frobeniusExponent K E F h then
    Additive.ofMul (Units.map (algebraMap K (SeparableClosure K)) π)
  else 0

end Layers

/-- An unramified cyclic extension of degree `n` of a nonarchimedean local field `K`, inside its
separable closure: an intermediate field `E` of `K^sep / K`, finite and Galois over `K`, with a
valuative relation and a topology making it a nonarchimedean local field that valuatively extends
`K`; a Frobenius layer on `E` (`FrobeniusLayer`: `E / K` is unramified, with an arithmetic
Frobenius and an isomorphism of `Gal(E/K)` with `ℤ/[E:K]` sending Frobenius to `1`); and the
equality `[E : K] = n`. -/
structure UnramifiedLayerData (n : ℕ) where
  E : IntermediateField K (SeparableClosure K)
  [finite : FiniteDimensional K E]
  [galoisField : IsGalois K E]
  [valued : ValuativeRel E]
  [topological : TopologicalSpace E]
  [localField : IsNonarchimedeanLocalField E]
  [extension : ValuativeExtension K E]
  frobenius : FrobeniusLayer K E
  degree_eq : Module.finrank K E = n

attribute [instance] UnramifiedLayerData.finite UnramifiedLayerData.galoisField
  UnramifiedLayerData.valued UnramifiedLayerData.topological
  UnramifiedLayerData.localField UnramifiedLayerData.extension

/-- The normalized local invariants of a nonarchimedean local field $K$: the additive isomorphisms
$\mathrm{inv} : \mathrm{Br}(K) → \mathbb Q/\mathbb Z$ such that, for every finite Galois extension
$E$ of $K$ in its separable closure that is a nonarchimedean local field valuatively extending $K$,
every Frobenius layer `F` on $E$ (`FrobeniusLayer`), every uniformizer $π$ of $K$ and every
two-cocycle `c` whose inhomogeneous values are `primitiveValue K E F π`, the invariant of the class
of `c` is $1/[E:K]$. -/
abbrev NormalizedLocalInvariant :=
  {inv : Br K ≃+ InvariantTarget //
    ∀ (E : IntermediateField K (SeparableClosure K))
      [FiniteDimensional K E] [IsGalois K E]
      [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [ValuativeExtension K E]
      (F : FrobeniusLayer K E) (π : Kˣ)
      (_hπ : valuation K (π : K) = uniformizer K)
      (c : TwoCocycles K),
      (∀ g h, inhomogeneousValue K c g h = primitiveValue K E F π g h) →
        inv (cocycleClass K c) = ((1 / (Module.finrank K E : ℚ) : ℚ) : InvariantTarget)}

end AlgebraicGeometry.BrauerLocalInvariant
