/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/Cotangent/ExtendScalars.lean` (AxiomMath/Stacks, revision
`c496df0d9beea9deaeabcea8492605f9a0a2313b`); the source file carries no individual copyright or
author notice.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modifications: the pure-tensor formula and the differential-generator extensionality proofs are
kept, in a standalone MathlibExt module.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Maps out of a scalar extension of a module of Kähler differentials

The cotangent complex of a ring map is built degreewise out of the modules
`B ⊗[Pₙ] Ω[Pₙ⁄A]`, that is, out of scalar extensions of modules of Kähler differentials. This
file records the two facts about such modules that the construction uses repeatedly: the value
of the adjunction isomorphism `ModuleCat.extendRestrictScalarsAdj` on a pure tensor, and the
extensionality principle saying that a map out of `S ⊗[P] Ω[P⁄A]` is determined by its values on
the pure differentials `1 ⊗ d p`.

## Main results

* `ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_tmul`: the `S`-linear map
  corresponding to an `R`-linear map `g` sends `s ⊗ₜ x` to `s • g x`.
* `ModuleCat.extendScalars_kaehlerDifferential_hom_ext`: two maps out of `S ⊗[P] Ω[P⁄A]` which
  agree on every `1 ⊗ d p` are equal, for the scalar extension as a functor value.
* `ModuleCat.baseChange_kaehlerDifferential_hom_ext`: the same statement for the base change
  written directly as an object `ModuleCat.of C (C ⊗[R] Ω[R⁄A])`.
* `ModuleCat.extendScalars_baseChange_kaehlerDifferential_hom_ext`: the same statement for the
  iterated scalar extension `C ⊗[B] (B ⊗[P] Ω[P⁄A])`.

## Implementation notes

Mathlib states the pure-tensor formula for `fromExtendScalars` only through
`HomEquiv.fromExtendScalars_hom_apply`, which composes it with `TensorProduct.lift`; using that
at a pure tensor needs `erw`. The formula below holds by `rfl`, so on a pure tensor written with
`⊗ₜ[R,f]` a single `rw` with it does the same work; on other spellings of the same element (for
example with the left factor typed in a restriction of scalars) use it through `Eq.trans`.

Extensionality for the functor value is proved by transporting along the adjunction isomorphism,
whose value on an element is `rfl`, and then inducting over the submodule spanned by the
differentials, which is all of `Ω[P⁄A]`. For the directly written base change the same induction
is carried out inside the tensor product.
-/

@[expose] public section

open scoped ChangeOfRings TensorProduct

universe u v

namespace ModuleCat

/-- The `S`-linear map on `S ⊗[R] X` corresponding to an `R`-linear map `g : X ⟶ Y` sends the
pure tensor `s ⊗ₜ x` to `s • g x`. -/
theorem ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_tmul
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S)
    {X : ModuleCat R} {Y : ModuleCat S} (g : X ⟶ (ModuleCat.restrictScalars f).obj Y)
    (s : S) (x : X) :
    ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars f g (s ⊗ₜ[R,f] x) = s • (g x : Y) :=
  rfl

/-- Every Kähler differential lies in the span of the pure differentials `d p`. -/
private theorem mem_span_range_kaehlerDifferential_D (A P : Type*) [CommRing A] [CommRing P]
    [Algebra A P] (ω : KaehlerDifferential A P) :
    ω ∈ Submodule.span P (Set.range (KaehlerDifferential.D A P)) := by
  rw [KaehlerDifferential.span_range_derivation]
  exact Submodule.mem_top

/-- Two maps out of the scalar extension `S ⊗[P] Ω[P⁄A]` of a module of Kähler differentials
which agree on every pure differential `1 ⊗ d p` are equal. -/
theorem extendScalars_kaehlerDifferential_hom_ext
    {A : Type u} {P S : Type v} [CommRing A] [CommRing P] [CommRing S] [Algebra A P]
    (f : P →+* S) {N : ModuleCat.{v} S}
    (α β : (ModuleCat.extendScalars f).obj (ModuleCat.of P (KaehlerDifferential A P)) ⟶ N)
    (h : ∀ p : P, α ((1 : S) ⊗ₜ KaehlerDifferential.D A P p) =
      β ((1 : S) ⊗ₜ KaehlerDifferential.D A P p)) : α = β := by
  apply ((ModuleCat.extendRestrictScalarsAdj f).homEquiv
    (ModuleCat.of P (KaehlerDifferential A P)) N).injective
  ext ω
  induction mem_span_range_kaehlerDifferential_D A P ω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      exact h p
  | zero => rw [map_zero, map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul p x _ hx => rw [map_smul, map_smul, hx]

/-- Two maps out of the base change `C ⊗[R] Ω[R⁄A]` of a module of Kähler differentials, taken
as an object of the category of `C`-modules, which agree on every pure differential `1 ⊗ d r`
are equal. -/
theorem baseChange_kaehlerDifferential_hom_ext
    {A : Type u} {R C : Type v} [CommRing A] [CommRing R] [CommRing C]
    [Algebra A R] [Algebra R C] {N : ModuleCat.{v} C}
    (α β : ModuleCat.of C (C ⊗[R] KaehlerDifferential A R) ⟶ N)
    (h : ∀ r : R,
      α ((1 : C) ⊗ₜ[R] KaehlerDifferential.D A R r) =
        β ((1 : C) ⊗ₜ[R] KaehlerDifferential.D A R r)) : α = β := by
  ext x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul c ω =>
    rw [← mul_one c, ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, map_smul]
    congr 1
    induction mem_span_range_kaehlerDifferential_D A R ω using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨r, rfl⟩ := hx
        exact h r
    | zero => simp
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
    | smul r x _ hx =>
        rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, ← mul_one (algebraMap R C r),
          ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, map_smul, hx]

/-- Two maps out of the iterated scalar extension `C ⊗[B] (B ⊗[P] Ω[P⁄A])` of a module of Kähler
differentials which agree on every `1 ⊗ (1 ⊗ d p)` are equal. -/
theorem extendScalars_baseChange_kaehlerDifferential_hom_ext
    {A : Type u} {P B C : Type v} [CommRing A] [CommRing P] [CommRing B] [CommRing C]
    [Algebra A P] [Algebra P B] (g : B →+* C) {N : ModuleCat.{v} C}
    (α β : (ModuleCat.extendScalars g).obj
        (ModuleCat.of B (B ⊗[P] KaehlerDifferential A P)) ⟶ N)
    (h : ∀ p : P,
      α ((1 : C) ⊗ₜ ((1 : B) ⊗ₜ[P] KaehlerDifferential.D A P p)) =
        β ((1 : C) ⊗ₜ ((1 : B) ⊗ₜ[P] KaehlerDifferential.D A P p))) : α = β :=
  ((ModuleCat.extendRestrictScalarsAdj g).homEquiv _ N).injective
    (baseChange_kaehlerDifferential_hom_ext (A := A) (R := P) _ _ h)

end ModuleCat

end
