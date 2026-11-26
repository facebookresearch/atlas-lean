/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.RingTheory.Length
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Natural-valued finite module length

Over an Artinian ring, a finite module has finite composition length, so its
`ENat` length can be converted safely to a natural number.  This file keeps
the raw natural values general; ENat.toNat sends infinite length to zero.
The cast-back, component-length and exact-sequence additivity laws retain
actual Artinian and finite hypotheses.

## Main declarations

* `HilbertSamuel.moduleLengthNat`
* `HilbertSamuel.moduleLengthNat_cast`
* `HilbertSamuel.moduleLengthNat_eq_add_of_exact`
* `HilbertSamuel.gradedPieceLength`
* `HilbertSamuel.gradedPieceLength_cast`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace HilbertSamuel

universe u v w z

/-- For a commutative ring `A` and an `A`-module `M` in an independent
universe, define its natural-number length as the natural value of its extended
composition length. Finite extended lengths retain their value; infinite length
has natural value zero. -/
def moduleLengthNat
    (A : Type u) [CommRing A]
    (M : Type v) [AddCommGroup M] [Module A M] : ℕ :=
  (Module.length A M).toNat

/-- For an Artinian commutative ring `A` and a finitely generated `A`-module
`M` in an independent universe, casting its natural-number length to extended
naturals gives exactly its composition length. -/
theorem moduleLengthNat_cast
    (A : Type u) [CommRing A] [IsArtinianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    (moduleLengthNat A M : ENat) = Module.length A M := by
  rw [moduleLengthNat, ENat.natCast_toNat_eq_self]
  apply Module.length_ne_top_iff.mpr
  have hfin : Module.Finite A M := inferInstance
  exact ((IsArtinianRing.tfae A M).out 1 4).mp hfin

/-- Let `A` be an Artinian commutative ring, and let `M₁ → M₂ → M₃` be
`A`-linear maps whose first map is injective, second map is surjective, and
image equals kernel at `M₂`. If `M₁` and `M₃` are finitely generated,
`lengthNat_A(M₂) = lengthNat_A(M₁) + lengthNat_A(M₃)`. The three module
universes are independent. -/
theorem moduleLengthNat_eq_add_of_exact
    (A : Type u) [CommRing A] [IsArtinianRing A]
    {M₁ : Type v} [AddCommGroup M₁] [Module A M₁] [Module.Finite A M₁]
    {M₂ : Type w} [AddCommGroup M₂] [Module A M₂]
    {M₃ : Type z} [AddCommGroup M₃] [Module A M₃] [Module.Finite A M₃]
    (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    moduleLengthNat A M₂ =
      moduleLengthNat A M₁ + moduleLengthNat A M₃ := by
  have h₁ : Module.length A M₁ ≠ ⊤ := by
    rw [Module.length_ne_top_iff]
    have hfin : Module.Finite A M₁ := inferInstance
    exact ((IsArtinianRing.tfae A M₁).out 1 4).mp hfin
  have h₃ : Module.length A M₃ ≠ ⊤ := by
    rw [Module.length_ne_top_iff]
    have hfin : Module.Finite A M₃ := inferInstance
    exact ((IsArtinianRing.tfae A M₃).out 1 4).mp hfin
  unfold moduleLengthNat
  rw [Module.length_eq_add_of_exact f g hf hg hfg,
    ENat.toNat_add h₁ h₃]

/-- For a commutative ring `A`, an `A`-module `M`, and any natural-number
indexed family of submodules `Mgrade`, the degree-`n` natural length is the
natural value of the composition length of `Mgrade(n)`. No grading or
finite-length assumption is required by this definition. -/
def gradedPieceLength
    (A : Type u) [CommRing A]
    {M : Type v} [AddCommGroup M] [Module A M]
    (Mgrade : ℕ → Submodule A M)
    (n : ℕ) : ℕ :=
  moduleLengthNat A (Mgrade n)

/-- For an Artinian commutative ring `A` and an `A`-module `M` with a
natural-number indexed family of finitely generated submodules `Mgrade`,
casting the natural length of `Mgrade(n)` to extended naturals gives its
composition length for every `n`. -/
theorem gradedPieceLength_cast
    (A : Type u) [CommRing A] [IsArtinianRing A]
    {M : Type v} [AddCommGroup M] [Module A M]
    (Mgrade : ℕ → Submodule A M)
    [∀ n, Module.Finite A (Mgrade n)]
    (n : ℕ) :
    (gradedPieceLength A Mgrade n : ENat) =
      Module.length A (Mgrade n) :=
  moduleLengthNat_cast A (Mgrade n)

end HilbertSamuel
