/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.RingTheory.Etale.GraphLocalRing
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Flat graph projections and local algebra maps

Let `R`, `A`, and `B` be commutative rings with `R`-algebra structures on `A` and `B`, in
independent universes. For an algebra map `f : A → B`, the graph evaluation `e : B ⊗_R A → B`
sends `b ⊗ a` to `b * f(a)`. The second inclusion `j : A → B ⊗_R A` satisfies `e ∘ j = f`.

If `B` is flat over `R`, then `j` is flat by base change. For a prime ideal `p` of `B`, it
induces a flat local map `A_(f⁻¹p) → (B ⊗_R A)_(e⁻¹p)`. Composing this projection with
localized graph evaluation gives the localized map of `f`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped TensorProduct

universe u v w

namespace Algebra.TensorProduct

variable {R : Type u} {A : Type v} {B : Type w}
  [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Second tensor inclusion is flat after flat scalar base change.

If `B` is flat over `R`, the ring homomorphism `A → B ⊗_R A` given by the second tensor
inclusion is flat. -/
theorem graphProjection_flat [Module.Flat R B] :
    (includeRight (R := R) (A := B) (B := A)).toRingHom.Flat := by
  let := rightAlgebra (R := R) (A := B) (B := A)
  let e : (B ⊗[R] A) ≃ₐ[A] (A ⊗[R] B) := (commRight R A B).symm
  have h : Module.Flat A (B ⊗[R] A) :=
    Module.Flat.of_linearEquiv e.toLinearEquiv
  change (algebraMap A (B ⊗[R] A)).Flat
  rw [RingHom.flat_algebraMap_iff]
  exact h

/-- Graph projection pulls back the graph ideal along the algebra map.

For any ideal `p` of `B`, the inverse image of `e⁻¹(p)` under the second inclusion `A → B ⊗_R
A` is `f⁻¹(p)`, where `e(b ⊗ a) = b * f(a)`. -/
theorem graphProjectionPrime_comap (f : A →ₐ[R] B) (p : Ideal B) :
    (p.comap (etaleGraphEvaluation f).toRingHom).comap
      (includeRight (R := R) (A := B) (B := A)).toRingHom =
        p.comap f.toRingHom := by
  rw [Ideal.comap_comap]
  congr 1
  ext a
  change (1 : B) * f a = f a
  exact one_mul _

/-- Local graph projection at an inverse image prime.

For a prime ideal `p` of `B`, localize the second tensor inclusion to define `A_(f⁻¹p) → (B
⊗_R A)_(e⁻¹p)`, using its prime inverse-image identity. -/
def graphProjectionLocalRingHom (f : A →ₐ[R] B) (p : Ideal B) [p.IsPrime] :
    Localization.AtPrime (p.comap f.toRingHom) →+*
      Localization.AtPrime (p.comap (etaleGraphEvaluation f).toRingHom) :=
  Localization.localRingHom (p.comap f.toRingHom)
    (p.comap (etaleGraphEvaluation f).toRingHom)
    (includeRight (R := R) (A := B) (B := A)).toRingHom
    (graphProjectionPrime_comap f p).symm

/-- Localized graph projection is flat.

If `B` is flat over `R`, the local graph projection `A_(f⁻¹p) → (B ⊗_R A)_(e⁻¹p)` is flat for
every prime `p` of `B`. -/
theorem graphProjectionLocalRingHom_flat [Module.Flat R B]
    (f : A →ₐ[R] B) (p : Ideal B) [p.IsPrime] :
    (graphProjectionLocalRingHom f p).Flat :=
  (graphProjection_flat (R := R) (A := A) (B := B)).localRingHom
    (p.comap (etaleGraphEvaluation f).toRingHom) (p.comap f.toRingHom)
      (graphProjectionPrime_comap f p).symm

/-- Localized graph evaluation and projection recover the local algebra map.

The local graph projection followed by localized evaluation `e` equals the localization of `f
: A → B` at `f⁻¹(p)` and `p`. -/
theorem graphProjectionLocalRingHom_comp_evaluation
    (f : A →ₐ[R] B) (p : Ideal B) [p.IsPrime] :
    (Localization.localRingHom
      (p.comap (etaleGraphEvaluation f).toRingHom) p
      (etaleGraphEvaluation f).toRingHom rfl).comp
        (graphProjectionLocalRingHom f p) =
      Localization.localRingHom (p.comap f.toRingHom) p f.toRingHom rfl := by
  symm
  apply Localization.localRingHom_unique
  intro a
  rw [RingHom.comp_apply]
  dsimp only [graphProjectionLocalRingHom]
  rw [Localization.localRingHom_to_map, Localization.localRingHom_to_map]
  change algebraMap B (Localization.AtPrime p) ((1 : B) * f a) = _
  rw [one_mul]
  rfl

end Algebra.TensorProduct
