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
# Flat projections of graphs

The second-factor tensor graph projection is a base change of the flat
coefficient algebra and remains flat at prime localizations. The localized
projection and graph evaluation compose to the localized algebra map.
Rings and primes have independent universes.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped TensorProduct

universe u v w

namespace Algebra.TensorProduct

variable {R : Type u} {A : Type v} {B : Type w}
  [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The actual second tensor inclusion is flat when the original
coefficient algebra is flat over the base. -/
theorem graphProjection_flat [Module.Flat R B] :
    (includeRight (R := R) (A := B) (B := A)).toRingHom.Flat := by
  let := rightAlgebra (R := R) (A := B) (B := A)
  let e : (B ⊗[R] A) ≃ₐ[A] (A ⊗[R] B) := (commRight R A B).symm
  have h : Module.Flat A (B ⊗[R] A) :=
    Module.Flat.of_linearEquiv e.toLinearEquiv
  change (algebraMap A (B ⊗[R] A)).Flat
  rw [RingHom.flat_algebraMap_iff]
  exact h

/-- The original graph prime pulls back along its second projection to
the original inverse-image prime of the original algebra map. -/
theorem graphProjectionPrime_comap (f : A →ₐ[R] B) (p : Ideal B) :
    (p.comap (etaleGraphEvaluation f).toRingHom).comap
      (includeRight (R := R) (A := B) (B := A)).toRingHom =
        p.comap f.toRingHom := by
  rw [Ideal.comap_comap]
  congr 1
  ext a
  change (1 : B) * f a = f a
  exact one_mul _

/-- The actual localized projection of the original graph. -/
def graphProjectionLocalRingHom (f : A →ₐ[R] B) (p : Ideal B) [p.IsPrime] :
    Localization.AtPrime (p.comap f.toRingHom) →+*
      Localization.AtPrime (p.comap (etaleGraphEvaluation f).toRingHom) :=
  Localization.localRingHom (p.comap f.toRingHom)
    (p.comap (etaleGraphEvaluation f).toRingHom)
    (includeRight (R := R) (A := B) (B := A)).toRingHom
    (graphProjectionPrime_comap f p).symm

/-- The actual localized graph projection is flat, with no flatness
assumption on a graph/support intersection quotient. -/
theorem graphProjectionLocalRingHom_flat [Module.Flat R B]
    (f : A →ₐ[R] B) (p : Ideal B) [p.IsPrime] :
    (graphProjectionLocalRingHom f p).Flat :=
  (graphProjection_flat (R := R) (A := A) (B := B)).localRingHom
    (p.comap (etaleGraphEvaluation f).toRingHom) (p.comap f.toRingHom)
      (graphProjectionPrime_comap f p).symm

/-- The same original local maps compose to the canonical original
localized algebra map, so coefficient restriction has its actual action. -/
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
