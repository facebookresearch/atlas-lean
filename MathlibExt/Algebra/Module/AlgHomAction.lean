/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.RingHom

/-!
# Scalar compatibility for a algebra representation

Restrict the native endomorphism evaluation action along an algebra
homomorphism. The resulting action has the original ground scalars.
-/

@[expose] public section
noncomputable section

universe u v w

namespace AlgHom

variable {R : Type u} {E : Type v} {M : Type w}
  [CommSemiring R] [Semiring E] [Algebra R E]
  [AddCommMonoid M] [Module R M]

/-- An algebra representation earns scalar compatibility for its actual
pullback of the native endomorphism action. -/
theorem moduleEnd_compHom_isScalarTower (ρ : E →ₐ[R] Module.End R M) :
    letI : Module E M := Module.compHom M ρ.toRingHom
    IsScalarTower R E M := by
  let : Module E M := Module.compHom M ρ.toRingHom
  apply IsScalarTower.of_algebraMap_smul
  intro r m
  change ρ (algebraMap R E r) m = r • m
  simpa only [Module.algebraMap_end_apply] using
    congrArg (fun f : Module.End R M => f m) (ρ.commutes r)

end AlgHom
