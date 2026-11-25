/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.RingTheory.Etale.DiagonalLocalRing

/-!
# Local graphs of étale algebras

An algebra homomorphism from an étale algebra to an arbitrary coefficient
algebra gives tensor evaluation along its graph. This map is étale and
surjective, so its target-prime localizations are isomorphisms.
The coefficient algebra need not be reduced or flat.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped TensorProduct

universe u v w

namespace Algebra.TensorProduct

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Literal evaluation of the graph of the original algebra map. -/
def etaleGraphEvaluation (f : A →ₐ[R] B) : B ⊗[R] A →ₐ[R] B :=
  lift (AlgHom.id R B) f (fun _ _ => Commute.all _ _)

/-- The graph evaluation acts on the actual pure tensor. -/
@[simp]
theorem etaleGraphEvaluation_tmul (f : A →ₐ[R] B) (b : B) (a : A) :
    etaleGraphEvaluation f (b ⊗ₜ[R] a) = b * f a := rfl

/-- The original graph evaluation is surjective through its left section. -/
theorem etaleGraphEvaluation_surjective (f : A →ₐ[R] B) :
    Function.Surjective (etaleGraphEvaluation f) := by
  intro b
  exact ⟨b ⊗ₜ[R] 1, by simp⟩

/-- The actual graph evaluation of an étale algebra is flat. -/
theorem etaleGraphEvaluation_flat [Algebra.Etale R A] (f : A →ₐ[R] B) :
    (etaleGraphEvaluation f).toRingHom.Flat := by
  let : Algebra (B ⊗[R] A) B := (etaleGraphEvaluation f).toRingHom.toAlgebra
  let : IsScalarTower B (B ⊗[R] A) B :=
    IsScalarTower.of_algebraMap_eq' (by
      ext b
      change b = etaleGraphEvaluation f (b ⊗ₜ[R] 1)
      simp)
  let : Algebra.Etale (B ⊗[R] A) B :=
    Algebra.Etale.of_restrictScalars B (B ⊗[R] A) B
  exact inferInstanceAs (Module.Flat (B ⊗[R] A) B)

/-- The actual prime local map of the étale graph is bijective. -/
theorem localRingHom_etaleGraphEvaluation_bijective [Algebra.Etale R A]
    (f : A →ₐ[R] B) (p : Ideal B) [p.IsPrime] :
    Function.Bijective
      (Localization.localRingHom
        (p.comap (etaleGraphEvaluation f).toRingHom) p
        (etaleGraphEvaluation f).toRingHom rfl) :=
  Localization.localRingHom_bijective_of_flat_of_surjective
    (etaleGraphEvaluation f).toRingHom
    (etaleGraphEvaluation_surjective f) (etaleGraphEvaluation_flat f) p

/-- The graph local comparison retains the original tensor evaluation
as its forward map. -/
def etaleGraphLocalRingEquiv [Algebra.Etale R A]
    (f : A →ₐ[R] B) (p : Ideal B) [p.IsPrime] :
    Localization.AtPrime (p.comap (etaleGraphEvaluation f).toRingHom) ≃+*
      Localization.AtPrime p :=
  RingEquiv.ofBijective
    (Localization.localRingHom
      (p.comap (etaleGraphEvaluation f).toRingHom) p
      (etaleGraphEvaluation f).toRingHom rfl)
    (localRingHom_etaleGraphEvaluation_bijective f p)

/-- The local comparison evaluates to the actual canonical graph map. -/
theorem etaleGraphLocalRingEquiv_apply [Algebra.Etale R A]
    (f : A →ₐ[R] B) (p : Ideal B) [p.IsPrime]
    (x : Localization.AtPrime (p.comap (etaleGraphEvaluation f).toRingHom)) :
    etaleGraphLocalRingEquiv f p x =
      Localization.localRingHom
        (p.comap (etaleGraphEvaluation f).toRingHom) p
        (etaleGraphEvaluation f).toRingHom rfl x := rfl

end Algebra.TensorProduct
