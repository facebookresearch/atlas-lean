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
# Local rings along graphs out of étale algebras

Let R,A,B be commutative rings with independent universes and A,B R-algebras. An R-algebra map
f:A→B gives graph evaluation γ:B⊗_R A→B, γ(b⊗a)=b f(a). It is surjective through b↦b⊗1.

If A is étale over R, γ is flat. For every prime p of B, its canonical local map (B⊗_R
A)_{γ⁻¹(p)}→B_p is bijective and gives a ring isomorphism with that forward map. Étaleness is
required on A; the coefficient algebra B need not be flat or reduced.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped TensorProduct

universe u v w

namespace Algebra.TensorProduct

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Let R,A,B be commutative rings in independent universes u,v,w, with A,B R-algebras and f:A→B an
R-algebra map. Put γ:B⊗_R A→B, γ(b⊗a)=b f(a). This is the R-algebra map γ, obtained from the
identity map on B and f on A. The two coefficient images commute because B is commutative. -/
def etaleGraphEvaluation (f : A →ₐ[R] B) : B ⊗[R] A →ₐ[R] B :=
  lift (AlgHom.id R B) f (fun _ _ => Commute.all _ _)

/-- Let R,A,B be commutative rings in independent universes u,v,w, with A,B R-algebras and f:A→B an
R-algebra map. Put γ:B⊗_R A→B, γ(b⊗a)=b f(a). For b∈B,a∈A, γ(b⊗_R a)=b f(a). This fixes the
graph evaluation's pure-tensor formula. -/
@[simp]
theorem etaleGraphEvaluation_tmul (f : A →ₐ[R] B) (b : B) (a : A) :
    etaleGraphEvaluation f (b ⊗ₜ[R] a) = b * f a := rfl

/-- Let R,A,B be commutative rings in independent universes u,v,w, with A,B R-algebras and f:A→B an
R-algebra map. Put γ:B⊗_R A→B, γ(b⊗a)=b f(a). The map γ is surjective since γ(b⊗1)=b for every
b∈B. No étaleness or flatness condition is needed for this surjectivity. -/
theorem etaleGraphEvaluation_surjective (f : A →ₐ[R] B) :
    Function.Surjective (etaleGraphEvaluation f) := by
  intro b
  exact ⟨b ⊗ₜ[R] 1, by simp⟩

/-- Let R,A,B be commutative rings in independent universes u,v,w, with A,B R-algebras and f:A→B an
R-algebra map. Put γ:B⊗_R A→B, γ(b⊗a)=b f(a). If A is étale over R, γ is a flat ring map. The
algebra B over B⊗_R A induced by γ is étale, and B may be an arbitrary R-algebra. -/
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

/-- Let R,A,B be commutative rings in independent universes u,v,w, with A,B R-algebras and f:A→B an
R-algebra map. Put γ:B⊗_R A→B, γ(b⊗a)=b f(a). Assume A is étale over R and p⊂B is prime. The
local map (B⊗_R A)_{γ⁻¹(p)}→B_p induced by γ is bijective, by flatness and surjectivity of graph
evaluation. -/
theorem localRingHom_etaleGraphEvaluation_bijective [Algebra.Etale R A]
    (f : A →ₐ[R] B) (p : Ideal B) [p.IsPrime] :
    Function.Bijective
      (Localization.localRingHom
        (p.comap (etaleGraphEvaluation f).toRingHom) p
        (etaleGraphEvaluation f).toRingHom rfl) :=
  Localization.localRingHom_bijective_of_flat_of_surjective
    (etaleGraphEvaluation f).toRingHom
    (etaleGraphEvaluation_surjective f) (etaleGraphEvaluation_flat f) p

/-- Let R,A,B be commutative rings in independent universes u,v,w, with A,B R-algebras and f:A→B an
R-algebra map. Put γ:B⊗_R A→B, γ(b⊗a)=b f(a). For A étale over R and prime p⊂B, this ring
isomorphism (B⊗_R A)_{γ⁻¹(p)}≅B_p has the canonical localization of γ as its forward map. -/
def etaleGraphLocalRingEquiv [Algebra.Etale R A]
    (f : A →ₐ[R] B) (p : Ideal B) [p.IsPrime] :
    Localization.AtPrime (p.comap (etaleGraphEvaluation f).toRingHom) ≃+*
      Localization.AtPrime p :=
  RingEquiv.ofBijective
    (Localization.localRingHom
      (p.comap (etaleGraphEvaluation f).toRingHom) p
      (etaleGraphEvaluation f).toRingHom rfl)
    (localRingHom_etaleGraphEvaluation_bijective f p)

/-- Let R,A,B be commutative rings in independent universes u,v,w, with A,B R-algebras and f:A→B an
R-algebra map. Put γ:B⊗_R A→B, γ(b⊗a)=b f(a). For A étale over R, prime p⊂B and x∈(B⊗_R
A)_{γ⁻¹(p)}, the forward graph ring equivalence evaluates to the canonical local-ring map
induced by γ at x. -/
theorem etaleGraphLocalRingEquiv_apply [Algebra.Etale R A]
    (f : A →ₐ[R] B) (p : Ideal B) [p.IsPrime]
    (x : Localization.AtPrime (p.comap (etaleGraphEvaluation f).toRingHom)) :
    etaleGraphLocalRingEquiv f p x =
      Localization.localRingHom
        (p.comap (etaleGraphEvaluation f).toRingHom) p
        (etaleGraphEvaluation f).toRingHom rfl x := rfl

end Algebra.TensorProduct
