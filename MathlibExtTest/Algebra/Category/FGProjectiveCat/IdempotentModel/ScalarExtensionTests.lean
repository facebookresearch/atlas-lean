/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Category.FGProjectiveCat.IdempotentModel.ScalarExtension

noncomputable section
open CategoryTheory
open FGProjectiveCat FGProjectiveCat.IdempotentModel
open ModuleCat.RingHomScalarExtension

universe uR uS
variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

-- Actual all-ring clients use the original ringScalarExtension and range realization.
example (f : R →+* S) (P : IdempotentModel R) :
    (ringScalarExtension f).obj ((equivalence R).functor.obj P) ≅
      (equivalence S).functor.obj (mapObject f P) :=
  scalarExtensionIso f P

example (I : Ideal R) [I.IsTwoSided] (P : IdempotentModel R) :
    (ringScalarExtension (Ideal.Quotient.mk I)).obj ((equivalence R).functor.obj P) ≅
      (equivalence (R ⧸ I)).functor.obj (mapObject (Ideal.Quotient.mk I) P) :=
  quotientScalarExtensionIso I P

example (f : R →+* S) (P : IdempotentModel R) (s : S) (p : range R P) (j : Fin P.X) :
    (rangeScalarExtensionLinearEquiv f P (pure f (range R P) s p)).val j =
      s * f (p.val j) :=
  rangeScalarExtensionLinearEquiv_pure f P s p j

-- The same coordinates and inverse are read through the original object isomorphism.
example (f : R →+* S) (P : IdempotentModel R) (s : S) (p : range R P) (j : Fin P.X) :
    (FGProjectiveCat.isoToLinearEquiv (eqToIso (equivalence_obj S (mapObject f P)))
      (FGProjectiveCat.isoToLinearEquiv (scalarExtensionIso f P)
        ((scalarRangeCarrierLinearEquiv f P).symm (pure f (range R P) s p)))).val j =
      s * f (p.val j) :=
  scalarExtensionIso_pure f P s p j

example (f : R →+* S) (P : IdempotentModel R) (x : range S (mapObject f P)) :
    scalarRangeCarrierLinearEquiv f P
      ((FGProjectiveCat.isoToLinearEquiv (scalarExtensionIso f P)).symm
        ((FGProjectiveCat.isoToLinearEquiv
          (eqToIso (equivalence_obj S (mapObject f P)))).symm x)) =
      ∑ i : Fin P.X, x.val i • pure f (range R P) 1 (matrixRow P i) :=
  scalarExtensionIso_inverse f P x

example (f : R →+* S) {P Q : IdempotentModel R} (g : P ⟶ Q) :
    (ringScalarExtension f).map ((equivalence R).functor.map g) ≫
        (scalarExtensionIso f Q).hom =
      (scalarExtensionIso f P).hom ≫ (equivalence S).functor.map (mapHom f g) :=
  scalarExtensionIso_naturality f g

-- The needed original carrier-map reader is available independently of the range model.
example (f : R →+* S) {P Q : FGProjectiveCat.{uR} R} (g : P ⟶ Q) :
    (scalarExtensionCarrierLinearEquiv f Q).toLinearMap.comp
        ((scalarExtension f).map g).hom.hom =
      (linearMap f g.hom.hom).comp (scalarExtensionCarrierLinearEquiv f P).toLinearMap :=
  scalarExtensionCarrierLinearEquiv_naturality f g

example (f : R →+* S) :
    (mapObject f ((Idempotents.toKaroubi (FiniteRowRanks R)).obj (0 : ℕ))).X =
      (0 : ℕ) := rfl

-- A noncommutative coefficient ring and its zero-ring quotient need no extra hypothesis.
example (P : IdempotentModel (Matrix (Fin 2) (Fin 2) ℤ)) :
    (ringScalarExtension (Ideal.Quotient.mk (⊤ : Ideal (Matrix (Fin 2) (Fin 2) ℤ)))).obj
        ((equivalence (Matrix (Fin 2) (Fin 2) ℤ)).functor.obj P) ≅
      (equivalence ((Matrix (Fin 2) (Fin 2) ℤ) ⧸ ⊤)).functor.obj
        (mapObject (Ideal.Quotient.mk (⊤ : Ideal (Matrix (Fin 2) (Fin 2) ℤ))) P) :=
  quotientScalarExtensionIso ⊤ P

#print axioms scalarExtensionIso
#print axioms scalarExtensionIso_naturality
#print axioms quotientScalarExtensionIso
#print axioms scalarExtensionCarrierLinearEquiv_naturality
