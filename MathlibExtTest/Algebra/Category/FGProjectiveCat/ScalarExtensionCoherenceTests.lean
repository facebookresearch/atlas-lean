/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtensionCoherence
public import Mathlib.Data.Matrix.Basis

/-!
# Computation clients for the original scalar-extension comparisons

The imported readers compute the actual ordered pure factors, their inverse
unit insertions, and the original shrink coordinates. The matrix clients
pin multiplication order in a noncommutative coefficient ring.
-/

public section
noncomputable section

open ModuleCat.RingHomScalarExtension

universe uR uS uT uP

section Independent

variable {R : Type uR} {S : Type uS} {T : Type uT} [Ring R] [Ring S] [Ring T]

example (g : S →+* T) (t : T) (s : S) :
    coefficientLinearEquiv g (pure g S t s) = t * g s :=
  coefficientLinearEquiv_pure g t s

example (g : S →+* T) (t : T) :
    (coefficientLinearEquiv g).symm t = pure g S t 1 :=
  coefficientLinearEquiv_symm g t

example (f : R →+* S) (g : S →+* T) (P : Type uP) [AddCommGroup P] [Module R P]
    (t : T) (s : S) (p : P) :
    compositionLinearEquiv f g P (pure g (tensor f P) t (pure f P s p)) =
      pure (g.comp f) P (t * g s) p :=
  compositionLinearEquiv_pure f g P t s p

example (f : R →+* S) (g : S →+* T) (P : Type uP) [AddCommGroup P] [Module R P]
    (t : T) (p : P) :
    (compositionLinearEquiv f g P).symm (pure (g.comp f) P t p) =
      pure g (tensor f P) t (pure f P 1 p) :=
  compositionLinearEquiv_symm_pure f g P t p

example (f : R →+* S) (P : FGProjectiveCat.{uR} R) (x : (FGProjectiveCat.ringScalarExtension f).obj P) :
    FGProjectiveCat.ringScalarExtensionCoordinates f P x =
      FGProjectiveCat.scalarExtensionCarrierLinearEquiv f P
        (FGProjectiveCat.UniverseEquivalence.shrinkLinearEquiv.{uS, uR} S
          ((FGProjectiveCat.scalarExtension f).obj P) x) :=
  FGProjectiveCat.ringScalarExtensionCoordinates_apply f P x

example (f : R →+* S) (P : FGProjectiveCat.{uR} R) (x : tensor f P) :
    (FGProjectiveCat.ringScalarExtensionCoordinates f P).symm x =
      (FGProjectiveCat.UniverseEquivalence.shrinkLinearEquiv.{uS, uR} S
        ((FGProjectiveCat.scalarExtension f).obj P)).symm
        ((FGProjectiveCat.scalarExtensionCarrierLinearEquiv f P).symm x) :=
  FGProjectiveCat.ringScalarExtensionCoordinates_symm_apply f P x

end Independent

private abbrev MatrixRing := Matrix (Fin 2) (Fin 2) ℤ

example :
    coefficientLinearEquiv (RingHom.id MatrixRing)
        (pure (RingHom.id MatrixRing) MatrixRing
          (Matrix.single (0 : Fin 2) 1 (1 : ℤ)) (Matrix.single (1 : Fin 2) 0 (1 : ℤ))) =
      Matrix.single (0 : Fin 2) 0 (1 : ℤ) := by
  rw [coefficientLinearEquiv_pure]
  simp

example :
    let f := Int.castRingHom MatrixRing
    coefficientLinearEquiv ((RingHom.id MatrixRing).comp f)
        (compositionLinearEquiv f (RingHom.id MatrixRing) ℤ
          (pure (RingHom.id MatrixRing) (tensor f ℤ) (Matrix.single (0 : Fin 2) 1 (1 : ℤ))
            (pure f ℤ (Matrix.single (1 : Fin 2) 0 (1 : ℤ)) 1))) =
      Matrix.single (0 : Fin 2) 0 (1 : ℤ) := by
  dsimp only
  rw [compositionLinearEquiv_pure, coefficientLinearEquiv_pure]
  simp

#print axioms ModuleCat.RingHomScalarExtension.coefficientLinearEquiv_pure
#print axioms ModuleCat.RingHomScalarExtension.compositionLinearEquiv_pure
#print axioms ModuleCat.RingHomScalarExtension.compositionLinearEquiv_symm_pure

end
