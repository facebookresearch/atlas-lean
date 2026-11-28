/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupProduct
import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupOneOneFunctoriality
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.Matrix.Notation
meta import Mathlib.Tactic.NormNum

/-!
# Nonzero cup products of coordinate characters

The two coordinate characters of the additive square of a commutative ring are one-cocycles
for its trivial representation. Their cup has value one tensor one on the ordered basis
pair and zero on the reversed pair. Every two-coboundary has equal values on these commuting
elements, so the cup class is nonzero whenever the ring is nontrivial. The integer instance
is a positive-degree cohomology product over a ring, and the all-degree cup cochain gives the
same ordered coordinate. A nonidentity integer group map doubles the first coordinate.
-/

open CategoryTheory MonoidalCategory groupCohomology
open scoped TensorProduct

noncomputable section
set_option autoImplicit false

namespace CupOneOneNonzeroTests

universe u

section General

variable (R : Type u) [CommRing R]

private abbrev G := Multiplicative (R × R)
private abbrev A : Rep R (G R) := Rep.trivial R (G R) R
private abbrev T : Rep R (G R) := A R ⊗ A R

private def first : cocycles₁ (A R) :=
  ⟨fun g => g.toAdd.1, (mem_cocycles₁_iff _).2 (fun g h => by
    change (g.toAdd + h.toAdd).1 = h.toAdd.1 + g.toAdd.1
    exact add_comm _ _)⟩

private def second : cocycles₁ (A R) :=
  ⟨fun g => g.toAdd.2, (mem_cocycles₁_iff _).2 (fun g h => by
    change (g.toAdd + h.toAdd).2 = h.toAdd.2 + g.toAdd.2
    exact add_comm _ _)⟩

private def e₁ : G R := Multiplicative.ofAdd (1, 0)
private def e₂ : G R := Multiplicative.ofAdd (0, 1)

private def tensorCoordinate : T R →ₗ[R] R := (TensorProduct.lid R R).toLinearMap

private lemma tensor_action (g : G R) (z : T R) : (T R).ρ g z = z := by
  change TensorProduct.map ((A R).ρ g) ((A R).ρ g) z = z
  rw [Rep.trivial_ρ, Rep.trivial_ρ, TensorProduct.map_id]
  rfl

private def cross : cocycles₂ (T R) := cupCocycleOneOne (A R) (A R) (first R) (second R)

private lemma cross_forward : tensorCoordinate R (cross R (e₁ R, e₂ R)) = 1 := by
  change (TensorProduct.lid R R) ((1 : R) ⊗ₜ[R] (1 : R)) = 1
  simp [smul_eq_mul]

private lemma cross_reverse : tensorCoordinate R (cross R (e₂ R, e₁ R)) = 0 := by
  change (TensorProduct.lid R R) ((0 : R) ⊗ₜ[R] (0 : R)) = 0
  simp

private lemma boundary_symmetric (f : G R → T R) (g h : G R) :
    d₁₂ (T R) f (g, h) = d₁₂ (T R) f (h, g) := by
  change (T R).ρ g (f h) - f (g * h) + f g =
    (T R).ρ h (f g) - f (h * g) + f h
  rw [tensor_action, tensor_action, mul_comm g h]
  abel

private theorem cross_class_nonzero [Nontrivial R] : H2π (T R) (cross R) ≠ 0 := by
  intro hz
  obtain ⟨f, hf⟩ := (H2π_eq_zero_iff (cross R)).1 hz
  have hfwd := congrFun hf (e₁ R, e₂ R)
  have hrev := congrFun hf (e₂ R, e₁ R)
  have heq : cross R (e₁ R, e₂ R) = cross R (e₂ R, e₁ R) :=
    hfwd.symm.trans ((boundary_symmetric R f (e₁ R) (e₂ R)).trans hrev)
  have hc := congrArg (tensorCoordinate R) heq
  rw [cross_forward, cross_reverse] at hc
  exact one_ne_zero hc

/-- The bilinear cohomology product is nonzero on the two coordinate classes. -/
example [Nontrivial R] :
    cupOneOne (A R) (A R) (H1π (A R) (first R)) (H1π (A R) (second R)) ≠ 0 := by
  rw [cupOneOne_H1π_H1π]
  exact cross_class_nonzero R

example [Nontrivial R] : H1π (A R) (first R) ≠ 0 := by
  intro hz
  have hcup := cross_class_nonzero R
  have hc := cupOneOne_H1π_H1π (A R) (A R) (first R) (second R)
  simp only [hz, map_zero, LinearMap.zero_apply] at hc
  exact hcup hc.symm

example [Nontrivial R] : H1π (A R) (second R) ≠ 0 := by
  intro hz
  have hcup := cross_class_nonzero R
  have hc := cupOneOne_H1π_H1π (A R) (A R) (first R) (second R)
  simp only [hz, map_zero, LinearMap.zero_apply] at hc
  exact hcup hc.symm

private def firstCochain : (inhomogeneousCochains (A R)).X 1 := fun g => (g 0).toAdd.1
private def secondCochain : (inhomogeneousCochains (A R)).X 1 := fun g => (g 0).toAdd.2
private def orderedPair : Fin 2 → G R := ![e₁ R, e₂ R]

/-- The arbitrary-degree cup pairing retains the ordered positive-degree coordinate. -/
example : tensorCoordinate R
    ((((inhomogeneousCupPairing (G R) R (A R) (A R)).pair 1 1).hom
      (firstCochain R ⊗ₜ[R] secondCochain R)) (orderedPair R)) = 1 := by
  have h := inhomogeneousCupPairing_apply (G R) R (A R) (A R) 1 1
    (firstCochain R) (secondCochain R) (orderedPair R)
  have hc := congrArg (tensorCoordinate R) h
  simpa [firstCochain, secondCochain, orderedPair, e₁, e₂, tensorCoordinate,
    smul_eq_mul] using hc

end General

private def doubleFirst : G ℤ →* G ℤ where
  toFun g := Multiplicative.ofAdd (2 * g.toAdd.1, g.toAdd.2)
  map_one' := by rfl
  map_mul' g h := by
    change Multiplicative.ofAdd (2 * (g.toAdd.1 + h.toAdd.1), g.toAdd.2 + h.toAdd.2) =
      Multiplicative.ofAdd (2 * g.toAdd.1 + 2 * h.toAdd.1, g.toAdd.2 + h.toAdd.2)
    rw [mul_add]

private def resIdentity : Rep.res doubleFirst (A ℤ) ⟶ A ℤ :=
  Rep.ofHom ⟨LinearMap.id, fun g => by rfl⟩

/-- An actual nonidentity group pullback doubles the detected ordered cup value. -/
example : tensorCoordinate ℤ
    ((mapCocycles₂ doubleFirst (resIdentity ⊗ₘ resIdentity) (cross ℤ)) (e₁ ℤ, e₂ ℤ)) = 2 := by
  rw [mapCocycles₂_cupCocycleOneOne_of_hom doubleFirst resIdentity resIdentity
    (first ℤ) (second ℤ)]
  change (TensorProduct.lid ℤ ℤ) ((2 : ℤ) ⊗ₜ[ℤ] (1 : ℤ)) = 2
  simp [smul_eq_mul]

end CupOneOneNonzeroTests
