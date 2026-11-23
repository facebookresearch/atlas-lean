/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtensionCoherence
public import MathlibExt.KTheory.Ring.Comparison.ScalarExtension

/-!
# Coherence for scalar extension on the original ring K₀ groups

The canonical balanced tensor comparisons and finite-projective shrink
coordinates give identity, composition and the regular-module class law on
the existing `scalarExtensionK0` maps. The ring universes remain independent.
No commutativity or Noetherian hypothesis is required.
-/

public section
noncomputable section

open CategoryTheory

universe uR uS uT

namespace FGProjectiveCat

variable {R : Type uR} {S : Type uS} {T : Type uT} [Ring R] [Ring S] [Ring T]

/-- The identity ring homomorphism acts as the identity on the original ring K₀ group. -/
@[simp]
theorem scalarExtensionK0_id (R : Type uR) [Ring R] :
    scalarExtensionK0 (RingHom.id R) = AddMonoidHom.id (AlgebraicKTheory.RingK0 R) := by
  apply AlgebraicKTheory.K0.hom_ext
  intro P
  change scalarExtensionK0 (RingHom.id R) (AlgebraicKTheory.K0.mk P) = AlgebraicKTheory.K0.mk P
  rw [scalarExtensionK0_mk]
  let e : (ringScalarExtension (RingHom.id R)).obj P ≃ₗ[R] P :=
    (ringScalarExtensionCoordinates (RingHom.id R) P).trans
      (ModuleCat.RingHomScalarExtension.identityTensorLinearEquiv R P)
  exact AlgebraicKTheory.K0.mk_congr_of_iso
    ((ModuleCat.isFGProjective.{uR} R).isoMk e.toModuleIso)

/-- The class of the original regular module maps to the class of the target regular module,
independently of the two ring universes. -/
@[simp]
theorem scalarExtensionK0_regular (f : R →+* S) :
    scalarExtensionK0 f (AlgebraicKTheory.K0.mk (FGProjectiveCat.of (R := R) R)) =
      AlgebraicKTheory.K0.mk (FGProjectiveCat.of (R := S) S) := by
  rw [scalarExtensionK0_mk]
  let P := FGProjectiveCat.of (R := R) R
  let e : (ringScalarExtension f).obj P ≃ₗ[S] S :=
    (ringScalarExtensionCoordinates f P).trans
      (ModuleCat.RingHomScalarExtension.coefficientLinearEquiv f)
  exact AlgebraicKTheory.K0.mk_congr_of_iso
    ((ModuleCat.isFGProjective.{uS} S).isoMk e.toModuleIso)

/-- The original scalar-extension maps compose on all of the fixed ring K₀ groups,
with independent source, intermediate and target ring universes. -/
theorem scalarExtensionK0_comp (f : R →+* S) (g : S →+* T) :
    scalarExtensionK0 (g.comp f) = (scalarExtensionK0 g).comp (scalarExtensionK0 f) := by
  apply AlgebraicKTheory.K0.hom_ext
  intro P
  change scalarExtensionK0 (g.comp f) (AlgebraicKTheory.K0.mk P) =
    scalarExtensionK0 g (scalarExtensionK0 f (AlgebraicKTheory.K0.mk P))
  rw [scalarExtensionK0_mk, scalarExtensionK0_mk, scalarExtensionK0_mk]
  let A := (ringScalarExtension f).obj P
  let e : (ringScalarExtension g).obj A ≃ₗ[T] (ringScalarExtension (g.comp f)).obj P :=
    (ringScalarExtensionCoordinates g A).trans
      ((ModuleCat.RingHomScalarExtension.tensorLinearEquiv g
        (ringScalarExtensionCoordinates f P)).trans
        ((ModuleCat.RingHomScalarExtension.compositionLinearEquiv f g P).trans
          (ringScalarExtensionCoordinates (g.comp f) P).symm))
  exact (AlgebraicKTheory.K0.mk_congr_of_iso
    ((ModuleCat.isFGProjective.{uT} T).isoMk e.toModuleIso)).symm

end FGProjectiveCat

end
