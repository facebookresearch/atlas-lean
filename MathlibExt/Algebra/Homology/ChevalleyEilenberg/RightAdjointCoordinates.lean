/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.DegreeAdjoint
public import Mathlib.Algebra.Lie.OfAssociative

/-!
# Right adjoint actions in exterior coordinates

Transport the adjoint action on an exterior power through a linear coordinate equivalence, and
negate it to obtain the right adjoint action. Its commutator uses reversed endomorphism
composition, so it is a Lie homomorphism to the opposite endomorphism algebra.

The ordered pure-wedge formula determines this action. Scalar, Lie, acting-Lie, and coordinate
carrier universes may be independent.
-/

@[expose] public section

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v v' w

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]
variable {S : Type v'} [LieRing S] [LieAlgebra R S] (ι : S →ₗ⁅R⁆ L)
variable (n : ℕ)
variable {M : Type w} [AddCommGroup M] [Module R M] (e : M ≃ₗ[R] ⋀[R]^n L)

/-- The left adjoint representation transported through the coordinates. -/
def leftAdjointCoordinates : S →ₗ⁅R⁆ Module.End R M :=
  e.symm.lieConj.toLieHom.comp ((degreeAdjointAction R L n).comp ι)

@[simp]
theorem leftAdjointCoordinates_apply (s : S) (m : M) :
    leftAdjointCoordinates R L ι n e s m =
      e.symm (degreeAdjointAction R L n (ι s) (e m)) := rfl

/-- The right action is the negative of the left representation. -/
def rightAdjointCoordinates : S →ₗ[R] Module.End R M :=
  -(leftAdjointCoordinates R L ι n e).toLinearMap

@[simp]
theorem rightAdjointCoordinates_apply (s : S) (m : M) :
    rightAdjointCoordinates R L ι n e s m =
      -(e.symm (degreeAdjointAction R L n (ι s) (e m))) := rfl

/-- Coordinates intertwine the transported action and the exterior action. -/
theorem rightAdjointCoordinates_conjugate (s : S) (m : M) :
    e (rightAdjointCoordinates R L ι n e s m) =
      rightDegreeAdjointAction R L ι n s (e m) := by
  rw [rightAdjointCoordinates_apply, map_neg, LinearEquiv.apply_symm_apply]
  rfl

/-- The right-adjoint sum, with brackets in the wedge positions. -/
theorem rightAdjointCoordinates_pure (s : S) (v : Fin n → L) :
    e (rightAdjointCoordinates R L ι n e s
        (e.symm (exteriorPower.ιMulti R n v))) =
      ∑ i : Fin n, exteriorPower.ιMulti R n (Function.update v i ⁅v i, ι s⁆) := by
  rw [rightAdjointCoordinates_conjugate, LinearEquiv.apply_symm_apply]
  exact rightDegreeAdjointAction_pure R L ι n s v

/-- The right adjoint action sends a Lie bracket to the commutator with reversed endomorphism
composition. -/
theorem rightAdjointCoordinates_antiLie (s t : S) :
    rightAdjointCoordinates R L ι n e ⁅s, t⁆ =
      (rightAdjointCoordinates R L ι n e t).comp
          (rightAdjointCoordinates R L ι n e s) -
        (rightAdjointCoordinates R L ι n e s).comp
          (rightAdjointCoordinates R L ι n e t) := by
  apply LinearMap.ext
  intro m
  have h :=
    congrArg (fun f : Module.End R M => f m)
      ((leftAdjointCoordinates R L ι n e).map_lie s t)
  change leftAdjointCoordinates R L ι n e ⁅s, t⁆ m =
    leftAdjointCoordinates R L ι n e s (leftAdjointCoordinates R L ι n e t m) -
      leftAdjointCoordinates R L ι n e t (leftAdjointCoordinates R L ι n e s m) at h
  change -(leftAdjointCoordinates R L ι n e ⁅s, t⁆ m) =
    -(leftAdjointCoordinates R L ι n e t
        (-(leftAdjointCoordinates R L ι n e s m))) -
      -(leftAdjointCoordinates R L ι n e s
        (-(leftAdjointCoordinates R L ι n e t m)))
  rw [h]
  simp only [map_neg, neg_neg, neg_sub]

/-- The right adjoint representation as a Lie homomorphism to the opposite endomorphism algebra. -/
def rightAdjointCoordinatesLieHom : S →ₗ⁅R⁆ (Module.End R M)ᵐᵒᵖ where
  toFun s := MulOpposite.op (rightAdjointCoordinates R L ι n e s)
  map_add' s t := by
    apply MulOpposite.unop_injective
    exact (rightAdjointCoordinates R L ι n e).map_add s t
  map_smul' r s := by
    apply MulOpposite.unop_injective
    exact (rightAdjointCoordinates R L ι n e).map_smul r s
  map_lie' {s t} := by
    apply MulOpposite.unop_injective
    exact rightAdjointCoordinates_antiLie R L ι n e s t

/-- The opposite-valued Lie map retains precisely the action. -/
@[simp]
theorem rightAdjointCoordinatesLieHom_unop (s : S) :
    MulOpposite.unop (rightAdjointCoordinatesLieHom R L ι n e s) =
      rightAdjointCoordinates R L ι n e s := rfl

/-- Agreement on all pure wedges uniquely determines a linear action. -/
theorem rightAdjointCoordinates_eq_of_pure (A : S →ₗ[R] Module.End R M)
    (hA : ∀ (s : S) (v : Fin n → L),
      e (A s (e.symm (exteriorPower.ιMulti R n v))) =
        ∑ i : Fin n, exteriorPower.ιMulti R n (Function.update v i ⁅v i, ι s⁆)) :
    A = rightAdjointCoordinates R L ι n e := by
  apply LinearMap.ext
  intro s
  apply LinearMap.ext
  intro m
  let f : ⋀[R]^n L →ₗ[R] ⋀[R]^n L :=
    e.toLinearMap.comp ((A s).comp e.symm.toLinearMap)
  have hf : f = rightDegreeAdjointAction R L ι n s := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change e (A s (e.symm (exteriorPower.ιMulti R n v))) =
      rightDegreeAdjointAction R L ι n s (exteriorPower.ιMulti R n v)
    exact (hA s v).trans (rightDegreeAdjointAction_pure R L ι n s v).symm
  apply e.injective
  rw [rightAdjointCoordinates_conjugate]
  have hm := LinearMap.congr_fun hf (e m)
  change e (A s (e.symm (e m))) =
    rightDegreeAdjointAction R L ι n s (e m) at hm
  simpa only [LinearEquiv.symm_apply_apply] using hm

end ChevalleyEilenberg
