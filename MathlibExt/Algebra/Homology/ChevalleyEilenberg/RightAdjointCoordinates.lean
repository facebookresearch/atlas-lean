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
# Exterior coordinates for right-adjoint Lie actions

Let ι : S → L be an R-Lie homomorphism and e : M ≃ₗ[R] ⋀[R]^n L. Conjugating the degree
adjoint representation along e gives a left S-representation on M. Its negative is the
right-adjoint action; in exterior coordinates it replaces each entry v_i by [v_i,ι(s)] and
sums the resulting words.

The right action satisfies the reversed endomorphism commutator equation and therefore gives a
Lie homomorphism into the opposite endomorphism ring. Agreement with its formula on every pure
wedge determines any linear action uniquely. All carrier universes may be separate.
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

/-- Let R be a commutative ring, L and S R-Lie algebras, ι : S →ₗ⁅R⁆ L, n : ℕ and e : M ≃ₗ[R]
⋀[R]^n L coordinates on an R-module M. leftAdjointCoordinates(s) = e⁻¹ ∘
degreeAdjointAction_L(n,ι(s)) ∘ e, a Lie homomorphism S →ₗ⁅R⁆ Module.End R M. -/
def leftAdjointCoordinates : S →ₗ⁅R⁆ Module.End R M :=
  e.symm.lieConj.toLieHom.comp ((degreeAdjointAction R L n).comp ι)

@[simp]
theorem leftAdjointCoordinates_apply (s : S) (m : M) :
    leftAdjointCoordinates R L ι n e s m =
      e.symm (degreeAdjointAction R L n (ι s) (e m)) := rfl

/-- Let R be a commutative ring, L and S R-Lie algebras, ι : S →ₗ⁅R⁆ L, n : ℕ and e : M ≃ₗ[R]
⋀[R]^n L coordinates on an R-module M. rightAdjointCoordinates : S →ₗ[R] Module.End R M is
−leftAdjointCoordinates. -/
def rightAdjointCoordinates : S →ₗ[R] Module.End R M :=
  -(leftAdjointCoordinates R L ι n e).toLinearMap

@[simp]
theorem rightAdjointCoordinates_apply (s : S) (m : M) :
    rightAdjointCoordinates R L ι n e s m =
      -(e.symm (degreeAdjointAction R L n (ι s) (e m))) := rfl

/-- Let R be a commutative ring, L and S R-Lie algebras, ι : S →ₗ⁅R⁆ L, n : ℕ and e : M ≃ₗ[R]
⋀[R]^n L coordinates on an R-module M. For s : S and m : M, e(rightAdjointCoordinates(s)(m)) =
rightDegreeAdjointAction_L(n,s)(e(m)). -/
theorem rightAdjointCoordinates_conjugate (s : S) (m : M) :
    e (rightAdjointCoordinates R L ι n e s m) =
      rightDegreeAdjointAction R L ι n s (e m) := by
  rw [rightAdjointCoordinates_apply, map_neg, LinearEquiv.apply_symm_apply]
  rfl

/-- Let R be a commutative ring, L and S R-Lie algebras, ι : S →ₗ⁅R⁆ L, n : ℕ and e : M ≃ₗ[R]
⋀[R]^n L coordinates on an R-module M. For s : S and v : Fin n → L,
e(rightAdjointCoordinates(s)(e.symm(ιMulti v))) = ∑ i : Fin n, ιMulti(Function.update v i
⁅v_i,ι(s)⁆). -/
theorem rightAdjointCoordinates_pure (s : S) (v : Fin n → L) :
    e (rightAdjointCoordinates R L ι n e s
        (e.symm (exteriorPower.ιMulti R n v))) =
      ∑ i : Fin n, exteriorPower.ιMulti R n (Function.update v i ⁅v i, ι s⁆) := by
  rw [rightAdjointCoordinates_conjugate, LinearEquiv.apply_symm_apply]
  exact rightDegreeAdjointAction_pure R L ι n s v

/-- Let R be a commutative ring, L and S R-Lie algebras, ι : S →ₗ⁅R⁆ L, n : ℕ and e : M ≃ₗ[R]
⋀[R]^n L coordinates on an R-module M. Writing ρ = rightAdjointCoordinates, ρ(⁅s,t⁆) = ρ(t) ∘
ρ(s) − ρ(s) ∘ ρ(t) for s,t : S. -/
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

/-- Let R be a commutative ring, L and S R-Lie algebras, ι : S →ₗ⁅R⁆ L, n : ℕ and e : M ≃ₗ[R]
⋀[R]^n L coordinates on an R-module M. rightAdjointCoordinatesLieHom : S →ₗ⁅R⁆ (Module.End R
M)ᵐᵒᵖ sends s to op(rightAdjointCoordinates(s)); the opposite multiplication matches its
reversed commutator law. -/
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

/-- Let R be a commutative ring, L and S R-Lie algebras, ι : S →ₗ⁅R⁆ L, n : ℕ and e : M ≃ₗ[R]
⋀[R]^n L coordinates on an R-module M. For s : S, unop(rightAdjointCoordinatesLieHom s) =
rightAdjointCoordinates s. -/
@[simp]
theorem rightAdjointCoordinatesLieHom_unop (s : S) :
    MulOpposite.unop (rightAdjointCoordinatesLieHom R L ι n e s) =
      rightAdjointCoordinates R L ι n e s := rfl

/-- Let R be a commutative ring, L and S R-Lie algebras, ι : S →ₗ⁅R⁆ L, n : ℕ and e : M ≃ₗ[R]
⋀[R]^n L coordinates on an R-module M. If A : S →ₗ[R] Module.End R M has e(A(s)(e.symm(ιMulti
v))) = ∑ i, ιMulti(update v i ⁅v_i,ι(s)⁆) for every s and v, then A = rightAdjointCoordinates. -/
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
