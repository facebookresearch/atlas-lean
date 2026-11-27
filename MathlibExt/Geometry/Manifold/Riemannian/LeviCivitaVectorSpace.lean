/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Manifold.Riemannian.VectorSpace

/-!
# Levi-Civita connection of a vector space

The Levi-Civita connection of a finite-dimensional real inner product space, with its standard
Riemannian metric, is the ordinary flat Frechet derivative.

## Main results

* `CovariantDerivative.leviCivitaConnection_vectorSpace_apply`: at a point `x`, the Levi-Civita
  derivative of a vector field `V` differentiable at `x` in direction `v` equals
  `fderiv ℝ V x v`. This extends `leviCivitaConnection_extend_vectorSpace` from constant fields
  to all fields differentiable at the point.

## References

* M. do Carmo, Riemannian Geometry, Ch. 2
* J. Lee, Introduction to Riemannian Manifolds, 2nd ed., Ch. 5
-/

@[expose] public section

open Bundle FiberBundle VectorField CovariantDerivative
open scoped Manifold ContDiff

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **The Levi-Civita connection of a vector space is the Fréchet derivative.** Let $F$ be a
finite-dimensional real inner product space with its standard Riemannian metric, let $V$ be a
vector field on $F$ and $x \in F$, and suppose $V$ is differentiable at $x$ as a section of the
tangent bundle. Then for every tangent vector $v \in T_xF$, the covariant derivative $\nabla_v V$
of $V$ at $x$ for the Levi-Civita connection $\nabla$ equals $DV(x)(v)$, the Fréchet derivative
of $V$ at $x$ applied to $v$. -/
theorem CovariantDerivative.leviCivitaConnection_vectorSpace_apply
    {V : Π y : F, TangentSpace 𝓘(ℝ, F) y} {x : F} (hV : MDiffAt (T% V) x)
    (v : TangentSpace 𝓘(ℝ, F) x) :
    leviCivitaConnection 𝓘(ℝ, F) F V x v = fderiv ℝ V x v := by
  set X : Π y : F, TangentSpace 𝓘(ℝ, F) y := extend F v with hXdef
  have hXm : MDiffAt (T% X) x := by
    rw [hXdef]
    exact mdifferentiableAt_extend_model_space v x
  have htor0 : (leviCivitaConnection 𝓘(ℝ, F) F).torsion = 0 :=
    torsion_leviCivitaConnection_eq_zero 𝓘(ℝ, F)
  have htor :=
    (torsion_eq_zero_iff (leviCivitaConnection 𝓘(ℝ, F) F)).mp htor0 hXm hV
  have hXx : X x = v := by
    rw [hXdef]
    exact extend_apply_self F v
  have hF : fderiv ℝ X x = 0 := by
    have hc : HasFDerivAt (fun _ : F => (v : F)) (0 : F →L[ℝ] F) x :=
      hasFDerivAt_const (v : F) x
    have heq : X =ᶠ[nhds x] (fun _ : F => (v : F)) := by
      filter_upwards with y
      rw [hXdef]
      exact extend_model_space x v y
    have hXhas : HasFDerivAt X 0 x := hc.congr_of_eventuallyEq heq
    exact hXhas.fderiv
  have e1 : mlieBracket 𝓘(ℝ, F) X V = mlieBracketWithin 𝓘(ℝ, F) X V Set.univ :=
    (mlieBracketWithin_univ).symm
  have e2 : mlieBracketWithin 𝓘(ℝ, F) X V Set.univ = lieBracketWithin ℝ X V Set.univ :=
    mlieBracketWithin_eq_lieBracketWithin
  have e3 : lieBracketWithin ℝ X V Set.univ = lieBracket ℝ X V :=
    lieBracketWithin_univ
  have e4 : lieBracket ℝ X V =
      fun y => (fderiv ℝ V y) (X y) - (fderiv ℝ X y) (V y) :=
    lieBracket_eq
  have hcomb : mlieBracket 𝓘(ℝ, F) X V =
      fun y => (fderiv ℝ V y) (X y) - (fderiv ℝ X y) (V y) :=
    e1.trans (e2.trans (e3.trans e4))
  have hEq : mlieBracket 𝓘(ℝ, F) X V x =
      (fderiv ℝ V x) (X x) - (fderiv ℝ X x) (V x) :=
    congrFun hcomb x
  have hbracket : mlieBracket 𝓘(ℝ, F) X V x = fderiv ℝ V x v := by
    rw [hEq, hF, hXx]
    exact sub_zero _
  have hzero : (leviCivitaConnection 𝓘(ℝ, F) F) X x = 0 := by
    rw [hXdef]
    exact leviCivitaConnection_extend_vectorSpace v x
  rw [hzero] at htor
  simp only [zero_apply, sub_zero] at htor
  rw [hXx, hbracket] at htor
  exact htor
