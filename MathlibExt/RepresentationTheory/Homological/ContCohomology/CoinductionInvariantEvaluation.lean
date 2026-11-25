/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.DiscreteCoinductionExactness
public import Mathlib.Topology.CompactOpen

/-!
# Actual invariants of continuous coinduction and identity evaluation

The invariant is the actual continuous orbit of its value at the identity.
Both directions retain the stored coefficient module. Their naturality
identifies the actual invariant-coinduction sequence with the underlying
coefficient sequence, hence preserves short exactness.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe r g w
namespace ContinuousCohomology

variable {R : Type r} [Ring R] [TopologicalSpace R]
variable {G : Type g} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Identity evaluation on the actual coinduced invariant coefficient module. -/
def coindInvariantEval (X : TopRep.{max g w, r, g} R G) :
    X.coind₁.ρ.invariants →L[R] X :=
  (ContinuousMap.evalCLM R (1 : G)).comp X.coind₁.ρ.invariants.subtypeL

/-- The true continuous orbit section of identity evaluation. -/
def coindInvariantOrbit (X : TopRep.{max g w, r, g} R G) [DiscreteTopology X]
    (hX : ((TopRep.toActionTopModFunc (k := R) (G := G)).obj X).IsContinuous) :
    X →L[R] X.coind₁.ρ.invariants := by
  let orbit : X →ₗ[R] C(G, X) :=
    { toFun := fun x => ⟨fun g => X.ρ g x,
        (TopRep.continuous_action hX).comp (continuous_id.prodMk continuous_const)⟩
      map_add' := fun x y => ContinuousMap.ext (fun g => map_add (X.ρ g) x y)
      map_smul' := fun a x => ContinuousMap.ext (fun g => map_smul (X.ρ g) a x) }
  let orbitL : X →ₗ[R] X.coind₁.ρ.invariants := orbit.codRestrict _ (fun x => by
    intro g
    apply ContinuousMap.ext
    intro h
    change X.ρ g (X.ρ (g⁻¹ * h) x) = X.ρ h x
    have hmul := congrArg (fun f : X →L[R] X => f x)
      (X.ρ.toMonoidHom.map_mul g (g⁻¹ * h))
    exact hmul.symm.trans (congrArg (fun a => X.ρ a x) (mul_inv_cancel_left g h)))
  exact { toLinearMap := orbitL, cont := continuous_of_discreteTopology }

/-- An invariant function is literally the orbit of its identity value. -/
theorem coindInvariant_value (X : TopRep.{max g w, r, g} R G)
    (c : X.coind₁.ρ.invariants) (g : G) : X.ρ g (c.val 1) = c.val g := by
  have h := congrArg (fun q : C(G, X) => q g) (c.property g)
  change X.ρ g (c.val (g⁻¹ * g)) = c.val g at h
  simpa only [inv_mul_cancel] using h

/-- Actual identity evaluation and the actual orbit section form a continuous linear equivalence. -/
def coindInvariantEquiv (X : TopRep.{max g w, r, g} R G) [DiscreteTopology X]
    (hX : ((TopRep.toActionTopModFunc (k := R) (G := G)).obj X).IsContinuous) :
    X.coind₁.ρ.invariants ≃L[R] X :=
  { toLinearEquiv :=
      { toLinearMap := (coindInvariantEval X).toLinearMap
        invFun := coindInvariantOrbit X hX
        left_inv := fun c => by
          apply Subtype.ext
          apply ContinuousMap.ext
          intro g
          exact coindInvariant_value X c g
        right_inv := fun x => by
          change X.ρ 1 x = x
          exact congrArg (fun f : X →L[R] X => f x) X.ρ.toMonoidHom.map_one }
    continuous_toFun := (coindInvariantEval X).continuous
    continuous_invFun := (coindInvariantOrbit X hX).continuous }

/-- The forward equivalence is the literal identity-coordinate value. -/
theorem coindInvariantEquiv_apply (X : TopRep.{max g w, r, g} R G) [DiscreteTopology X]
    (hX : ((TopRep.toActionTopModFunc (k := R) (G := G)).obj X).IsContinuous)
    (c : X.coind₁.ρ.invariants) : coindInvariantEquiv X hX c = c.val 1 := rfl

/-- The inverse equivalence retains every actual orbit coordinate. -/
theorem coindInvariantEquiv_symm_apply (X : TopRep.{max g w, r, g} R G) [DiscreteTopology X]
    (hX : ((TopRep.toActionTopModFunc (k := R) (G := G)).obj X).IsContinuous)
    (x : X) (g : G) : ((coindInvariantEquiv X hX).symm x).val g = X.ρ g x := rfl

/-- Evaluation is natural under the actual stored coefficient arrow. -/
theorem coindInvariantEval_naturality {X Y : TopRep.{max g w, r, g} R G} (f : X ⟶ Y)
    (c : X.coind₁.ρ.invariants) :
    coindInvariantEval Y
      (((TopRep.invariantsFunctor R G).map ((TopRep.coind₁Functor R G).map f)).hom c) =
      f.hom (coindInvariantEval X c) := rfl

end ContinuousCohomology
