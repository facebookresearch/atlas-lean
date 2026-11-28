/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import
  MathlibExt.RepresentationTheory.Homological.ContCohomology.DiscreteCoinductionExactness
public import Mathlib.Topology.CompactOpen

/-!
# Invariant coinduced functions and evaluation at the identity

Let R be a ring with a topology, G a topological group and X a
topological R-representation. In the diagonal coinduction C(G,X),
an invariant function F satisfies F(g) = g • F(1).
Evaluation at 1 is a continuous R-linear map C(G,X)^G → X.

When X is discrete and its action is jointly continuous, the inverse
is the orbit map x ↦ (g ↦ g • x), giving
C(G,X)^G ≅L[R] X. Evaluation is natural under continuous equivariant
coefficient maps. No local compactness of G is required for these
identity-evaluation statements.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe r g w
namespace ContinuousCohomology

variable {R : Type r} [Ring R] [TopologicalSpace R]
variable {G : Type g} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Let R be a ring equipped with a topology and G a topological
group. A coefficient X is a topological R-module with a G-representation
by continuous R-linear maps. Scalar, group and carrier universes are independent.
Write Coind(X) = C(G,X) with compact-open topology and diagonal action
(g • F)(x) = g • F(g⁻¹x).
Evaluation at the identity gives the continuous R-linear map
C(G,X)^G → X, F ↦ F(1), from the invariant submodule with its
subspace topology. -/
def coindInvariantEval (X : TopRep.{max g w, r, g} R G) :
    X.coind₁.ρ.invariants →L[R] X :=
  (ContinuousMap.evalCLM R (1 : G)).comp X.coind₁.ρ.invariants.subtypeL

/-- Let R be a ring equipped with a topology and G a topological
group. A coefficient X is a topological R-module with a G-representation
by continuous R-linear maps. Scalar, group and carrier universes are independent.
Write Coind(X) = C(G,X) with compact-open topology and diagonal action
(g • F)(x) = g • F(g⁻¹x).
If X is discrete and the G-action on X is jointly continuous,
the orbit map X → C(G,X)^G, x ↦ (g ↦ g • x), is continuous
and R-linear. -/
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

/-- Let R be a ring equipped with a topology and G a topological
group. A coefficient X is a topological R-module with a G-representation
by continuous R-linear maps. Scalar, group and carrier universes are independent.
Write Coind(X) = C(G,X) with compact-open topology and diagonal action
(g • F)(x) = g • F(g⁻¹x).
For an invariant F ∈ C(G,X)^G and g ∈ G, one has
F(g) = g • F(1). -/
theorem coindInvariant_value (X : TopRep.{max g w, r, g} R G)
    (c : X.coind₁.ρ.invariants) (g : G) : X.ρ g (c.val 1) = c.val g := by
  have h := congrArg (fun q : C(G, X) => q g) (c.property g)
  change X.ρ g (c.val (g⁻¹ * g)) = c.val g at h
  simpa only [inv_mul_cancel] using h

/-- Let R be a ring equipped with a topology and G a topological
group. A coefficient X is a topological R-module with a G-representation
by continuous R-linear maps. Scalar, group and carrier universes are independent.
Write Coind(X) = C(G,X) with compact-open topology and diagonal action
(g • F)(x) = g • F(g⁻¹x).
For discrete X with jointly continuous G-action, evaluation and
the orbit map give the continuous R-linear equivalence
C(G,X)^G ≅L[R] X. -/
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

/-- Let R be a ring equipped with a topology and G a topological
group. A coefficient X is a topological R-module with a G-representation
by continuous R-linear maps. Scalar, group and carrier universes are independent.
Write Coind(X) = C(G,X) with compact-open topology and diagonal action
(g • F)(x) = g • F(g⁻¹x).
For discrete X with jointly continuous action and F ∈ C(G,X)^G,
the invariant-coinduction equivalence has value F ↦ F(1). -/
theorem coindInvariantEquiv_apply (X : TopRep.{max g w, r, g} R G) [DiscreteTopology X]
    (hX : ((TopRep.toActionTopModFunc (k := R) (G := G)).obj X).IsContinuous)
    (c : X.coind₁.ρ.invariants) : coindInvariantEquiv X hX c = c.val 1 := rfl

/-- Let R be a ring equipped with a topology and G a topological
group. A coefficient X is a topological R-module with a G-representation
by continuous R-linear maps. Scalar, group and carrier universes are independent.
Write Coind(X) = C(G,X) with compact-open topology and diagonal action
(g • F)(x) = g • F(g⁻¹x).
For discrete X with jointly continuous action, the inverse
equivalence sends x ∈ X to F_x(g) = g • x for every g ∈ G. -/
theorem coindInvariantEquiv_symm_apply (X : TopRep.{max g w, r, g} R G) [DiscreteTopology X]
    (hX : ((TopRep.toActionTopModFunc (k := R) (G := G)).obj X).IsContinuous)
    (x : X) (g : G) : ((coindInvariantEquiv X hX).symm x).val g = X.ρ g x := rfl

/-- Let R be a ring equipped with a topology and G a topological
group. A coefficient X is a topological R-module with a G-representation
by continuous R-linear maps. Scalar, group and carrier universes are independent.
For a continuous equivariant R-linear f : X → Y, identity
evaluation satisfies eval_Y(Inv(Coind(f))(F)) = f(eval_X(F))
for every invariant coinduced function F. -/
theorem coindInvariantEval_naturality {X Y : TopRep.{max g w, r, g} R G} (f : X ⟶ Y)
    (c : X.coind₁.ρ.invariants) :
    coindInvariantEval Y
      (((TopRep.invariantsFunctor R G).map ((TopRep.coind₁Functor R G).map f)).hom c) =
      f.hom (coindInvariantEval X c) := rfl

end ContinuousCohomology
