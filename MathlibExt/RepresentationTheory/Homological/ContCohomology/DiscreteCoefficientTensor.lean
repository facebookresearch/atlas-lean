/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import Mathlib.RepresentationTheory.Continuous.TopRep
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import MathlibExt.RepresentationTheory.Continuous.ContinuousActionBridge

/-!
# Discrete tensor coefficients with a continuous group action

Let R be a commutative ring with a topology and G a profinite group.
For discrete topological R-representations A and B, the tensor coefficient
has carrier A ⊗[R] B with discrete topology and diagonal action
g • (a ⊗ b)=(g • a) ⊗ (g • b).

The scalar action is continuous; more generally, continuity on the first
discrete factor suffices for the discrete tensor's scalar action.
If both original G-actions are jointly continuous, so is the tensor action.
Two continuous equivariant coefficient maps induce their ordinary tensor
map, retaining the factor order. The scalar, group and carrier universes
are independent.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct
universe u v w a b c x
namespace ContinuousCohomology

/-- Let R be a commutative ring with a topology and A,B additive
commutative groups with R-module structures and discrete topologies.
If the scalar action R × A → A is continuous, then the induced
R-action on A ⊗[R] B with discrete topology is continuous.
No scalar-continuity hypothesis on B is required. -/
theorem tensorContinuousSMul
    {R : Type u} [CommRing R] [TopologicalSpace R]
    {A : Type a} [AddCommGroup A] [Module R A] [TopologicalSpace A]
    [DiscreteTopology A] [ContinuousSMul R A]
    {B : Type b} [AddCommGroup B] [Module R B] [TopologicalSpace B]
    [DiscreteTopology B] :
    @ContinuousSMul R (A ⊗[R] B) _ ‹TopologicalSpace R› ⊥ := by
  let tensorTopology : TopologicalSpace (A ⊗[R] B) := ⊥
  let : DiscreteTopology (A ⊗[R] B) := ⟨rfl⟩
  change ContinuousSMul R (A ⊗[R] B)
  refine ⟨?_⟩
  rw [continuous_prod_of_discrete_right]
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    have ht : Continuous (fun p : A × B => p.1 ⊗ₜ[R] p.2) :=
      continuous_of_discreteTopology
    have hmap : Continuous (fun r : R => (r • a, b)) :=
      (continuous_id.smul continuous_const).prodMk continuous_const
    have h := ht.comp hmap
    change Continuous (fun r : R => (r • a) ⊗ₜ[R] b) at h
    simpa only [TensorProduct.smul_tmul'] using h
  | add x y hx hy =>
    have h := hx.add hy
    change Continuous (fun r : R => r • x + r • y) at h
    simpa only [smul_add] using h

variable {R : Type u} [CommRing R] [TopologicalSpace R]
variable {G : ProfiniteGrp.{v}}

/-- Let R be a commutative ring with a topology, G a profinite
group, and A,B topological R-representations with discrete coefficient
topologies. Scalar, group and coefficient universes are independent.
This tensor coefficient has carrier A ⊗[R] B, discrete topology
and representation g • (a ⊗ b)=(g • a) ⊗ (g • b). -/
def discreteTensorCoefficient
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] : TopRep.{max v w, u, v} R G := by
  letI : TopologicalSpace (A ⊗[R] B) := ⊥
  letI : DiscreteTopology (A ⊗[R] B) := ⟨rfl⟩
  letI : ContinuousSMul R (A ⊗[R] B) := tensorContinuousSMul
  exact TopRep.of
    { toMonoidHom :=
      { toFun := fun g =>
          { toLinearMap := TensorProduct.map (A.ρ g).toLinearMap (B.ρ g).toLinearMap
            cont := continuous_of_discreteTopology }
        map_one' := by
          apply ContinuousLinearMap.ext
          intro x
          induction x using TensorProduct.inductionOn with
          | tmul a b =>
            change A.ρ 1 a ⊗ₜ[R] B.ρ 1 b = a ⊗ₜ[R] b
            exact congrArg₂ (fun a b => a ⊗ₜ[R] b)
              (congrArg (fun f : A →L[R] A => f a) (map_one A.ρ))
              (congrArg (fun f : B →L[R] B => f b) (map_one B.ρ))
          | add x y hx hy =>
            simpa only [map_add] using congrArg₂ (· + ·) hx hy
        map_mul' := fun g h => by
          apply ContinuousLinearMap.ext
          intro x
          induction x using TensorProduct.inductionOn with
          | tmul a b =>
            change A.ρ (g * h) a ⊗ₜ[R] B.ρ (g * h) b =
              A.ρ g (A.ρ h a) ⊗ₜ[R] B.ρ g (B.ρ h b)
            exact congrArg₂ (fun a b => a ⊗ₜ[R] b)
              (congrArg (fun f : A →L[R] A => f a) (map_mul A.ρ g h))
              (congrArg (fun f : B →L[R] B => f b) (map_mul B.ρ g h))
          | add x y hx hy =>
            simpa only [map_add] using congrArg₂ (· + ·) hx hy } }

/-- Let R be a commutative ring with a topology, G a profinite
group, and A,B topological R-representations with discrete coefficient
topologies. Scalar, group and coefficient universes are independent.
The tensor coefficient's underlying module is exactly the algebraic
tensor product A ⊗[R] B. -/
theorem discreteTensorCoefficient_carrier
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] :
    (discreteTensorCoefficient A B).V = TensorProduct R A B := rfl

instance discreteTensorCoefficient_discrete
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] :
    DiscreteTopology (discreteTensorCoefficient A B) := ⟨rfl⟩

/-- Let R be a commutative ring with a topology, G a profinite
group, and A,B topological R-representations with discrete coefficient
topologies. Scalar, group and coefficient universes are independent.
On a pure tensor, the group action is
g • (a ⊗[R] b)=(A.ρ(g)a) ⊗[R] (B.ρ(g)b). -/
theorem discreteTensorCoefficient_action_tmul
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] (g : G) (a : A) (b : B) :
    (discreteTensorCoefficient A B).ρ g (a ⊗ₜ[R] b) =
      A.ρ g a ⊗ₜ[R] B.ρ g b := by
  change TensorProduct.map (A.ρ g).toLinearMap (B.ρ g).toLinearMap (a ⊗ₜ[R] b) = _
  exact TensorProduct.map_tmul _ _ _ _

/-- Let R be a commutative ring with a topology, G a profinite
group, and A,B topological R-representations with discrete coefficient
topologies. Scalar, group and coefficient universes are independent.
If the G-actions on A and B are jointly continuous, the diagonal
action on the discrete tensor coefficient is jointly continuous. -/
theorem discreteTensorCoefficient_action_isContinuous
    (A B : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B]
    (hA : ((TopRep.toActionTopModFunc (k := R) (G := G)).obj A).IsContinuous)
    (hB : ((TopRep.toActionTopModFunc (k := R) (G := G)).obj B).IsContinuous) :
    ((TopRep.toActionTopModFunc (k := R) (G := G)).obj
      (discreteTensorCoefficient A B)).IsContinuous := by
  let T := discreteTensorCoefficient A B
  have hT : Continuous (fun x : G × T => T.ρ x.1 x.2) := by
    rw [continuous_prod_of_discrete_right]
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      have ha : Continuous (fun g : G => A.ρ g a) :=
        (TopRep.continuous_action hA).comp (continuous_id.prodMk continuous_const)
      have hb : Continuous (fun g : G => B.ρ g b) :=
        (TopRep.continuous_action hB).comp (continuous_id.prodMk continuous_const)
      have ht : Continuous (fun y : A × B => (show T from y.1 ⊗ₜ[R] y.2)) :=
        continuous_of_discreteTopology
      have h := ht.comp (ha.prodMk hb)
      change Continuous (fun g : G => (show T from A.ρ g a ⊗ₜ[R] B.ρ g b)) at h
      simpa only [T, discreteTensorCoefficient_action_tmul] using h
    | add x y hx hy =>
      have h := hx.add hy
      change Continuous (fun g : G => T.ρ g x + T.ρ g y) at h
      exact h.congr fun g => ((T.ρ g).map_add x y).symm
  apply (Action.isContinuous_def _).mpr
  change Continuous (fun x : G × T => T.ρ x.1 x.2)
  exact hT

/-- Let R be a commutative ring with a topology, G a profinite
group, and A,B topological R-representations with discrete coefficient
topologies. Scalar, group and coefficient universes are independent.
For continuous equivariant R-linear f : A → A′ and g : B → B′,
with all four coefficients discrete, the induced coefficient morphism
is f ⊗[R] g : A ⊗[R] B → A′ ⊗[R] B′. -/
def discreteTensorCoefficientMap
    {A B A' B' : TopRep.{max v w, u, v} R G}
    [DiscreteTopology A] [DiscreteTopology B] [DiscreteTopology A'] [DiscreteTopology B']
    (f : A ⟶ A') (g : B ⟶ B') :
    discreteTensorCoefficient A B ⟶ discreteTensorCoefficient A' B' :=
  TopRep.ofHom (ρ := (discreteTensorCoefficient A B).ρ)
    (σ := (discreteTensorCoefficient A' B').ρ)
    { toContinuousLinearMap :=
        (show discreteTensorCoefficient A B →L[R] discreteTensorCoefficient A' B' from
          { toLinearMap := TensorProduct.map f.hom.toLinearMap g.hom.toLinearMap
            cont := continuous_of_discreteTopology })
      isIntertwining' h := by
        have hf : f.hom.toLinearMap.comp (A.ρ h).toLinearMap =
            (A'.ρ h).toLinearMap.comp f.hom.toLinearMap := by
          apply LinearMap.ext
          intro a
          exact TopRep.hom_comm_apply f h a
        have hg : g.hom.toLinearMap.comp (B.ρ h).toLinearMap =
            (B'.ρ h).toLinearMap.comp g.hom.toLinearMap := by
          apply LinearMap.ext
          intro b
          exact TopRep.hom_comm_apply g h b
        have ht : (TensorProduct.map f.hom.toLinearMap g.hom.toLinearMap).comp
            (TensorProduct.map (A.ρ h).toLinearMap (B.ρ h).toLinearMap) =
            (TensorProduct.map (A'.ρ h).toLinearMap (B'.ρ h).toLinearMap).comp
              (TensorProduct.map f.hom.toLinearMap g.hom.toLinearMap) :=
          (TensorProduct.map_comp _ _ _ _).symm.trans
            ((congrArg₂ (fun f g => TensorProduct.map f g) hf hg).trans
              (TensorProduct.map_comp _ _ _ _))
        apply ContinuousLinearMap.ext
        intro z
        change TensorProduct.map f.hom.toLinearMap g.hom.toLinearMap
            (TensorProduct.map (A.ρ h).toLinearMap (B.ρ h).toLinearMap z) =
          TensorProduct.map (A'.ρ h).toLinearMap (B'.ρ h).toLinearMap
            (TensorProduct.map f.hom.toLinearMap g.hom.toLinearMap z)
        exact DFunLike.congr_fun ht z }

/-- Let R be a commutative ring with a topology, G a profinite
group, and A,B topological R-representations with discrete coefficient
topologies. Scalar, group and coefficient universes are independent.
For continuous equivariant maps f : A → A′ and g : B → B′
between discrete coefficients, the tensor coefficient map has value
a ⊗ b ↦ f(a) ⊗ g(b). -/
theorem discreteTensorCoefficientMap_tmul
    {A B A' B' : TopRep.{max v w, u, v} R G}
    [DiscreteTopology A] [DiscreteTopology B] [DiscreteTopology A'] [DiscreteTopology B']
    (f : A ⟶ A') (g : B ⟶ B') (a : A) (b : B) :
    (discreteTensorCoefficientMap f g).hom (a ⊗ₜ[R] b) = f.hom a ⊗ₜ[R] g.hom b := by
  change TensorProduct.map f.hom.toLinearMap g.hom.toLinearMap (a ⊗ₜ[R] b) = _
  exact TensorProduct.map_tmul _ _ _ _

end ContinuousCohomology
