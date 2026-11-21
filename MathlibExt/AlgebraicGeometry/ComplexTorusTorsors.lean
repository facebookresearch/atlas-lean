/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.Topology.Algebra.Group.Units
public import MathlibExt.AlgebraicGeometry.ComplexAnalytification
public import MathlibExt.AlgebraicGeometry.BettiFunctoriality
public import MathlibExt.Topology.ContinuousBorel
/-!
# Actual algebraic and continuous complex-torus torsors

The torus is literally Spec C[T,T⁻¹], with Mathlib's completed Hopf-induced
group-object structure. Its complex points are normalized by Laurent
coordinate evaluation at an actual complex unit. The action is an actual
scheme morphism with unit/associativity laws; its analytic action must agree
on every such point. A torsor has the actual action-to-fibre-product map
invertible, together with a smooth surjective quotient morphism.

The invariant-quotient equation is proved on the analytification, yielding
an actual continuous-group Borel augmentation and equivariant restriction
maps on the existing rational derived-sheaf cohomology.

The Laurent normalization follows AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/AlgebraicGeometry/GroupScheme/Examples/Multiplicative.lean,
Apache 2.0. Modification notice: specialize to the direct complex model and
retain only actual point evaluation and group/torsor data; no new global
multiplicative-group representability or torsor existence is claimed.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.ComplexTorusTorsors
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory _root_.CategoryTheory.MonObj
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ComplexAnalytification
open MathlibExt.AlgebraicGeometry.PerverseSheaves
abbrev Point : ComplexScheme := Over.mk (𝟙 (Spec (.of ℂ)))
abbrev Gm : ComplexScheme :=
  (Spec (.of (LaurentPolynomial ℂ))).asOver (Spec (.of ℂ))
instance : GrpObj Gm := inferInstance

def pointOfUnit (g : ℂˣ) : Point ⟶ Gm :=
  Over.homMk (Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id ℂ) g))) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hc : (LaurentPolynomial.eval₂ (RingHom.id ℂ) g).comp
        (algebraMap ℂ (LaurentPolynomial ℂ)) = RingHom.id ℂ := by
      ext z
      exact LaurentPolynomial.eval₂_C _ _ z
    simpa only [hc, CommRingCat.ofHom_id] using Spec.map_id (.of ℂ))

def pointOf {X : ComplexScheme} (x : space X) : Point ⟶ X :=
  Over.homMk x.hom x.hom_comp

structure GmAction (X : ComplexScheme) where
  action : Gm ⊗ X ⟶ X
  unit : (η[Gm] ▷ X) ≫ action = (λ_ X).hom
  assoc : (μ[Gm] ▷ X) ≫ action = (α_ Gm Gm X).hom ≫ (Gm ◁ action) ≫ action

variable {X Y : ComplexScheme} (A : GmAction X) (q : X ⟶ Y)

def relation (h : A.action ≫ q = snd Gm X ≫ q) :
    (Gm ⊗ X).left ⟶ pullback q.left q.left :=
  pullback.lift (snd Gm X).left A.action.left
    (by simpa using (congrArg (fun f : Gm ⊗ X ⟶ Y => f.left) h).symm)

class TorusTorsor where
  [mulAction : MulAction ℂˣ (space X)]
  [continuousAction : ContinuousSMul ℂˣ (space X)]
  compatibility : ∀ (g : ℂˣ) (x : space X),
    (g • x).hom = (lift (pointOfUnit g) (pointOf x) ≫ A.action).left
  invariant : A.action ≫ q = snd Gm X ≫ q
  [relationIso : IsIso (relation A q invariant)]
  [smooth : Smooth q.left]
  [surjective : Surjective q.left]
attribute [instance_reducible] TorusTorsor.mulAction
attribute [instance] TorusTorsor.mulAction TorusTorsor.continuousAction
attribute [instance] TorusTorsor.relationIso TorusTorsor.smooth TorusTorsor.surjective

theorem quotientInvariant [T : TorusTorsor A q] (g : ℂˣ) (x : space X) :
    spaceMap q (g • x) = spaceMap q x := by
  apply ComplexPoints.ext
  change (g • x).hom ≫ q.left = x.hom ≫ q.left
  rw [T.compatibility]
  change (lift (pointOfUnit g) (pointOf x) ≫ A.action ≫ q).left = x.hom ≫ q.left
  rw [T.invariant]
  simp [pointOf]


/-- The canonical map from the literal continuous-torus Borel model to the
actual scheme quotient analytification. -/
def borelQuotientMap [T : TorusTorsor A q] :
    MathlibExt.Topology.ContinuousBorel.borel ℂˣ (space X) ⟶ space Y :=
  MathlibExt.Topology.ContinuousBorel.borelToQuotient (G := ℂˣ)
    (spaceMap q) (quotientInvariant A q)

/-- Equivariant restriction is the actual inverse-image map for the
constructed continuous Borel realization, rather than a chosen linear map. -/
def equivariantRestriction {Z W : TopCat.{0}}
    [MulAction ℂˣ Z] [MulAction ℂˣ W] (f : Z ⟶ W)
    (hf : ∀ (g : ℂˣ) (x : Z), f (g • x) = g • f x) (n : ℤ) :=
  BettiFunctoriality.cohomologyPullback
    (MathlibExt.Topology.ContinuousBorel.borelMap f hf) n

end MathlibExt.AlgebraicGeometry.ComplexTorusTorsors
