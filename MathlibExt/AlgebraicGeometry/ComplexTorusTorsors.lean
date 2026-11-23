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
/-- The point `Spec ℂ`, as a scheme over `ℂ`. -/
abbrev Point : ComplexScheme := Over.mk (𝟙 (Spec (.of ℂ)))

/-- The multiplicative group `Spec ℂ[T, T⁻¹]` over `ℂ`. Its group-object
structure is Mathlib's, induced by the Hopf algebra of Laurent polynomials. -/
abbrev Gm : ComplexScheme :=
  (Spec (.of (LaurentPolynomial ℂ))).asOver (Spec (.of ℂ))

/-- The complex point of `Gm` given by a unit `g`: evaluation of Laurent
polynomials at `g`. -/
def pointOfUnit (g : ℂˣ) : Point ⟶ Gm :=
  Over.homMk (Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id ℂ) g))) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hc : (LaurentPolynomial.eval₂ (RingHom.id ℂ) g).comp
        (algebraMap ℂ (LaurentPolynomial ℂ)) = RingHom.id ℂ := by
      ext z
      exact LaurentPolynomial.eval₂_C _ _ z
    simpa only [hc, CommRingCat.ofHom_id] using Spec.map_id (.of ℂ))

/-- A complex point of `X`, as a morphism from the point over `ℂ`. -/
def pointOf {X : ComplexScheme} (x : space X) : Point ⟶ X :=
  Over.homMk x.hom x.hom_comp

/-- An action of `Gm` on a scheme over `ℂ`, with its unit and associativity
laws. -/
structure GmAction (X : ComplexScheme) where
  /-- The action morphism `Gm × X ⟶ X` over `ℂ`. -/
  action : Gm ⊗ X ⟶ X
  /-- The unit of `Gm` acts trivially. -/
  unit : (η[Gm] ▷ X) ≫ action = (λ_ X).hom
  /-- The action is associative. -/
  assoc : (μ[Gm] ▷ X) ≫ action = (α_ Gm Gm X).hom ≫ (Gm ◁ action) ≫ action

variable {X Y : ComplexScheme} (A : GmAction X) (q : X ⟶ Y)

/-- For an invariant map `q`, the map `(g, x) ↦ (x, g • x)` into the fibre
product of `q` with itself. -/
def relation (h : A.action ≫ q = snd Gm X ≫ q) :
    (Gm ⊗ X).left ⟶ pullback q.left q.left :=
  pullback.lift (snd Gm X).left A.action.left
    (by simpa using (congrArg (fun f : Gm ⊗ X ⟶ Y => f.left) h).symm)

/-- `q : X ⟶ Y` is a `Gm`-torsor for the action `A`: `q` is invariant, smooth
and surjective, and `(g, x) ↦ (x, g • x)` is an isomorphism onto `X ×_Y X`.
The action of `ℂˣ` on complex points is part of the data, pinned down by
`compatibility` (it is the action induced by `A`), and is continuous. -/
class TorusTorsor where
  /-- The action of `ℂˣ` on the complex points of `X`. -/
  [mulAction : MulAction ℂˣ (space X)]
  /-- That action is continuous. -/
  [continuousAction : ContinuousSMul ℂˣ (space X)]
  /-- It is the action induced by `A` on complex points. -/
  compatibility : ∀ (g : ℂˣ) (x : space X),
    (g • x).hom = (lift (pointOfUnit g) (pointOf x) ≫ A.action).left
  /-- The quotient map is invariant. -/
  invariant : A.action ≫ q = snd Gm X ≫ q
  /-- The action is free and transitive on the fibres of `q`. -/
  [relationIso : IsIso (relation A q invariant)]
  /-- The quotient map is smooth. -/
  [smooth : Smooth q.left]
  /-- The quotient map is surjective. -/
  [surjective : Surjective q.left]
attribute [instance_reducible] TorusTorsor.mulAction
attribute [instance] TorusTorsor.mulAction TorusTorsor.continuousAction
attribute [instance] TorusTorsor.relationIso TorusTorsor.smooth TorusTorsor.surjective

/-- The quotient map is invariant on complex points. -/
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
    [MulAction ℂˣ Z] [ContinuousSMul ℂˣ Z] [MulAction ℂˣ W] [ContinuousSMul ℂˣ W] (f : Z ⟶ W)
    (hf : ∀ (g : ℂˣ) (x : Z), f (g • x) = g • f x) (n : ℤ) :=
  BettiFunctoriality.cohomologyPullback
    (MathlibExt.Topology.ContinuousBorel.borelMap f hf) n

end MathlibExt.AlgebraicGeometry.ComplexTorusTorsors
