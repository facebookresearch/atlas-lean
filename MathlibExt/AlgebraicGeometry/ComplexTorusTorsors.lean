/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.CategoryTheory.Monoidal.Mod
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
coordinate evaluation at an actual complex unit. An action is Mathlib's
`ModObj Gm X`, an actual scheme morphism with unit/associativity laws; its
analytic action must agree on every such point. A torsor has the actual action-to-fibre-product map
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

/-- The multiplicative group $\mathbb{G}_m = \operatorname{Spec} \mathbb{C}[T, T^{-1}]$ as a scheme
over $\operatorname{Spec} \mathbb{C}$. Its group-object structure is induced by the Hopf algebra
structure of $\mathbb{C}[T, T^{-1}]$, the group algebra of $\mathbb{Z}$. -/
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

variable {X Y : ComplexScheme} (A : ModObj Gm X) (q : X ⟶ Y)

/-- For an invariant map `q`, the map `(g, x) ↦ (x, g • x)` into the fibre
product of `q` with itself. -/
def relation (h : A.smul ≫ q = snd Gm X ≫ q) :
    (Gm ⊗ X).left ⟶ pullback q.left q.left :=
  pullback.lift (snd Gm X).left A.smul.left
    (by simpa using (congrArg (fun f : Gm ⊗ X ⟶ Y => f.left) h).symm)

/-- A $\mathbb{G}_m$-torsor structure on $q : X \to Y$ for the action $A$ of $\mathbb{G}_m$ on $X$
(schemes over $\mathbb{C}$): a continuous action of $\mathbb{C}^\times$ on the space of complex
points of $X$ (`mulAction`, `continuousAction`) under which $g \cdot x$ is the image of $(g, x)$
under the action morphism of $A$ (`compatibility`); and the conditions that $q$ is invariant,
$q(g \cdot x) = q(x)$ as morphisms $\mathbb{G}_m \times X \to Y$ (`invariant`), that the morphism
$\mathbb{G}_m \times X \to X \times_Y X$, $(g, x) \mapsto (x, g \cdot x)$, is an isomorphism
(`relationIso`), and that $q$ is smooth and surjective (`smooth`, `surjective`). -/
class TorusTorsor where
  /-- The action of `ℂˣ` on the complex points of `X` induced by `A`. -/
  [mulAction : MulAction ℂˣ (space X)]
  /-- That action is continuous. -/
  [continuousAction : ContinuousSMul ℂˣ (space X)]
  /-- It is the action induced by `A` on complex points. -/
  compatibility : ∀ (g : ℂˣ) (x : space X),
    (g • x).hom = (lift (pointOfUnit g) (pointOf x) ≫ A.smul).left
  /-- The quotient map is invariant. -/
  invariant : A.smul ≫ q = snd Gm X ≫ q
  /-- The action is free and transitive on the fibres of `q`. -/
  [relationIso : IsIso (relation A q invariant)]
  /-- The quotient map is smooth. -/
  [smooth : Smooth q.left]
  /-- The quotient map is surjective. -/
  [surjective : Surjective q.left]
attribute [instance] TorusTorsor.relationIso TorusTorsor.smooth TorusTorsor.surjective

/-- The quotient map is invariant on complex points, for the analytic action of
the torsor. -/
theorem quotientInvariant [T : TorusTorsor A q] (g : ℂˣ) (x : space X) :
    letI := T.mulAction
    spaceMap q (g • x) = spaceMap q x := by
  let := T.mulAction
  apply ComplexPoints.ext
  change (g • x).hom ≫ q.left = x.hom ≫ q.left
  rw [T.compatibility]
  change (lift (pointOfUnit g) (pointOf x) ≫ A.smul ≫ q).left = x.hom ≫ q.left
  rw [T.invariant]
  simp [pointOf]

/-- The continuous-torus Borel model of the complex points of the source of a
torsor, for the torsor's own analytic action. -/
abbrev torsorBorel [T : TorusTorsor A q] : TopCat.{0} :=
  letI := T.mulAction
  letI := T.continuousAction
  MathlibExt.Topology.ContinuousBorel.borel ℂˣ (space X)

/-- The canonical map from the literal continuous-torus Borel model to the
actual scheme quotient analytification. -/
def borelQuotientMap [T : TorusTorsor A q] : torsorBorel A q ⟶ space Y :=
  letI := T.mulAction
  letI := T.continuousAction
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
