/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GroupTorsorGeometry
public import MathlibExt.AlgebraicGeometry.GeneralStackGeometry
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The actual affine quotient sources for filtrations and modifications

The multiplicative group is Spec of the native Laurent-polynomial Hopf
algebra. The affine line and nodal surface have their literal coordinate
rings. An action comparison is fixed on every scheme-valued point and
coordinate; these equations determine the entire action by Yoneda.

The punctured surface removes the closed origin, by D(s) ∪ D(t), rather
than removing the closed point of the trait. No lifting criterion or
good-moduli-space existence is built into these source definitions.

References: Alper–Halpern-Leistner–Heinloth, arXiv:1812.01128v5,
§2.3 and §3.5, equation (3.6), Definitions 3.36 and 3.38.
Native group and quotient-family operations are existing Mathlib and
GroupTorsorGeometry operations; this file fixes their coordinates.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ThetaQuotientSources

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj Opposite
open _root_.AlgebraicGeometry
open GroupTorsorGeometry
open _root_.AlgebraicGeometry.GeneralStackGeometry

universe u
variable (R : Type u) [CommRing R]

/-- The actual multiplicative group, with its native Laurent Hopf structure. -/
abbrev multiplicativeGroup : Over (Spec (.of R)) :=
  (Spec (.of (LaurentPolynomial R))).asOver (Spec (.of R))

/-- The literal affine line over the trait. -/
abbrev affineLine : Over (Spec (.of R)) :=
  (Spec (.of (Polynomial R))).asOver (Spec (.of R))

open scoped TensorProduct

/-- The fixed coaction sends X to T ⊗ X. -/
def contractingCoaction : Polynomial R →ₐ[R] LaurentPolynomial R ⊗[R] Polynomial R :=
  Polynomial.aeval ((LaurentPolynomial.T 1) ⊗ₜ[R] Polynomial.X)

/-- The source scheme action is Spec of that actual coaction. -/
def contractingMap : ((multiplicativeGroup R) ⊗ affineLine R).left ⟶ (affineLine R).left :=
  (pullbackSpecIso R (LaurentPolynomial R) (Polynomial R)).hom ≫
    Spec.map (CommRingCat.ofHom (contractingCoaction R).toRingHom)

/-- Pullback of an affine coordinate through the native global-section isomorphism. -/
def coordinate {B : Type u} [CommRing B] {T : Scheme.{u}}
    (f : T ⟶ Spec (.of B)) (b : B) : Γ(T, ⊤) :=
  (((Scheme.ΓSpecIso (.of B)).inv ≫ f.appTop).hom) b

/-- The contracting weight-one action is normalized on all scheme tests. -/
class ContractingAction where
  [action : ModObj (multiplicativeGroup R) (affineLine R)]
  map_normalized : γ[multiplicativeGroup R,affineLine R].left = contractingMap R
  normalized : ∀ (T : Scheme.{u})
    (g : T ⟶ (multiplicativeGroup R).left) (x : T ⟶ (affineLine R).left)
    (h : g ≫ (multiplicativeGroup R).hom = x ≫ (affineLine R).hom),
    coordinate (pullback.lift g x h ≫ γ[multiplicativeGroup R,affineLine R].left)
      Polynomial.X =
      coordinate g (LaurentPolynomial.T 1) * coordinate x Polynomial.X

attribute [instance_reducible] ContractingAction.action
attribute [instance] ContractingAction.action

/-- Actual Θ-valued points: torsors and equivariant maps to the affine line. -/
abbrev ThetaObject (A : ContractingAction R) (T : Over (Spec (.of R))) :=
  let _ := A.action
  QuotientObject (multiplicativeGroup R) (affineLine R) T

/-- The fixed coordinate ring R[s,t]/(st-π). -/
def nodeIdeal (π : R) : Ideal (MvPolynomial (Fin 2) R) :=
  Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C π}

abbrev NodeRing (π : R) := MvPolynomial (Fin 2) R ⧸ nodeIdeal R π

def nodeS (π : R) : NodeRing R π :=
  Ideal.Quotient.mk (nodeIdeal R π) (MvPolynomial.X 0)

def nodeT (π : R) : NodeRing R π :=
  Ideal.Quotient.mk (nodeIdeal R π) (MvPolynomial.X 1)

/-- The actual affine surface, including nilpotents in R. -/
abbrev nodeSurface (π : R) : Over (Spec (.of R)) :=
  (Spec (.of (NodeRing R π))).asOver (Spec (.of R))

/-- The two weights are fixed to +1 and -1 on the actual surface coordinates. -/
class OppositeWeightAction (π : R) where
  [action : ModObj (multiplicativeGroup R) (nodeSurface R π)]
  coaction : NodeRing R π →ₐ[R] LaurentPolynomial R ⊗[R] NodeRing R π
  coaction_s : coaction (nodeS R π) = (LaurentPolynomial.T 1) ⊗ₜ[R] nodeS R π
  coaction_t : coaction (nodeT R π) = (LaurentPolynomial.T (-1)) ⊗ₜ[R] nodeT R π
  map_normalized : γ[multiplicativeGroup R,nodeSurface R π].left =
    (pullbackSpecIso R (LaurentPolynomial R) (NodeRing R π)).hom ≫
      Spec.map (CommRingCat.ofHom coaction.toRingHom)
  normalized_s : ∀ (T : Scheme.{u})
    (g : T ⟶ (multiplicativeGroup R).left) (x : T ⟶ (nodeSurface R π).left)
    (h : g ≫ (multiplicativeGroup R).hom = x ≫ (nodeSurface R π).hom),
    coordinate (pullback.lift g x h ≫ γ[multiplicativeGroup R,nodeSurface R π].left)
      (nodeS R π) = coordinate g (LaurentPolynomial.T 1) * coordinate x (nodeS R π)
  normalized_t : ∀ (T : Scheme.{u})
    (g : T ⟶ (multiplicativeGroup R).left) (x : T ⟶ (nodeSurface R π).left)
    (h : g ≫ (multiplicativeGroup R).hom = x ≫ (nodeSurface R π).hom),
    coordinate (pullback.lift g x h ≫ γ[multiplicativeGroup R,nodeSurface R π].left)
      (nodeT R π) = coordinate g (LaurentPolynomial.T (-1)) * coordinate x (nodeT R π)

attribute [instance_reducible] OppositeWeightAction.action
attribute [instance] OppositeWeightAction.action

abbrev SurfaceObject {π : R} (A : OppositeWeightAction R π)
    (T : Over (Spec (.of R))) :=
  let _ := A.action
  QuotientObject (multiplicativeGroup R) (nodeSurface R π) T

def sOpen (π : R) : (nodeSurface R π).left.Opens :=
  (nodeSurface R π).left.basicOpen ((Scheme.ΓSpecIso (.of (NodeRing R π))).inv.hom (nodeS R π))

def tOpen (π : R) : (nodeSurface R π).left.Opens :=
  (nodeSurface R π).left.basicOpen ((Scheme.ΓSpecIso (.of (NodeRing R π))).inv.hom (nodeT R π))

/-- Removing the origin is exactly D(s) ∪ D(t). -/
def puncturedSurface (π : R) : (nodeSurface R π).left.Opens := sOpen R π ⊔ tOpen R π

/-- The trait's Θ puncture removes the closed origin, by D(π) ∪ D(X). -/
def thetaPuncture (π : R) : (affineLine R).left.Opens :=
  (affineLine R).left.basicOpen
      ((Scheme.ΓSpecIso (.of (Polynomial R))).inv.hom (Polynomial.C π)) ⊔
    (affineLine R).left.basicOpen
      ((Scheme.ΓSpecIso (.of (Polynomial R))).inv.hom Polynomial.X)

/-- A presentation of a stack over $\operatorname{Spec} R$ as the quotient stack $[W/G]$, for a
group scheme $G$ over $R$ acting on an $R$-scheme $W$: a stack over $\operatorname{Spec} R$; for
every $R$-scheme $T$, an equivalence between its fibre groupoid over $T$ and the groupoid of fppf
$G$-torsors over $T$ with $G$-equivariant maps to $W$ (`QuotientObject`); and, for every morphism
$f : V \to T$ and every object $x$ over $T$, a pullback of the torsor of $x$ along $f$, identified
with the fibre product (`Reindex`), and an isomorphism from the image of the restriction of $x$
along $f$ to the resulting quotient object over $V$. These isomorphisms are natural in $x$, for
every arrow of the fibre, and compatible with the identity and composition isomorphisms of the
stack. -/
structure QuotientSource {G W : Over (Spec (.of R))} [GrpObj G] [ModObj G W] where
  stack : RelativeStack (Spec (.of R))
  fibre : ∀ T : Over (Spec (.of R)), stack.Fibre T ≌ QuotientObject G W T
  reindex : ∀ {T V : Over (Spec (.of R))} (f : V ⟶ T)
    (x : stack.Fibre T), Reindex G ((fibre T).functor.obj x).torsor f
  restriction : ∀ {T V : Over (Spec (.of R))} (f : V ⟶ T)
    (x : stack.Fibre T),
    QuotientIso G W
      ((fibre V).functor.obj ((stack.toPseudofunctor.map f.op.toLoc).toFunctor.obj x))
      (reindexObject G W ((fibre T).functor.obj x) f (reindex f x))
  arrow_naturality : ∀ {T V : Over (Spec (.of R))} (f : V ⟶ T)
    {x y : stack.Fibre T} (a : x ⟶ y),
    (((fibre V).functor.map ((stack.toPseudofunctor.map f.op.toLoc).toFunctor.map a)).iso.hom ≫
      (restriction f y).iso.hom ≫ (reindex f y).original G) =
      (restriction f x).iso.hom ≫ (reindex f x).original G ≫
        ((fibre T).functor.map a).iso.hom
  identity_normalized : ∀ (T : Over (Spec (.of R))) (x : stack.Fibre T),
    (restriction (𝟙 T) x).iso.hom ≫ (reindex (𝟙 T) x).original G =
      ((fibre T).functor.map
        ((Cat.Hom.toNatIso (stack.toPseudofunctor.mapId (.mk (op T)))).hom.app x)).iso.hom
  composition_normalized : ∀ {T V U : Over (Spec (.of R))}
    (f : V ⟶ T) (g : U ⟶ V) (x : stack.Fibre T),
    (restriction (g ≫ f) x).iso.hom ≫ (reindex (g ≫ f) x).original G =
      ((fibre U).functor.map
        ((Cat.Hom.toNatIso
          (stack.toPseudofunctor.mapComp f.op.toLoc g.op.toLoc)).hom.app x)).iso.hom ≫
      (restriction g ((stack.toPseudofunctor.map f.op.toLoc).toFunctor.obj x)).iso.hom ≫
      (reindex g ((stack.toPseudofunctor.map f.op.toLoc).toFunctor.obj x)).original G ≫
      (restriction f x).iso.hom ≫ (reindex f x).original G

end MathlibExt.AlgebraicGeometry.ThetaQuotientSources
