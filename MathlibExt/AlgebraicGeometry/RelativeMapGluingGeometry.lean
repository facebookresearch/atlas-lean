/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ExpandedTargetGluingModels
public import MathlibExt.AlgebraicGeometry.RelativeRootEquivalenceGroups

/-!
# Actual relative-source gluing along ordered matching roots

The matching graph uses the actual incidence of ordered roots in the two
relative types. Its connectivity/genus equation are explicit. The glued
marked scheme is the quotient of the actual domain components identifying
exactly the matching root sections. Its map to the actual joined expanded
target is fixed on every component. This is the geometric operation
underlying Jun Li's Phi_eta, not a supplied arbitrary gluing function.
Source: Jun Li arXiv:math/0110113v1, Section3.1, pp30--32.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeMapGluingGeometry

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open ExpandedTargetChainGeometry RelativeProjectiveLineModels StandardRelativeExpansionModels
open ExpandedRelativeFamilies RelativeMapTypeModels RelativeExpandedMapFamilies
open ExpandedTargetGluingModels MarkedCurveStabilization
open scoped BigOperators

variable {n n' r g : ℕ} (G : RelativeType n r) (H : RelativeType n' r)

/-- Admissible gluing of two relative types along their `r` roots, matched in order. This is the
restricted case of Li's gluing (math/0009097v1, Def. 4.11): both sides are nonempty (a
`RelativeType` has a vertex) and the glued markings put all left legs before all right legs,
rather than an arbitrary order-preserving shuffle. -/
structure AdmissibleGluing : Prop where
  order : ∀ i : Fin r, G.order i = H.order i
  genus : g + G.vertices + H.vertices =
    (∑ v, G.genus v) + (∑ v, H.genus v) + r + 1
  connected : ∀ a b : Fin G.vertices ⊕ Fin H.vertices, Relation.ReflTransGen
    (fun a b => ∃ i : Fin r,
      (a = Sum.inl (G.rootLabels i).1 ∧ b = Sum.inr (H.rootLabels i).1) ∨
      (b = Sum.inl (G.rootLabels i).1 ∧ a = Sum.inr (H.rootLabels i).1)) a b

variable {k : Type} [Field k]
  (P Q : RelativePair (k := k))
  (R : ProjectiveLine P.divisor.left (normalLineModule P))
  (R' : ProjectiveLine Q.divisor.left (normalLineModule Q))
  (S : StandardSystem P R) (S' : StandardSystem Q R')
  (W : SingularTarget P Q) (T : Over (Spec (.of k)))
  (F : TypeFamily P R S G T) (F' : TypeFamily Q R' S' H T)

def rootSection (i : Fin r) :
    T.left ⟶ (F.maps (G.rootLabels i).1).curve.X :=
  (F.maps (G.rootLabels i).1).curve.marking
    (Fin.natAdd (G.legs (G.rootLabels i).1) (G.rootLabels i).2)

def rootSectionRight (i : Fin r) :
    T.left ⟶ (F'.maps (H.rootLabels i).1).curve.X :=
  (F'.maps (H.rootLabels i).1).curve.marking
    (Fin.natAdd (H.legs (H.rootLabels i).1) (H.rootLabels i).2)

def RootMatch : Prop :=
  ∀ i : Fin r, RelativeMapTypeModels.evaluation P R S G T F i ≫ W.divisor.hom =
    RelativeMapTypeModels.evaluation Q R' S' H T F' i

structure SourceJoin where
  curve : MarkedFamily T.left (n + n') g
  left : ∀ v : Fin G.vertices, (F.maps v).curve.X ⟶ curve.X
  right : ∀ v : Fin H.vertices, (F'.maps v).curve.X ⟶ curve.X
  left_over : ∀ v, left v ≫ curve.π = (F.maps v).curve.π
  right_over : ∀ v, right v ≫ curve.π = (F'.maps v).curve.π
  roots : ∀ i : Fin r,
    rootSection G P R S T F i ≫ left (G.rootLabels i).1 =
      rootSectionRight H Q R' S' T F' i ≫ right (H.rootLabels i).1
  left_legs : ∀ i : Fin n,
    (F.maps (G.legLabels i).1).curve.marking
      (Fin.castAdd (G.roots (G.legLabels i).1) (G.legLabels i).2) ≫ left (G.legLabels i).1 =
        curve.marking (Fin.castAdd n' i)
  right_legs : ∀ i : Fin n',
    (F'.maps (H.legLabels i).1).curve.marking
      (Fin.castAdd (H.roots (H.legLabels i).1) (H.legLabels i).2) ≫ right (H.legLabels i).1 =
        curve.marking (Fin.natAdd n i)
  universal : ∀ (Z : Scheme.{0}) (z : Z ⟶ T.left)
      (f : ∀ v : Fin G.vertices, (F.maps v).curve.X ⟶ Z)
      (h : ∀ v : Fin H.vertices, (F'.maps v).curve.X ⟶ Z),
    (∀ v, f v ≫ z = (F.maps v).curve.π) → (∀ v, h v ≫ z = (F'.maps v).curve.π) →
    (∀ i : Fin r, rootSection G P R S T F i ≫ f (G.rootLabels i).1 =
      rootSectionRight H Q R' S' T F' i ≫ h (H.rootLabels i).1) →
        ∃! q : curve.X ⟶ Z, q ≫ z = curve.π ∧
          (∀ v, left v ≫ q = f v) ∧ (∀ v, right v ≫ q = h v)

variable (X : TargetJoin P Q R R' S S' W T F.target F'.target)
  (C : SourceJoin (g := g) G H P Q R R' S S' T F F')

/-- The raw map out of the pushout of the two sources into the joined target. It does not by
itself enforce matching contact orders or stability (branch orders `1` and `2` can define a map
of nodes without being predeformable), so it is not on its own a certificate of a stable glued
map in Li's sense. -/
structure JoinedMap where
  map : C.curve.X ⟶ X.scheme.left
  over : map ≫ X.projection.left = C.curve.π
  left : ∀ v : Fin G.vertices, C.left v ≫ map = (F.maps v).map ≫ X.left.left
  right : ∀ v : Fin H.vertices, C.right v ≫ map = (F'.maps v).map ≫ X.right.left

end MathlibExt.AlgebraicGeometry.RelativeMapGluingGeometry
