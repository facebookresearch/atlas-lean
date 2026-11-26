/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GroupTorsorGeometry
public import MathlibExt.AlgebraicGeometry.IntegralChowChernModels

/-!
# Actual fixed-point scheme functors and component embeddings

Fixed points are actual scheme maps on every parameter scheme.
Their equality is the equality of the two original G×T action
maps, including nonreduced tests. A fixed-scheme model represents
exactly that functor and has the actual closed inclusion.

Components retain genuine open/closed subscheme embeddings,
disjointness and a covering of the represented fixed scheme.

References: Graber–Pandharipande, arXiv:alg-geom/9708001v2,
§1; Maulik–Okounkov, arXiv:1211.1287v3, §3.2.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.TorusFixedSchemeModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory _root_.CategoryTheory.MonObj
open _root_.AlgebraicGeometry
open IntegralChowChernModels

variable (G : Over (Spec (.of ℂ))) [GrpObj G] (X : Over (Spec (.of ℂ))) [ModObj G X]

/-- Every fixed point satisfies equality of the full parameterized scheme action maps. -/
def FixedPoint {T : Over (Spec (.of ℂ))} (x : T ⟶ X) : Prop :=
  (G ◁ x) ≫ γ[G,X] = snd G T ≫ x

theorem fixedReindex {T U : Over (Spec (.of ℂ))} (f : U ⟶ T) (x : T ⟶ X)
    (h : FixedPoint G X x) : FixedPoint G X (f ≫ x) := by
  change (G ◁ (f ≫ x)) ≫ γ[G,X] = snd G U ≫ (f ≫ x)
  rw [whiskerLeft_comp,Category.assoc,h]
  rw [← Category.assoc,whiskerLeft_snd,Category.assoc]

/-- The closed scheme represents all actual fixed maps, not a point-set fixed subset. -/
structure FixedSchemeModel where
  scheme : Over (Spec (.of ℂ))
  inclusion : scheme ⟶ X
  [closed : IsClosedImmersion inclusion.left]
  fixed : FixedPoint G X inclusion
  universal : ∀ (T : Over (Spec (.of ℂ))) (x : T ⟶ X), FixedPoint G X x →
    ∃! f : T ⟶ scheme, f ≫ inclusion=x

attribute [instance] FixedSchemeModel.closed

/-- A genuine fixed-scheme component with its original inclusion. -/
structure FixedComponent (F : FixedSchemeModel G X) where
  data : SchemeData
  inclusion : data.scheme ⟶ F.scheme
  [openImmersion : IsOpenImmersion inclusion.left]
  [closedImmersion : IsClosedImmersion inclusion.left]
  connected : ConnectedSpace data.scheme.left

attribute [instance] FixedComponent.openImmersion FixedComponent.closedImmersion

def FixedComponent.toAmbient {F : FixedSchemeModel G X} (Z : FixedComponent G X F) :
    Z.data.scheme ⟶ X := Z.inclusion ≫ F.inclusion

/-- A finite actual component decomposition of the represented fixed scheme. -/
structure FixedComponents (F : FixedSchemeModel G X) where
  count : ℕ
  component : Fin count → FixedComponent G X F
  disjoint : Pairwise (fun i j => Disjoint
    (Set.range (component i).inclusion.left) (Set.range (component j).inclusion.left))
  cover : (⋃ i, Set.range (component i).inclusion.left)=Set.univ

end MathlibExt.AlgebraicGeometry.TorusFixedSchemeModels
