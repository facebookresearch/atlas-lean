/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies
public import MathlibExt.AlgebraicGeometry.StackCycleRelations

/-!
# Actual stable marked-curve stack models

The fibre category is the full subgroupoid of actual marked proper, flat,
finitely presented nodal scheme families with finite marked automorphisms.
Its arrows are actual curve isomorphisms preserving the base and markings.
The stack comparison is an equivalence on every scheme-valued fibre.
Reindexing is fixed by Cartesian scheme maps on objects and arrows, and
native pseudofunctor unit/composition cells use those same projection maps.

No geometric stack or universal curve is represented by an unrelated type.
The native family/base-change definitions reuse the completed TauCeti
source at 62bbc0596dc3539d488232e4e924a338548ea0a9, Apache 2.0,
Curves/StableMaps and Curves/Prestable. Stack realization and native
comparison constructors remain Wanted integration work.
References: Deligne--Mumford stable curves; Janda--Pandharipande--Pixton--
Zvonkine, arXiv:1602.04705v2, Sections 0.3.2--0.3.3, printed pp8--9.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StableCurveStackModels

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry
open StackCycleGeometry StackCycleRelations
open MarkedCurveStabilization

variable {k : Type} [Field k]

/-- Actual stable-curve objects, with the inherited full native groupoid. -/
abbrev CurveFamily (T : Over (Spec (.of k))) (g n : ℕ) :=
  (show ObjectProperty
      (GeneralStableMapFamilies.Family (𝟙 (Spec (.of k))) n g T.left T.hom)
    from fun F => MarkedCurveStabilization.IsStable F.curve).FullSubcategory

abbrev curve {T : Over (Spec (.of k))} {g n : ℕ} (F : CurveFamily T g n) :=
  F.obj.curve

/-- Every source map is the actual Cartesian family reindex. -/
structure FamilyBaseChange {T U : Over (Spec (.of k))} (f : T ⟶ U) {g n : ℕ}
    (F : CurveFamily T g n) (G : CurveFamily U g n) where
  projection : (curve F).X ⟶ (curve G).X
  cartesian : IsPullback projection (curve F).π (curve G).π f.left
  markings : ∀ i : Fin n, (curve F).marking i ≫ projection = f.left ≫ (curve G).marking i

/-- Pure stack dimension `d`: a cycle atlas exists, and on every cycle atlas each irreducible
component of the atlas has dimension `d` plus the atlas's relative rank. Requiring an atlas
keeps the condition from holding vacuously when no cycle atlas exists. -/
def HasDimension (X : Stack (Spec (.of k))) (d : ℤ) : Prop :=
  Nonempty (CycleAtlas X) ∧
  ∀ (a : CycleAtlas X) (Z : Set a.atlas.U.left),
    Z ∈ irreducibleComponents a.atlas.U.left →
      ∃ r : ℕ, (r : ℤ) = d + a.relativeRank ∧ topologicalKrullDim Z = (r : ℕ)

/-- Source-normalized actual stable marked-curve moduli with every scheme
test and full native unit/composition comparison retained. -/
structure StableCurveStackModel (g n : ℕ) where
  stack : Stack (Spec (.of k))
  family : ∀ T : Over (Spec (.of k)), stack.Fibre T ⥤ CurveFamily T g n
  equivalence : ∀ T : Over (Spec (.of k)), (family T).IsEquivalence
  dm : stack.IsDeligneMumfordStack
  finiteType : FiniteTypeArtin k stack
  dimension : HasDimension stack (3 * (g : ℤ) - 3 + n)
  reindex : ∀ {T U : Over (Spec (.of k))} (f : T ⟶ U) (x : stack.Fibre U),
    FamilyBaseChange f ((family T).obj ((pull stack f).obj x)) ((family U).obj x)
  naturality : ∀ {T U : Over (Spec (.of k))} (f : T ⟶ U)
      {x y : stack.Fibre U} (h : x ⟶ y),
    ((family T).map ((pull stack f).map h)).hom.iso.hom ≫ (reindex f y).projection =
      (reindex f x).projection ≫ ((family U).map h).hom.iso.hom
  unit_normalization : ∀ (T : Over (Spec (.of k))) (x : stack.Fibre T),
    ((family T).map
      ((stack.toPseudofunctor.mapId (.mk (op T))).hom.toNatTrans.app x)).hom.iso.hom =
        (reindex (𝟙 T) x).projection
  composition_normalization : ∀ {T U V : Over (Spec (.of k))}
      (f : T ⟶ U) (g' : U ⟶ V) (x : stack.Fibre V),
    ((family T).map
      ((stack.toPseudofunctor.mapComp g'.op.toLoc f.op.toLoc).inv.toNatTrans.app x)).hom.iso.hom ≫
        (reindex (f ≫ g') x).projection =
      (reindex f ((pull stack g').obj x)).projection ≫ (reindex g' x).projection

/-- The actual stable marked family over a scheme-valued moduli point. -/
def familyAt {g n : ℕ} (M : StableCurveStackModel (k := k) g n)
    (T : Over (Spec (.of k))) (x : M.stack.Fibre T) : MarkedFamily T.left n g :=
  curve ((M.family T).obj x)

end MathlibExt.AlgebraicGeometry.StableCurveStackModels
