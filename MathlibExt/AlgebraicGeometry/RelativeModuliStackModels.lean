/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeMapTypeModels
public import MathlibExt.AlgebraicGeometry.StackChowGroups

/-!
# Actual relative-map moduli with every family comparison

The stack represents the full native groupoid of maps to expanded targets,
with fixed genera, ordered markings/contact and actual contracted curve
classes. All disconnected components share one target. Reindexing is fixed
by Cartesian target/domain maps and all boundary, contact/evaluation squares.
Native stack unit/composition cells use those same maps on every component.
Source: Jun Li arXiv:math/0009097v1, Sections4.2--4.3;
arXiv:math/0110113v1, Sections2.1 and3.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeModuliStackModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open ExpandedTargetChainGeometry RelativeProjectiveLineModels StandardRelativeExpansionModels
open ExpandedRelativeFamilies RelativeExpandedMapFamilies RelativeMapTypeModels
open StackCycleGeometry StackCycleRelations

variable {k : Type} [Field k]
  (P : RelativePair (k := k)) (R : ProjectiveLine P.divisor.left (normalLineModule P))
  (S : StandardSystem P R) {n r : ℕ} (G : RelativeType n r)

structure FamilyBaseChange {T U : Over (Spec (.of k))} (f : T ⟶ U)
    (F : TypeFamily P R S G T) (H : TypeFamily P R S G U) where
  target : F.target.scheme ⟶ H.target.scheme
  target_cartesian : IsPullback target F.target.projection H.target.projection f
  target_contraction : target ≫ H.target.contraction = F.target.contraction
  target_boundary : F.target.boundary ≫ target = prod.map (𝟙 P.divisor) f ≫ H.target.boundary
  source : ∀ v : Fin G.vertices, (F.maps v).curve.X ⟶ (H.maps v).curve.X
  source_cartesian : ∀ v, IsPullback (source v) (F.maps v).curve.π (H.maps v).curve.π f.left
  marking : ∀ (v : Fin G.vertices) (i : Fin (G.legs v + G.roots v)),
    (F.maps v).curve.marking i ≫ source v = f.left ≫ (H.maps v).curve.marking i
  map : ∀ v, (F.maps v).map ≫ target.left = source v ≫ (H.maps v).map
  evaluation : ∀ i : Fin r,
    RelativeMapTypeModels.evaluation P R S G T F i = f ≫ RelativeMapTypeModels.evaluation P R S G U H i

variable [LocallyOfFiniteType P.target.hom] [IsNoetherian P.target.left]
  (beta : Fin G.vertices → RelativeCurveClasses.CurveClass P.target)

/-- The moduli stack of stable relative maps of the given Chow-refined type (`HasVertexClasses`):
the subfunctor of Li's moduli (math/0009097v1, Defs. 4.6–4.7) fixing the pushed Chow classes,
not only the degree. -/
structure RelativeModuliModel where
  stack : Stack (Spec (.of k))
  family : ∀ T : Over (Spec (.of k)), stack.Fibre T ⥤ StableTypeFamily P R S G T beta
  equivalence : ∀ T : Over (Spec (.of k)), (family T).IsEquivalence
  dm : stack.IsDeligneMumfordStack
  finiteType : FiniteTypeArtin k stack
  reindex : ∀ {T U : Over (Spec (.of k))} (f : T ⟶ U) (x : stack.Fibre U),
    FamilyBaseChange P R S G f ((family T).obj ((pull stack f).obj x)).obj ((family U).obj x).obj
  target_naturality : ∀ {T U : Over (Spec (.of k))} (f : T ⟶ U)
      {x y : stack.Fibre U} (h : x ⟶ y),
    ((family T).map ((pull stack f).map h)).hom.target.iso.hom ≫ (reindex f y).target =
      (reindex f x).target ≫ ((family U).map h).hom.target.iso.hom
  source_naturality : ∀ {T U : Over (Spec (.of k))} (f : T ⟶ U)
      {x y : stack.Fibre U} (h : x ⟶ y) (v : Fin G.vertices),
    (((family T).map ((pull stack f).map h)).hom.source v).hom ≫ (reindex f y).source v =
      (reindex f x).source v ≫ (((family U).map h).hom.source v).hom
  target_unit : ∀ (T : Over (Spec (.of k))) (x : stack.Fibre T),
    ((family T).map
      ((stack.toPseudofunctor.mapId (.mk (op T))).hom.toNatTrans.app x)).hom.target.iso.hom =
        (reindex (𝟙 T) x).target
  source_unit : ∀ (T : Over (Spec (.of k))) (x : stack.Fibre T) (v : Fin G.vertices),
    (((family T).map
      ((stack.toPseudofunctor.mapId (.mk (op T))).hom.toNatTrans.app x)).hom.source v).hom =
        (reindex (𝟙 T) x).source v
  target_comp : ∀ {T U V : Over (Spec (.of k))} (f : T ⟶ U) (g : U ⟶ V) (x : stack.Fibre V),
    ((family T).map
      ((stack.toPseudofunctor.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app x)).hom.target.iso.hom ≫
        (reindex (f ≫ g) x).target = (reindex f ((pull stack g).obj x)).target ≫ (reindex g x).target
  source_comp : ∀ {T U V : Over (Spec (.of k))} (f : T ⟶ U) (g : U ⟶ V)
      (x : stack.Fibre V) (v : Fin G.vertices),
    (((family T).map
      ((stack.toPseudofunctor.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app x)).hom.source v).hom ≫
        (reindex (f ≫ g) x).source v = (reindex f ((pull stack g).obj x)).source v ≫ (reindex g x).source v

end MathlibExt.AlgebraicGeometry.RelativeModuliStackModels
