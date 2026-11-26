/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RubberMapFamilies
public import MathlibExt.AlgebraicGeometry.GraphClutchingModels

/-!
# Actual rubber moduli and marked-curve stabilization

The fibre groupoid consists of the actual signed-contact rubber families
and their combined finite geometric automorphisms. Their targets are rubber
targets, framed only fppf-locally on the base, so the fibre groupoids are
closed under descent: twisted targets such as the projective completion of a
nontrivial line bundle on the base are included. Every reindex is a
Cartesian target/domain map preserving both endpoint ideals and all marks.
Native stack units/compositions are normalized to these exact maps.

Epsilon is an actual stack morphism fixed by the native marked-curve
stabilization contraction on every family, arrow and base change. No
independent curve-forgetting map is supplied.
Source: JPPZ arXiv:1602.04705v2, Section0.2.4, printed p6;
Jun Li arXiv:math/0009097v1 and math/0110113v1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RubberModuliStackModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open RelativeProjectiveLineModels ExpandedTargetChainGeometry StandardRelativeExpansionModels
open RubberMapFamilies MarkedCurveStabilization CoherentCurveLinearSeries
open StackCycleGeometry StackCycleRelations StableCurveStackModels GraphClutchingModels

variable {k : Type} [Field k]
  (O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k))))
  (P : RelativePair (k := k)) (D : OriginalRubberPair O P)
  (R : ProjectiveLine P.divisor.left (normalLineModule P)) (S : StandardSystem P R)
  {g n : ℕ} (a : Fin n → ℤ)

abbrev StableFamily (T : Over (Spec (.of k))) :=
  (show ObjectProperty (RubberFamily O P D R S T g n a) from
    IsStableRubber O P D R S).FullSubcategory

structure FamilyBaseChange {T U : Over (Spec (.of k))} (h : T ⟶ U)
    (F : RubberFamily O P D R S T g n a) (H : RubberFamily O P D R S U g n a) where
  target : F.target.scheme ⟶ H.target.scheme
  target_cartesian : IsPullback target F.target.projection H.target.projection h
  zero : F.target.zero = H.target.zero.comap target.left
  infinity : F.target.boundary.left.ker = H.target.boundary.left.ker.comap target.left
  source : F.curve.X ⟶ H.curve.X
  source_cartesian : IsPullback source F.curve.π H.curve.π h.left
  markings : ∀ i : Fin n, F.curve.marking i ≫ source = h.left ≫ H.curve.marking i
  map : source ≫ H.map = F.map ≫ target.left

structure RubberModuliModel where
  stack : Stack (Spec (.of k))
  family : ∀ T : Over (Spec (.of k)), stack.Fibre T ⥤ StableFamily O P D R S (g := g) a T
  equivalence : ∀ T : Over (Spec (.of k)), (family T).IsEquivalence
  dm : stack.IsDeligneMumfordStack
  finiteType : FiniteTypeArtin k stack
  reindex : ∀ {T U : Over (Spec (.of k))} (h : T ⟶ U) (x : stack.Fibre U),
    FamilyBaseChange O P D R S a h ((family T).obj ((pull stack h).obj x)).obj
      ((family U).obj x).obj
  target_naturality : ∀ {T U : Over (Spec (.of k))} (h : T ⟶ U) {x y : stack.Fibre U} (f : x ⟶ y),
    ((family T).map ((pull stack h).map f)).hom.target.iso.hom ≫ (reindex h y).target =
      (reindex h x).target ≫ ((family U).map f).hom.target.iso.hom
  source_naturality : ∀ {T U : Over (Spec (.of k))} (h : T ⟶ U) {x y : stack.Fibre U} (f : x ⟶ y),
    ((family T).map ((pull stack h).map f)).hom.source.hom ≫ (reindex h y).source =
      (reindex h x).source ≫ ((family U).map f).hom.source.hom
  target_unit : ∀ (T : Over (Spec (.of k))) (x : stack.Fibre T),
    ((family T).map ((stack.toPseudofunctor.mapId
      (.mk (op T))).hom.toNatTrans.app x)).hom.target.iso.hom =
      (reindex (𝟙 T) x).target
  source_unit : ∀ (T : Over (Spec (.of k))) (x : stack.Fibre T),
    ((family T).map ((stack.toPseudofunctor.mapId
      (.mk (op T))).hom.toNatTrans.app x)).hom.source.hom =
      (reindex (𝟙 T) x).source
  target_comp : ∀ {T U V : Over (Spec (.of k))} (h : T ⟶ U) (f : U ⟶ V) (x : stack.Fibre V),
    ((family T).map
      ((stack.toPseudofunctor.mapComp
        f.op.toLoc h.op.toLoc).inv.toNatTrans.app x)).hom.target.iso.hom ≫
        (reindex (h ≫ f) x).target =
          (reindex h ((pull stack f).obj x)).target ≫ (reindex f x).target
  source_comp : ∀ {T U V : Over (Spec (.of k))} (h : T ⟶ U) (f : U ⟶ V) (x : stack.Fibre V),
    ((family T).map
      ((stack.toPseudofunctor.mapComp f.op.toLoc h.op.toLoc).inv.toNatTrans.app x)).hom.source.hom ≫
        (reindex (h ≫ f) x).source =
          (reindex h ((pull stack f).obj x)).source ≫ (reindex f x).source

structure MarkedStabilization {T : Scheme.{0}} (F G : MarkedFamily T n g) where
  stable : MarkedCurveStabilization.IsStable G
  contraction : F.X ⟶ G.X
  over : contraction ≫ G.π = F.π
  markings : ∀ i : Fin n, F.marking i ≫ contraction = G.marking i
  genus : IsGenusPreservingContraction contraction
  universal : ∀ (H : MarkedFamily T n g), MarkedCurveStabilization.IsStable H →
    ∀ f : F.X ⟶ H.X, f ≫ H.π = F.π →
    (∀ i : Fin n, F.marking i ≫ f = H.marking i) → IsGenusPreservingContraction f →
      ∃! e : G.X ≅ H.X, contraction ≫ e.hom = f ∧ e.hom ≫ H.π = G.π

variable (B : RubberModuliModel O P D R S (g := g) a) (M : StableCurveStackModel (k := k) g n)

structure EpsilonData where
  map : StackHom B.stack M.stack
  stabilization : ∀ (T : Over (Spec (.of k))) (x : B.stack.Fibre T),
    MarkedStabilization (((B.family T).obj x).obj.curve) (mappedFamilyAt M map T x)
  arrows : ∀ (T : Over (Spec (.of k))) {x y : B.stack.Fibre T} (f : x ⟶ y),
    ((B.family T).map f).hom.source.hom ≫ (stabilization T y).contraction =
      (stabilization T x).contraction ≫ (mappedFamilyArrow M map T f).hom
  reindex : ∀ {T U : Over (Spec (.of k))} (h : T ⟶ U) (x : B.stack.Fibre U),
    (B.reindex h x).source ≫ (stabilization U x).contraction =
      (stabilization T ((pull B.stack h).obj x)).contraction ≫ mappedFamilyReindex M map h x

end MathlibExt.AlgebraicGeometry.RubberModuliStackModels
