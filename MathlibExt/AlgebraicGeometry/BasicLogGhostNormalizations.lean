/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BasicLogGeometricGhosts

/-!
# Source-normalized basicization on every geometric stalk

The target is the ghost sheaf of the actual initial basic enhancement on
the same ordinary stable family. Its quotient comparison is fixed by the
actual generic target-log maps, every node smoothing element, the native
group quotient and saturation, and the characteristic map of the genuine
comparison to the original base log structure.

Specialization and base-change maps are computed from the native site
point/sheaf maps under these identifications. Base change retains the
actual G3 pullback square and strict I1 log arrows, rather than an unrelated
list of ghost monoids or a new basicness predicate.

Reference: Gross–Siebert arXiv:1102.4322v2, Construction1.16,
Definition1.20, Lemma1.23, Proposition1.24 and diagram1.16.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BasicLogGhostNormalizations

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open EtaleLogSchemes EtaleLogDiagrams GeometricLogGhosts LogCurveFamilies FormalLogSmoothness
open BasicLogMapFamilies BasicLogGeometricGhosts LogMapBasicMonoids LogStructures

variable [InverseImageTheory.{0}]
variable {X S : LogScheme.{0}} {q : EtaleLogSchemes.Hom X S} {n g : ℕ}
  {W : Scheme.{0}} {b : W ⟶ S.scheme} (M : StableLogMap q n g W b) (B : Basicization M)

def originalBase : LogScheme.{0} := ⟨W,M.curve.baseLog⟩
def minimalBase : LogScheme.{0} := ⟨W,B.enhancement.curve.baseLog⟩
def minimalCurve : LogScheme.{0} := ⟨M.family.curve.X,B.enhancement.curve.curveLog⟩

variable {K : Type} [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ W) (H : FibreType M t)

/-- The actual characteristic map of the base-log comparison, followed
by the native geometric site-point fibre functor. -/
def originalComparison : ghost (minimalBase M B) t ⟶ ghost (originalBase M) t :=
  (point t).sheafFiber.map
    (RingedSiteLogMorphisms.characteristicMap W.smallEtaleTopology B.enhancement.baseComparison)

def nodeBaseIso (L : LogStructure W.smallEtaleTopology (EtaleLogSchemes.structureRing W))
    (e : Fin H.strata.nodeCount) :
    ghost ⟨W,L⟩ ((H.strata.nodePoint e).curve ≫ M.family.curve.π) ≅ ghost ⟨W,L⟩ t :=
  eqToIso (congrArg (fun x : Spec (.of K) ⟶ W ↦ ghost ⟨W,L⟩ x) (H.strata.node_base e))

def minimalVertexProjection (v : Fin H.strata.vertexCount) :
    ghost (minimalBase M B) ((H.strata.vertex v).curve ≫ M.family.curve.π) ≅
      ghost (minimalCurve M B) (H.strata.vertex v).curve := by
  letI := B.enhancement.curve.ordinaryGhost (H.strata.vertex v).field (H.strata.vertex v).curve
    (H.strata.ordinary v).1 (H.strata.ordinary v).2
  exact asIso (B.enhancement.curve.integral.ghostMap
    (H.strata.vertex v).field (H.strata.vertex v).curve).map

/-- Ordinary geometric ghost operations. Their sections, field maps and
ordered node charts are fixed independently of the desired quotient iso. -/
structure FibreOperators where
  originalVertex : ∀ v : Fin H.strata.vertexCount, GhostMap
    (homOfAlong ⟨M.family.curve.X,M.curve.curveLog⟩ X M.family.map M.targetMap) (H.strata.vertex v).curve
  minimalVertex : ∀ v : Fin H.strata.vertexCount, GhostMap
    (homOfAlong (minimalCurve M B) X M.family.map B.enhancement.targetMap) (H.strata.vertex v).curve
  originalField : ∀ v : Fin H.strata.vertexCount,
    FieldGhostComparison (originalBase M) (H.strata.vertex v).scalar t
      ((H.strata.vertex v).curve ≫ M.family.curve.π) (H.strata.vertex v).base.symm
  minimalField : ∀ v : Fin H.strata.vertexCount,
    FieldGhostComparison (minimalBase M B) (H.strata.vertex v).scalar t
      ((H.strata.vertex v).curve ≫ M.family.curve.π) (H.strata.vertex v).base.symm
  rho : Fin H.strata.nodeCount → ghost (minimalBase M B) t
  rho_nonunit : ∀ e, ¬ IsUnit (rho e)
  nodeIso : ∀ e, ghost (minimalCurve M B) (H.strata.nodePoint e).curve ≅
    nodeMonoid (ghost (minimalBase M B) t) (rho e)
  node_projection : ∀ e,
    (B.enhancement.curve.integral.ghostMap K (H.strata.nodePoint e).curve).map ≫ (nodeIso e).hom =
      (nodeBaseIso M t H B.enhancement.curve.baseLog e).hom ≫ pushout.inl _ _
  branch₁ : ∀ e,
    ((H.generization₁ e).curve.sheafFiber.app
      (characteristic M.family.curve.X.smallEtaleTopology B.enhancement.curve.curveLog)) ≫
      (minimalVertexProjection M B t H (H.branch₁ e)).inv =
    (nodeIso e).hom ≫ nodeBranch1 _ (rho e) ≫ (minimalField (H.branch₁ e)).iso.hom
  branch₂ : ∀ e,
    ((H.generization₂ e).curve.sheafFiber.app
      (characteristic M.family.curve.X.smallEtaleTopology B.enhancement.curve.curveLog)) ≫
      (minimalVertexProjection M B t H (H.branch₂ e)).inv =
    (nodeIso e).hom ≫ nodeBranch2 _ (rho e) ≫ (minimalField (H.branch₂ e)).iso.hom

namespace FibreOperators

variable {M B t H} (O : FibreOperators M B t H)

def originalVertexImage (v : Fin H.strata.vertexCount) :
    ghost X ((H.strata.vertex v).curve ≫ M.family.map) ⟶ ghost (originalBase M) t :=
  (O.originalVertex v).map ≫ (vertexProjection M t H.strata v).inv ≫ (O.originalField v).iso.inv

def minimalVertexImage (v : Fin H.strata.vertexCount) :
    ghost X ((H.strata.vertex v).curve ≫ M.family.map) ⟶ ghost (minimalBase M B) t :=
  (O.minimalVertex v).map ≫ (minimalVertexProjection M B t H v).inv ≫ (O.minimalField v).iso.inv

def originalSmoothing (_O : FibreOperators M B t H) (e : Fin H.strata.nodeCount) : ghost (originalBase M) t :=
  (nodeBaseIso M t H M.curve.baseLog e).hom.hom (H.coordinates e).rho

def vertexGroup (v : Fin H.strata.vertexCount) :
    Additive (Algebra.GrothendieckGroup ((H.contactDiagram).vertex v)) →+
      Additive (Algebra.GrothendieckGroup (ghost (originalBase M) t)) where
  toFun x := Additive.ofMul (LogStructures.groupMap (O.originalVertexImage v) x.toMul)
  map_zero' := by simpa using congrArg Additive.ofMul (map_one (LogStructures.groupMap (O.originalVertexImage v)))
  map_add' x y := by
    simpa using congrArg Additive.ofMul (map_mul (LogStructures.groupMap (O.originalVertexImage v)) x.toMul y.toMul)

/-- The source product map on actual generic stalks and actual smoothing
generators, before quotienting or saturation. -/
def totalOriginal : TotalGroup H.contactDiagram →+
    Additive (Algebra.GrothendieckGroup (ghost (originalBase M) t)) where
  toFun x := (∑ v, O.vertexGroup v (x.1 v)) +
    ∑ e, x.2 e • Additive.ofMul (Algebra.GrothendieckGroup.of (O.originalSmoothing e))
  map_zero' := by simp
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, Finset.sum_add_distrib, add_zsmul]
    abel

end FibreOperators

def vertexClass (v : Fin H.strata.vertexCount) (m : H.contactDiagram.vertex v) : basicMonoid H.contactDiagram :=
  positiveClass H.contactDiagram
    (fun w ↦ if h : w = v then h.symm ▸ m else 1, fun _ ↦ 0)

/-- All conclusions refer to the actual initial enhancement's ghost stalk.
The quotient, saturation and comparison maps are normalized on the whole
group projection and every actual generic/node generator. -/
structure BasicGhostModel where
  operations : FibreOperators M B t H
  quotient : BasicGroup H.contactDiagram →+
    Additive (Algebra.GrothendieckGroup (ghost (originalBase M) t))
  quotient_normalized : ∀ x : TotalGroup H.contactDiagram,
    quotient (groupProjection H.contactDiagram x) = operations.totalOriginal x
  originalMap : basicMonoid H.contactDiagram →* ghost (originalBase M) t
  originalMap_group : ∀ x : basicMonoid H.contactDiagram,
    Additive.ofMul (Algebra.GrothendieckGroup.of (originalMap x)) = quotient x.val.toAdd
  iso : basicMonoid H.contactDiagram ≃* ghost (minimalBase M B) t
  vertex_normalized : ∀ (v : Fin H.strata.vertexCount) (m : H.contactDiagram.vertex v),
    iso (vertexClass M t H v m) = (operations.minimalVertexImage v).hom m
  node_normalized : ∀ e, iso (smoothing H.contactDiagram e) = operations.rho e
  comparison_normalized : (originalComparison M B t).hom.comp iso.toMonoidHom = originalMap

namespace BasicGhostModel

variable {M B t H}

variable {L : Type} [Field L] [IsAlgClosed L] {u : Spec (.of L) ⟶ W} {J : FibreType M u}
  (G : BasicGhostModel M B t H) (G' : BasicGhostModel M B u J)
  (a : point u ⟶ point t)

/-- Every specialization map is the actual site-point map on the same
basic characteristic sheaf, transported through the normalized quotients. -/
def specialization : basicMonoid H.contactDiagram →* basicMonoid J.contactDiagram :=
  G'.iso.symm.toMonoidHom.comp
    ((a.sheafFiber.app (characteristic W.smallEtaleTopology B.enhancement.curve.baseLog)).hom.comp G.iso.toMonoidHom)

theorem specialization_normalized (x : basicMonoid H.contactDiagram) :
    G'.iso (G.specialization G' a x) =
      (a.sheafFiber.app (characteristic W.smallEtaleTopology B.enhancement.curve.baseLog)).hom (G.iso x) := by
  simp [specialization, MonoidHom.comp_apply]
  rfl

end BasicGhostModel

section BaseChange

variable {W' : Scheme.{0}} (h : W' ⟶ W) (M' : StableLogMap q n g W' (h ≫ b))
  (C : GeneralStableMapFamilies.BaseChangeData M.family h M'.family)

/-- Actual Cartesian log-family base change: G3 fixes the underlying
curve/markings/map and I1 fixes both strict inverse-log comparisons. -/
structure LogBaseChange where
  base : MorphismAlong ⟨W',M'.curve.baseLog⟩ (originalBase M) h
  curve : MorphismAlong ⟨M'.family.curve.X,M'.curve.curveLog⟩
    ⟨M.family.curve.X,M.curve.curveLog⟩ C.sourceMap
  base_strict : IsStrict (homOfAlong ⟨W',M'.curve.baseLog⟩ (originalBase M) h base)
  curve_strict : IsStrict (homOfAlong ⟨M'.family.curve.X,M'.curve.curveLog⟩
    ⟨M.family.curve.X,M.curve.curveLog⟩ C.sourceMap curve)
  projection : Square
    (homOfAlong ⟨M'.family.curve.X,M'.curve.curveLog⟩ ⟨M.family.curve.X,M.curve.curveLog⟩ C.sourceMap curve)
    (homOfAlong ⟨M.family.curve.X,M.curve.curveLog⟩ (originalBase M) M.family.curve.π M.curve.projection)
    (homOfAlong ⟨M'.family.curve.X,M'.curve.curveLog⟩ ⟨W',M'.curve.baseLog⟩ M'.family.curve.π M'.curve.projection)
    (homOfAlong ⟨W',M'.curve.baseLog⟩ (originalBase M) h base)
  target : ∀ (U : X.scheme.Etale) (m : (monoid X.scheme.smallEtaleTopology X.log).obj.obj (op U)),
    (monoid M'.family.curve.X.smallEtaleTopology M'.curve.curveLog).obj.map
      ((EtaleBaseChangeCoherence.composition C.sourceMap M.family.map).inv.app U).op
      (curve.left.hom.app (op ((SmallEtaleGeometry.etaleBaseChange M.family.map).obj U))
        (M.targetMap.left.hom.app (op U) m)) =
    (monoid M'.family.curve.X.smallEtaleTopology M'.curve.curveLog).obj.map
      ((eqToIso (congrArg SmallEtaleGeometry.etaleBaseChange C.map)).hom.app U).op
      (M'.targetMap.left.hom.app (op U) m)
  base_square : ∀ (U : S.scheme.Etale) (m : (monoid S.scheme.smallEtaleTopology S.log).obj.obj (op U)),
    (monoid W'.smallEtaleTopology M'.curve.baseLog).obj.map
      ((EtaleBaseChangeCoherence.composition h b).inv.app U).op
      (base.left.hom.app (op ((SmallEtaleGeometry.etaleBaseChange b).obj U))
        (M.baseMap.left.hom.app (op U) m)) = M'.baseMap.left.hom.app (op U) m

variable (B' : Basicization M') (A : LogBaseChange M h M' C)

/-- Basicization retains this very underlying family base change and
commutes with both actual comparisons to the original log family. -/
structure BasicizedBaseChange where
  change : LogBaseChange B.enhancement.toStableLogMap h B'.enhancement.toStableLogMap C
  base_comparison : B.enhancement.baseComparison.hom.left ≫ A.base.left =
    change.base.left ≫ (pushMonoids h).map B'.enhancement.baseComparison.hom.left
  curve_comparison : B.enhancement.curveComparison.hom.left ≫ A.curve.left =
    change.curve.left ≫ (pushMonoids C.sourceMap).map B'.enhancement.curveComparison.hom.left

namespace BasicizedBaseChange

variable {M B h M' C B' A} (N : BasicizedBaseChange M B h M' C B' A)

def baseHom : EtaleLogSchemes.Hom (minimalBase M' B') (minimalBase M B) :=
  homOfAlong (minimalBase M' B') (minimalBase M B) h N.change.base

variable {x : Spec (.of K) ⟶ W'} {H₀ : FibreType M (x ≫ h)} {H₁ : FibreType M' x}
  (G₀ : BasicGhostModel M B (x ≫ h) H₀) (G₁ : BasicGhostModel M' B' x H₁)
  (f : GhostMap N.baseHom x)

/-- Every actual family base change acts on the source quotient through
its strict native log-base map on the actual geometric stalk. -/
def monoidMap : basicMonoid H₀.contactDiagram →* basicMonoid H₁.contactDiagram :=
  G₁.iso.symm.toMonoidHom.comp (f.map.hom.comp G₀.iso.toMonoidHom)

theorem monoidMap_normalized (z : basicMonoid H₀.contactDiagram) :
    G₁.iso (N.monoidMap G₀ G₁ f z) = f.map.hom (G₀.iso z) := by
  simp [monoidMap, MonoidHom.comp_apply]
  rfl

end BasicizedBaseChange

end BaseChange

end MathlibExt.AlgebraicGeometry.BasicLogGhostNormalizations
