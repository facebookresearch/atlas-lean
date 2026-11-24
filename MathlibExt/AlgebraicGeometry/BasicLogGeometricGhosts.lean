/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BasicLogMapFamilies
public import MathlibExt.AlgebraicGeometry.LogMapBasicMonoids
public import Mathlib.CategoryTheory.Sites.Point.Category

/-!
# Basic log ghosts on actual geometric curve fibres

The vertices enumerate the actual irreducible components of the geometric
fibre; the nodes enumerate its actual nodal field-valued points. Both
branches are native morphisms of small-étale site points, compatible with
the original target map on every étale lift. Target characteristic monoids
are actual geometric stalks, and branch generizations are their native
sheaf-fibre maps.

The node contact is computed by the pushout map (q,a,b) ↦ b−a from
Q ⊕_N N². Its branch order is fixed by both actual curve-generization
diagrams. Thus the existing quotient/torsion quotient/root-closure basic
monoid uses the source's actual generic/node/contact data.

Reference: Gross–Siebert arXiv:1102.4322v2, Discussion1.8,
equations1.7/1.8, Construction1.16, equation1.14 and Proposition1.24.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BasicLogGeometricGhosts

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open EtaleLogSchemes EtaleLogDiagrams GeometricLogGhosts LogCurveFamilies
open BasicLogMapFamilies LogMapBasicMonoids LogStructures
open FormalLogSmoothness

variable [InverseImageTheory.{0}]

/-- The source's Zariski-defined fs log scope is given by actual open
chart schemes, their actual chart maps and finite saturated monoids. -/
def HasZariskiFineSaturatedCharts (Y : LogScheme.{0}) : Prop :=
  ∀ x : Y.scheme, ∃ U : Y.scheme.Etale,
    IsOpenImmersion U.hom ∧ x ∈ Set.range U.hom ∧
      ∃ P : CommMonCat.{1}, IsFineSaturatedMonoid P ∧
        Nonempty (LogStructures.Chart Y.scheme.smallEtaleTopology Y.log U P)

def fieldOrigin (K : Type) [Field K] : Spec (.of K) :=
  ⟨⊥, inferInstance⟩

/-- Extension of an actual geometric étale lift along the original field map. -/
def fieldLift {Y : Scheme.{0}} {K L : Type} [Field K] [IsSepClosed K] [Field L] [IsSepClosed L]
    (f : K →+* L) (x : Spec (.of K) ⟶ Y) (y : Spec (.of L) ⟶ Y)
    (h : Spec.map (CommRingCat.ofHom f) ≫ x = y) (U : Y.Etale)
    (a : (point x).fiber.obj U) : (point y).fiber.obj U :=
  Over.homMk (Spec.map (CommRingCat.ofHom f) ≫ a.left) (by rw [Category.assoc, Over.w a]; exact h)

/-- Every field-extension stalk isomorphism is fixed on every actual log
section and every original étale lift. -/
structure FieldGhostComparison (Y : LogScheme.{0}) {K L : Type}
    [Field K] [IsSepClosed K] [Field L] [IsSepClosed L]
    (f : K →+* L) (x : Spec (.of K) ⟶ Y.scheme) (y : Spec (.of L) ⟶ Y.scheme)
    (h : Spec.map (CommRingCat.ofHom f) ≫ x = y) where
  iso : ghost Y x ≅ ghost Y y
  normalized : ∀ (U : Y.scheme.Etale) (a : (point x).fiber.obj U)
    (m : (monoid Y.scheme.smallEtaleTopology Y.log).obj.obj (op U)),
    iso.hom.hom (((point x).toPresheafFiber U a (characteristic Y.scheme.smallEtaleTopology Y.log).obj).hom
      ((characteristicMap Y.scheme.smallEtaleTopology Y.log).hom.app (op U) m)) =
    ((point y).toPresheafFiber U (fieldLift f x y h U a)
      (characteristic Y.scheme.smallEtaleTopology Y.log).obj).hom
        ((characteristicMap Y.scheme.smallEtaleTopology Y.log).hom.app (op U) m)

variable {X S : LogScheme.{0}} {q : EtaleLogSchemes.Hom X S} {n g : ℕ}
  {W : Scheme.{0}} {b : W ⟶ S.scheme} (M : StableLogMap q n g W b)
  {K : Type} [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ W)

abbrev fibre := (MarkedCurveStabilization.fiberCurve M.family.curve.π t).left

/-- A geometric point of the literal fibre, with the original coefficient
field map and its actual structural-square equation. -/
structure FibrePoint where
  field : Type
  [fieldInst : Field field]
  [closed : IsAlgClosed field]
  scalar : K →+* field
  map : Spec (.of field) ⟶ fibre M t
  square : map ≫ pullback.snd M.family.curve.π t = Spec.map (CommRingCat.ofHom scalar)

attribute [instance] FibrePoint.fieldInst FibrePoint.closed

namespace FibrePoint

variable {M t}

def curve (x : FibrePoint M t) : Spec (.of x.field) ⟶ M.family.curve.X :=
  x.map ≫ pullback.fst M.family.curve.π t

def underlying (x : FibrePoint M t) : fibre M t := x.map (fieldOrigin x.field)

theorem base (x : FibrePoint M t) :
    x.curve ≫ M.family.curve.π = Spec.map (CommRingCat.ofHom x.scalar) ≫ t := by
  rw [curve, Category.assoc, pullback.condition, ← Category.assoc, x.square]

end FibrePoint

/-- Source strata enumerate all actual components and all actual nodes.
The chosen generic geometric points are representatives of those native
components; extra vertices or duplicate nodes cannot be inserted. -/
structure FibreStrata where
  vertexCount : ℕ
  nodeCount : ℕ
  vertex : Fin vertexCount → FibrePoint M t
  component : Fin vertexCount → {Z : Set (fibre M t) | Z ∈ irreducibleComponents (fibre M t)}
  components_bijective : Function.Bijective component
  generic : ∀ v, IsGenericPoint (vertex v).underlying (component v).val
  ordinary : ∀ v, ¬ IsMarking M.family.curve (vertex v).curve ∧ ¬ IsNode M.family.curve (vertex v).curve
  node : Fin nodeCount → (Spec (.of K) ⟶ fibre M t)
  node_over : ∀ e, node e ≫ pullback.snd M.family.curve.π t = 𝟙 _
  nodes_injective : Function.Injective node
  nodes_complete : ∀ (x : Spec (.of K) ⟶ fibre M t), x ≫ pullback.snd M.family.curve.π t = 𝟙 _ →
    (IsNode M.family.curve (x ≫ pullback.fst M.family.curve.π t) ↔ ∃ e, node e = x)

namespace FibreStrata

variable {M t} (F : FibreStrata M t)

def nodePoint (e : Fin F.nodeCount) : FibrePoint M t where
  field := K
  scalar := RingHom.id K
  map := F.node e
  square := by rw [F.node_over]; exact (Spec.map_id _).symm

theorem node_isNode (e : Fin F.nodeCount) : IsNode M.family.curve (F.nodePoint e).curve := by
  exact (F.nodes_complete (F.node e) (F.node_over e)).mpr ⟨e, rfl⟩

theorem node_base (e : Fin F.nodeCount) : (F.nodePoint e).curve ≫ M.family.curve.π = t := by
  rw [(F.nodePoint e).base]
  simp [nodePoint]

end FibreStrata

variable (F : FibreStrata M t)

/-- An actual branch generization, including compatibility with the target
on every geometric étale lift. These are native site-point morphisms. -/
structure Branch (v : Fin F.vertexCount) (e : Fin F.nodeCount) where
  curve : point (F.vertex v).curve ⟶ point (F.nodePoint e).curve
  target : point ((F.vertex v).curve ≫ M.family.map) ⟶ point ((F.nodePoint e).curve ≫ M.family.map)
  target_normalization : ∀ (U : X.scheme.Etale)
    (a : (point ((F.nodePoint e).curve ≫ M.family.map)).fiber.obj U),
    curve.hom.app ((SmallEtaleGeometry.etaleBaseChange M.family.map).obj U)
      (geometricLift M.family.map (F.nodePoint e).curve U a) =
    geometricLift M.family.map (F.vertex v).curve U (target.hom.app U a)

namespace Branch

variable {M t F} {v : Fin F.vertexCount} {e : Fin F.nodeCount} (a : Branch M t F v e)

def targetGhost : ghost X ((F.nodePoint e).curve ≫ M.family.map) ⟶
    ghost X ((F.vertex v).curve ≫ M.family.map) :=
  a.target.sheafFiber.app (characteristic X.scheme.smallEtaleTopology X.log)

def curveGhost : ghost ⟨M.family.curve.X, M.curve.curveLog⟩ (F.nodePoint e).curve ⟶
    ghost ⟨M.family.curve.X, M.curve.curveLog⟩ (F.vertex v).curve :=
  a.curve.sheafFiber.app (characteristic M.family.curve.X.smallEtaleTopology M.curve.curveLog)

end Branch

def nodeBranch1 (Q : CommMonCat.{1}) (rho : Q) : nodeMonoid Q rho ⟶ Q :=
  pushout.desc (𝟙 Q) ((_root_.CategoryTheory.Limits.prod.fst :
    _root_.CategoryTheory.Limits.prod NatMonoid NatMonoid ⟶ NatMonoid) ≫ smoothingMap Q rho) (by
    simp [diagonalNat, Category.assoc])

def nodeBranch2 (Q : CommMonCat.{1}) (rho : Q) : nodeMonoid Q rho ⟶ Q :=
  pushout.desc (𝟙 Q) ((_root_.CategoryTheory.Limits.prod.snd :
    _root_.CategoryTheory.Limits.prod NatMonoid NatMonoid ⟶ NatMonoid) ≫ smoothingMap Q rho) (by
    simp [diagonalNat, Category.assoc])

abbrev IntegerMonoid : CommMonCat.{1} := .of (ULift.{1} (Multiplicative ℤ))

def natPositive : NatMonoid ⟶ IntegerMonoid := CommMonCat.ofHom
  { toFun := fun x ↦ ULift.up (Multiplicative.ofAdd ((Multiplicative.toAdd x.down : ℕ) : ℤ))
    map_one' := rfl
    map_mul' x y := by
      apply ULift.ext
      apply Multiplicative.toAdd.injective
      change ((x.down.toAdd + y.down.toAdd : ℕ) : ℤ) = (x.down.toAdd : ℤ) + (y.down.toAdd : ℤ)
      simp }

def natNegative : NatMonoid ⟶ IntegerMonoid := CommMonCat.ofHom
  { toFun := fun x ↦ ULift.up (Multiplicative.ofAdd (-((Multiplicative.toAdd x.down : ℕ) : ℤ)))
    map_one' := by apply ULift.ext; simp
    map_mul' x y := by
      apply ULift.ext
      apply Multiplicative.toAdd.injective
      change -((x.down.toAdd + y.down.toAdd : ℕ) : ℤ) = -(x.down.toAdd : ℤ) + -(y.down.toAdd : ℤ)
      simp [add_comm] }

def branchDifference : _root_.CategoryTheory.Limits.prod NatMonoid NatMonoid ⟶ IntegerMonoid := CommMonCat.ofHom
  ((natNegative.hom.comp (_root_.CategoryTheory.Limits.prod.fst :
    _root_.CategoryTheory.Limits.prod NatMonoid NatMonoid ⟶ NatMonoid).hom) *
    (natPositive.hom.comp (_root_.CategoryTheory.Limits.prod.snd :
      _root_.CategoryTheory.Limits.prod NatMonoid NatMonoid ⟶ NatMonoid).hom))

/-- The contact map is the native pushout of zero on Q and b−a on N². -/
def nodeDifference (Q : CommMonCat.{1}) (rho : Q) : nodeMonoid Q rho ⟶ IntegerMonoid :=
  pushout.desc (CommMonCat.ofHom (1 : Q →* IntegerMonoid)) branchDifference (by
    have h₁ : diagonalNat ≫ (_root_.CategoryTheory.Limits.prod.fst :
      _root_.CategoryTheory.Limits.prod NatMonoid NatMonoid ⟶ NatMonoid) = 𝟙 NatMonoid := by simp [diagonalNat]
    have h₂ : diagonalNat ≫ (_root_.CategoryTheory.Limits.prod.snd :
      _root_.CategoryTheory.Limits.prod NatMonoid NatMonoid ⟶ NatMonoid) = 𝟙 NatMonoid := by simp [diagonalNat]
    apply CommMonCat.hom_ext
    apply MonoidHom.ext
    intro x
    have a₁ : (_root_.CategoryTheory.Limits.prod.fst :
      _root_.CategoryTheory.Limits.prod NatMonoid NatMonoid ⟶ NatMonoid).hom (diagonalNat.hom x) = x := by
      change (diagonalNat ≫ _root_.CategoryTheory.Limits.prod.fst).hom x = x
      rw [h₁]; rfl
    have a₂ : (_root_.CategoryTheory.Limits.prod.snd :
      _root_.CategoryTheory.Limits.prod NatMonoid NatMonoid ⟶ NatMonoid).hom (diagonalNat.hom x) = x := by
      change (diagonalNat ≫ _root_.CategoryTheory.Limits.prod.snd).hom x = x
      rw [h₂]; rfl
    change (1 : IntegerMonoid) = natNegative.hom
      ((_root_.CategoryTheory.Limits.prod.fst :
        _root_.CategoryTheory.Limits.prod NatMonoid NatMonoid ⟶ NatMonoid).hom (diagonalNat.hom x)) *
      natPositive.hom ((_root_.CategoryTheory.Limits.prod.snd :
        _root_.CategoryTheory.Limits.prod NatMonoid NatMonoid ⟶ NatMonoid).hom (diagonalNat.hom x))
    rw [a₁, a₂]
    apply ULift.ext
    apply Multiplicative.toAdd.injective
    change (0 : ℤ) = - (x.down.toAdd : ℤ) + (x.down.toAdd : ℤ)
    simp)

def integerDown : IntegerMonoid →* Multiplicative ℤ where
  toFun x := x.down
  map_one' := rfl
  map_mul' _ _ := rfl

def groupContact {P : CommMonCat.{1}} (f : P ⟶ IntegerMonoid) :
    Additive (Algebra.GrothendieckGroup P) →+ ℤ where
  toFun x := Multiplicative.toAdd
    ((Algebra.GrothendieckGroup.lift (integerDown.comp f.hom)) x.toMul)
  map_zero' := by
    simpa using congrArg Multiplicative.toAdd
      (map_one (Algebra.GrothendieckGroup.lift (integerDown.comp f.hom)))
  map_add' x y := by
    simpa using congrArg Multiplicative.toAdd
      (map_mul (Algebra.GrothendieckGroup.lift (integerDown.comp f.hom)) x.toMul y.toMul)

def vertexProjection (v : Fin F.vertexCount) :
    ghost ⟨W,M.curve.baseLog⟩ ((F.vertex v).curve ≫ M.family.curve.π) ≅
      ghost ⟨M.family.curve.X,M.curve.curveLog⟩ (F.vertex v).curve := by
  letI := M.curve.ordinaryGhost (F.vertex v).field (F.vertex v).curve (F.ordinary v).1 (F.ordinary v).2
  exact asIso (M.curve.integral.ghostMap (F.vertex v).field (F.vertex v).curve).map

/-- Every coordinate is from the original curve's actual node-ghost
pushout and its target-log map. Both ordered branches fix the chart. -/
structure NodeCoordinates (e : Fin F.nodeCount) (v₁ v₂ : Fin F.vertexCount)
    (a₁ : Branch M t F v₁ e) (a₂ : Branch M t F v₂ e) where
  rho : ghost ⟨W, M.curve.baseLog⟩ ((F.nodePoint e).curve ≫ M.family.curve.π)
  nonunit : ¬ IsUnit rho
  iso : ghost ⟨M.family.curve.X, M.curve.curveLog⟩ (F.nodePoint e).curve ≅
    nodeMonoid (ghost ⟨W, M.curve.baseLog⟩ ((F.nodePoint e).curve ≫ M.family.curve.π)) rho
  projection : (M.curve.integral.ghostMap K (F.nodePoint e).curve).map ≫ iso.hom = pushout.inl _ _
  target : GhostMap
    (homOfAlong ⟨M.family.curve.X,M.curve.curveLog⟩ X M.family.map M.targetMap) (F.nodePoint e).curve
  base₁ : FieldGhostComparison ⟨W,M.curve.baseLog⟩ (F.vertex v₁).scalar
    ((F.nodePoint e).curve ≫ M.family.curve.π) ((F.vertex v₁).curve ≫ M.family.curve.π)
      (by rw [F.node_base]; exact (F.vertex v₁).base.symm)
  base₂ : FieldGhostComparison ⟨W,M.curve.baseLog⟩ (F.vertex v₂).scalar
    ((F.nodePoint e).curve ≫ M.family.curve.π) ((F.vertex v₂).curve ≫ M.family.curve.π)
      (by rw [F.node_base]; exact (F.vertex v₂).base.symm)
  branch₁ : a₁.curveGhost ≫ (vertexProjection M t F v₁).inv =
      iso.hom ≫ nodeBranch1 _ rho ≫ base₁.iso.hom
  branch₂ : a₂.curveGhost ≫ (vertexProjection M t F v₂).inv =
      iso.hom ≫ nodeBranch2 _ rho ≫ base₂.iso.hom

structure FibreType where
  strata : FibreStrata M t
  branch₁ : Fin strata.nodeCount → Fin strata.vertexCount
  branch₂ : Fin strata.nodeCount → Fin strata.vertexCount
  generization₁ : ∀ e, Branch M t strata (branch₁ e) e
  generization₂ : ∀ e, Branch M t strata (branch₂ e) e
  coordinates : ∀ e, NodeCoordinates M t strata e (branch₁ e) (branch₂ e) (generization₁ e) (generization₂ e)

namespace FibreType

variable {M t} (H : FibreType M t)

/-- The actual source diagram in Construction1.16, with no free monoids
or independently assigned contact homomorphism. -/
def contactDiagram : ContactDiagram.{1,0} (Fin H.strata.vertexCount) (Fin H.strata.nodeCount) where
  vertex v := ghost X ((H.strata.vertex v).curve ≫ M.family.map)
  node e := ghost X ((H.strata.nodePoint e).curve ≫ M.family.map)
  branch1 := H.branch₁
  branch2 := H.branch₂
  generization1 e := (H.generization₁ e).targetGhost.hom
  generization2 e := (H.generization₂ e).targetGhost.hom
  contact e := groupContact
    ((H.coordinates e).target.map ≫ (H.coordinates e).iso.hom ≫ nodeDifference _ (H.coordinates e).rho)

end FibreType

end MathlibExt.AlgebraicGeometry.BasicLogGeometricGhosts
