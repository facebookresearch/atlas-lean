/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeModuliStackModels
public import MathlibExt.AlgebraicGeometry.RelativeRootEquivalenceGroups
public import MathlibExt.AlgebraicGeometry.StableMapNumericalClasses

/-!
# Full relative types, including the empty source

The existing positive-vertex APIs are preserved. `FullType` has the same
ordered incidence, genera and positive contact weights and permits zero
vertices. Every component still maps to one actual expanded target.
Automorphisms retain that target even for the empty source.

Root relabeling acts on the actual ordered incidence and contact functions.
The finite equivalence group preserves genera, degrees, legs and roots.
Its cardinal and the product of the contact orders are computed.

Source: Jun Li, arXiv:math/0110113v1, introduction pp2--4 and Section3.1,
pp31--32; arXiv:math/0009097v1, Definitions4.6--4.8.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LiGluingRelativeTypes

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open ExpandedTargetChainGeometry RelativeProjectiveLineModels StandardRelativeExpansionModels
open ExpandedRelativeFamilies RelativeExpandedMapFamilies
open StackCycleGeometry StackCycleRelations
open scoped BigOperators

/-- A relative map type that may have no vertices: `RelativeMapTypeModels.RelativeType` without its
nonemptiness field, so that the empty type indexes the unit term of the gluing formula. -/
structure FullType (n r : ℕ) where
  vertices : ℕ
  legs : Fin vertices → ℕ
  roots : Fin vertices → ℕ
  genus : Fin vertices → ℕ
  legLabels : Fin n ≃ (Σ v : Fin vertices, Fin (legs v))
  rootLabels : Fin r ≃ (Σ v : Fin vertices, Fin (roots v))
  order : Fin r → ℕ
  positive : ∀ i, 0 < order i
  relativelyConnected : vertices = 1 ∨ ∀ v : Fin vertices, ∃ i : Fin r, (rootLabels i).1 = v

def ofNative {n r : ℕ} (G : RelativeMapTypeModels.RelativeType n r) : FullType n r :=
  ⟨G.vertices, G.legs, G.roots, G.genus, G.legLabels, G.rootLabels,
    G.order, G.positive, G.relativelyConnected⟩

def toNative {n r : ℕ} (G : FullType n r) (h : 0 < G.vertices) :
    RelativeMapTypeModels.RelativeType n r :=
  ⟨G.vertices, h, G.legs, G.roots, G.genus, G.legLabels, G.rootLabels,
    G.order, G.positive, G.relativelyConnected⟩

@[simp] theorem ofNative_toNative {n r : ℕ} (G : FullType n r) (h : 0 < G.vertices) :
    ofNative (toNative G h) = G := by cases G; rfl

def emptyType : FullType 0 0 where
  vertices := 0
  legs := Fin.elim0
  roots := Fin.elim0
  genus := Fin.elim0
  legLabels := Equiv.equivOfIsEmpty _ _
  rootLabels := Equiv.equivOfIsEmpty _ _
  order := Fin.elim0
  positive := fun i => Fin.elim0 i
  relativelyConnected := Or.inr (fun v => Fin.elim0 v)

def relabelRoots {n r : ℕ} (G : FullType n r) (s : Equiv.Perm (Fin r)) : FullType n r where
  vertices := G.vertices
  legs := G.legs
  roots := G.roots
  genus := G.genus
  legLabels := G.legLabels
  rootLabels := s.trans G.rootLabels
  order := fun i => G.order (s i)
  positive := fun i => G.positive (s i)
  relativelyConnected := G.relativelyConnected.imp id (by
    intro h v
    obtain ⟨i, hi⟩ := h v
    exact ⟨s.symm i, by simpa using hi⟩)

def relabelVertices {n r : ℕ} (G : FullType n r)
    (v : Equiv.Perm (Fin G.vertices)) : FullType n r where
  vertices := G.vertices
  legs := fun i => G.legs (v i)
  roots := fun i => G.roots (v i)
  genus := fun i => G.genus (v i)
  legLabels := G.legLabels.trans (Equiv.sigmaCongrLeft v).symm
  rootLabels := G.rootLabels.trans (Equiv.sigmaCongrLeft v).symm
  order := G.order
  positive := G.positive
  relativelyConnected := G.relativelyConnected.imp id (by
    intro h i
    obtain ⟨j, hj⟩ := h (v i)
    refine ⟨j, ?_⟩
    change v.symm (G.rootLabels j).1 = i
    simpa only [Equiv.symm_apply_apply] using congrArg v.symm hj)

def relabelDegreeLabels {n r : ℕ} (G : FullType n r) {A : Type*}
    (beta : Fin G.vertices → A) (v : Equiv.Perm (Fin G.vertices)) :
    Fin (relabelVertices G v).vertices → A := fun i => beta (v i)

variable {k : Type} [Field k]
  (P : RelativePair (k := k)) (R : ProjectiveLine P.divisor.left (normalLineModule P))
  (S : StandardSystem P R) {n r : ℕ} (G : FullType n r) (T : Over (Spec (.of k)))

structure Family where
  target : ExpandedFamily P R S T
  maps : ∀ v : Fin G.vertices,
    RelativeMapOn P R S T target (G.legs v) (G.roots v) (G.genus v)
      (fun i => G.order (G.rootLabels.symm ⟨v, i⟩))

def evaluation (F : Family P R S G T) (i : Fin r) : T ⟶ P.divisor :=
  rootEvaluation P R S T (F.maps (G.rootLabels i).1) (G.rootLabels i).2

def allEvaluations (F : Family P R S G T) : T ⟶ ∏ᶜ (fun _ : Fin r => P.divisor) :=
  Pi.lift (evaluation P R S G T F)

def fromNative (G : RelativeMapTypeModels.RelativeType n r)
    (F : RelativeMapTypeModels.TypeFamily P R S G T) : Family P R S (ofNative G) T :=
  ⟨F.target, F.maps⟩

def asNative (h : 0 < G.vertices) (F : Family P R S G T) :
    RelativeMapTypeModels.TypeFamily P R S (toNative G h) T := ⟨F.target, F.maps⟩

def asDisconnected (h : 0 < G.vertices) (F : Family P R S G T) :
    DisconnectedRelativeFamily P R S T n r G.order :=
  ⟨G.vertices, h, G.legs, G.roots, G.genus, G.legLabels, G.rootLabels, F.target, F.maps⟩

def relabelFamily (s : Equiv.Perm (Fin r)) (F : Family P R S G T) :
    Family P R S (relabelRoots G s) T where
  target := F.target
  maps := fun v => by simpa [relabelRoots] using F.maps v

def relabelVertexFamily (v : Equiv.Perm (Fin G.vertices)) (F : Family P R S G T) :
    Family P R S (relabelVertices G v) T where
  target := F.target
  maps := fun i => by simpa [relabelVertices] using F.maps (v i)

structure FamilyIso (F H : Family P R S G T) where
  target : ExpandedIso P R S F.target H.target
  source : ∀ v : Fin G.vertices, (F.maps v).curve.X ≅ (H.maps v).curve.X
  over : ∀ v, (source v).hom ≫ (H.maps v).curve.π = (F.maps v).curve.π
  marking : ∀ (v : Fin G.vertices) (i : Fin (G.legs v + G.roots v)),
    (F.maps v).curve.marking i ≫ (source v).hom = (H.maps v).curve.marking i
  map : ∀ v, (source v).hom ≫ (H.maps v).map = (F.maps v).map ≫ target.iso.hom.left

@[ext] theorem FamilyIso.ext {F H : Family P R S G T} (f h : FamilyIso P R S G T F H)
    (target : f.target = h.target) (source : f.source = h.source) : f = h := by
  cases f; cases h; cases target; cases source; rfl

instance familyGroupoid : Groupoid (Family P R S G T) where
  Hom F H := FamilyIso P R S G T F H
  id F :=
    { target := ⟨Iso.refl _, by simp, by simp, by simp⟩
      source := fun _ => Iso.refl _
      over := by intro v; simp
      marking := by intro v i; simp
      map := by intro v; simp }
  comp f h :=
    { target := ⟨f.target.iso ≪≫ h.target.iso, by simp [Category.assoc, h.target.over, f.target.over],
        by simp [Category.assoc, h.target.contraction, f.target.contraction],
        by simp [← Category.assoc, f.target.boundary, h.target.boundary]⟩
      source := fun v => f.source v ≪≫ h.source v
      over := by intro v; simp [Category.assoc, h.over, f.over]
      marking := by intro v i; simp [← Category.assoc, f.marking, h.marking]
      map := by
        intro v
        simp only [Iso.trans_hom, Over.comp_left]
        rw [Category.assoc, h.map, ← Category.assoc, f.map, Category.assoc] }
  inv f :=
    { target := ⟨f.target.iso.symm, by rw [← f.target.over]; simp,
        by rw [← f.target.contraction]; simp, by rw [← f.target.boundary]; simp⟩
      source := fun v => (f.source v).symm
      over := by intro v; rw [← f.over]; simp
      marking := by intro v i; rw [← f.marking]; simp
      map := by
        intro v
        dsimp only [Iso.symm_hom]
        apply (cancel_epi (f.source v).hom).1
        rw [← Category.assoc, (f.source v).hom_inv_id, Category.id_comp,
          ← Category.assoc, f.map, Category.assoc, ← Over.comp_left,
          f.target.iso.hom_inv_id, Over.id_left, Category.comp_id] }
  id_comp f := by apply FamilyIso.ext <;> ext <;> simp
  comp_id f := by apply FamilyIso.ext <;> ext <;> simp
  assoc f h j := by apply FamilyIso.ext <;> ext <;> simp
  inv_comp f := by apply FamilyIso.ext <;> ext <;> simp
  comp_inv f := by apply FamilyIso.ext <;> ext <;> simp

/-- One actual target automorphism, including when there are no components. -/
structure GeometricAutomorphism (F : Family P R S G T)
    (Ω : Type) [Field Ω] (x : Spec (.of Ω) ⟶ T.left) where
  target : pullback F.target.projection.left x ≅ pullback F.target.projection.left x
  target_over : target.hom ≫ pullback.snd F.target.projection.left x =
    pullback.snd F.target.projection.left x
  contraction : target.hom ≫ pullback.fst F.target.projection.left x ≫ F.target.contraction.left =
    pullback.fst F.target.projection.left x ≫ F.target.contraction.left
  boundary : (F.target.boundary.left.ker.comap (pullback.fst F.target.projection.left x)).comap
    target.hom = F.target.boundary.left.ker.comap (pullback.fst F.target.projection.left x)
  source : ∀ v : Fin G.vertices, pullback (F.maps v).curve.π x ≅ pullback (F.maps v).curve.π x
  source_over : ∀ v, (source v).hom ≫ pullback.snd (F.maps v).curve.π x =
    pullback.snd (F.maps v).curve.π x
  marking : ∀ v i,
    MarkedCurveStabilization.fiberMark (F.maps v).curve.π ((F.maps v).curve.marking i)
      ((F.maps v).curve.section_eq i) x ≫ (source v).hom =
    MarkedCurveStabilization.fiberMark (F.maps v).curve.π ((F.maps v).curve.marking i)
      ((F.maps v).curve.section_eq i) x
  map : ∀ v, (source v).hom ≫ fibreMap P R S T (F.maps v) x =
    fibreMap P R S T (F.maps v) x ≫ target.hom

def IsStable (F : Family P R S G T) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T.left),
    Finite (GeometricAutomorphism P R S G T F Ω x)

variable [LocallyOfFiniteType P.target.hom] [IsNoetherian P.target.left]

/-- Each vertex map has its numerical class on every geometric fibre (Li, Def. 4.6): a locally
constant condition, so the stable families with these classes form a union of connected
components of the moduli of stable relative maps. -/
def HasVertexClasses
    (beta : Fin G.vertices → StableMapNumericalClasses.NumericalClass P.target.left)
    (F : Family P R S G T) : Prop :=
  ∀ v, StableMapNumericalClasses.HasNumericalClass (contractedFamily P R S T (F.maps v)).curve.π
    (contractedFamily P R S T (F.maps v)).map (beta v)

abbrev StableFamily
    (beta : Fin G.vertices → StableMapNumericalClasses.NumericalClass P.target.left) :=
  (show ObjectProperty (Family P R S G T) from
    fun F => IsStable P R S G T F ∧ HasVertexClasses P R S G T beta F).FullSubcategory

structure FamilyBaseChange {T U : Over (Spec (.of k))} (f : T ⟶ U)
    (F : Family P R S G T) (H : Family P R S G U) where
  target : F.target.scheme ⟶ H.target.scheme
  target_cartesian : IsPullback target F.target.projection H.target.projection f
  target_contraction : target ≫ H.target.contraction = F.target.contraction
  target_boundary : F.target.boundary ≫ target = prod.map (𝟙 P.divisor) f ≫ H.target.boundary
  source : ∀ v : Fin G.vertices, (F.maps v).curve.X ⟶ (H.maps v).curve.X
  source_cartesian : ∀ v, IsPullback (source v) (F.maps v).curve.π (H.maps v).curve.π f.left
  marking : ∀ v i, (F.maps v).curve.marking i ≫ source v = f.left ≫ (H.maps v).curve.marking i
  map : ∀ v, (F.maps v).map ≫ target.left = source v ≫ (H.maps v).map
  evaluation : ∀ i : Fin r,
    LiGluingRelativeTypes.evaluation P R S G T F i = f ≫ LiGluingRelativeTypes.evaluation P R S G U H i

structure ModuliModel
    (beta : Fin G.vertices → StableMapNumericalClasses.NumericalClass P.target.left) where
  stack : Stack (Spec (.of k))
  family : ∀ T : Over (Spec (.of k)), stack.Fibre T ⥤ StableFamily P R S G T beta
  equivalence : ∀ T, (family T).IsEquivalence
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
    ((family T).map ((stack.toPseudofunctor.mapId (.mk (op T))).hom.toNatTrans.app x)).hom.target.iso.hom =
      (reindex (𝟙 T) x).target
  source_unit : ∀ (T : Over (Spec (.of k))) (x : stack.Fibre T) (v : Fin G.vertices),
    (((family T).map ((stack.toPseudofunctor.mapId (.mk (op T))).hom.toNatTrans.app x)).hom.source v).hom =
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

section RootGroup

variable {n r : ℕ} (G : FullType n r) {A : Type*} (beta : Fin G.vertices → A)

/-- A permutation of the relative markings is induced by a vertex permutation preserving genera,
numerical classes, the ordinary markings and contact orders. This is
`RelativeRootEquivalenceGroups.eligible` for possibly empty types. -/
def eligible (s : Equiv.Perm (Fin r)) : Prop :=
  ∃ v : Equiv.Perm (Fin G.vertices),
    (∀ i, G.genus (v i) = G.genus i) ∧ (∀ i, beta (v i) = beta i) ∧
    (∀ i : Fin n, v (G.legLabels i).1 = (G.legLabels i).1) ∧
    (∀ i : Fin r, (G.rootLabels (s i)).1 = v (G.rootLabels i).1) ∧
    (∀ i : Fin r, G.order (s i) = G.order i)

/-- The group of eligible permutations of the relative markings. -/
def rootGroup : Subgroup (Equiv.Perm (Fin r)) where
  carrier := {s | eligible G beta s}
  one_mem' := ⟨1, by simp, by simp, by simp, by simp, by simp⟩
  mul_mem' := by
    rintro s t ⟨v, hg, hb, hl, hr, ho⟩ ⟨w, kg, kb, kl, kr, ko⟩
    refine ⟨v * w, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; exact (hg (w i)).trans (kg i)
    · intro i; exact (hb (w i)).trans (kb i)
    · intro i; change v (w (G.legLabels i).1) = _; rw [kl, hl]
    · intro i; change (G.rootLabels (s (t i))).1 = v (w (G.rootLabels i).1); rw [hr, kr]
    · intro i; exact (ho (t i)).trans (ko i)
  inv_mem' := by
    rintro s ⟨v, hg, hb, hl, hr, ho⟩
    refine ⟨v⁻¹, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; simpa using (hg (v⁻¹ i)).symm
    · intro i; simpa using (hb (v⁻¹ i)).symm
    · intro i; exact v.symm_apply_eq.mpr (hl i).symm
    · intro i
      apply v.injective
      simpa using (hr (s.symm i)).symm
    · intro i; simpa using (ho (s⁻¹ i)).symm

variable {n' : ℕ} (H : FullType n' r) {B : Type*} (gamma : Fin H.vertices → B)

/-- Permutations of the relative markings that are eligible for both sides of the gluing. -/
def equivalenceGroup : Subgroup (Equiv.Perm (Fin r)) := rootGroup G beta ⊓ rootGroup H gamma

instance equivalenceGroupFintype : Fintype (equivalenceGroup G beta H gamma) := Fintype.ofFinite _

def equivalenceOrder : ℕ := Fintype.card (equivalenceGroup G beta H gamma)
def contactMultiplicity : ℕ := ∏ i : Fin r, G.order i
/-- The gluing coefficient: the product of the contact orders divided by the order of the
equivalence group. -/
def coefficient : ℚ := (contactMultiplicity G : ℚ) / (equivalenceOrder G beta H gamma : ℚ)

theorem equivalenceOrder_pos : 0 < equivalenceOrder G beta H gamma := Fintype.card_pos
theorem contactMultiplicity_pos : 0 < contactMultiplicity G :=
  Finset.prod_pos (fun i _ => G.positive i)

@[simp] theorem contactMultiplicity_zero (G : FullType n 0) : contactMultiplicity G = 1 := by
  simp [contactMultiplicity]

@[simp] theorem equivalenceOrder_zero (G : FullType n 0) (beta : Fin G.vertices → A)
    (H : FullType n' 0) (gamma : Fin H.vertices → B) : equivalenceOrder G beta H gamma = 1 := by
  exact Fintype.card_eq_one_iff.mpr ⟨1, fun a => Subsingleton.elim a 1⟩

@[simp] theorem coefficient_zero (G : FullType n 0) (beta : Fin G.vertices → A)
    (H : FullType n' 0) (gamma : Fin H.vertices → B) : coefficient G beta H gamma = 1 := by
  simp [coefficient]

end RootGroup

end MathlibExt.AlgebraicGeometry.LiGluingRelativeTypes
