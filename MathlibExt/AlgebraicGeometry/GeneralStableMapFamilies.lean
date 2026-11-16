/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The general prestable-map/evaluation/category/base-change signatures adapt
TauCetiProject/TauCeti at 62bbc0596dc3539d488232e4e924a338548ea0a9,
TauCeti/AlgebraicGeometry/Curves/StableMaps/{Basic,Category,Contracted}.lean.
Copyright (c) 2026 The Tau Ceti contributors. Apache 2.0.
Modification notice: use the existing native MarkedFamily for arbitrary n,g,
retain a fixed target over an arbitrary base, expose geometric map stability
and native cycle-class constraints. Complete source base-change primitives
are dependencies/ports, not new Wanted claims.
-/

module

public import MathlibExt.AlgebraicGeometry.MarkedCurveStabilization
public import MathlibExt.AlgebraicGeometry.RelativeCurveClasses
public import MathlibExt.AlgebraicGeometry.StableLineMaps

/-!
# General stable-map family contracts

The target/base, parameter, marking count and genus are arbitrary. The
source is an actual marked nodal family; the map and every evaluation are
actual scheme morphisms. Geometric stability tests every algebraically
closed field fibre and every map-and-mark-preserving automorphism.

The native groupoid contains actual source isomorphisms with their map,
base and marking equations. Cartesian base-change data specify actual
pullback squares and normalized marking maps; the map part is constructed
from that data. The general source-family construction itself is already
covered public TauCeti mathematics. General stable-map stack/algebraicity,
POT and gluing/invariant providers remain separate work.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.MarkedCurveStabilization

structure Family {V S : Scheme.{0}} (q : V ⟶ S) (n g : ℕ)
    (T : Scheme.{0}) (b : T ⟶ S) where
  curve : MarkedFamily T n g
  map : curve.X ⟶ V
  over : map ≫ q = curve.π ≫ b

variable {V S T : Scheme.{0}} {q : V ⟶ S} {n g : ℕ} {b : T ⟶ S}
    (F : Family q n g T b)

def evaluation (i : Fin n) : T ⟶ V := F.curve.marking i ≫ F.map

theorem evaluation_over (i : Fin n) : evaluation F i ≫ q = b := by
  rw [evaluation, Category.assoc, F.over, ← Category.assoc, F.curve.section_eq]
  simp

def mapToRelativeTarget : F.curve.X ⟶ pullback q b :=
  pullback.lift F.map F.curve.π F.over

def geometricAutomorphisms (Ω : Type) [Field Ω] (p : Spec (.of Ω) ⟶ T) :=
  {e : fiberCurve F.curve.π p ≅ fiberCurve F.curve.π p //
    e.hom.left ≫ pullback.fst F.curve.π p ≫ F.map =
      pullback.fst F.curve.π p ≫ F.map ∧
    ∀ i : Fin n, fiberMark F.curve.π (F.curve.marking i) (F.curve.section_eq i) p ≫
      e.hom.left = fiberMark F.curve.π (F.curve.marking i) (F.curve.section_eq i) p}

def IsGeometricallyStable : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ T),
    Finite (geometricAutomorphisms F Ω p)

structure Hom (G : Family q n g T b) where
  iso : F.curve.X ≅ G.curve.X
  over : iso.hom ≫ G.curve.π = F.curve.π
  markings : ∀ i, F.curve.marking i ≫ iso.hom = G.curve.marking i
  map : iso.hom ≫ G.map = F.map

@[ext] theorem hom_ext {G : Family q n g T b} {a c : Hom F G}
    (h : a.iso = c.iso) : a = c := by cases a; cases c; cases h; rfl

instance familyGroupoid : Groupoid (Family q n g T b) where
  Hom F G := Hom F G
  id F := ⟨Iso.refl _, by simp, by simp, by simp⟩
  comp a c := ⟨a.iso ≪≫ c.iso, by simp [Category.assoc, c.over, a.over],
    by intro i; simp [← Category.assoc, a.markings, c.markings],
    by simp [Category.assoc, c.map, a.map]⟩
  inv a := ⟨a.iso.symm, by rw [← a.over]; simp,
    by intro i; rw [← a.markings i]; simp, by rw [← a.map]; simp⟩
  id_comp a := by apply hom_ext; ext; simp
  comp_id a := by apply hom_ext; ext; simp
  assoc a c d := by apply hom_ext; ext; simp
  inv_comp a := by apply hom_ext; ext; simp


theorem evaluation_eq_of_hom {G : Family q n g T b} (e : F ⟶ G) (i : Fin n) :
    evaluation F i = evaluation G i := by
  rw [evaluation, ← e.map, ← Category.assoc, e.markings, evaluation]

structure BaseChangeData {T' : Scheme.{0}} (h : T' ⟶ T)
    (F' : Family q n g T' (h ≫ b)) where
  sourceMap : F'.curve.X ⟶ F.curve.X
  square : IsPullback sourceMap F'.curve.π F.curve.π h
  markings : ∀ i, F'.curve.marking i ≫ sourceMap = h ≫ F.curve.marking i
  map : sourceMap ≫ F.map = F'.map

/-- The actual map component of a Cartesian source-family base change. -/
def baseChangeMap {T' : Scheme.{0}} (h : T' ⟶ T) (C : MarkedFamily T' n g)
    (a : C.X ⟶ F.curve.X) (ha : IsPullback a C.π F.curve.π h) :
    Family q n g T' (h ≫ b) where
  curve := C
  map := a ≫ F.map
  over := by rw [Category.assoc, F.over, ← Category.assoc, ha.w]; simp [Category.assoc]


section CurveClasses

variable {k : Type} [Field k]
    (X T : MathlibExt.AlgebraicGeometry.RelativeCurveClasses.SchemeOver k)
    {n g : ℕ} (F : Family X.hom n g T.left T.hom)

/-- The actual map of a geometric source fibre into the scalar-extended target. -/
def geometricMap (Ω : Type) [Field Ω] [Algebra k Ω]
    (p : Spec (.of Ω) ⟶ T.left)
    (hp : p ≫ T.hom = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    (fiberCurve F.curve.π p).left ⟶
      (MathlibExt.AlgebraicGeometry.RelativeCurveClasses.fieldBaseChange X Ω).left :=
  pullback.lift (pullback.fst F.curve.π p ≫ F.map) (pullback.snd F.curve.π p) (by
    rw [Category.assoc, F.over, ← Category.assoc, pullback.condition]
    simp only [Category.assoc, hp])

/-- A fixed actual Chow curve class on every geometric fibre. The right side
is the computed native flat cycle sum, tested on every representative of β;
no arbitrary class base-change function occurs in the contract. -/
def HasCurveClass [LocallyOfFiniteType X.hom] [IsNoetherian X.left]
    (β : MathlibExt.AlgebraicGeometry.RelativeCurveClasses.CurveClass X) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    (p : Spec (.of Ω) ⟶ T.left)
    (hp : p ≫ T.hom = Spec.map (CommRingCat.ofHom (algebraMap k Ω))),
    ∃ hC : IsNoetherian (fiberCurve F.curve.π p).left,
    ∃ hX : IsNoetherian
      (MathlibExt.AlgebraicGeometry.RelativeCurveClasses.fieldBaseChange X Ω).left,
    ∃ hf : IsProper (geometricMap X T F Ω p hp),
    letI := hC
    letI := hX
    letI := hf
    ∀ c : MathlibExt.AlgebraicGeometry.GeometricChow.CycleGroup X.left 1,
      (MathlibExt.AlgebraicGeometry.RelativeCurveClasses.relations X 1).mkQ c = β →
      MathlibExt.AlgebraicGeometry.RelativeCurveClasses.pushedCurveClass
        (fiberCurve F.curve.π p).left (geometricMap X T F Ω p hp) =
      (MathlibExt.AlgebraicGeometry.RelativeCurveClasses.relations
        (MathlibExt.AlgebraicGeometry.RelativeCurveClasses.fieldBaseChange X Ω) 1).mkQ
        (MathlibExt.AlgebraicGeometry.GeometricChowOperators.flatCyclePullback
          (MathlibExt.AlgebraicGeometry.RelativeCurveClasses.fieldProjection X Ω) 1 0 c)

/-- General map-stable, class-controlled families. This is a public contract
on actual objects; no moduli-stack/properness provider is assumed by its type. -/
structure StableFamily [LocallyOfFiniteType X.hom] [IsNoetherian X.left]
    (β : MathlibExt.AlgebraicGeometry.RelativeCurveClasses.CurveClass X) where
  toFamily : Family X.hom n g T.left T.hom
  stable : IsGeometricallyStable toFamily
  curveClass : HasCurveClass X T toFamily β

end CurveClasses


section ScopedAdapter

open MathlibExt.AlgebraicGeometry.AlgebraicBundleGeometry
open MathlibExt.AlgebraicGeometry.PerverseSheaves

variable {r : ℕ}
  {X : ProjectiveBundle MathlibExt.AlgebraicGeometry.StableLineMaps.Point 0 r
    (MathlibExt.AlgebraicGeometry.StableLineMaps.targetGenerators r)}
  {T : ComplexScheme}

/-- The previous degree-one packet embeds into the general family contract. -/
def ofStableLine (F : MathlibExt.AlgebraicGeometry.StableLineMaps.StableLineFamily r X T) :
    Family X.projection.left 1 0 T.left T.hom :=
  ⟨F.curve, F.map, F.over⟩

theorem ofStableLine_stable
    (F : MathlibExt.AlgebraicGeometry.StableLineMaps.StableLineFamily r X T) :
    IsGeometricallyStable (ofStableLine F) := by
  intro Ω _ _ p
  let := F.stable Ω p
  let inclusion : geometricAutomorphisms (ofStableLine F) Ω p →
      MathlibExt.AlgebraicGeometry.StableLineMaps.mapAut r X F.curve F.map p :=
    fun e => ⟨e.val, e.property.1, e.property.2 0⟩
  exact Finite.of_injective inclusion (by
    intro a c h
    apply Subtype.ext
    exact congrArg
      (fun e : MathlibExt.AlgebraicGeometry.StableLineMaps.mapAut r X F.curve F.map p => e.val) h)

end ScopedAdapter

end MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies
