/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`TauCeti/AlgebraicGeometry/Curves/StableMaps/Basic.lean`,
`TauCeti/AlgebraicGeometry/Curves/StableMaps/Category.lean` and
`TauCeti/AlgebraicGeometry/Curves/StableMaps/Contracted.lean`
(TauCetiProject/TauCeti, revision 62bbc0596dc3539d488232e4e924a338548ea0a9):
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Tau Ceti contributors
Modifications: the prestable-map, evaluation, category and base-change signatures use the
native `MarkedFamily` for arbitrary `n` and `g` and keep a fixed target over an arbitrary base.
-/
module

public import MathlibExt.AlgebraicGeometry.MarkedCurveStabilization

/-!
# General stable-map family contracts

The target/base, parameter, marking count and genus are arbitrary. The
source is an actual marked nodal family; the map and every evaluation are
actual scheme morphisms. Geometric stability tests every algebraically
closed field fibre and every map-and-mark-preserving automorphism.

The native groupoid contains actual source isomorphisms with their map,
base and marking equations. Cartesian base-change data specify actual
pullback squares and normalized marking maps; the map part is constructed
from that data. Curve-class constraints are in `GeneralStableMapCurveClasses` and the
degree-one projective-line adapter is in `GeneralStableLineAdapters`, so that consumers of
the core family API (for instance log stable maps) do not import Chow groups, bundle
geometry or analytification. General stable-map stack/algebraicity, POT and
gluing/invariant providers remain separate work.
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

end MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies
