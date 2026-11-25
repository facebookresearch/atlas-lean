/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MarkedFirstOrderFamilies

/-!
# Actual target composition and forgetting markings for stable-map families

Composition and marking restriction keep the actual source family and
all its scheme maps. Stabilization records its actual contraction,
the structure-unit isomorphism, vanishing of R1, and uniqueness among
stable map factorizations. The admissibility condition retains the
genus/marking boundary and excludes an unstable constant projection.

First-order composition is the literal map on dual-number families and
descends to the actual family-isomorphism quotient.
References: Graber–Harris–Starr math/0109220v1, §2, Definition 2.2;
Knudsen, Stable curves II, §1; Stacks Project, Tag 0E7N.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StableMapCompositionFamilies

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies
open MathlibExt.AlgebraicGeometry.MarkedCurveStabilization
open MathlibExt.AlgebraicGeometry.MarkedFirstOrderFamilies
open MathlibExt.AlgebraicGeometry.GenericSectionMaps
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.FiniteCoverLocalComparison
open MathlibExt.AlgebraicGeometry.RationalResolution

variable {V Y S T : Scheme.{0}} {q : V ⟶ S} {r : Y ⟶ S}
    {n g : ℕ} {b : T ⟶ S}

/-- Literal composition with a target morphism over the same base. -/
def composeTarget (F : Family q n g T b) (h : V ⟶ Y) (over : h ≫ r = q) : Family r n g T b where
  curve := F.curve
  map := F.map ≫ h
  over := by rw [Category.assoc, over, F.over]

/-- Retain exactly the specified distinct markings, with no genus specialization. -/
def retainMarkings (C : MarkedFamily T n g) {m : ℕ} (a : Fin m → Fin n)
    (injective : Function.Injective a) : MarkedFamily T m g where
  X := C.X
  π := C.π
  proper := C.proper
  flat := C.flat
  finitePresentation := C.finitePresentation
  marking i := C.marking (a i)
  section_eq i := C.section_eq (a i)
  disjoint _ _ h := C.disjoint (fun e => h (injective e))
  smoothMarking i := C.smoothMarking (a i)
  fibers := C.fibers

def forgetMarkings (F : Family q n g T b) {m : ℕ} (a : Fin m → Fin n)
    (injective : Function.Injective a) : Family q m g T b :=
  ⟨retainMarkings F.curve a injective, F.map, F.over⟩

theorem composeTarget_evaluation (F : Family q n g T b) (h : V ⟶ Y) (over : h ≫ r = q)
    (i : Fin n) : evaluation (composeTarget F h over) i = evaluation F i ≫ h := by
  exact (Category.assoc _ _ _).symm

theorem forgetMarkings_evaluation (F : Family q n g T b) {m : ℕ} (a : Fin m → Fin n)
    (injective : Function.Injective a) (i : Fin m) :
    evaluation (forgetMarkings F a injective) i = evaluation F (a i) := rfl

/-- A projected geometric fiber is constant only if its actual map factors
through its base point. -/
def IsFiberConstant (F : Family q n g T b) (h : V ⟶ Y)
    {Ω : Type} [Field Ω] (p : Spec (.of Ω) ⟶ T) : Prop :=
  ∃ y : Spec (.of Ω) ⟶ Y,
    pullback.snd F.curve.π p ≫ y = pullback.fst F.curve.π p ≫ F.map ≫ h

/-- Constant projections require a stable retained marked curve; positive-degree projections
are admissible for every genus and marking count. -/
def IsStabilizable (F : Family q n g T b) (h : V ⟶ Y) (m : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ T),
    0 < (2 * (g : ℤ) - 2 + (m : ℤ)) ∨ ¬ IsFiberConstant F h p

/-- A genus-preserving contraction has the actual structure-unit normalization. -/
structure Contraction (X Z : Scheme.{0}) where
  map : X ⟶ Z
  proper : IsProper map
  surjective : Function.Surjective map
  unit : IsIso (structureUnit map)
  higher : IsZero (((Scheme.Modules.pushforward map).rightDerived 1).obj (structureModule X))

/-- The actual stable map after target composition and forgetting selected markings. -/
structure Stabilization (F : Family q n g T b) (h : V ⟶ Y) (over : h ≫ r = q)
    {m : ℕ} (a : Fin m → Fin n) (injective : Function.Injective a) where
  family : Family r m g T b
  stable : IsGeometricallyStable family
  contraction : Contraction F.curve.X family.curve.X
  base : contraction.map ≫ family.curve.π = F.curve.π
  markings : ∀ i : Fin m, F.curve.marking (a i) ≫ contraction.map = family.curve.marking i
  target : contraction.map ≫ family.map = F.map ≫ h
  unique : ∀ (G : Family r m g T b), IsGeometricallyStable G →
    ∀ (c : Contraction F.curve.X G.curve.X), c.map ≫ G.curve.π = F.curve.π →
      (∀ i : Fin m, F.curve.marking (a i) ≫ c.map = G.curve.marking i) →
      c.map ≫ G.map = F.map ≫ h →
        ∃! e : family ⟶ G, contraction.map ≫ e.iso.hom = c.map

section FirstOrder
variable {Ω : Type} [Field Ω] {b : Spec (.of Ω) ⟶ S}
    (F : Family q n g (Spec (.of Ω)) b) (h : V ⟶ Y) (over : h ≫ r = q)

/-- Actual first-order composition retains the same Cartesian reduction. -/
def composeDeformation (D : Deformation F) : Deformation (composeTarget F h over) where
  family := composeTarget D.family h over
  reductionMap := D.reductionMap
  square := D.square
  markings := D.markings
  targetMap := by
    change D.reductionMap ≫ (D.family.map ≫ h) = F.map ≫ h
    rw [← Category.assoc, D.targetMap]

theorem composeDeformation_isomorphic {D E : Deformation F} (e : Isomorphic F D E) :
    Isomorphic (composeTarget F h over) (composeDeformation F h over D)
      (composeDeformation F h over E) := by
  obtain ⟨e, he⟩ := e
  refine ⟨⟨e.iso, e.over, e.markings, ?_⟩, he⟩
  change e.iso.hom ≫ (E.family.map ≫ h) = D.family.map ≫ h
  rw [← Category.assoc, e.map]

def composeClasses : DeformationClasses F → DeformationClasses (composeTarget F h over) :=
  Quotient.lift (fun D => deformationClass _ (composeDeformation F h over D))
    (fun _ _ e => Quotient.sound (composeDeformation_isomorphic F h over e))

end FirstOrder
end MathlibExt.AlgebraicGeometry.StableMapCompositionFamilies
