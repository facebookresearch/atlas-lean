/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GroupTorsorGeometry
public import MathlibExt.AlgebraicGeometry.QuotientLineDescentModels
public import MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies

/-!
# Actual quasimap torsor, associated-bundle and parameter families

A family uses an actual marked nodal curve and an actual quotient-stack
point on that curve. Its associated bundle and graph-descended section
are those of GroupTorsorGeometry. Reindexing computes the original
equivariant map through the Cartesian source and torsor comparisons.

No flatness of the basepoint subscheme, constancy of its length, or
family regularization is asserted here.

Reference: Ciocan-Fontanine–Kim–Maulik, arXiv:1106.3724v2,
§2.3, Definition 2.4.1 and Definitions 3.1.5–3.1.6.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.QuasimapAssociatedFamilies

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open _root_.AlgebraicGeometry
open GroupTorsorGeometry QuotientLineDescentModels
open MathlibExt.AlgebraicGeometry.MarkedCurveStabilization

variable {S : Scheme.{0}} (G W : Over S) [GrpObj G] [ModObj G W]
variable (n g : ℕ) (T : Over S)

/-- An actual family of marked maps to [W/G], before imposing stability. -/
structure Family where
  curve : MarkedFamily T.left n g
  quotient : QuotientObject G W (Over.mk (curve.π ≫ T.hom))

variable {G W n g T}

/-- Isomorphisms of the actual curve and torsor, preserving every marking and map. -/
structure FamilyIso (F H : Family G W n g T) where
  curve : F.curve.X ≅ H.curve.X
  over : curve.hom ≫ H.curve.π = F.curve.π
  markings : ∀ i, F.curve.marking i ≫ curve.hom = H.curve.marking i
  total : F.quotient.torsor.total ≅ H.quotient.torsor.total
  projection : total.hom.left ≫ H.quotient.torsor.projection.left =
    F.quotient.torsor.projection.left ≫ curve.hom
  equivariant : γ[G,F.quotient.torsor.total] ≫ total.hom =
    (G ◁ total.hom) ≫ γ[G,H.quotient.torsor.total]
  target : total.hom ≫ H.quotient.map = F.quotient.map

@[ext]
theorem FamilyIso.ext {F H : Family G W n g T} {a b : FamilyIso F H}
    (hc : a.curve.hom = b.curve.hom) (hp : a.total.hom = b.total.hom) : a = b := by
  have hci : a.curve = b.curve := Iso.ext hc
  have hpi : a.total = b.total := Iso.ext hp
  cases a
  cases b
  cases hci
  cases hpi
  rfl

def FamilyIso.id (F : Family G W n g T) : FamilyIso F F where
  curve := Iso.refl _
  over := by simp
  markings _ := by simp
  total := Iso.refl _
  projection := by simp
  equivariant := by simp
  target := by simp

def FamilyIso.comp {F H K : Family G W n g T}
    (a : FamilyIso F H) (b : FamilyIso H K) : FamilyIso F K where
  curve := a.curve ≪≫ b.curve
  over := by simp [Category.assoc, b.over, a.over]
  markings i := by simp [← Category.assoc, a.markings i, b.markings i]
  total := a.total ≪≫ b.total
  projection := by
    change (a.total.hom.left ≫ b.total.hom.left) ≫ K.quotient.torsor.projection.left =
      F.quotient.torsor.projection.left ≫ (a.curve.hom ≫ b.curve.hom)
    rw [Category.assoc, b.projection, ← Category.assoc, a.projection, Category.assoc]
  equivariant := by
    change γ[G,F.quotient.torsor.total] ≫ (a.total.hom ≫ b.total.hom) =
      (G ◁ (a.total.hom ≫ b.total.hom)) ≫ γ[G,K.quotient.torsor.total]
    rw [← Category.assoc, a.equivariant, Category.assoc, b.equivariant,
      ← Category.assoc, ← whiskerLeft_comp]
  target := by simp [Category.assoc, b.target, a.target]

def FamilyIso.symm {F H : Family G W n g T} (a : FamilyIso F H) : FamilyIso H F where
  curve := a.curve.symm
  over := by rw [← a.over]; simp
  markings i := by rw [← a.markings i]; simp
  total := a.total.symm
  projection := by
    have hi : a.total.inv.left ≫ a.total.hom.left = 𝟙 _ :=
      congrArg Over.Hom.left a.total.inv_hom_id
    have h := congrArg (fun h => a.total.inv.left ≫ h) a.projection
    change a.total.inv.left ≫ (a.total.hom.left ≫ H.quotient.torsor.projection.left) =
      a.total.inv.left ≫ (F.quotient.torsor.projection.left ≫ a.curve.hom) at h
    rw [← Category.assoc, hi, Category.id_comp] at h
    change a.total.inv.left ≫ F.quotient.torsor.projection.left =
      H.quotient.torsor.projection.left ≫ a.curve.inv
    simpa [Category.assoc] using
      (congrArg (fun h => h ≫ a.curve.inv) h).symm
  equivariant := by
    apply (cancel_mono a.total.hom).1
    change (γ[G,H.quotient.torsor.total] ≫ a.total.inv) ≫ a.total.hom =
      ((G ◁ a.total.inv) ≫ γ[G,F.quotient.torsor.total]) ≫ a.total.hom
    rw [Category.assoc, a.total.inv_hom_id, Category.comp_id, Category.assoc,
      a.equivariant, ← Category.assoc, ← whiskerLeft_comp]
    simp
  target := by rw [← a.target]; simp

instance familyCategory : Category (Family G W n g T) where
  Hom := FamilyIso
  id := FamilyIso.id
  comp := FamilyIso.comp
  id_comp a := by apply FamilyIso.ext <;> simp [FamilyIso.id, FamilyIso.comp]
  comp_id a := by apply FamilyIso.ext <;> simp [FamilyIso.id, FamilyIso.comp]
  assoc a b c := by apply FamilyIso.ext <;> simp [FamilyIso.comp]

instance familyIsGroupoid : IsGroupoid (Family G W n g T) where
  all_isIso a := by
    refine ⟨⟨FamilyIso.symm a, ?_, ?_⟩⟩
    · apply FamilyIso.ext
      · change a.curve.hom ≫ a.curve.inv = 𝟙 _
        exact a.curve.hom_inv_id
      · change a.total.hom ≫ a.total.inv = 𝟙 _
        exact a.total.hom_inv_id
    · apply FamilyIso.ext
      · change a.curve.inv ≫ a.curve.hom = 𝟙 _
        exact a.curve.inv_hom_id
      · change a.total.inv ≫ a.total.hom = 𝟙 _
        exact a.total.inv_hom_id

/-- The associated W-bundle and the actual graph section of the same quotient point. -/
abbrev AssociatedFamily (F : Family G W n g T) :=
  AssociatedBundle G W F.quotient

/-- An actual curve reindex carries its whole Cartesian square and every marking. -/
structure CurveReindex (F : Family G W n g T) {T' : Over S} (f : T' ⟶ T) where
  curve : MarkedFamily T'.left n g
  map : curve.X ⟶ F.curve.X
  square : IsPullback map curve.π F.curve.π f.left
  markings : ∀ i, curve.marking i ≫ map = f.left ≫ F.curve.marking i

def CurveReindex.overMap {F : Family G W n g T} {T' : Over S} {f : T' ⟶ T}
    (C : CurveReindex F f) :
    Over.mk (C.curve.π ≫ T'.hom) ⟶ Over.mk (F.curve.π ≫ T.hom) :=
  Over.homMk C.map (by
    change C.map ≫ (F.curve.π ≫ T.hom) = C.curve.π ≫ T'.hom
    rw [← Category.assoc, C.square.w, Category.assoc, Over.w f])

/-- Reindexing the family computes its equivariant map, rather than selecting a new section. -/
def reindexFamily (F : Family G W n g T) {T' : Over S} (f : T' ⟶ T)
    (C : CurveReindex F f) (P : Reindex G F.quotient.torsor C.overMap) :
    Family G W n g T' where
  curve := C.curve
  quotient := reindexObject G W F.quotient C.overMap P

/-- The associated-bundle comparison is the actual quotient/section Cartesian comparison. -/
abbrev AssociatedFamilyReindex (F : Family G W n g T) {T' : Over S} (f : T' ⟶ T)
    (C : CurveReindex F f) (P : Reindex G F.quotient.torsor C.overMap)
    (B : AssociatedFamily F) (B' : AssociatedFamily (reindexFamily F f C P)) :=
  AssociatedReindex G W F.quotient C.overMap P B B'

/-- The induced line is fixed by the original equivariant line's full descent datum. -/
abbrev InducedLine (F : Family G W n g T) (L : LinearizedLineBundles.LinearizedLineBundle G W) :=
  DescendedLine G W F.quotient L

end MathlibExt.AlgebraicGeometry.QuasimapAssociatedFamilies
