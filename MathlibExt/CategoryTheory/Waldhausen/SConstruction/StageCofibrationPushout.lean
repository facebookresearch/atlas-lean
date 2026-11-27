/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageCofibrationEverywhere
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StagePushout

/-!
# Pushouts along finite-stage cofibrations

Objectwise pushout choices assemble functorially into the existing
`StagePushoutPresentation`.  For a stage cofibration the ambient Waldhausen
pushout axiom supplies those choices, while
`StagePushoutPresentation.isStage_of_stageCofibration` supplies the stage
property of the apex.

No Waldhausen structure on stages is installed in this file.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

local instance stageCofibrationPushoutWaldhausenC : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

/-- Objectwise pushout choices for two stage morphisms with common source. -/
structure StagePushoutComponentData {n : ℕ} {A M N : Stage C n}
    (f : A ⟶ M) (g : A ⟶ N) where
  /-- The chosen pushout object at an interval. -/
  apexObj : Ar n → C
  /-- The chosen leg from the first target. -/
  inlApp : ∀ x, M.obj.obj x ⟶ apexObj x
  /-- The chosen leg from the second target. -/
  inrApp : ∀ x, N.obj.obj x ⟶ apexObj x
  /-- The chosen square is a pushout. -/
  isPushoutApp : ∀ x,
    IsPushout (f.hom.app x) (g.hom.app x) (inlApp x) (inrApp x)

namespace StagePushoutComponentData

variable {C}
variable {n : ℕ} {A M N : Stage C n} {f : A ⟶ M} {g : A ⟶ N}

/-- The map between chosen component pushouts induced by an indexing arrow. -/
def apexMap (D : StagePushoutComponentData C f g)
    {x y : Ar n} (r : x ⟶ y) : D.apexObj x ⟶ D.apexObj y :=
  (D.isPushoutApp x).desc
    (M.obj.map r ≫ D.inlApp y)
    (N.obj.map r ≫ D.inrApp y) (by
      rw [← Category.assoc, ← f.hom.naturality r,
        Category.assoc, (D.isPushoutApp y).w, ← Category.assoc,
        g.hom.naturality r, Category.assoc])

@[reassoc]
theorem inlApp_apexMap (D : StagePushoutComponentData C f g)
    {x y : Ar n} (r : x ⟶ y) :
    D.inlApp x ≫ D.apexMap r = M.obj.map r ≫ D.inlApp y :=
  (D.isPushoutApp x).inl_desc _ _ _

@[reassoc]
theorem inrApp_apexMap (D : StagePushoutComponentData C f g)
    {x y : Ar n} (r : x ⟶ y) :
    D.inrApp x ≫ D.apexMap r = N.obj.map r ≫ D.inrApp y :=
  (D.isPushoutApp x).inr_desc _ _ _

/-- The functor assembled from objectwise pushout choices. -/
def apex (D : StagePushoutComponentData C f g) : Ar n ⥤ C where
  obj := D.apexObj
  map := fun r ↦ D.apexMap r
  map_id x := by
    apply (D.isPushoutApp x).hom_ext
    · simp only [inlApp_apexMap, Functor.map_id, Category.id_comp,
        Category.comp_id]
    · simp only [inrApp_apexMap, Functor.map_id, Category.id_comp,
        Category.comp_id]
  map_comp r s := by
    apply (D.isPushoutApp _).hom_ext
    · rw [D.inlApp_apexMap (r ≫ s), ← Category.assoc,
        D.inlApp_apexMap r, Category.assoc,
        D.inlApp_apexMap s, Functor.map_comp, Category.assoc]
    · rw [D.inrApp_apexMap (r ≫ s), ← Category.assoc,
        D.inrApp_apexMap r, Category.assoc,
        D.inrApp_apexMap s, Functor.map_comp, Category.assoc]

/-- The first family of chosen legs as a natural transformation. -/
def inl (D : StagePushoutComponentData C f g) : M.obj ⟶ D.apex where
  app := D.inlApp
  naturality := fun _ _ r ↦ (D.inlApp_apexMap r).symm

/-- The second family of chosen legs as a natural transformation. -/
def inr (D : StagePushoutComponentData C f g) : N.obj ⟶ D.apex where
  app := D.inrApp
  naturality := fun _ _ r ↦ (D.inrApp_apexMap r).symm

/-- Objectwise choices assemble into a functorial pushout presentation. -/
def toPresentation (D : StagePushoutComponentData C f g) :
    StagePushoutPresentation C f g where
  apex := D.apex
  inl := D.inl
  inr := D.inr
  isPushout_app x := by
    change IsPushout (f.hom.app x) (g.hom.app x)
      (D.inlApp x) (D.inrApp x)
    exact D.isPushoutApp x

end StagePushoutComponentData

namespace StagePushoutPresentation

variable {C}
variable {n : ℕ} {A M N : Stage C n} {f : A ⟶ M} {g : A ⟶ N}

/-- The first presentation leg, bundled as a morphism into the stage apex. -/
def inlToStage (P : StagePushoutPresentation C f g)
    (hf : stageCofibrations C n f) : M ⟶ P.toStage hf :=
  ⟨P.inl⟩

/-- The second presentation leg, bundled as a morphism into the stage apex. -/
def inrToStage (P : StagePushoutPresentation C f g)
    (hf : stageCofibrations C n f) : N ⟶ P.toStage hf :=
  ⟨P.inr⟩

/-- The bundled presentation square is a pushout in the full stage
subcategory. -/
theorem isPushout_toStage (P : StagePushoutPresentation C f g)
    (hf : stageCofibrations C n f) :
    IsPushout f g (P.inlToStage hf) (P.inrToStage hf) := by
  apply IsPushout.of_map_of_faithful (forget C n)
  apply IsPushout.of_forall_isPushout_app
  exact P.isPushout_app

/-- The cobase-changed leg of a functorial pointwise pushout presentation is
again a stage cofibration. -/
theorem inrToStage_stageCofibrations
    (P : StagePushoutPresentation C f g)
    (hf : stageCofibrations C n f) :
    stageCofibrations C n (P.inrToStage hf) := by
  apply stageCofibrations_of_everywhere C
  have hfevery : stageCofibrationsEverywhere C n f :=
    stageCofibrationsEverywhere_of_stageCofibrations C hf
  intro i j k hij hjk
  obtain ⟨K, pA, pM, df, hpushF, hpA, hpM, hdf⟩ := hfevery hij hjk
  have hNcof : IsCofibration (N.obj.map (horiz hij hjk)) :=
    (N.property.cofiber_triple hij hjk).1
  obtain ⟨R, rPij, rNik, hRraw, _⟩ :=
    WaldhausenCategoryWithoutGluing.cofibration_pushout (C := C)
      (N.obj.map (horiz hij hjk)) hNcof
      (P.apex.obj (interval i j hij))
      (P.inr.app (interval i j hij))
  have hR : IsPushout (N.obj.map (horiz hij hjk))
      (P.inr.app (interval i j hij)) rNik rPij := hRraw.flip
  have hagreeQ :
      A.obj.map (horiz hij hjk) ≫
          (g.hom.app (interval i k (hij.trans hjk)) ≫ rNik) =
        f.hom.app (interval i j hij) ≫
          (P.inl.app (interval i j hij) ≫ rPij) := by
    calc
      A.obj.map (horiz hij hjk) ≫
          (g.hom.app (interval i k (hij.trans hjk)) ≫ rNik) =
        (A.obj.map (horiz hij hjk) ≫
          g.hom.app (interval i k (hij.trans hjk))) ≫ rNik :=
            (Category.assoc _ _ _).symm
      _ = (g.hom.app (interval i j hij) ≫
          N.obj.map (horiz hij hjk)) ≫ rNik := by
            rw [g.hom.naturality]
      _ = g.hom.app (interval i j hij) ≫
          (N.obj.map (horiz hij hjk) ≫ rNik) := Category.assoc _ _ _
      _ = g.hom.app (interval i j hij) ≫
          (P.inr.app (interval i j hij) ≫ rPij) := by rw [hR.w]
      _ = (g.hom.app (interval i j hij) ≫
          P.inr.app (interval i j hij)) ≫ rPij :=
            (Category.assoc _ _ _).symm
      _ = (f.hom.app (interval i j hij) ≫
          P.inl.app (interval i j hij)) ≫ rPij := by
            rw [(P.isPushout_app (interval i j hij)).w]
      _ = f.hom.app (interval i j hij) ≫
          (P.inl.app (interval i j hij) ≫ rPij) := Category.assoc _ _ _
  let q : K ⟶ R := hpushF.desc
    (g.hom.app (interval i k (hij.trans hjk)) ≫ rNik)
    (P.inl.app (interval i j hij) ≫ rPij) hagreeQ
  have hpAq : pA ≫ q =
      g.hom.app (interval i k (hij.trans hjk)) ≫ rNik :=
    hpushF.inl_desc _ _ _
  have hpMq : pM ≫ q =
      P.inl.app (interval i j hij) ≫ rPij :=
    hpushF.inr_desc _ _ _
  let d : R ⟶ P.apex.obj (interval i k (hij.trans hjk)) :=
    hR.desc (P.inr.app (interval i k (hij.trans hjk)))
      (P.apex.map (horiz hij hjk)) (P.inr.naturality (horiz hij hjk))
  have hrNik : rNik ≫ d =
      P.inr.app (interval i k (hij.trans hjk)) := hR.inl_desc _ _ _
  have hrPij : rPij ≫ d = P.apex.map (horiz hij hjk) :=
    hR.inr_desc _ _ _
  have houterQ : IsPushout
      (f.hom.app (interval i j hij))
      (A.obj.map (horiz hij hjk) ≫
        g.hom.app (interval i k (hij.trans hjk)))
      (pM ≫ q) rNik := by
    rw [g.hom.naturality, hpMq]
    exact (P.isPushout_app (interval i j hij)).paste_vert hRraw
  have hQ : IsPushout pA
      (g.hom.app (interval i k (hij.trans hjk))) q rNik :=
    houterQ.of_top hpAq hpushF.flip
  have hcomm : df ≫ P.inl.app (interval i k (hij.trans hjk)) = q ≫ d := by
    apply hpushF.hom_ext
    · calc
        pA ≫ (df ≫ P.inl.app (interval i k (hij.trans hjk))) =
            (pA ≫ df) ≫ P.inl.app (interval i k (hij.trans hjk)) :=
              (Category.assoc _ _ _).symm
        _ = f.hom.app (interval i k (hij.trans hjk)) ≫
            P.inl.app (interval i k (hij.trans hjk)) := by rw [hpA]
        _ = g.hom.app (interval i k (hij.trans hjk)) ≫
            P.inr.app (interval i k (hij.trans hjk)) :=
              (P.isPushout_app (interval i k (hij.trans hjk))).w
        _ = g.hom.app (interval i k (hij.trans hjk)) ≫ (rNik ≫ d) := by
              rw [hrNik]
        _ = (g.hom.app (interval i k (hij.trans hjk)) ≫ rNik) ≫ d :=
              (Category.assoc _ _ _).symm
        _ = (pA ≫ q) ≫ d := by rw [hpAq]
        _ = pA ≫ (q ≫ d) := Category.assoc _ _ _
    · calc
        pM ≫ (df ≫ P.inl.app (interval i k (hij.trans hjk))) =
            (pM ≫ df) ≫ P.inl.app (interval i k (hij.trans hjk)) :=
              (Category.assoc _ _ _).symm
        _ = M.obj.map (horiz hij hjk) ≫
            P.inl.app (interval i k (hij.trans hjk)) := by rw [hpM]
        _ = P.inl.app (interval i j hij) ≫
            P.apex.map (horiz hij hjk) := P.inl.naturality (horiz hij hjk)
        _ = P.inl.app (interval i j hij) ≫ (rPij ≫ d) := by rw [hrPij]
        _ = (P.inl.app (interval i j hij) ≫ rPij) ≫ d :=
              (Category.assoc _ _ _).symm
        _ = (pM ≫ q) ≫ d := by rw [hpMq]
        _ = pM ≫ (q ≫ d) := Category.assoc _ _ _
  have houterD : IsPushout (pA ≫ df)
      (g.hom.app (interval i k (hij.trans hjk)))
      (P.inl.app (interval i k (hij.trans hjk))) (rNik ≫ d) := by
    rw [hpA, hrNik]
    exact P.isPushout_app (interval i k (hij.trans hjk))
  have hright : IsPushout df q
      (P.inl.app (interval i k (hij.trans hjk))) d :=
    houterD.of_left hcomm hQ
  have hd : IsCofibration d :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout hright.flip hdf
  exact ⟨R, rNik, rPij, d, hR, hrNik, hrPij, hd⟩

end StagePushoutPresentation

namespace StageCofibrationPushout

variable {C}
variable {n : ℕ} {A M N : Stage C n} {f : A ⟶ M} {g : A ⟶ N}

/-- One ambient pushout choice at an interval, in the orientation returned by
the Waldhausen pushout axiom. -/
structure ComponentChoice (x : Ar n) where
  apex : C
  inN : N.obj.obj x ⟶ apex
  inM : M.obj.obj x ⟶ apex
  isPushout : IsPushout (g.hom.app x) (f.hom.app x) inN inM
  inN_isCofibration : IsCofibration inN

/-- Select one ambient component pushout along a stage cofibration. -/
noncomputable def componentChoice
    (hf : stageCofibrations C n f) (x : Ar n) : ComponentChoice (f := f) (g := g) x := by
  let h :=
    WaldhausenCategoryWithoutGluing.cofibration_pushout (C := C)
      (f.hom.app x) (stageCofibrations_app C hf x)
      (N.obj.obj x) (g.hom.app x)
  let P := h.choose
  let inN := h.choose_spec.choose
  let inM := h.choose_spec.choose_spec.choose
  let hs := h.choose_spec.choose_spec.choose_spec
  exact ⟨P, inN, inM, hs.1, hs.2⟩

/-- Canonical classical choice of component pushouts along a stage
cofibration. -/
noncomputable def componentData
    (hf : stageCofibrations C n f) : StagePushoutComponentData C f g where
  apexObj x := (componentChoice (g := g) hf x).apex
  inlApp x := (componentChoice (g := g) hf x).inM
  inrApp x := (componentChoice (g := g) hf x).inN
  isPushoutApp x := (componentChoice (g := g) hf x).isPushout.flip

/-- The functorial pointwise pushout presentation selected from the ambient
Waldhausen pushout axiom. -/
noncomputable def presentation (hf : stageCofibrations C n f) :
    StagePushoutPresentation C f g :=
  (componentData (g := g) hf).toPresentation

/-- The selected pushout apex, bundled as a finite stage. -/
noncomputable def apexStage (hf : stageCofibrations C n f) : Stage C n :=
  (presentation (g := g) hf).toStage hf

/-- The selected leg from the original target into the pushout stage. -/
noncomputable def inl (hf : stageCofibrations C n f) :
    M ⟶ apexStage (g := g) hf :=
  (presentation (g := g) hf).inlToStage hf

/-- The selected cobase-changed leg into the pushout stage. -/
noncomputable def inr (hf : stageCofibrations C n f) :
    N ⟶ apexStage (g := g) hf :=
  (presentation (g := g) hf).inrToStage hf

/-- The selected square is a pushout in the stage category. -/
theorem isPushout (hf : stageCofibrations C n f) :
    IsPushout f g (inl (g := g) hf) (inr (g := g) hf) :=
  (presentation (g := g) hf).isPushout_toStage hf

/-- The selected cobase-changed leg is again a stage cofibration. -/
theorem inr_stageCofibrations (hf : stageCofibrations C n f) :
    stageCofibrations C n (inr (g := g) hf) :=
  (presentation (g := g) hf).inrToStage_stageCofibrations hf

/-- Pushouts along stage cofibrations exist and preserve the cofibration leg. -/
theorem exists_pushout (hf : stageCofibrations C n f) :
    ∃ (P : Stage C n) (inN : N ⟶ P) (inM : M ⟶ P),
      IsPushout g f inN inM ∧ stageCofibrations C n inN :=
  ⟨apexStage (g := g) hf, inr (g := g) hf, inl (g := g) hf,
    (isPushout (g := g) hf).flip, inr_stageCofibrations (g := g) hf⟩

end StageCofibrationPushout

end CategoryTheory.Waldhausen.SConstruction
