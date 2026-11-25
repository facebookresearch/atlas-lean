/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LineBundleTaskContracts

/-!
# Native global-section and pullback formulas over an affine base

The section maps below are literal unit morphisms, scheme/module pullbacks,
and evaluation at one. Linear comparison data must agree with that formula
on every actual section. No cohomology or section-space carrier is supplied.
Native section/pullback linearity is source integration, not new Wanted work.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GenericSectionMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts

variable {R : Type} [CommRing R]

def scalarMap (X : Over (Spec (.of R))) : R →+* Γ(X.left, ⊤) :=
  X.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom

def sections (X : Over (Spec (.of R))) : X.left.Modules ⥤ ModuleCat R :=
  SheafOfModules.evaluation X.left.ringCatSheaf (op (⊤ : X.left.Opens)) ⋙
    ModuleCat.restrictScalars (scalarMap X)

abbrev Sections (X : Over (Spec (.of R))) (M : X.left.Modules) :=
  (sections X).obj M

/-- The actual unit morphism of a global section. -/
def sectionHom (X : Over (Spec (.of R))) (M : X.left.Modules) (s : Sections X M) :
    structureModule X.left ⟶ M := by
  let t : M.val.obj (op (⊤ : X.left.Opens)) := s
  refine (SheafOfModules.unitHomEquiv M).symm ?_
  refine PresheafOfModules.sectionsMk
    (fun U ↦ M.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op t) ?_
  intro U W f
  have h : (homOfLE (le_top : U.unop ≤ ⊤)).op ≫ f =
      (homOfLE (le_top : W.unop ≤ ⊤)).op := Subsingleton.elim _ _
  rw [← PresheafOfModules.map_comp_apply, h]

/-- Evaluation of the actual unit morphism at the actual section one. -/
def homSection (X : Over (Spec (.of R))) {M : X.left.Modules}
    (s : structureModule X.left ⟶ M) : Sections X M :=
  (s.val.app (op ⊤)).hom (1 : Γ(X.left, ⊤))

/-- Evaluating the morphism of a global section at one returns the section. -/
@[simp] theorem homSection_sectionHom (X : Over (Spec (.of R))) (M : X.left.Modules)
    (s : Sections X M) : homSection X (sectionHom X M s) = s := by
  change (M.unitHomEquiv (sectionHom X M s)).val (op ⊤) = s
  unfold sectionHom
  simp only [Equiv.apply_symm_apply]
  change M.val.map (homOfLE (le_top : (⊤ : X.left.Opens) ≤ ⊤)).op s = s
  rw [show (homOfLE (le_top : (⊤ : X.left.Opens) ≤ ⊤)).op = 𝟙 (op ⊤) from Subsingleton.elim _ _]
  simp
  rfl

/-- A morphism from the structure sheaf is the morphism of its value at one. -/
@[simp] theorem sectionHom_homSection (X : Over (Spec (.of R))) (M : X.left.Modules)
    (φ : structureModule X.left ⟶ M) : sectionHom X M (homSection X φ) = φ := by
  apply (SheafOfModules.unitHomEquiv M).injective
  unfold sectionHom
  simp only [Equiv.apply_symm_apply]
  ext U
  change (SheafOfModules.val M).map (homOfLE (le_top : U.unop ≤ ⊤)).op
      ((φ.val.app (op ⊤)).hom (1 : Γ(X.left, ⊤))) = (φ.val.app U).hom (1 : Γ(X.left, U.unop))
  have h := PresheafOfModules.naturality_apply φ.val (homOfLE (le_top : U.unop ≤ ⊤)).op
    (1 : Γ(X.left, ⊤))
  refine h.symm.trans ?_
  congr 1
  exact PresheafOfModules.unit_map_one _ _

/-- Actual restriction/pullback followed by the prescribed module map. -/
def pullSection {X Y : Over (Spec (.of R))} (f : X ⟶ Y)
    {M : Y.left.Modules} {N : X.left.Modules}
    (α : (Scheme.Modules.pullback f.left).obj M ⟶ N) (s : Sections Y M) : Sections X N :=
  homSection X (pullbackSection f.left (sectionHom Y M s) ≫ α)

/-- Proof-only linearity adapter to that fixed native pullback formula. -/
structure PullbackLinear {X Y : Over (Spec (.of R))} (f : X ⟶ Y)
    (M : Y.left.Modules) (N : X.left.Modules)
    (α : (Scheme.Modules.pullback f.left).obj M ⟶ N) where
  map : Sections Y M →ₗ[R] Sections X N
  normalized : ∀ s, map s = pullSection f α s


/-- The canonical top-section comparison of a pulled-back module on an actual open. -/
def openSectionsIso (X : Over (Spec (.of R))) (M : X.left.Modules) (U : X.left.Opens) :
    Γ((Scheme.Modules.pullback U.ι).obj M, ⊤) ≅ Γ(M, U) := by
  have h : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U := by
    ext x
    simp
  exact ((Scheme.Modules.toPresheaf U.toScheme ⋙
    (CategoryTheory.evaluation _ _).obj (op (⊤ : U.toScheme.Opens))).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm) ≪≫
    M.restrictAppIso U.ι ⊤ ≪≫
      (M.presheaf.mapIso (eqToIso h).op).symm


/-- Native morphism represented by an actual top section, without a chosen scalar base. -/
def topSectionHom (X : Scheme.{0}) (M : X.Modules) (s : Γ(M,⊤)) :
    structureModule X ⟶ M :=
  sectionHom (Over.mk X.toSpecΓ) M s

/-- Native open pullback of sections for arbitrary scheme maps, including absolute Frobenius. -/
def localPullbackSection {X Y : Scheme.{0}} (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (W : Y.Opens) (h : W ≤ f ⁻¹ᵁ U) (s : Γ(M,U)) :
    Γ((Scheme.Modules.pullback f).obj M,W) := by
  let XR := Over.mk X.toSpecΓ
  let YR := Over.mk Y.toSpecΓ
  let a := f.resLE U W h
  let q := topSectionHom U.toScheme ((Scheme.Modules.pullback U.ι).obj M)
    ((openSectionsIso XR M U).inv s)
  let comparison :
      (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback U.ι).obj M) ⟶
        (Scheme.Modules.pullback W.ι).obj ((Scheme.Modules.pullback f).obj M) :=
    (Scheme.Modules.pullbackComp a U.ι).hom.app M ≫
      (Scheme.Modules.pullbackCongr (Scheme.Hom.resLE_comp_ι f h)).hom.app M ≫
        (Scheme.Modules.pullbackComp W.ι f).inv.app M
  exact (openSectionsIso YR ((Scheme.Modules.pullback f).obj M) W).hom
    (((pullbackSection a q ≫ comparison).val.app (op ⊤)).hom
      (1 : Γ(W.toScheme,⊤)))

end MathlibExt.AlgebraicGeometry.GenericSectionMaps
