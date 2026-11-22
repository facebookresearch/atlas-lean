/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.ShiftedHom

/-!
# All original orthogonal cofiber choices and shifted Hom tests

The source is the unchanged whole Arrow I replacement and every actual
positive I suspension iterate. Each caller supplies the original cofiber
span's actual colimit witness. The full chosen colimit comparison transports
both cofiber legs, every Arrow map, every shifted target map and both Hom
functions. Its nullity assertion concerns the caller's original collapse.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.ChosenCofiberHom

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open PointedCGWH.Spectra.Orthogonal.ShiftedHomTests

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev C := OrthogonalCarrier.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev H := toHomotopyCategory C.{u, v}
private abbrev cone := OriginalICone.cone (B := B) (I := O.{u, v})
private abbrev inclusion := OriginalICone.inclusion (B := B) (I := O.{u, v})
private abbrev canonicalCone := OriginalISuspension.cocone (B := B) (I := O.{u, v})
private abbrev canonicalLimit := OriginalISuspension.coconeIsColimit (B := B) (I := O.{u, v})
private abbrev sourceSuspension (s : ℕ) :=
  NativeK.FiberHomTests.originalQSuspensionIterate (B := B) (I := O.{u, v}) s
private abbrev canonicalCofiber (s : ℕ) :=
  NativeK.FiberHomTests.originalQSuspensionCofiber (B := B) (I := O.{u, v}) s

variable (d : ∀ F : Arrow C.{u, v}, PushoutCocone (inclusion.app F.left) F.hom)
  (hd : ∀ F, IsColimit (d F))

/-- Every original caller cofiber acts on the whole original suspended Q Arrow. -/
def chosenCofiber (s : ℕ) : Arrow C.{u, v} ⥤ C.{u, v} :=
  (sourceSuspension s).mapArrow ⋙ OrdinaryHoChosenPuppe.cofiberFunctor cone inclusion d hd

/-- The full original colimit comparison keeps the caller's unchanged
carrier, both original legs and every whole Arrow transformation. -/
def chosenCofiberIso (s : ℕ) : canonicalCofiber s ≅ chosenCofiber d hd s :=
  Functor.isoWhiskerLeft (sourceSuspension s).mapArrow
    (OrdinaryHoChosenFiberCofiberComparison.cofiberChoiceNatIso
      cone inclusion canonicalCone canonicalLimit d hd)

/-- The forward function keeps the entire original cone leg. -/
theorem chosenCofiberIso_hom_cone (s : ℕ) (F : Arrow C.{u, v}) :
    (canonicalCone ((sourceSuspension s).mapArrow.obj F)).inl ≫
        (chosenCofiberIso d hd s).hom.app F =
      (d ((sourceSuspension s).mapArrow.obj F)).inl :=
  OrdinaryHoChosenFiberCofiberComparison.cofiberChoiceIso_hom_cone
    cone inclusion canonicalCone canonicalLimit d hd _

/-- The forward function keeps the whole original target leg. -/
theorem chosenCofiberIso_hom_target (s : ℕ) (F : Arrow C.{u, v}) :
    (canonicalCone ((sourceSuspension s).mapArrow.obj F)).inr ≫
        (chosenCofiberIso d hd s).hom.app F =
      (d ((sourceSuspension s).mapArrow.obj F)).inr :=
  OrdinaryHoChosenFiberCofiberComparison.cofiberChoiceIso_hom_target
    cone inclusion canonicalCone canonicalLimit d hd _

/-- The inverse keeps the same original cone leg in the opposite direction. -/
theorem chosenCofiberIso_inv_cone (s : ℕ) (F : Arrow C.{u, v}) :
    (d ((sourceSuspension s).mapArrow.obj F)).inl ≫
        (chosenCofiberIso d hd s).inv.app F =
      (canonicalCone ((sourceSuspension s).mapArrow.obj F)).inl :=
  OrdinaryHoChosenFiberCofiberComparison.cofiberChoiceIso_inv_cone
    cone inclusion canonicalCone canonicalLimit d hd _

/-- The inverse retains the entire original target leg. -/
theorem chosenCofiberIso_inv_target (s : ℕ) (F : Arrow C.{u, v}) :
    (d ((sourceSuspension s).mapArrow.obj F)).inr ≫
        (chosenCofiberIso d hd s).inv.app F =
      (canonicalCone ((sourceSuspension s).mapArrow.obj F)).inr :=
  OrdinaryHoChosenFiberCofiberComparison.cofiberChoiceIso_inv_target
    cone inclusion canonicalCone canonicalLimit d hd _

/-- Both complete inverse functions transport every actual caller cofiber
Hom test to the same original canonical cofiber test. -/
def chosenHomEquiv (r s : ℕ) (F : Arrow C.{u, v}) (E : C.{u, v}) :
    (H.obj ((chosenCofiber d hd s).obj F) ⟶ H.obj ((loopTarget r).obj E)) ≃
      (H.obj ((canonicalCofiber s).obj F) ⟶ H.obj ((loopTarget r).obj E)) :=
  Iso.homCongr ((H.mapIso ((chosenCofiberIso d hd s).app F)).symm) (Iso.refl _)

/-- The forward function is the original full chosen-colimit comparison precomposition. -/
theorem chosenHomEquiv_apply (r s : ℕ) (F : Arrow C.{u, v}) (E : C.{u, v})
    (g : H.obj ((chosenCofiber d hd s).obj F) ⟶ H.obj ((loopTarget r).obj E)) :
    chosenHomEquiv d hd r s F E g = H.map ((chosenCofiberIso d hd s).hom.app F) ≫ g := by
  simp only [chosenHomEquiv, Iso.homCongr_apply, Iso.symm_inv, Functor.mapIso_hom,
    Iso.app_hom, Iso.refl_hom, Category.comp_id]

/-- The inverse function is the same original inverse colimit comparison precomposition. -/
theorem chosenHomEquiv_symm_apply (r s : ℕ) (F : Arrow C.{u, v}) (E : C.{u, v})
    (g : H.obj ((canonicalCofiber s).obj F) ⟶ H.obj ((loopTarget r).obj E)) :
    (chosenHomEquiv d hd r s F E).symm g = H.map ((chosenCofiberIso d hd s).inv.app F) ≫ g := by
  simp only [chosenHomEquiv, Iso.homCongr_symm, Iso.homCongr_apply, Iso.symm_inv,
    Iso.symm_hom, Functor.mapIso_inv, Iso.app_inv, Iso.refl_inv, Category.comp_id]

/-- Every full original suspended Q Arrow square is retained by the forward test function. -/
theorem chosenHomEquiv_source (r s : ℕ) {F G : Arrow C.{u, v}} (q : F ⟶ G) (E : C.{u, v})
    (g : H.obj ((chosenCofiber d hd s).obj G) ⟶ H.obj ((loopTarget r).obj E)) :
    chosenHomEquiv d hd r s F E (H.map ((chosenCofiber d hd s).map q) ≫ g) =
      H.map ((canonicalCofiber s).map q) ≫ chosenHomEquiv d hd r s G E g := by
  rw [chosenHomEquiv_apply, chosenHomEquiv_apply, ← Category.assoc, ← Category.assoc]
  have h := H.congr_map ((chosenCofiberIso d hd s).hom.naturality q)
  simp only [Functor.map_comp] at h
  exact congrArg (fun a => a ≫ g) h.symm

/-- Every full original target map is retained by the forward shifted test function. -/
theorem chosenHomEquiv_target (r s : ℕ) (F : Arrow C.{u, v})
    {E E' : C.{u, v}} (t : E ⟶ E')
    (g : H.obj ((chosenCofiber d hd s).obj F) ⟶ H.obj ((loopTarget r).obj E)) :
    chosenHomEquiv d hd r s F E' (g ≫ H.map ((loopTarget r).map t)) =
      chosenHomEquiv d hd r s F E g ≫ H.map ((loopTarget r).map t) := by
  rw [chosenHomEquiv_apply, chosenHomEquiv_apply, Category.assoc]

/-- The same entire original suspended Q Arrow square is retained by the inverse test function. -/
theorem chosenHomEquiv_symm_source (r s : ℕ) {F G : Arrow C.{u, v}} (q : F ⟶ G)
    (E : C.{u, v}) (g : H.obj ((canonicalCofiber s).obj G) ⟶ H.obj ((loopTarget r).obj E)) :
    (chosenHomEquiv d hd r s F E).symm (H.map ((canonicalCofiber s).map q) ≫ g) =
      H.map ((chosenCofiber d hd s).map q) ≫ (chosenHomEquiv d hd r s G E).symm g := by
  apply (chosenHomEquiv d hd r s F E).injective
  rw [Equiv.apply_symm_apply, chosenHomEquiv_source, Equiv.apply_symm_apply]

/-- Every whole shifted target map is retained by the inverse test function as well. -/
theorem chosenHomEquiv_symm_target (r s : ℕ) (F : Arrow C.{u, v})
    {E E' : C.{u, v}} (t : E ⟶ E')
    (g : H.obj ((canonicalCofiber s).obj F) ⟶ H.obj ((loopTarget r).obj E)) :
    (chosenHomEquiv d hd r s F E').symm (g ≫ H.map ((loopTarget r).map t)) =
      (chosenHomEquiv d hd r s F E).symm g ≫ H.map ((loopTarget r).map t) := by
  apply (chosenHomEquiv d hd r s F E').injective
  rw [Equiv.apply_symm_apply, chosenHomEquiv_target, Equiv.apply_symm_apply]

/-- Every Hom test of the same caller cofiber is trivial when its original
whole Arrow is an Omega-target test equivalence. -/
theorem chosenHom_subsingleton {X Y : C.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests orthogonalFamily f) (r s : ℕ) (E : C.{u, v})
    (hE : NativeK.IsOmega orthogonalFamily E) :
    Subsingleton (H.obj ((chosenCofiber d hd s).obj (Arrow.mk f)) ⟶
      H.obj ((loopTarget r).obj E)) := by
  let e := chosenHomEquiv d hd r s (Arrow.mk f) E
  refine ⟨fun g h => e.injective ?_⟩
  exact (shiftedCofiberHom_eq_null f hf r s E hE (e g)).trans
    (shiftedCofiberHom_eq_null f hf r s E hE (e h)).symm

/-- The caller's actual Hom class is its original null class, at every
original source suspension and target loop shift. -/
theorem chosenHom_eq_null {X Y : C.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests orthogonalFamily f) (r s : ℕ) (E : C.{u, v})
    (hE : NativeK.IsOmega orthogonalFamily E)
    (g : H.obj ((chosenCofiber d hd s).obj (Arrow.mk f)) ⟶ H.obj ((loopTarget r).obj E)) :
    g = OrdinaryHoCofiberKernel.nullHom ((chosenCofiber d hd s).obj (Arrow.mk f))
      ((loopTarget r).obj E) := by
  let _ := chosenHom_subsingleton d hd f hf r s E hE
  exact Subsingleton.elim _ _

/-- The collapse remains the caller's original map to the original native
zero, and it satisfies all the original Omega-target tests. -/
theorem chosenCollapse_omegaTests {X Y : C.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests orthogonalFamily f) (s : ℕ) :
    NativeK.omegaTests orthogonalFamily
      (Diagrams.toZero ((chosenCofiber d hd s).obj (Arrow.mk f))) := by
  intro E hE
  let _ : IsFibrant E := HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant E
  have hh : Subsingleton
      (H.obj ((chosenCofiber d hd s).obj (Arrow.mk f)) ⟶ H.obj E) :=
    chosenHom_subsingleton d hd f hf 0 s E hE
  exact (OrdinaryHoPuppeCofiberNull.toZero_precomposition_bijective_iff
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
      ((chosenCofiber d hd s).obj (Arrow.mk f)) E).mpr
      hh

end PointedCGWH.Spectra.Orthogonal.ChosenCofiberHom
