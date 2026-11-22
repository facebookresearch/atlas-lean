/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OriginalOrdinaryJPathCone
import Mathlib.CategoryTheory.Localization.HomEquiv
import Mathlib.CategoryTheory.Localization.Opposite

/-!
# The actual original covariant Puppe connecting position

The original κ-J cone supplies the opposite chosen Puppe boundary.
The canonical localization Hom equivalence transposes that same boundary
and its complete image/kernel law to the original ordinary homotopy category.
The earned weak comparison from the caller fibre then transports the
connecting map to the same fibre and retains its original projection.

The loop carrier here is the original J path-fibre. Its comparison with
the original derived ordinary loop functor and the signed integer sequence
remain subsequent source constructions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe w u v
open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopicalAlgebra.OriginalOrdinaryCovariantPuppeConnection

variable {C : Type u} [Category.{v} C] [ModelCategory C]

private instance opLocalization :
    (toHomotopyCategory C).op.IsLocalization (weakEquivalences Cᵒᵖ) := by
  rw [weakEquivalences_op]
  infer_instance

/-- The whole Hom equivalence uses the original canonical localization and its opposite. -/
def homEquiv (A B : Cᵒᵖ) :
    ((toHomotopyCategory Cᵒᵖ).obj A ⟶ (toHomotopyCategory Cᵒᵖ).obj B) ≃
      ((toHomotopyCategory C).obj B.unop ⟶ (toHomotopyCategory C).obj A.unop) :=
  (Localization.homEquiv (weakEquivalences Cᵒᵖ)
    (toHomotopyCategory Cᵒᵖ) (toHomotopyCategory C).op).trans
      (opEquiv ((toHomotopyCategory C).op.obj A) ((toHomotopyCategory C).op.obj B))

/-- Every original point-set map retains its actual reversed image. -/
theorem homEquiv_map {A B : Cᵒᵖ} (f : A ⟶ B) :
    homEquiv A B ((toHomotopyCategory Cᵒᵖ).map f) =
      (toHomotopyCategory C).map f.unop := by
  change (Localization.homEquiv (weakEquivalences Cᵒᵖ)
    (toHomotopyCategory Cᵒᵖ) (toHomotopyCategory C).op
      ((toHomotopyCategory Cᵒᵖ).map f)).unop = _
  rw [Localization.homEquiv_map]
  rfl

/-- The full original comparison reverses every actual Ho composite. -/
theorem homEquiv_comp {A B D : Cᵒᵖ}
    (f : (toHomotopyCategory Cᵒᵖ).obj A ⟶ (toHomotopyCategory Cᵒᵖ).obj B)
    (g : (toHomotopyCategory Cᵒᵖ).obj B ⟶ (toHomotopyCategory Cᵒᵖ).obj D) :
    homEquiv A D (f ≫ g) = homEquiv B D g ≫ homEquiv A B f := by
  change (Localization.homEquiv (weakEquivalences Cᵒᵖ)
    (toHomotopyCategory Cᵒᵖ) (toHomotopyCategory C).op (f ≫ g)).unop = _
  rw [Localization.homEquiv_comp]
  rfl

variable [HasZeroObject C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z)

/-- The actual caller zero word is retained in the original homotopy category. -/
def null (A B : C) : (toHomotopyCategory C).obj A ⟶ (toHomotopyCategory C).obj B :=
  (toHomotopyCategory C).map (OrdinaryHoChosenPuppe.nullMap Z hZ A B)

/-- The entire original Hom comparison retains both caller zero endpoint functions. -/
theorem homEquiv_null (A B : Cᵒᵖ) :
    homEquiv A B (OrdinaryHoCofiberKernel.nullHom A B) = null Z hZ B.unop A.unop := by
  unfold OrdinaryHoCofiberKernel.nullHom null
  rw [homEquiv_map]
  have h := OrdinaryHoChosenPuppe.actualNullMap_eq_chosen (op Z) hZ.op A B
  rw [← h]
  apply (toHomotopyCategory C).congr_map
  unfold OrdinaryHoChosenPuppe.nullMap OrdinaryHoChosenPuppe.toZero OrdinaryHoChosenPuppe.fromZero
  rw [unop_comp]
  congr 1
  · exact hZ.isTerminal.hom_ext _ _
  · exact hZ.isInitial.hom_ext _ _

local notation "P" => OriginalOrdinaryJPathCone.oppositeCone d Z hZ
local notation "ι" => OriginalOrdinaryJPathCone.oppositeInclusion d Z hZ
local notation "c" => OriginalOrdinaryJPathCone.oppositeCofiberCocone d Z hZ
local notation "hc" => OriginalOrdinaryJPathCone.oppositeCofiberIsColimit d Z hZ
local notation "H" => toHomotopyCategory C
local notation "Hᵒ" => toHomotopyCategory Cᵒᵖ

/-- The loop is the original J path-fibre from the opposite chosen suspension. -/
def loopObject (Y : C) : C :=
  (OrdinaryHoChosenPuppe.suspensionCone P ι c (op Z) hZ.op (op Y)).pt.unop

/-- The opposite chosen cofiber retains its actual original carrier. -/
abbrev cofiberObject {X Y : C} (p : X ⟶ Y) : C := (c (Arrow.mk p.op)).pt.unop

/-- The connecting arrow is the original opposite Puppe boundary, reversed. -/
def boundary {X Y : C} (p : X ⟶ Y) : loopObject d Z hZ Y ⟶ cofiberObject d Z hZ p :=
  (OrdinaryHoChosenPuppe.boundary P ι c hc (op Z) hZ.op (Arrow.mk p.op)).unop

/-- The complete connecting map is the image of the same original boundary. -/
def connectingToCofiber {X Y : C} (p : X ⟶ Y) :
    (H).obj (loopObject d Z hZ Y) ⟶ (H).obj (cofiberObject d Z hZ p) :=
  (H).map (boundary d Z hZ p)

/-- The input projection keeps the original opposite-cofiber target leg. -/
def cofiberProjection {X Y : C} (p : X ⟶ Y) :
    (H).obj (cofiberObject d Z hZ p) ⟶ (H).obj X := (H).map (c (Arrow.mk p.op)).inr.unop

omit [HasZeroObject C] in
private theorem op_isCofibrant (X : C) [IsFibrant X] : IsCofibrant (op X) := by
  apply (isCofibrant_iff_of_isInitial (terminal.from X).op terminalIsTerminal.op).mpr
  exact (cofibration_op_iff _).mpr inferInstance

omit [HasZeroObject C] in
private theorem op_isFibrant (X : C) [IsCofibrant X] : IsFibrant (op X) := by
  apply (isFibrant_iff_of_isTerminal (initial.to X).op initialIsInitial.op).mpr
  exact (fibration_op_iff _).mpr inferInstance

/-- The original opposite Puppe image law gives covariant exactness on the same path-cofiber carrier. -/
theorem exact_at_cofiber {X Y : C} (p : X ⟶ Y) [Fibration p] [IsFibrant Y]
    (K : C) [IsCofibrant K] (g : (H).obj K ⟶ (H).obj (cofiberObject d Z hZ p)) :
    (∃ l : (H).obj K ⟶ (H).obj (loopObject d Z hZ Y),
      l ≫ connectingToCofiber d Z hZ p = g) ↔
      g ≫ cofiberProjection d Z hZ p = null Z hZ K X := by
  let : IsFibrant X := isFibrant_of_fibration p
  let : IsCofibrant (op X) := op_isCofibrant X
  let : IsFibrant (op K) := op_isFibrant K
  let : Cofibration ((ι).app (op Y)) := OriginalOrdinaryJPathCone.oppositeInclusion_cofibration d Z hZ _
  let F := Arrow.mk p.op
  let : IsCofibrant F.right := inferInstanceAs (IsCofibrant (op X))
  let : Cofibration ((ι).app F.left) :=
    OriginalOrdinaryJPathCone.oppositeInclusion_cofibration d Z hZ F.left
  let S := OrdinaryHoChosenPuppe.suspensionCone P ι c (op Z) hZ.op (op Y)
  let eC := homEquiv (c F).pt (op K)
  let eS := homEquiv S.pt (op K)
  let eX := homEquiv (op X) (op K)
  have hOriginal := OrdinaryHoChosenPuppe.second_exact (op Z) hZ.op P ι c hc F (op K) (eC.symm g)
  constructor
  · rintro ⟨l, hl⟩
    have hLift : (Hᵒ).map (OrdinaryHoChosenPuppe.boundary P ι c hc (op Z) hZ.op F) ≫
        eS.symm l = eC.symm g := by
      apply eC.injective
      change homEquiv (c F).pt (op K) _ = _
      rw [homEquiv_comp, homEquiv_map]
      simpa only [F, S, Arrow.mk, eS, eC, Equiv.apply_symm_apply, connectingToCofiber, boundary] using hl
    have h := congrArg eX (hOriginal.mp ⟨eS.symm l, hLift⟩)
    change homEquiv (op X) (op K) ((Hᵒ).map (c F).inr ≫ eC.symm g) =
      homEquiv (op X) (op K) (OrdinaryHoCofiberKernel.nullHom (op X) (op K)) at h
    rw [homEquiv_comp, homEquiv_map, homEquiv_null] at h
    simpa only [F, Arrow.mk, eC, Equiv.apply_symm_apply, cofiberProjection] using h
  · intro hg
    have hNull : (Hᵒ).map (c F).inr ≫ eC.symm g = OrdinaryHoCofiberKernel.nullHom (op X) (op K) := by
      apply eX.injective
      change homEquiv (op X) (op K) _ = _
      rw [homEquiv_comp, homEquiv_map, homEquiv_null]
      simpa only [F, S, Arrow.mk, eC, Equiv.apply_symm_apply, cofiberProjection] using hg
    obtain ⟨l, hl⟩ := hOriginal.mpr hNull
    refine ⟨eS l, ?_⟩
    have h := congrArg eC hl
    change homEquiv (c F).pt (op K)
        ((Hᵒ).map (OrdinaryHoChosenPuppe.boundary P ι c hc (op Z) hZ.op F) ≫ l) = _ at h
    rw [homEquiv_comp, homEquiv_map] at h
    simpa only [F, S, Arrow.mk, eC, Equiv.apply_symm_apply, eS, connectingToCofiber, boundary] using h

variable {X Y : C} (p : X ⟶ Y) [Fibration p] [IsFibrant Y]
  (s : PullbackCone p (hZ.isInitial.to Y)) (hs : IsLimit s)

/-- The original fibre comparison is a Ho isomorphism from its earned weak comparison. -/
def fiberComparisonIso : (H).obj s.pt ≅ (H).obj (cofiberObject d Z hZ p) := by
  let : IsIso ((H).map (OriginalOrdinaryJPathCone.fiberToOppositeCofiber d Z hZ p s)) :=
    (weakEquivalence_iff_isIso_toHomotopyCategory_map _).mp
      ((weakEquivalence_iff _).mp (OriginalOrdinaryJPathCone.fiberToOppositeCofiber_weak d Z hZ p s hs))
  exact asIso ((H).map (OriginalOrdinaryJPathCone.fiberToOppositeCofiber d Z hZ p s))

omit [HasZeroObject C] in
/-- Both full source maps preserve the actual original first fibre projection. -/
theorem fiberComparisonIso_projection :
    (fiberComparisonIso d Z hZ p s hs).hom ≫ cofiberProjection d Z hZ p = (H).map s.fst := by
  change (H).map _ ≫ (H).map _ = _
  rw [← (H).map_comp, OriginalOrdinaryJPathCone.fiberToOppositeCofiber_fst]

/-- The connecting map into the same caller fibre uses the complete earned comparison inverse. -/
def connectingToFiber : (H).obj (loopObject d Z hZ Y) ⟶ (H).obj s.pt :=
  connectingToCofiber d Z hZ p ≫ (fiberComparisonIso d Z hZ p s hs).inv

/-- The whole covariant connecting image is the null kernel of the caller's original fibre projection. -/
theorem exact_at_fiber (K : C) [IsCofibrant K] (g : (H).obj K ⟶ (H).obj s.pt) :
    (∃ l : (H).obj K ⟶ (H).obj (loopObject d Z hZ Y),
      l ≫ connectingToFiber d Z hZ p s hs = g) ↔
      g ≫ (H).map s.fst = null Z hZ K X := by
  let e := fiberComparisonIso d Z hZ p s hs
  have hImage :
      (∃ l : (H).obj K ⟶ (H).obj (loopObject d Z hZ Y),
        l ≫ connectingToFiber d Z hZ p s hs = g) ↔
      ∃ l : (H).obj K ⟶ (H).obj (loopObject d Z hZ Y), l ≫ connectingToCofiber d Z hZ p = g ≫ e.hom := by
    constructor
    · rintro ⟨l, hl⟩
      refine ⟨l, ?_⟩
      have h := congrArg (fun q => q ≫ e.hom) hl
      simpa only [connectingToFiber, e, Category.assoc, Iso.inv_hom_id, Category.comp_id] using h
    · rintro ⟨l, hl⟩
      refine ⟨l, ?_⟩
      have h := congrArg (fun q => q ≫ e.inv) hl
      simpa only [connectingToFiber, e, Category.assoc, Iso.hom_inv_id, Category.comp_id] using h
  have hKernel : (g ≫ e.hom) ≫ cofiberProjection d Z hZ p = null Z hZ K X ↔
      g ≫ (H).map s.fst = null Z hZ K X := by
    rw [Category.assoc, fiberComparisonIso_projection]
  exact hImage.trans ((exact_at_cofiber d Z hZ p K (g ≫ e.hom)).trans hKernel)

end HomotopicalAlgebra.OriginalOrdinaryCovariantPuppeConnection
