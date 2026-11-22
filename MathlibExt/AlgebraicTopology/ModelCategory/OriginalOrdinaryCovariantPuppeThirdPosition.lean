/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OriginalOrdinaryFibrantJLoopComparison
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenPuppeHomSequence
import MathlibExt.AlgebraicTopology.ModelCategory.OriginalOrdinaryHoPuppeConnection

/-!
# The actual third original covariant Puppe position

The third chosen Puppe theorem is applied in the opposite model category
to the same original κ-J cone. Its cone cofibrations and weak contractions
are the actual original J factor classes. The canonical opposite-localization
Hom equivalence therefore gives the original loop-image/connecting-kernel law.

The caller-selected fibre is compared by its earned weak map. The raw loop
comparison on fibrant objects then identifies the source map with the actual
derived ordinary loop image of the original fibration. No opposite generation,
properness, suspension-equivalence or stable-model premise is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe w u v
open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopicalAlgebra.OriginalOrdinaryCovariantPuppeThirdPosition

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z)

local notation "Pᵒ" => OriginalOrdinaryJPathCone.oppositeCone g Z hZ
local notation "ιᵒ" => OriginalOrdinaryJPathCone.oppositeInclusion g Z hZ
local notation "cᵒ" => OriginalOrdinaryJPathCone.oppositeCofiberCocone g Z hZ
local notation "hcᵒ" => OriginalOrdinaryJPathCone.oppositeCofiberIsColimit g Z hZ
local notation "H" => toHomotopyCategory C
local notation "Hᵒ" => toHomotopyCategory Cᵒᵖ
local notation "L" => OriginalOrdinaryJLoopFunctor.loopFunctor g Z hZ

omit [HasZeroObject C] in
private theorem op_isCofibrant (A : C) [IsFibrant A] : IsCofibrant (op A) := by
  apply (isCofibrant_iff_of_isInitial (terminal.from A).op terminalIsTerminal.op).mpr
  exact (cofibration_op_iff _).mpr inferInstance

omit [HasZeroObject C] in
private theorem op_isFibrant (A : C) [IsCofibrant A] : IsFibrant (op A) := by
  apply (isFibrant_iff_of_isTerminal (initial.to A).op initialIsInitial.op).mpr
  exact (fibration_op_iff _).mpr inferInstance

section PointSet

variable {A B : C} (p : A ⟶ B) [Fibration p] [IsFibrant B]

/-- The complete original raw J-loop image is the original connecting/cofiber null kernel. -/
theorem exact_at_loop_cofiber (K : C) [IsCofibrant K]
    (l : (H).obj K ⟶ (H).obj (OriginalOrdinaryCovariantPuppeConnection.loopObject g Z hZ B)) :
    (∃ h : (H).obj K ⟶ (H).obj (OriginalOrdinaryCovariantPuppeConnection.loopObject g Z hZ A),
      h ≫ (H).map ((L).map p) = l) ↔
      l ≫ OriginalOrdinaryCovariantPuppeConnection.connectingToCofiber g Z hZ p =
        OriginalOrdinaryCovariantPuppeConnection.null Z hZ K
          (OriginalOrdinaryCovariantPuppeConnection.cofiberObject g Z hZ p) := by
  let : IsFibrant A := isFibrant_of_fibration p
  let : IsCofibrant (op A) := op_isCofibrant A
  let : IsFibrant (op K) := op_isFibrant K
  let : Cofibration ((ιᵒ).app (op A)) := OriginalOrdinaryJPathCone.oppositeInclusion_cofibration g Z hZ _
  let : Cofibration ((ιᵒ).app (op B)) := OriginalOrdinaryJPathCone.oppositeInclusion_cofibration g Z hZ _
  let F := Arrow.mk p.op
  let : IsCofibrant F.right := inferInstanceAs (IsCofibrant (op A))
  let : Cofibration ((ιᵒ).app F.left) :=
    OriginalOrdinaryJPathCone.oppositeInclusion_cofibration g Z hZ F.left
  let : Cofibration ((ιᵒ).app F.right) :=
    OriginalOrdinaryJPathCone.oppositeInclusion_cofibration g Z hZ F.right
  let SA := OrdinaryHoChosenPuppe.suspensionCone Pᵒ ιᵒ cᵒ (op Z) hZ.op (op A)
  let SB := OrdinaryHoChosenPuppe.suspensionCone Pᵒ ιᵒ cᵒ (op Z) hZ.op (op B)
  let eA := OriginalOrdinaryCovariantPuppeConnection.homEquiv SA.pt (op K)
  let eB := OriginalOrdinaryCovariantPuppeConnection.homEquiv SB.pt (op K)
  let eC := OriginalOrdinaryCovariantPuppeConnection.homEquiv (cᵒ F).pt (op K)
  have hOriginal := OrdinaryHoChosenPuppeHomSequence.third_exact (op Z) hZ.op Pᵒ ιᵒ cᵒ hcᵒ F (op K)
    (OriginalOrdinaryJPathCone.opposite_toZero_weak g Z hZ F.right) (eB.symm l)
  have hImage :
      (∃ h : (H).obj K ⟶ (H).obj (OriginalOrdinaryCovariantPuppeConnection.loopObject g Z hZ A),
        h ≫ (H).map ((L).map p) = l) ↔
      (∃ h : (Hᵒ).obj SA.pt ⟶ (Hᵒ).obj (op K),
        (Hᵒ).map (OrdinaryHoChosenPuppe.suspensionMap Pᵒ ιᵒ cᵒ hcᵒ (op Z) hZ.op p.op) ≫ h = eB.symm l) := by
    constructor
    · rintro ⟨h, hh⟩
      refine ⟨eA.symm h, ?_⟩
      apply eB.injective
      rw [OriginalOrdinaryCovariantPuppeConnection.homEquiv_comp,
        OriginalOrdinaryCovariantPuppeConnection.homEquiv_map]
      simpa only [eA, eB, SA, SB, Equiv.apply_symm_apply, OriginalOrdinaryJLoopFunctor.loopFunctor_map] using hh
    · rintro ⟨h, hh⟩
      refine ⟨eA h, ?_⟩
      have he := congrArg eB hh
      rw [OriginalOrdinaryCovariantPuppeConnection.homEquiv_comp,
        OriginalOrdinaryCovariantPuppeConnection.homEquiv_map] at he
      simpa only [eA, eB, SA, SB, Equiv.apply_symm_apply, OriginalOrdinaryJLoopFunctor.loopFunctor_map] using he
  have hKernel :
      (Hᵒ).map (OrdinaryHoChosenPuppe.boundary Pᵒ ιᵒ cᵒ hcᵒ (op Z) hZ.op F) ≫ eB.symm l =
        OrdinaryHoCofiberKernel.nullHom (cᵒ F).pt (op K) ↔
      l ≫ OriginalOrdinaryCovariantPuppeConnection.connectingToCofiber g Z hZ p =
        OriginalOrdinaryCovariantPuppeConnection.null Z hZ K
          (OriginalOrdinaryCovariantPuppeConnection.cofiberObject g Z hZ p) := by
    constructor
    · intro h
      have he := congrArg eC h
      change OriginalOrdinaryCovariantPuppeConnection.homEquiv (cᵒ F).pt (op K)
        ((Hᵒ).map (OrdinaryHoChosenPuppe.boundary Pᵒ ιᵒ cᵒ hcᵒ (op Z) hZ.op F) ≫ eB.symm l) =
        OriginalOrdinaryCovariantPuppeConnection.homEquiv (cᵒ F).pt (op K)
          (OrdinaryHoCofiberKernel.nullHom (cᵒ F).pt (op K)) at he
      rw [OriginalOrdinaryCovariantPuppeConnection.homEquiv_comp,
        OriginalOrdinaryCovariantPuppeConnection.homEquiv_map,
        OriginalOrdinaryCovariantPuppeConnection.homEquiv_null Z hZ] at he
      simpa only [eB, SB, F, Arrow.mk, Equiv.apply_symm_apply,
        OriginalOrdinaryCovariantPuppeConnection.connectingToCofiber,
        OriginalOrdinaryCovariantPuppeConnection.boundary,
        OriginalOrdinaryCovariantPuppeConnection.cofiberObject] using he
    · intro h
      apply eC.injective
      change OriginalOrdinaryCovariantPuppeConnection.homEquiv (cᵒ F).pt (op K)
        ((Hᵒ).map (OrdinaryHoChosenPuppe.boundary Pᵒ ιᵒ cᵒ hcᵒ (op Z) hZ.op F) ≫ eB.symm l) =
        OriginalOrdinaryCovariantPuppeConnection.homEquiv (cᵒ F).pt (op K)
          (OrdinaryHoCofiberKernel.nullHom (cᵒ F).pt (op K))
      rw [OriginalOrdinaryCovariantPuppeConnection.homEquiv_comp,
        OriginalOrdinaryCovariantPuppeConnection.homEquiv_map,
        OriginalOrdinaryCovariantPuppeConnection.homEquiv_null Z hZ]
      simpa only [eB, SB, F, Arrow.mk, Equiv.apply_symm_apply,
        OriginalOrdinaryCovariantPuppeConnection.connectingToCofiber,
        OriginalOrdinaryCovariantPuppeConnection.boundary,
        OriginalOrdinaryCovariantPuppeConnection.cofiberObject] using h
  exact hImage.trans (hOriginal.trans hKernel)

variable (s : PullbackCone p (hZ.isInitial.to B)) (hs : IsLimit s)

/-- The complete raw J-loop image is the connecting null kernel in the SAME actual caller fibre. -/
theorem exact_at_loop_fiber (K : C) [IsCofibrant K]
    (l : (H).obj K ⟶ (H).obj (OriginalOrdinaryCovariantPuppeConnection.loopObject g Z hZ B)) :
    (∃ h : (H).obj K ⟶ (H).obj (OriginalOrdinaryCovariantPuppeConnection.loopObject g Z hZ A),
      h ≫ (H).map ((L).map p) = l) ↔
      l ≫ OriginalOrdinaryCovariantPuppeConnection.connectingToFiber g Z hZ p s hs =
        OriginalOrdinaryCovariantPuppeConnection.null Z hZ K s.pt := by
  let e := OriginalOrdinaryCovariantPuppeConnection.fiberComparisonIso g Z hZ p s hs
  have hNull : OriginalOrdinaryCovariantPuppeConnection.null Z hZ K s.pt ≫ e.hom =
      OriginalOrdinaryCovariantPuppeConnection.null Z hZ K
        (OriginalOrdinaryCovariantPuppeConnection.cofiberObject g Z hZ p) := by
    rw [OriginalOrdinaryHoPuppeConnection.pointNull_eq_hoNull g Z hZ,
      OriginalOrdinaryHoPuppeConnection.pointNull_eq_hoNull g Z hZ,
      OriginalOrdinaryHoFibrationFiberKernel.null_postcomp]
  have hKernel :
      l ≫ OriginalOrdinaryCovariantPuppeConnection.connectingToFiber g Z hZ p s hs =
        OriginalOrdinaryCovariantPuppeConnection.null Z hZ K s.pt ↔
      l ≫ OriginalOrdinaryCovariantPuppeConnection.connectingToCofiber g Z hZ p =
        OriginalOrdinaryCovariantPuppeConnection.null Z hZ K
          (OriginalOrdinaryCovariantPuppeConnection.cofiberObject g Z hZ p) := by
    rw [← cancel_mono e.hom, hNull]
    simp only [OriginalOrdinaryCovariantPuppeConnection.connectingToFiber, e,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (exact_at_loop_cofiber g Z hZ p K l).trans hKernel.symm

variable [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]

local notation "Ω" => DerivedSuspensionLoopAdjunction.loops (GeneratedFunctorialReplacements.fromGeneration g)

/-- Derived ordinary loops enter the SAME caller fibre through the earned raw-loop comparison at its fibrant target. -/
def pointConnecting : (Ω).obj ((H).obj B) ⟶ (H).obj s.pt :=
  (OriginalOrdinaryFibrantJLoopComparison.rawLoopsIso g Z hZ B).hom ≫
    OriginalOrdinaryCovariantPuppeConnection.connectingToFiber g Z hZ p s hs

/-- Both fibrant endpoint comparisons transport the entire original fibration loop-image to its connecting null kernel.
-/
theorem exact_at_derived_loop (K : C) [IsCofibrant K]
    (l : (H).obj K ⟶ (Ω).obj ((H).obj B)) :
    (∃ h : (H).obj K ⟶ (Ω).obj ((H).obj A), h ≫ (Ω).map ((H).map p) = l) ↔
      l ≫ pointConnecting g Z hZ p s hs =
        OriginalOrdinaryCovariantPuppeConnection.null Z hZ K s.pt := by
  let : IsFibrant A := isFibrant_of_fibration p
  let eA := OriginalOrdinaryFibrantJLoopComparison.rawLoopsIso g Z hZ A
  let eB := OriginalOrdinaryFibrantJLoopComparison.rawLoopsIso g Z hZ B
  have hn : (Ω).map ((H).map p) ≫ eB.hom = eA.hom ≫ (H).map ((L).map p) :=
    OriginalOrdinaryFibrantJLoopComparison.rawLoopsIso_naturality g Z hZ p
  have hImage :
      (∃ h : (H).obj K ⟶ (Ω).obj ((H).obj A), h ≫ (Ω).map ((H).map p) = l) ↔
      (∃ h : (H).obj K ⟶ (H).obj ((L).obj A),
        h ≫ (H).map ((L).map p) = l ≫ eB.hom) := by
    constructor
    · rintro ⟨h, hh⟩
      refine ⟨h ≫ eA.hom, ?_⟩
      calc
        (h ≫ eA.hom) ≫ (H).map ((L).map p) =
            h ≫ (Ω).map ((H).map p) ≫ eB.hom := by rw [Category.assoc, ← hn]
        _ = l ≫ eB.hom := by rw [← Category.assoc, hh]
    · rintro ⟨h, hh⟩
      refine ⟨h ≫ eA.inv, ?_⟩
      apply (cancel_mono eB.hom).mp
      calc
        ((h ≫ eA.inv) ≫ (Ω).map ((H).map p)) ≫ eB.hom =
            h ≫ eA.inv ≫ ((Ω).map ((H).map p) ≫ eB.hom) := by simp only [Category.assoc]
        _ = h ≫ eA.inv ≫ (eA.hom ≫ (H).map ((L).map p)) := by rw [hn]
        _ = h ≫ (H).map ((L).map p) := by simp only [Iso.inv_hom_id_assoc]
        _ = l ≫ eB.hom := hh
  have hKernel :
      (l ≫ eB.hom) ≫ OriginalOrdinaryCovariantPuppeConnection.connectingToFiber g Z hZ p s hs =
          OriginalOrdinaryCovariantPuppeConnection.null Z hZ K s.pt ↔
        l ≫ pointConnecting g Z hZ p s hs =
          OriginalOrdinaryCovariantPuppeConnection.null Z hZ K s.pt := by
    simp only [pointConnecting, eB, Category.assoc]
  exact hImage.trans ((exact_at_loop_fiber g Z hZ p s hs K (l ≫ eB.hom)).trans hKernel)

end PointSet

section HomotopyCategory

variable [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
local notation "Ω" => DerivedSuspensionLoopAdjunction.loops (GeneratedFunctorialReplacements.fromGeneration g)
local notation "N" => OriginalOrdinaryHoFibrationFiberKernel.null g Z hZ

variable {X Y : HomotopyCategory C} (f : X ⟶ Y)
  (s : PullbackCone (OriginalOrdinaryHoFibrationSource.projection g f)
    (hZ.isInitial.to (OriginalOrdinaryHoArrowSource.targetObject g Y)))
  (hs : IsLimit s)

local notation "p" => OriginalOrdinaryHoFibrationSource.projection g f
local notation "F" => OriginalOrdinaryHoFibrationFiberKernel.fiber g Z hZ f s
local notation "i" => OriginalOrdinaryHoFibrationFiberKernel.inclusion g Z hZ f s
local notation "δ" => OriginalOrdinaryHoPuppeConnection.connecting g Z hZ f s hs

local instance originalProjectionFibration : Fibration p :=
  OriginalOrdinaryHoFibrationSource.projection_fibration g f

local instance originalTargetFibrant : IsFibrant (OriginalOrdinaryHoArrowSource.targetObject g Y) :=
  OriginalOrdinaryHoArrowSource.target_isFibrant g Y

/-- The ordinary loop image retains BOTH endpoint functions of the original full κ-J fibration Arrow square. -/
theorem projection_loop_square :
    (Ω).map ((H).map p) ≫ (Ω).map (OriginalOrdinaryHoArrowSource.targetIso g Y).hom =
      (Ω).map (OriginalOrdinaryHoFibrationSource.sourceIso g f).hom ≫ (Ω).map f := by
  rw [← (Ω).map_comp, ← (Ω).map_comp, OriginalOrdinaryHoFibrationSource.projection_square]

/-- Normalization identifies the already constructed original connecting word with the SAME fibrant-target raw-loop
word. -/
theorem connecting_eq_normalized :
    δ = ((Ω).mapIso (OriginalOrdinaryHoArrowSource.targetIso g Y)).inv ≫
      pointConnecting g Z hZ p s hs := by
  let B₀ := OriginalOrdinaryHoArrowSource.preimage Y
  let B₁ := OriginalOrdinaryHoArrowSource.targetObject g Y
  have hb : (OriginalOrdinaryHoArrowSource.targetIso g Y).inv =
      (OriginalOrdinaryHoArrowSource.preimageIso Y).inv ≫
        (H).map ((GeneratedFunctorialReplacements.unit g).app B₀) := by
    rfl
  have hu := OriginalOrdinaryFibrantJLoopComparison.rawLoopsIso_unit g Z hZ B₀
  change (Ω).map ((H).map ((GeneratedFunctorialReplacements.unit g).app B₀)) ≫
      (OriginalOrdinaryFibrantJLoopComparison.rawLoopsIso g Z hZ B₁).hom =
    (OriginalOrdinaryJLoopComparison.loopsIsoJ Z hZ g B₀).hom at hu
  change (Ω).map ((OriginalOrdinaryHoArrowSource.preimageIso Y).inv) ≫
      (OriginalOrdinaryJLoopComparison.loopsIsoJ Z hZ g B₀).hom ≫
        OriginalOrdinaryCovariantPuppeConnection.connectingToFiber g Z hZ p s hs =
    (Ω).map ((OriginalOrdinaryHoArrowSource.targetIso g Y).inv) ≫
      ((OriginalOrdinaryFibrantJLoopComparison.rawLoopsIso g Z hZ B₁).hom ≫
        OriginalOrdinaryCovariantPuppeConnection.connectingToFiber g Z hZ p s hs)
  calc
    (Ω).map ((OriginalOrdinaryHoArrowSource.preimageIso Y).inv) ≫
        (OriginalOrdinaryJLoopComparison.loopsIsoJ Z hZ g B₀).hom ≫
          OriginalOrdinaryCovariantPuppeConnection.connectingToFiber g Z hZ p s hs =
      (Ω).map ((OriginalOrdinaryHoArrowSource.preimageIso Y).inv) ≫
        ((Ω).map ((H).map ((GeneratedFunctorialReplacements.unit g).app B₀)) ≫
          (OriginalOrdinaryFibrantJLoopComparison.rawLoopsIso g Z hZ B₁).hom) ≫
            OriginalOrdinaryCovariantPuppeConnection.connectingToFiber g Z hZ p s hs := by
      rw [hu]
    _ = (Ω).map ((OriginalOrdinaryHoArrowSource.targetIso g Y).inv) ≫
        ((OriginalOrdinaryFibrantJLoopComparison.rawLoopsIso g Z hZ B₁).hom ≫
          OriginalOrdinaryCovariantPuppeConnection.connectingToFiber g Z hZ p s hs) := by
      rw [hb, (Ω).map_comp]
      simp only [Category.assoc]

/-- At every Ho coefficient, the complete original ordinary loop image is the already constructed connecting null
kernel. -/
theorem loop_image_iff (T : HomotopyCategory C) (l : T ⟶ (Ω).obj Y) :
    (∃ h : T ⟶ (Ω).obj X, h ≫ (Ω).map f = l) ↔ l ≫ δ = N T F := by
  let K := OriginalOrdinaryHoArrowSource.sourceObject g T
  let e := OriginalOrdinaryHoArrowSource.sourceIso g T
  let : IsCofibrant K := OriginalOrdinaryHoArrowSource.source_isCofibrant g T
  let a := (Ω).mapIso (OriginalOrdinaryHoFibrationSource.sourceIso g f)
  let b := (Ω).mapIso (OriginalOrdinaryHoArrowSource.targetIso g Y)
  have hSquare : (Ω).map ((H).map p) ≫ b.hom = a.hom ≫ (Ω).map f :=
    projection_loop_square g f
  have hImage :
      (∃ h : T ⟶ (Ω).obj X, h ≫ (Ω).map f = l) ↔
      (∃ h : (H).obj K ⟶ (Ω).obj ((H).obj (OriginalOrdinaryHoFibrationSource.sourceObject g f)),
        h ≫ (Ω).map ((H).map p) = (e.hom ≫ l) ≫ b.inv) := by
    constructor
    · rintro ⟨h, hh⟩
      refine ⟨e.hom ≫ h ≫ a.inv, ?_⟩
      apply (cancel_mono b.hom).mp
      have ht := congrArg (fun q => e.hom ≫ q) hh
      simpa only [Category.assoc, hSquare, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
        Category.comp_id] using ht
    · rintro ⟨h, hh⟩
      refine ⟨e.inv ≫ h ≫ a.hom, ?_⟩
      apply (cancel_epi e.hom).mp
      calc
        e.hom ≫ ((e.inv ≫ h ≫ a.hom) ≫ (Ω).map f) =
            (h ≫ (Ω).map ((H).map p)) ≫ b.hom := by
          simp only [Category.assoc, hSquare, Iso.hom_inv_id_assoc]
        _ = ((e.hom ≫ l) ≫ b.inv) ≫ b.hom := by rw [hh]
        _ = e.hom ≫ l := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hn : OriginalOrdinaryCovariantPuppeConnection.null Z hZ K s.pt = e.hom ≫ N T F := by
    rw [OriginalOrdinaryHoPuppeConnection.pointNull_eq_hoNull g Z hZ]
    exact (OriginalOrdinaryHoFibrationFiberKernel.null_precomp g Z hZ e.hom).symm
  have hFac : ((e.hom ≫ l) ≫ b.inv) ≫ pointConnecting g Z hZ p s hs =
      e.hom ≫ (l ≫ δ) := by
    rw [connecting_eq_normalized g Z hZ f s hs]
    simp only [b, Category.assoc]
  have hKernel :
      ((e.hom ≫ l) ≫ b.inv) ≫ pointConnecting g Z hZ p s hs =
          OriginalOrdinaryCovariantPuppeConnection.null Z hZ K s.pt ↔ l ≫ δ = N T F := by
    constructor
    · intro hk
      apply (cancel_epi e.hom).mp
      rw [← hFac, hk, hn]
    · intro hk
      rw [hFac, hk, ← hn]
  exact hImage.trans ((exact_at_derived_loop g Z hZ p s hs K ((e.hom ≫ l) ≫ b.inv)).trans hKernel)

/-- Every full original ordinary loop connecting null map has an actual preimage under the loop image of the SAME
original Ho arrow. -/
def loopLift (T : HomotopyCategory C) (l : T ⟶ (Ω).obj Y) (hl : l ≫ δ = N T F) :
    T ⟶ (Ω).obj X :=
  Classical.choose ((loop_image_iff g Z hZ f s hs T l).mpr hl)

/-- The complete source-built loop lift recovers the entire caller's loop map. -/
theorem loopLift_fac (T : HomotopyCategory C) (l : T ⟶ (Ω).obj Y) (hl : l ≫ δ = N T F) :
    loopLift g Z hZ f s hs T l hl ≫ (Ω).map f = l :=
  Classical.choose_spec ((loop_image_iff g Z hZ f s hs T l).mpr hl)

/-- The actual full ordinary loop image followed by the original connecting map is the same source-built null word. -/
theorem loop_connecting :
    (Ω).map f ≫ δ = N ((Ω).obj X) F :=
  (loop_image_iff g Z hZ f s hs ((Ω).obj X) ((Ω).map f)).mp ⟨𝟙 _, Category.id_comp _⟩

/-- All three adjacent covariant exact positions refer to the SAME original Ho arrow, κ-Q/R/J choices and limiting
caller fibre. -/
theorem three_positions (T : HomotopyCategory C) :
    (∀ l : T ⟶ (Ω).obj Y, (∃ h : T ⟶ (Ω).obj X, h ≫ (Ω).map f = l) ↔
      l ≫ δ = N T F) ∧
    (∀ h : T ⟶ F, (∃ l : T ⟶ (Ω).obj Y, l ≫ δ = h) ↔ h ≫ i = N T X) ∧
    (∀ h : T ⟶ X, (∃ l : T ⟶ F, l ≫ i = h) ↔ h ≫ f = N T Y) :=
  ⟨loop_image_iff g Z hZ f s hs T,
    OriginalOrdinaryHoPuppeConnection.connecting_image_iff g Z hZ f s hs T,
    OriginalOrdinaryHoFibrationFiberKernel.fiber_image_iff g Z hZ f s hs T⟩

/-- Every original coefficient family retains ALL supplied labels in the three actual ordinary covariant exact
positions. -/
theorem generator_three_positions {I : Type*} (G : I → HomotopyCategory C) (k : I) :
    (∀ l : G k ⟶ (Ω).obj Y, (∃ h : G k ⟶ (Ω).obj X, h ≫ (Ω).map f = l) ↔
      l ≫ δ = N (G k) F) ∧
    (∀ h : G k ⟶ F, (∃ l : G k ⟶ (Ω).obj Y, l ≫ δ = h) ↔ h ≫ i = N (G k) X) ∧
    (∀ h : G k ⟶ X, (∃ l : G k ⟶ F, l ≫ i = h) ↔ h ≫ f = N (G k) Y) :=
  three_positions g Z hZ f s hs (G k)

end HomotopyCategory

end HomotopicalAlgebra.OriginalOrdinaryCovariantPuppeThirdPosition
