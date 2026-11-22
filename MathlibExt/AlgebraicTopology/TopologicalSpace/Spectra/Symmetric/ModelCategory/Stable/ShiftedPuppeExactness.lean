/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.Stable.ShiftedHom

/-!
# The actual integer-shifted symmetric Q-cofiber Hom sequence

Each cofiber is the actual chosen Puppe cofiber of the original whole
arrow Q(f). The target leg uses the inverse of the original Q counit;
the connecting function uses the actual chosen Puppe boundary and the
inverse of the original suspension Hom comparison.

All three consecutive image/null-kernel laws are proved at every integer
and every original Omega target. The original input map, Q map, target
leg and connecting map are retained. No exactness record is an input.
The source is MMSS, *Model categories of diagram spectra*, December 30,
1999 manuscript, Theorem 8.12(vi), pages 27–28.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Symmetric.Stable.ShiftedPuppeTests

private abbrev C := Actual.SymmetricCarrier.{u, v}
private abbrev Index := PointedCGWH.SymmetricOperatorIndex.{u, v}

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant


variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private abbrev H := toHomotopyCategory C.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B)
  (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
private abbrev ISusp := OriginalISuspension.suspension (B := B)
  (I := PointedCGWH.SymmetricOperatorIndex.{u, v})
private abbrev QF (F : Arrow C.{u, v}) := Q.mapArrow.obj F
private abbrev CQ := NativeK.CofiberNullity.cofiberQ (B := B)
  (I := PointedCGWH.SymmetricOperatorIndex.{u, v})
private abbrev qIso (X : C.{u, v}) :=
  NativeOmegaRecovery.NativeSymmetricDelooping.epsilonHoIso (B := B) X

local notation "cone" => OriginalICone.cone (B := B)
  (I := Index)
local notation "ι" => OriginalICone.inclusion (B := B)
  (I := Index)
local notation "c" => OriginalISuspension.cocone (B := B)
  (I := Index)
local notation "hc" => OriginalISuspension.coconeIsColimit (B := B)
  (I := Index)

private instance nativeZero : HasZeroObject C.{u, v} := Diagrams.nativeHasZeroObject

private theorem originalQCofibrant (X : C.{u, v}) : IsCofibrant (Q.obj X) :=
  Replacement.isCofibrant_cofibrantReplacement (B := B) X

private theorem originalQArrowLeftCofibrant (F : Arrow C.{u, v}) :
    IsCofibrant (QF F).left := by
  change IsCofibrant (Q.obj F.left)
  exact originalQCofibrant F.left

private theorem originalQArrowRightCofibrant (F : Arrow C.{u, v}) :
    IsCofibrant (QF F).right := by
  change IsCofibrant (Q.obj F.right)
  exact originalQCofibrant F.right

private theorem originalConeCofibration (X : C.{u, v}) : Cofibration ((ι).app X) :=
  (HomotopicalAlgebra.cofibration_iff _).mpr (OriginalICone.inclusion_cofibration X)

attribute [local instance] originalQCofibrant originalQArrowLeftCofibrant
  originalQArrowRightCofibrant originalConeCofibration

private theorem originalConeCollapse_weak (X : C.{u, v}) :
    weakEquivalences C.{u, v}
      (OrdinaryHoChosenPuppe.toZero Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
        ((cone).obj X)) := by
  have h : (OriginalICone.contraction (B := B)).app X =
      OrdinaryHoChosenPuppe.toZero Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
        ((cone).obj X) := Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  exact h ▸ (OriginalICone.contraction_trivialFibration X).2

/-- The actual original target leg of the chosen Q-cofiber, transported by the same Q counit. -/
def targetLegHo (F : Arrow C.{u, v}) : H.{u, v}.obj F.right ⟶ H.{u, v}.obj (CQ.obj F) :=
  (qIso F.right).inv ≫ H.{u, v}.map (c (QF F)).inr

/-- Precomposing by the actual original Q counit recovers the original chosen cofiber target leg. -/
theorem targetLegHo_counit (F : Arrow C.{u, v}) :
    (qIso F.right).hom ≫ targetLegHo (B := B) F = H.{u, v}.map (c (QF F)).inr := by
  change (qIso F.right).hom ≫ ((qIso F.right).inv ≫ _) = _
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The connecting morphism is the image of the same actual chosen Q-cofiber boundary. -/
def boundaryHo (F : Arrow C.{u, v}) :
    H.{u, v}.obj (CQ.obj F) ⟶ H.{u, v}.obj (ISusp.obj (Q.obj F.left)) :=
  H.{u, v}.map (OrdinaryHoChosenPuppe.boundary cone ι c hc
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (QF F))

/-- The original source restriction acts by the unchanged input arrow at every integer degree. -/
def sourceRestriction (q : ℤ) (F : Arrow C.{u, v}) (E : C.{u, v}) :
    ShiftedHom.test (B := B) q F.right E → ShiftedHom.test (B := B) q F.left E :=
  fun g => H.{u, v}.map F.hom ≫ g

/-- The cofiber restriction uses the whole original Q-counit/target-leg comparison. -/
def targetRestriction (q : ℤ) (F : Arrow C.{u, v}) (E : C.{u, v}) :
    ShiftedHom.test (B := B) q (CQ.obj F) E → ShiftedHom.test (B := B) q F.right E :=
  fun g => targetLegHo (B := B) F ≫ g

/-- The degree-changing connecting function uses the actual boundary and original inverse shift. -/
def connecting (q : ℤ) (F : Arrow C.{u, v}) (E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E) :
    ShiftedHom.test (B := B) (q + 1) F.left E → ShiftedHom.test (B := B) q (CQ.obj F) E :=
  fun g => boundaryHo (B := B) F ≫
    (ShiftedHom.suspensionHomEquiv (B := B) q F.left E hE).symm g

/-- The source kernel retains both original Q counits and the unchanged original map. -/
theorem sourceRestriction_Q_kernel_iff (q : ℤ) (F : Arrow C.{u, v}) (E : C.{u, v})
    (g : ShiftedHom.test (B := B) q F.right E) :
    H.{u, v}.map (QF F).hom ≫ ((qIso F.right).hom ≫ g) =
        OrdinaryHoCofiberKernel.nullHom (Q.obj F.left) ((ShiftedTargets.target q).obj E) ↔
      sourceRestriction (B := B) q F E g =
        OrdinaryHoCofiberKernel.nullHom F.left ((ShiftedTargets.target q).obj E) := by
  have hNat : H.{u, v}.map (QF F).hom ≫ (qIso F.right).hom =
      (qIso F.left).hom ≫ H.{u, v}.map F.hom :=
    (Replacement.cofibrantReplacementProjectionIso (B := B)
      (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).hom.naturality F.hom
  have hNull : (qIso F.left).hom ≫
      OrdinaryHoCofiberKernel.nullHom F.left ((ShiftedTargets.target q).obj E) =
        OrdinaryHoCofiberKernel.nullHom (Q.obj F.left) ((ShiftedTargets.target q).obj E) := by
    exact ShiftedHom.nullHom_precomp (B := B) (qIso F.left).hom
  rw [← Category.assoc, hNat, Category.assoc, ← hNull]
  exact cancel_epi (qIso F.left).hom

/-- The target kernel retains the actual chosen target leg and original inverse Q counit. -/
theorem targetRestriction_Q_kernel_iff (q : ℤ) (F : Arrow C.{u, v}) (E : C.{u, v})
    (g : ShiftedHom.test (B := B) q (CQ.obj F) E) :
    targetRestriction (B := B) q F E g =
        OrdinaryHoCofiberKernel.nullHom F.right ((ShiftedTargets.target q).obj E) ↔
      H.{u, v}.map (c (QF F)).inr ≫ g =
        OrdinaryHoCofiberKernel.nullHom (Q.obj F.right) ((ShiftedTargets.target q).obj E) := by
  have hNull : (qIso F.right).hom ≫
      OrdinaryHoCofiberKernel.nullHom F.right ((ShiftedTargets.target q).obj E) =
        OrdinaryHoCofiberKernel.nullHom (Q.obj F.right) ((ShiftedTargets.target q).obj E) := by
    exact ShiftedHom.nullHom_precomp (B := B) (qIso F.right).hom
  constructor
  · intro h
    have h' := congrArg (fun m => (qIso F.right).hom ≫ m) h
    change (qIso F.right).hom ≫ (targetLegHo (B := B) F ≫ g) = _ at h'
    rw [← Category.assoc, targetLegHo_counit, hNull] at h'
    exact h'
  · intro h
    apply (cancel_epi (qIso F.right).hom).mp
    change (qIso F.right).hom ≫ (targetLegHo (B := B) F ≫ g) = _
    rw [← Category.assoc, targetLegHo_counit, hNull]
    exact h

/-- Exactness at the original target holds for every integer and actual Omega target. -/
theorem exact_at_target (q : ℤ) (F : Arrow C.{u, v}) (E : C.{u, v})
    (g : ShiftedHom.test (B := B) q F.right E) :
    (∃ h : ShiftedHom.test (B := B) q (CQ.obj F) E,
      targetRestriction (B := B) q F E h = g) ↔
      sourceRestriction (B := B) q F E g =
        OrdinaryHoCofiberKernel.nullHom F.left ((ShiftedTargets.target q).obj E) := by
  have hExact :
      (∃ h : ShiftedHom.test (B := B) q (CQ.obj F) E,
        H.{u, v}.map (c (QF F)).inr ≫ h = (qIso F.right).hom ≫ g) ↔
      H.{u, v}.map (QF F).hom ≫ ((qIso F.right).hom ≫ g) =
        OrdinaryHoCofiberKernel.nullHom (Q.obj F.left) ((ShiftedTargets.target q).obj E) :=
    OrdinaryHoChosenPuppe.first_exact
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero cone ι c hc (QF F)
      ((ShiftedTargets.target q).obj E) (originalConeCollapse_weak (Q.obj F.left))
      ((qIso F.right).hom ≫ g)
  constructor
  · rintro ⟨h, rfl⟩
    apply (sourceRestriction_Q_kernel_iff (B := B) q F E _).mp
    apply hExact.mp
    refine ⟨h, ?_⟩
    change _ = (qIso F.right).hom ≫ (targetLegHo (B := B) F ≫ h)
    rw [← Category.assoc, targetLegHo_counit]
  · intro h
    obtain ⟨k, hk⟩ := hExact.mpr
      ((sourceRestriction_Q_kernel_iff (B := B) q F E g).mpr h)
    refine ⟨k, ?_⟩
    apply (cancel_epi (qIso F.right).hom).mp
    change (qIso F.right).hom ≫ (targetLegHo (B := B) F ≫ k) = _
    rw [← Category.assoc, targetLegHo_counit]
    exact hk

/-- Exactness at the same original Q-cofiber uses its actual boundary at every integer. -/
theorem exact_at_cofiber (q : ℤ) (F : Arrow C.{u, v}) (E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) q (CQ.obj F) E) :
    (∃ h : ShiftedHom.test (B := B) (q + 1) F.left E,
      connecting (B := B) q F E hE h = g) ↔
      targetRestriction (B := B) q F E g =
        OrdinaryHoCofiberKernel.nullHom F.right ((ShiftedTargets.target q).obj E) := by
  have hExact :
      (∃ h : H.{u, v}.obj (ISusp.obj (Q.obj F.left)) ⟶
        H.{u, v}.obj ((ShiftedTargets.target q).obj E), boundaryHo (B := B) F ≫ h = g) ↔
      H.{u, v}.map (c (QF F)).inr ≫ g =
        OrdinaryHoCofiberKernel.nullHom (Q.obj F.right) ((ShiftedTargets.target q).obj E) :=
    OrdinaryHoChosenPuppe.second_exact
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero cone ι c hc (QF F)
      ((ShiftedTargets.target q).obj E) g
  constructor
  · rintro ⟨h, hh⟩
    apply (targetRestriction_Q_kernel_iff (B := B) q F E g).mpr
    exact hExact.mp ⟨(ShiftedHom.suspensionHomEquiv (B := B) q F.left E hE).symm h, hh⟩
  · intro h
    obtain ⟨k, hk⟩ := hExact.mpr
      ((targetRestriction_Q_kernel_iff (B := B) q F E g).mp h)
    refine ⟨ShiftedHom.suspensionHomEquiv (B := B) q F.left E hE k, ?_⟩
    change boundaryHo (B := B) F ≫
      (ShiftedHom.suspensionHomEquiv (B := B) q F.left E hE).symm
        (ShiftedHom.suspensionHomEquiv (B := B) q F.left E hE k) = g
    rw [Equiv.symm_apply_apply]
    exact hk

/-- Exactness at the shifted original source uses the actual consecutive Puppe boundary law. -/
theorem exact_at_shifted_source (q : ℤ) (F : Arrow C.{u, v}) (E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) (q + 1) F.left E) :
    (∃ h : ShiftedHom.test (B := B) (q + 1) F.right E,
      sourceRestriction (B := B) (q + 1) F E h = g) ↔
      connecting (B := B) q F E hE g =
        OrdinaryHoCofiberKernel.nullHom (CQ.obj F) ((ShiftedTargets.target q).obj E) := by
  have hExact :
      (∃ h : H.{u, v}.obj (ISusp.obj (Q.obj F.right)) ⟶
        H.{u, v}.obj ((ShiftedTargets.target q).obj E),
        H.{u, v}.map (ISusp.map (Q.map F.hom)) ≫ h =
          (ShiftedHom.suspensionHomEquiv (B := B) q F.left E hE).symm g) ↔
      connecting (B := B) q F E hE g =
        OrdinaryHoCofiberKernel.nullHom (CQ.obj F) ((ShiftedTargets.target q).obj E) :=
    OrdinaryHoChosenPuppeHomSequence.third_exact
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero cone ι c hc (QF F)
      ((ShiftedTargets.target q).obj E) (originalConeCollapse_weak (Q.obj F.right))
      ((ShiftedHom.suspensionHomEquiv (B := B) q F.left E hE).symm g)
  constructor
  · rintro ⟨h, hh⟩
    apply hExact.mp
    refine ⟨(ShiftedHom.suspensionHomEquiv (B := B) q F.right E hE).symm h, ?_⟩
    have hNat : (ShiftedHom.suspensionHomEquiv (B := B) q F.left E hE).symm
        (H.{u, v}.map F.hom ≫ h) =
      H.{u, v}.map (ISusp.map (Q.map F.hom)) ≫
        (ShiftedHom.suspensionHomEquiv (B := B) q F.right E hE).symm h :=
      ShiftedHom.suspensionHomEquiv_symm_source (B := B) q F.hom E hE h
    change _ = (ShiftedHom.suspensionHomEquiv (B := B) q F.left E hE).symm g
    rw [← hNat]
    exact congrArg (ShiftedHom.suspensionHomEquiv (B := B) q F.left E hE).symm hh
  · intro h
    obtain ⟨k, hk⟩ := hExact.mpr h
    refine ⟨ShiftedHom.suspensionHomEquiv (B := B) q F.right E hE k, ?_⟩
    change H.{u, v}.map F.hom ≫
      ShiftedHom.suspensionHomEquiv (B := B) q F.right E hE k = g
    rw [← ShiftedHom.suspensionHomEquiv_source (B := B) q F.hom E hE k,
      hk, Equiv.apply_symm_apply]

/-- All three original exactness positions hold simultaneously at every integer degree. -/
theorem three_exact_positions (q : ℤ) (F : Arrow C.{u, v}) (E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E) :
    (∀ g : ShiftedHom.test (B := B) q F.right E,
      (∃ h, targetRestriction (B := B) q F E h = g) ↔
        sourceRestriction (B := B) q F E g =
          OrdinaryHoCofiberKernel.nullHom F.left ((ShiftedTargets.target q).obj E)) ∧
    (∀ g : ShiftedHom.test (B := B) q (CQ.obj F) E,
      (∃ h, connecting (B := B) q F E hE h = g) ↔
        targetRestriction (B := B) q F E g =
          OrdinaryHoCofiberKernel.nullHom F.right ((ShiftedTargets.target q).obj E)) ∧
    (∀ g : ShiftedHom.test (B := B) (q + 1) F.left E,
      (∃ h, sourceRestriction (B := B) (q + 1) F E h = g) ↔
        connecting (B := B) q F E hE g =
          OrdinaryHoCofiberKernel.nullHom (CQ.obj F) ((ShiftedTargets.target q).obj E)) :=
  ⟨exact_at_target (B := B) q F E, exact_at_cofiber (B := B) q F E hE,
    exact_at_shifted_source (B := B) q F E hE⟩

/-- Every original Arrow square retains both full cofiber and suspension boundary actions. -/
theorem boundaryHo_naturality {F G : Arrow C.{u, v}} (φ : F ⟶ G) :
    H.{u, v}.map (CQ.map φ) ≫ boundaryHo (B := B) G =
      boundaryHo (B := B) F ≫ H.{u, v}.map (ISusp.map (Q.map φ.left)) := by
  have h := OrdinaryHoChosenPuppe.boundary_naturality cone ι c hc
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (Q.mapArrow.map φ)
  have hHo := H.{u, v}.congr_map h
  simp only [Functor.map_comp] at hHo
  change H.{u, v}.map (CQ.map φ) ≫ boundaryHo (B := B) G =
    boundaryHo (B := B) F ≫ H.{u, v}.map (ISusp.map (Q.map φ.left)) at hHo
  exact hHo

/-- Every original Arrow square retains both target-leg components after the original Q counit. -/
theorem targetLegHo_naturality {F G : Arrow C.{u, v}} (φ : F ⟶ G) :
    H.{u, v}.map φ.right ≫ targetLegHo (B := B) G =
      targetLegHo (B := B) F ≫ H.{u, v}.map (CQ.map φ) := by
  have hQ : H.{u, v}.map φ.right ≫ (qIso G.right).inv =
      (qIso F.right).inv ≫ H.{u, v}.map (Q.map φ.right) :=
    NativeOmegaRecovery.NativeSymmetricDelooping.epsilonHoIso_inv_naturality (B := B) φ.right
  have hTarget := OrdinaryHoChosenPuppe.cofiberMap_target cone ι c hc (Q.mapArrow.map φ)
  have hTargetHo : H.{u, v}.map (c (QF F)).inr ≫ H.{u, v}.map (CQ.map φ) =
      H.{u, v}.map (Q.map φ.right) ≫ H.{u, v}.map (c (QF G)).inr := by
    have h := H.{u, v}.congr_map hTarget
    simp only [Functor.map_comp] at h
    change H.{u, v}.map (c (QF F)).inr ≫ H.{u, v}.map (CQ.map φ) =
      H.{u, v}.map (Q.map φ.right) ≫ H.{u, v}.map (c (QF G)).inr at h
    exact h
  change H.{u, v}.map φ.right ≫ ((qIso G.right).inv ≫ _) =
    ((qIso F.right).inv ≫ _) ≫ _
  rw [← Category.assoc, hQ, Category.assoc, ← hTargetHo, ← Category.assoc]

/-- The full source restriction commutes with both components of every original Arrow square. -/
theorem sourceRestriction_source (q : ℤ) {F G : Arrow C.{u, v}} (φ : F ⟶ G)
    (E : C.{u, v}) (g : ShiftedHom.test (B := B) q G.right E) :
    sourceRestriction (B := B) q F E (H.{u, v}.map φ.right ≫ g) =
      H.{u, v}.map φ.left ≫ sourceRestriction (B := B) q G E g := by
  have h := H.{u, v}.congr_map φ.w
  simp only [Functor.map_comp] at h
  unfold sourceRestriction
  rw [← Category.assoc, ← h, Category.assoc]

/-- Every original target transformation commutes with the entire source restriction function. -/
theorem sourceRestriction_target (q : ℤ) (F : Arrow C.{u, v}) {E E' : C.{u, v}}
    (t : E ⟶ E') (g : ShiftedHom.test (B := B) q F.right E) :
    sourceRestriction (B := B) q F E'
        (g ≫ H.{u, v}.map ((ShiftedTargets.target q).map t)) =
      sourceRestriction (B := B) q F E g ≫
        H.{u, v}.map ((ShiftedTargets.target q).map t) := by
  exact (Category.assoc _ _ _).symm

/-- The complete cofiber restriction retains the original Arrow target component and Q map. -/
theorem targetRestriction_source (q : ℤ) {F G : Arrow C.{u, v}} (φ : F ⟶ G)
    (E : C.{u, v}) (g : ShiftedHom.test (B := B) q (CQ.obj G) E) :
    targetRestriction (B := B) q F E (H.{u, v}.map (CQ.map φ) ≫ g) =
      H.{u, v}.map φ.right ≫ targetRestriction (B := B) q G E g := by
  unfold targetRestriction
  rw [← Category.assoc, ← targetLegHo_naturality, Category.assoc]

/-- Every original target map commutes with the whole chosen Q-cofiber restriction function. -/
theorem targetRestriction_target (q : ℤ) (F : Arrow C.{u, v}) {E E' : C.{u, v}}
    (t : E ⟶ E') (g : ShiftedHom.test (B := B) q (CQ.obj F) E) :
    targetRestriction (B := B) q F E'
        (g ≫ H.{u, v}.map ((ShiftedTargets.target q).map t)) =
      targetRestriction (B := B) q F E g ≫
        H.{u, v}.map ((ShiftedTargets.target q).map t) := by
  exact (Category.assoc _ _ _).symm

/-- The complete source Arrow action commutes with the full integer connecting function. -/
theorem connecting_source (q : ℤ) {F G : Arrow C.{u, v}} (φ : F ⟶ G)
    (E : C.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) (q + 1) G.left E) :
    connecting (B := B) q F E hE (H.{u, v}.map φ.left ≫ g) =
      H.{u, v}.map (CQ.map φ) ≫ connecting (B := B) q G E hE g := by
  unfold connecting
  rw [ShiftedHom.suspensionHomEquiv_symm_source, ← Category.assoc,
    ← boundaryHo_naturality, Category.assoc]

/-- Every complete Omega target transformation commutes with the integer connecting function. -/
theorem connecting_target (q : ℤ) (F : Arrow C.{u, v}) {E E' : C.{u, v}}
    (hE : Actual.SymmetricIsOmega E) (hE' : Actual.SymmetricIsOmega E') (t : E ⟶ E')
    (g : ShiftedHom.test (B := B) (q + 1) F.left E) :
    connecting (B := B) q F E' hE'
        (g ≫ H.{u, v}.map ((ShiftedTargets.target (q + 1)).map t)) =
      connecting (B := B) q F E hE g ≫ H.{u, v}.map ((ShiftedTargets.target q).map t) := by
  unfold connecting
  rw [ShiftedHom.suspensionHomEquiv_symm_target (B := B) q F.left hE hE' t,
    Category.assoc]

end PointedCGWH.Spectra.Symmetric.Stable.ShiftedPuppeTests
