/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKOriginalFiberComparison

/-!
# The original comparison and the original Q-cofiber boundary

The boundary of the caller's original Q cofiber lands in the original I
suspension of its Q source. The two actual corner/cofiber zigzag maps and
the full resolved Q-fiber suspension isomorphism normalize the existing
resolved boundary equation to that same source.

Every original Arrow and arbitrary chosen-fiber family is retained. The
normalization uses the original counit, its naturality in level Ho and the
actual suspension functor. No boundary equation or comparison is supplied
as an assumption. Integer invertibility and Omega tests are separate results.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
namespace OriginalFiberComparison

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private abbrev BoundaryD := EnrichedFunctorCat PointedCGWH.{u, v} I

attribute [local instance] Native.modelCategory
  Replacement.isCofibrant_cofibrantReplacement Native.allObjectsFibrant

private instance boundaryJFactorization :
    MorphismProperty.HasFunctorialFactorization
      (trivialCofibrations (BoundaryD (I := I))) (fibrations (BoundaryD (I := I))) :=
  (Native.functorialFactorizations (B := B) (A := I)).2

omit B in
private instance boundaryZero : HasZeroObject (BoundaryD (I := I)) :=
  Diagrams.nativeHasZeroObject

local notation "Q" => Replacement.cofibrantReplacement (B := B) (A := I)
local notation "ε" => Replacement.cofibrantReplacementCounit (B := B) (A := I)
local notation "S" => OriginalISuspension.suspension (B := B) (I := I)
local notation "H" => toHomotopyCategory (BoundaryD (I := I))
local notation "cone" => OriginalICone.cone (B := B) (I := I)
local notation "ι" => OriginalICone.inclusion (B := B) (I := I)
local notation "c" => OriginalISuspension.cocone (B := B) (I := I)
local notation "hc" => OriginalISuspension.coconeIsColimit (B := B) (I := I)
local notation "P" => OrdinaryHoChosenFiberMaps.fibrantFibrationProperty
  (C := BoundaryD (I := I))

private theorem boundaryConeCollapseWeak (X : BoundaryD (I := I)) :
    weakEquivalences (BoundaryD (I := I))
      (OrdinaryHoChosenPuppe.toZero Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
        ((cone).obj X)) := by
  have h : (OriginalICone.contraction (B := B)).app X =
      OrdinaryHoChosenPuppe.toZero Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
        ((cone).obj X) := Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  exact h ▸ (OriginalICone.contraction_trivialFibration X).2

private theorem suspensionQMapWeak {X Y : BoundaryD (I := I)} (f : X ⟶ Y)
    (hf : weakEquivalences (BoundaryD (I := I)) f) :
    weakEquivalences (BoundaryD (I := I)) ((S).map ((Q).map f)) := by
  let _ : WeakEquivalence ((Q).map f) := (weakEquivalence_iff _).mpr
    (OrdinaryHoChosenFiberCofiberComparison.ArrowResolution.Q_map_weak
      (Q) (ε) (Replacement.cofibrantReplacementCounit_mem_trivialFibrations (B := B)) f hf)
  exact FiberHomTests.originalISuspensionMap_weak (B := B) ((Q).map f)

private theorem suspensionQInverts :
    (weakEquivalences (BoundaryD (I := I))).IsInvertedBy ((Q) ⋙ (S) ⋙ (H)) :=
  fun _ _ f hf => Localization.inverts (H) _ _ (suspensionQMapWeak (B := B) f hf)

private def suspensionQHoFunctor :
    HomotopyCategory (BoundaryD (I := I)) ⥤ HomotopyCategory (BoundaryD (I := I)) :=
  Localization.Construction.lift ((Q) ⋙ (S) ⋙ (H)) (suspensionQInverts (B := B))

private theorem suspensionQHoFunctor_fac :
    (H) ⋙ suspensionQHoFunctor (B := B) (I := I) = (Q) ⋙ (S) ⋙ (H) :=
  Localization.Construction.fac ((Q) ⋙ (S) ⋙ (H)) (suspensionQInverts (B := B))

private theorem suspensionQMapCongr {X Y : BoundaryD (I := I)} (f g : X ⟶ Y)
    (h : (H).map f = (H).map g) :
    (H).map ((S).map ((Q).map f)) = (H).map ((S).map ((Q).map g)) := by
  have h' := congrArg (fun k => (suspensionQHoFunctor (B := B) (I := I)).map k) h
  change ((H) ⋙ suspensionQHoFunctor (B := B) (I := I)).map f =
    ((H) ⋙ suspensionQHoFunctor (B := B) (I := I)).map g at h'
  rw [suspensionQHoFunctor_fac] at h'
  exact h'

private theorem suspensionMapCongr {X Y : BoundaryD (I := I)} [IsCofibrant X]
    (f g : X ⟶ Y) (h : (H).map f = (H).map g) :
    (H).map ((S).map f) = (H).map ((S).map g) := by
  let _ : IsCofibrant ((𝟭 (BoundaryD (I := I))).obj X) := inferInstanceAs (IsCofibrant X)
  let _ : WeakEquivalence ((ε).app X) := (weakEquivalence_iff _).mpr
    (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (B := B) X)
  let _ : IsIso ((H).map ((S).map ((ε).app X))) :=
    Localization.inverts (H) _ _
      (FiberHomTests.originalISuspensionMap_weak (B := B) ((ε).app X))
  have hf : (H).map ((S).map ((Q).map f)) ≫ (H).map ((S).map ((ε).app Y)) =
      (H).map ((S).map ((ε).app X)) ≫ (H).map ((S).map f) := by
    simpa only [Functor.map_comp, Functor.id_map] using
      (H).congr_map ((S).congr_map ((ε).naturality f))
  have hg : (H).map ((S).map ((Q).map g)) ≫ (H).map ((S).map ((ε).app Y)) =
      (H).map ((S).map ((ε).app X)) ≫ (H).map ((S).map g) := by
    simpa only [Functor.map_comp, Functor.id_map] using
      (H).congr_map ((S).congr_map ((ε).naturality g))
  apply (cancel_epi ((H).map ((S).map ((ε).app X)))).mp
  rw [← hf, ← hg, suspensionQMapCongr (B := B) f g h]

private theorem suspendedCounitCoherence (X : BoundaryD (I := I)) :
    (H).map ((S).map ((Q).map ((ε).app X))) =
      (H).map ((S).map ((ε).app ((Q).obj X))) := by
  let _ : IsIso ((H).map ((ε).app X)) := Localization.inverts (H) _ _
    (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (B := B) X)
  have h : (H).map ((Q).map ((ε).app X)) = (H).map ((ε).app ((Q).obj X)) := by
    apply (cancel_mono ((H).map ((ε).app X))).mp
    have hn := (ε).naturality ((ε).app X)
    change (Q).map ((ε).app X) ≫ (ε).app X =
      (ε).app ((Q).obj X) ≫ (ε).app X at hn
    simpa only [Functor.map_comp] using (H).congr_map hn
  exact suspensionMapCongr (B := B) _ _ h

/-- The literal original chosen Q-cofiber boundary has the original suspended Q source. -/
def originalQCofiberBoundary (F : Arrow (BoundaryD (I := I))) :
    (CofiberNullity.cofiberQ (B := B) (I := I)).obj F ⟶ (S).obj ((Q).obj F.left) :=
  OrdinaryHoChosenPuppe.boundary (cone) (ι) (c) (hc)
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((Q).mapArrow.obj F)

/-- Every complete original Arrow square retains both actual Q-boundary endpoints. -/
@[reassoc]
theorem originalQCofiberBoundary_naturality {F G : Arrow (BoundaryD (I := I))}
    (q : F ⟶ G) :
    (CofiberNullity.cofiberQ (B := B)).map q ≫ originalQCofiberBoundary (B := B) G =
      originalQCofiberBoundary (B := B) F ≫ (S).map ((Q).map q.left) :=
  OrdinaryHoChosenPuppe.boundary_naturality (cone) (ι) (c) (hc)
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((Q).mapArrow.map q)

/-- The complete chosen boundary is natural on the original entire Arrow category. -/
def originalQCofiberBoundaryNatTrans :
    CofiberNullity.cofiberQ (B := B) (I := I) ⟶ Arrow.leftFunc ⋙ (Q) ⋙ (S) where
  app F := originalQCofiberBoundary (B := B) F
  naturality _ _ q := originalQCofiberBoundary_naturality (B := B) q

/-- The entire original cone leg maps to the same chosen suspension cone leg. -/
@[reassoc]
theorem originalQCofiberBoundary_cone (F : Arrow (BoundaryD (I := I))) :
    (c ((Q).mapArrow.obj F)).inl ≫ originalQCofiberBoundary (B := B) F =
      (OrdinaryHoChosenPuppe.suspensionCone (cone) (ι) (c)
        Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((Q).obj F.left)).inl :=
  OrdinaryHoChosenPuppe.boundary_cone (cone) (ι) (c) (hc)
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((Q).mapArrow.obj F)

/-- The entire original target leg retains its zero collapse and chosen suspension zero leg. -/
@[reassoc]
theorem originalQCofiberBoundary_target (F : Arrow (BoundaryD (I := I))) :
    (c ((Q).mapArrow.obj F)).inr ≫ originalQCofiberBoundary (B := B) F =
      OrdinaryHoChosenPuppe.toZero Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
        ((Q).obj F.right) ≫
      (OrdinaryHoChosenPuppe.suspensionCone (cone) (ι) (c)
        Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((Q).obj F.left)).inr :=
  OrdinaryHoChosenPuppe.boundary_target (cone) (ι) (c) (hc)
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((Q).mapArrow.obj F)

/-- The actual resolved cofiber boundary normalizes through Q of the original corner projection. -/
@[reassoc]
theorem QCofiberToResolutionHoIso_boundary (F : Arrow (BoundaryD (I := I))) :
    (QCofiberToResolutionHoIso (B := B) (I := I)).hom.app F ≫
      (H).map (OrdinaryHoChosenPuppe.boundary (cone) (ι) (c) (hc)
        Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((resolution (B := B)).obj F)) ≫
      (H).map ((S).map ((Q).map (pullback.fst F.hom ((ε).app F.right)))) =
        (H).map (originalQCofiberBoundary (B := B) F) := by
  let rF := (resolution (B := B)).obj F
  let tF := (OrdinaryHoChosenFiberCofiberComparison.ArrowResolution.intermediateFunctor
    (Q) (ε)).obj F
  let qQ := OrdinaryHoChosenFiberCofiberComparison.ArrowResolution.intermediateToQ (Q) (ε) F
  let qR := OrdinaryHoChosenFiberCofiberComparison.ArrowResolution.intermediateToResolution
    (Q) (ε) F
  let p := pullback.fst F.hom ((ε).app F.right)
  let j := OrdinaryHoChosenFiberCofiberComparison.ArrowResolution.sourceToCorner (Q) (ε) F
  let A : (H).obj (c tF).pt ⟶ (H).obj (c ((Q).mapArrow.obj F)).pt :=
    (H).map (OrdinaryHoChosenPuppe.cofiberMap (cone) (ι) (c) (hc) qQ)
  let Rmap : (H).obj (c tF).pt ⟶ (H).obj (c rF).pt :=
    (H).map (OrdinaryHoChosenPuppe.cofiberMap (cone) (ι) (c) (hc) qR)
  let eC : (H).obj (c ((Q).mapArrow.obj F)).pt ⟶ (H).obj (c rF).pt :=
    (QCofiberToResolutionHoIso (B := B)).hom.app F
  let β := (H).map (originalQCofiberBoundary (B := B) F)
  let σ := (H).map (OrdinaryHoChosenPuppe.boundary (cone) (ι) (c) (hc)
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero rF)
  let τ := (H).map (OrdinaryHoChosenPuppe.boundary (cone) (ι) (c) (hc)
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero tF)
  let uQ := (H).map ((S).map ((ε).app ((Q).obj F.left)))
  let uR := (H).map ((S).map ((Q).map j))
  let ν := (H).map ((S).map ((Q).map p))
  let _ : IsIso A := Localization.inverts (H) _ _
    (OrdinaryHoChosenFiberCofiberComparison.ArrowResolution.intermediateToQ_cofiber_weak
      Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (Q) (ε)
      (Replacement.isCofibrant_cofibrantReplacement (B := B))
      (Replacement.cofibrantReplacementCounit_mem_trivialFibrations (B := B))
      (cone) (ι) (c) (hc) (fun X _ => OriginalICone.inclusion_cofibration X)
      (fun X _ => boundaryConeCollapseWeak (B := B) X) F)
  have hJoin : A ≫ eC = Rmap :=
    OrdinaryHoChosenFiberHomSequence.OriginalJoin.QCofiberToResolutionHoIso_equation
      Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (Q) (ε)
      (Replacement.isCofibrant_cofibrantReplacement (B := B))
      (Replacement.cofibrantReplacementCounit_mem_trivialFibrations (B := B))
      (cone) (ι) (c) (hc) (fun X _ => OriginalICone.inclusion_cofibration X)
      (fun X _ => boundaryConeCollapseWeak (B := B) X) F
  have hQ : A ≫ β = τ ≫ uQ := by
    have h := (H).congr_map
      (OrdinaryHoChosenPuppe.boundary_naturality (cone) (ι) (c) (hc)
        Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero qQ)
    simp only [Functor.map_comp] at h
    change A ≫ β = τ ≫ uQ at h
    exact h
  have hR : Rmap ≫ σ = τ ≫ uR := by
    have h := (H).congr_map
      (OrdinaryHoChosenPuppe.boundary_naturality (cone) (ι) (c) (hc)
        Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero qR)
    simp only [Functor.map_comp] at h
    change Rmap ≫ σ = τ ≫ uR at h
    exact h
  change eC ≫ σ ≫ ν = β
  apply (cancel_epi A).mp
  calc
    A ≫ (eC ≫ σ ≫ ν) = (A ≫ eC) ≫ σ ≫ ν := by simp only [Category.assoc]
    _ = (Rmap ≫ σ) ≫ ν := by rw [hJoin, Category.assoc]
    _ = (τ ≫ uR) ≫ ν := by rw [hR]
    _ = τ ≫ (H).map ((S).map ((Q).map (j ≫ p))) := by
      simp only [uR, ν, Functor.map_comp, Category.assoc]
    _ = τ ≫ (H).map ((S).map ((Q).map ((ε).app F.left))) := by
      rw [show j ≫ p = (ε).app F.left from
        OrdinaryHoChosenFiberCofiberComparison.ArrowResolution.sourceToCorner_fst (Q) (ε) F]
    _ = τ ≫ uQ := by rw [suspendedCounitCoherence]
    _ = A ≫ β := hQ.symm

variable (a : ∀ F : Arrow (BoundaryD (I := I)), PullbackCone F.hom (Diagrams.zeroTo F.right))
  (ha : ∀ F, IsLimit (a F))

private abbrev genericResolvedSuspensionIso :=
  OrdinaryHoChosenFiberHomSequence.OriginalJoin.resolvedQFiberSuspensionHoIso
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero a ha (Q) (ε)
    (Replacement.isCofibrant_cofibrantReplacement (B := B))
    (Replacement.cofibrantReplacementCounit_mem_trivialFibrations (B := B))
    (cone) (ι) (c) (hc) (fun X _ => OriginalICone.inclusion_cofibration X)
    (fun X _ => boundaryConeCollapseWeak (B := B) X)

/-- The full native resolved Q-fiber suspension isomorphism uses the actual chosen-fiber map. -/
def originalResolvedQFiberSuspensionHoIso :
    (P).ι ⋙ resolution (B := B) ⋙ Diagrams.FiberGeometry.chosenFiberFunctor a ha ⋙
      (Q) ⋙ (S) ⋙ (H) ≅
    (P).ι ⋙ Diagrams.FiberGeometry.chosenFiberFunctor a ha ⋙ (Q) ⋙ (S) ⋙ (H) := by
  let τ := Functor.whiskerLeft (P).ι (Functor.whiskerRight
    (Functor.whiskerRight (resolutionToOriginal (B := B) (I := I))
      (Diagrams.FiberGeometry.chosenFiberFunctor a ha)) ((Q) ⋙ (S) ⋙ (H)))
  let _ : ∀ F, IsIso (τ.app F) := fun F => by
    change IsIso ((H).map ((S).map ((Q).map (Diagrams.FiberGeometry.chosenFiberMap
      ((resolutionToOriginal (B := B)).app F.obj) (a ((resolution (B := B)).obj F.obj))
        (a F.obj) (ha F.obj)))))
    have hmap := congrArg (fun f => (H).map ((S).map ((Q).map f)))
      (chosenFiberMap_eq_generic a ha ((resolutionToOriginal (B := B)).app F.obj))
    exact hmap.symm ▸
      inferInstanceAs (IsIso ((genericResolvedSuspensionIso (B := B) a ha).hom.app F))
  let _ : IsIso τ := NatIso.isIso_of_isIso_app τ
  exact asIso τ

/-- Its full original forward map retains the same original resolved-to-caller Arrow. -/
theorem originalResolvedQFiberSuspensionHoIso_hom (F : (P).FullSubcategory) :
    (originalResolvedQFiberSuspensionHoIso (B := B) a ha).hom.app F =
      (H).map ((S).map ((Q).map (Diagrams.FiberGeometry.chosenFiberMap
        ((resolutionToOriginal (B := B)).app F.obj) (a ((resolution (B := B)).obj F.obj))
          (a F.obj) (ha F.obj)))) := rfl

private theorem resolvedSuspensionHom_eq_generic (F : (P).FullSubcategory) :
    (originalResolvedQFiberSuspensionHoIso (B := B) a ha).hom.app F =
      (genericResolvedSuspensionIso (B := B) a ha).hom.app F := by
  rw [originalResolvedQFiberSuspensionHoIso_hom]
  exact congrArg (fun f => (H).map ((S).map ((Q).map f)))
    (chosenFiberMap_eq_generic a ha ((resolutionToOriginal (B := B)).app F.obj))

/-- Both actual original counit functions normalize the complete resolved fiber projection. -/
theorem originalResolvedQFiberProjection_normalization (F : (P).FullSubcategory) :
    (H).map ((S).map ((ε).app (a ((resolution (B := B)).obj F.obj)).pt ≫
        (a ((resolution (B := B)).obj F.obj)).fst)) ≫
      (H).map ((S).map ((Q).map (pullback.fst F.obj.hom ((ε).app F.obj.right)))) =
    (originalResolvedQFiberSuspensionHoIso (B := B) a ha).hom.app F ≫
      (H).map ((S).map ((Q).map (a F.obj).fst)) := by
  let rF := (resolution (B := B)).obj F.obj
  let p := pullback.fst F.obj.hom ((ε).app F.obj.right)
  let α := Diagrams.FiberGeometry.chosenFiberMap
    ((resolutionToOriginal (B := B)).app F.obj) (a rF) (a F.obj) (ha F.obj)
  have hfst : α ≫ (a F.obj).fst =
      (a rF).fst ≫ (ε).app
        (OrdinaryHoChosenFiberCofiberComparison.ArrowResolution.corner (Q) (ε) F.obj) ≫ p :=
    Diagrams.FiberGeometry.chosenFiberMap_fst _ _ _ _
  have heps : (H).map ((S).map ((ε).app (a rF).pt ≫ (a rF).fst)) =
      (H).map ((S).map ((Q).map (a rF).fst)) ≫
        (H).map ((S).map ((ε).app rF.left)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact (H).congr_map ((S).congr_map ((ε).naturality (a rF).fst).symm)
  rw [originalResolvedQFiberSuspensionHoIso_hom]
  change _ = (H).map ((S).map ((Q).map α)) ≫ (H).map ((S).map ((Q).map (a F.obj).fst))
  conv_rhs => rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, hfst]
  change (H).map ((S).map ((ε).app (a rF).pt ≫ (a rF).fst)) ≫
    (H).map ((S).map ((Q).map p)) = _
  rw [heps]
  change ((H).map ((S).map ((Q).map (a rF).fst)) ≫
      (H).map ((S).map ((ε).app ((Q).obj
        (OrdinaryHoChosenFiberCofiberComparison.ArrowResolution.corner (Q) (ε) F.obj))))) ≫ _ = _
  rw [← suspendedCounitCoherence]
  simp only [Functor.map_comp, Category.assoc]

/-- The original fibrant-fibration comparison has the actual original Q-cofiber boundary law. -/
@[reassoc]
theorem originalFibrationComparison_boundary (F : (P).FullSubcategory) :
    (originalFibrationComparison (B := B) a ha).app F ≫
      (H).map (originalQCofiberBoundary (B := B) F.obj) =
        (H).map ((S).map ((Q).map (a F.obj).fst)) := by
  have h :=
    OrdinaryHoChosenFiberHomSequence.OriginalJoin.originalSuspendedFiberToQCofiber_boundary
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero a ha (Q) (ε)
    (Replacement.isCofibrant_cofibrantReplacement (B := B))
    (Replacement.cofibrantReplacementCounit_mem_trivialFibrations (B := B))
    (cone) (ι) (c) (hc) (fun X _ => OriginalICone.inclusion_cofibration X)
    (fun X _ => boundaryConeCollapseWeak (B := B) X) F
  change (genericResolvedSuspensionIso (B := B) a ha).hom.app F ≫
      (originalFibrationComparison (B := B) a ha).app F ≫
        (QCofiberToResolutionHoIso (B := B)).hom.app F.obj ≫
          (H).map (OrdinaryHoChosenPuppe.boundary (cone) (ι) (c) (hc)
            Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
              ((resolution (B := B)).obj F.obj)) = _ at h
  rw [← resolvedSuspensionHom_eq_generic] at h
  have h' := congrArg (fun m => m ≫
    (H).map ((S).map ((Q).map (pullback.fst F.obj.hom ((ε).app F.obj.right))))) h
  simp only [Category.assoc] at h'
  rw [QCofiberToResolutionHoIso_boundary] at h'
  exact (cancel_epi ((originalResolvedQFiberSuspensionHoIso (B := B) a ha).hom.app F)).mp
    (h'.trans (originalResolvedQFiberProjection_normalization (B := B) a ha F))

/-- On every original K-right Arrow, the same comparison recovers suspension of its Q-fiber leg. -/
@[reassoc]
theorem originalComparison_boundary (s : NativeStabilizationFamily.{u, v} I L)
    (F : (rightArrowProperty s).FullSubcategory) :
    (originalComparison (B := B) a ha s).app F ≫
      (H).map (originalQCofiberBoundary (B := B) F.obj) =
        (H).map ((OriginalISuspension.suspension (B := B)).map ((Q).map (a F.obj).fst)) := by
  change (nativeFibrationComparison (B := B) a ha).app (rightArrowAsFibrantFibration s F) ≫ _ = _
  rw [nativeFibrationComparison_app]
  exact originalFibrationComparison_boundary (B := B) a ha (rightArrowAsFibrantFibration s F)

/-- Every whole original Arrow square retains the boundary's original suspended Q-source map. -/
theorem originalComparison_boundary_naturality (s : NativeStabilizationFamily.{u, v} I L)
    {F G : (rightArrowProperty s).FullSubcategory} (q : F ⟶ G) :
    (H).map ((S).map ((Q).map (Diagrams.FiberGeometry.chosenFiberMap q.hom
        (a F.obj) (a G.obj) (ha G.obj)))) ≫
      ((originalComparison (B := B) a ha s).app G ≫
        (H).map (originalQCofiberBoundary (B := B) G.obj)) =
    ((originalComparison (B := B) a ha s).app F ≫
        (H).map (originalQCofiberBoundary (B := B) F.obj)) ≫
      (H).map ((S).map ((Q).map q.hom.left)) := by
  rw [originalComparison_boundary, originalComparison_boundary]
  simpa only [Functor.map_comp] using (H).congr_map ((S).congr_map ((Q).congr_map
    (Diagrams.FiberGeometry.chosenFiberMap_fst q.hom (a F.obj) (a G.obj) (ha G.obj))))

variable (b : ∀ F : Arrow (BoundaryD (I := I)), PullbackCone F.hom (Diagrams.zeroTo F.right))
  (hb : ∀ F, IsLimit (b F))

/-- The same original boundary and both complete arbitrary chosen-fiber families commute. -/
theorem originalComparison_boundary_choice (s : NativeStabilizationFamily.{u, v} I L)
    (F : (rightArrowProperty s).FullSubcategory) :
    (H).map ((S).map ((Q).map (OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram
        Diagrams.zeroDiagram_isZero a ha b hb F.obj).hom)) ≫
      ((originalComparison (B := B) b hb s).app F ≫
        (H).map (originalQCofiberBoundary (B := B) F.obj)) =
    (originalComparison (B := B) a ha s).app F ≫
      (H).map (originalQCofiberBoundary (B := B) F.obj) := by
  simpa only [Category.assoc] using congrArg (fun m => m ≫
    (H).map (originalQCofiberBoundary (B := B) F.obj))
    (originalComparison_choice (B := B) a ha b hb s F)

/-- The inverse of the same original chosen-fiber isomorphism retains the same boundary equation. -/
theorem originalComparison_boundary_choice_inv (s : NativeStabilizationFamily.{u, v} I L)
    (F : (rightArrowProperty s).FullSubcategory) :
    (H).map ((S).map ((Q).map (OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram
        Diagrams.zeroDiagram_isZero a ha b hb F.obj).inv)) ≫
      ((originalComparison (B := B) a ha s).app F ≫
        (H).map (originalQCofiberBoundary (B := B) F.obj)) =
    (originalComparison (B := B) b hb s).app F ≫
      (H).map (originalQCofiberBoundary (B := B) F.obj) := by
  let e := (H).mapIso ((S).mapIso ((Q).mapIso (OrdinaryHoChosenFiberMaps.choiceIso
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero a ha b hb F.obj)))
  have h := originalComparison_boundary_choice (B := B) a ha b hb s F
  change e.hom ≫ _ = _ at h
  change e.inv ≫ _ = _
  rw [← h, ← Category.assoc, e.inv_hom_id, Category.id_comp]

end OriginalFiberComparison
end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
