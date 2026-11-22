/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationK
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.LevelFibrancy
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyPrecompositionLifting
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Path

/-!
# Actual native K-local products, paths and homotopy Hom

All statements use the literal original K right class and actual native
model. Its constructed local objects are closed under native products and
good level path objects. Actual K-left maps between cofibrant objects give
a bijection on Ho(level) Hom into those local objects. Identification with
the original Omega predicate and stable-model admission remain separate.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat PointedCGWH.EnrichedFunctorMapping
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams
open scoped CGWH.modelCategory MonoidalClosed

private theorem cornerTrivialOfSourceTrivial
    {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
    {C₃ : Type u₃} [Category.{v₃} C₃] [ModelCategory C₃] {G : C₁ᵒᵖ ⥤ C₂ ⥤ C₃}
    {A C : C₁} {X Y : C₂} {j : A ⟶ C} {p : X ⟶ Y}
    (sq : G.PullbackObjObj j p) (hFib : fibrations C₃ sq.π)
    (hX : trivialFibrations C₃ ((G.map j.op).app X))
    (hY : trivialFibrations C₃ ((G.map j.op).app Y)) :
    trivialFibrations C₃ sq.π := by
  have hfst : trivialFibrations C₃ sq.fst :=
    MorphismProperty.of_isPullback sq.isPullback.flip hY
  let _ : WeakEquivalence sq.fst := (HomotopicalAlgebra.weakEquivalence_iff _).mpr hfst.2
  let _ : WeakEquivalence ((G.map j.op).app X) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr hX.2
  have hWeak : WeakEquivalence sq.π := weakEquivalence_of_postcomp_of_fac sq.π_fst
  exact ⟨hFib, (HomotopicalAlgebra.weakEquivalence_iff _).mp hWeak⟩

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : NativeStabilizationFamily.{u, v} I L)
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private abbrev NativeCarrier := EnrichedFunctorCat PointedCGWH.{u, v} I

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- Every original native level trivial fibration is in the full constructed K right class. -/
theorem levelTrivialFibrations_le_right :
    trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) ≤
    (generators s).rlp := by
  intro X Y p hp A C i hi
  have h : (cofibrations (NativeCarrier (I := I))).rlp p := by
    rwa [cofibrations_rlp]
  exact h i (generators_le_cofibrations s i hi)

/-- Locality pulls back through the actual original native level trivial fibrations. -/
theorem local_of_levelTrivialFibration {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)}
    (p : X ⟶ Y) (hp : trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) p)
    (hY : (generators s).rlp (toZero Y)) : (generators s).rlp (toZero X) := by
  have h := (generators s).rlp.comp_mem p (toZero Y) (levelTrivialFibrations_le_right s _ hp) hY
  rwa [toZero_naturality] at h

/-- An actual K-local target makes each original cylinder source mapping arrow trivial fibrant. -/
theorem mappingSource_trivial_of_local (l : L) (X : (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (hX : (generators s).rlp (toZero X)) :
    trivialFibrations PointedCGWH.{u, v} (mapSource (cylinderSource s l) X) := by
  have h := ((lifting_iff s (toZero X)).mp hX).2 l
  exact ((trivialFibrations PointedCGWH.{u, v}).arrow_mk_iso_iff
    (PointedCGWH.NativeMappingZeroSource.cornerArrowIso (cylinderSource s l) X)).mp h

/-- A level fibration between the actual constructed local objects has all original K lifting. -/
theorem levelFibration_between_local_mem_right
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (p : X ⟶ Y)
    (hp : fibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) p)
    (hX : (generators s).rlp (toZero X)) (hY : (generators s).rlp (toZero Y)) :
    (generators s).rlp p := by
  apply (lifting_iff s p).mpr
  refine ⟨hp, fun l => ?_⟩
  let k := cylinderSource s l
  let pb := PointedCGWH.NativeMappingCorner.square k p
  have hFib :=
    HomotopicalAlgebra.EnrichedProjective.Native.CurrentMappingSM7.fibration
      k p ((HomotopicalAlgebra.cofibration_iff _).mp
        (cylinderSource_cofibration s l)) hp pb
  exact cornerTrivialOfSourceTrivial pb hFib
    (mappingSource_trivial_of_local s l X hX) (mappingSource_trivial_of_local s l Y hY)

omit B in
/-- The actual original native product of two constructed local objects is local. -/
theorem product_local (X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (hX : (generators s).rlp (toZero X)) (hY : (generators s).rlp (toZero Y)) :
    (generators s).rlp (toZero (X ⨯ Y)) := by
  have sq : IsPullback (prod.fst : X ⨯ Y ⟶ X) (prod.snd : X ⨯ Y ⟶ Y)
      (toZero X) (toZero Y) := by
    have h := IsPullback.of_isLimit_binaryFan_of_isTerminal
      (limit.isLimit (pair X Y)) (zeroDiagramIsTerminal (A := I))
    have hX : (zeroDiagramIsTerminal (A := I)).from X = toZero X :=
      (zeroDiagramIsTerminal (A := I)).hom_ext _ _
    have hY : (zeroDiagramIsTerminal (A := I)).from Y = toZero Y :=
      (zeroDiagramIsTerminal (A := I)).hom_ext _ _
    rw [hX, hY] at h
    exact h
  have hfst : (generators s).rlp (prod.fst : X ⨯ Y ⟶ X) :=
    MorphismProperty.of_isPullback sq.flip hY
  have h := (generators s).rlp.comp_mem prod.fst (toZero X) hfst hX
  rwa [toZero_naturality] at h

/-- Every actual good level path object of a constructed local target is local. -/
theorem goodPath_local (Z : (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (hZ : (generators s).rlp (toZero Z)) (P : PathObject Z) [P.IsGood] :
    (generators s).rlp (toZero P.P) := by
  let _ : IsFibrant Z := HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant Z
  have hp : trivialFibrations (NativeCarrier (I := I)) P.p₀ :=
    ⟨HomotopicalAlgebra.mem_fibrations _, HomotopicalAlgebra.mem_weakEquivalences _⟩
  exact local_of_levelTrivialFibration s P.p₀ hp hZ

/-- Its same original joint path projection has the full original K right lifting. -/
theorem goodPath_projection_mem_right (Z : (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (hZ : (generators s).rlp (toZero Z)) (P : PathObject Z) [P.IsGood] : (generators s).rlp P.p :=
  levelFibration_between_local_mem_right s P.p (HomotopicalAlgebra.mem_fibrations _)
    (goodPath_local s Z hZ P) (product_local s Z Z hZ hZ)

omit B in
/-- A constructed local object's actual map to the chosen native terminal remains K-right. -/
theorem chosenTerminal_mem_right (Z : (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (hZ : (generators s).rlp (toZero Z)) : (generators s).rlp (terminal.from Z) := by
  let e : zeroDiagram (A := I) ≅ ⊤_ (NativeCarrier (I := I)) :=
    { hom := terminal.from _
      inv := zeroDiagramIsTerminal.from _
      hom_inv_id := zeroDiagramIsTerminal.hom_ext _ _
      inv_hom_id := terminal.hom_ext _ _ }
  let a : Arrow.mk (toZero Z) ≅ Arrow.mk (terminal.from Z) :=
    Arrow.isoMk' _ _ (Iso.refl _) e (terminal.hom_ext _ _)
  exact ((generators s).rlp.arrow_mk_iso_iff a).mp hZ

/-- Original K-left maps induce a bijection of actual native Ho(level) Hom into local targets. -/
theorem left_Ho_precomp_bijective
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y) (hf : (generators s).rlp.llp f)
    [IsCofibrant X] (Z : (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (hZ : (generators s).rlp (toZero Z)) (P : PathObject Z) [P.IsGood] :
    Function.Bijective (fun g :
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Y ⟶
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z =>
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f ≫ g) := by
  let _ : Cofibration f := (HomotopicalAlgebra.cofibration_iff _).mpr
    (left_le_cofibrations s _ hf)
  let _ : IsCofibrant Y := isCofibrant_of_cofibration f
  let _ : IsFibrant Z := HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant Z
  let _ : HasLiftingProperty f (terminal.from Z) := hf _ (chosenTerminal_mem_right s Z hZ)
  let _ : HasLiftingProperty f P.p := hf _ (goodPath_projection_mem_right s Z hZ P)
  exact bijective_Ho_precomp_of_terminal_path_lifting f P

/-- The actual original J/κ/B path functor stays in the constructed K-local objects. -/
theorem originalPath_local (Z : (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (hZ : (generators s).rlp (toZero Z)) :
    (generators s).rlp (toZero ((HomotopicalAlgebra.EnrichedProjective.Native.Path.pathFunctor
      (B := B)).obj Z)) := by
  let P := HomotopicalAlgebra.EnrichedProjective.Native.Path.pathObject (B := B) Z
  let _ : P.IsVeryGood :=
    HomotopicalAlgebra.EnrichedProjective.Native.Path.pathObject_isVeryGood Z
  exact goodPath_local s Z hZ P

/-- Its SAME original J joint endpoint map has every literal K lifting property. -/
theorem originalPath_endpoints_mem_right (Z : (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (hZ : (generators s).rlp (toZero Z)) :
    (generators s).rlp ((HomotopicalAlgebra.EnrichedProjective.Native.Path.endpoints
      (B := B)).app Z) := by
  let P := HomotopicalAlgebra.EnrichedProjective.Native.Path.pathObject (B := B) Z
  let _ : P.IsVeryGood :=
    HomotopicalAlgebra.EnrichedProjective.Native.Path.pathObject_isVeryGood Z
  have he : P.p = (HomotopicalAlgebra.EnrichedProjective.Native.Path.endpoints (B := B)).app Z := by
    apply prod.hom_ext
    · exact prod.lift_fst _ _
    · exact prod.lift_snd _ _
  rw [← he]
  exact goodPath_projection_mem_right s Z hZ P

/-- Actual original K-left maps and original J path give the native Ho(level) Hom bijection. -/
theorem left_Ho_precomp_bijective_originalPath
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y) (hf : (generators s).rlp.llp f)
    [IsCofibrant X] (Z : (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (hZ : (generators s).rlp (toZero Z)) :
    Function.Bijective (fun g :
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Y ⟶
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z =>
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f ≫ g) := by
  let P := HomotopicalAlgebra.EnrichedProjective.Native.Path.pathObject (B := B) Z
  let _ : P.IsVeryGood :=
    HomotopicalAlgebra.EnrichedProjective.Native.Path.pathObject_isVeryGood Z
  exact left_Ho_precomp_bijective s f hf Z hZ P

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
