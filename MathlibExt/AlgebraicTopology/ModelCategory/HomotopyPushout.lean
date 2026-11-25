/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.ProperSpanGluing
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantSpanReplacement
public import MathlibExt.AlgebraicTopology.ModelCategory.Replacement

import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantCube

/-!
# Functorial homotopy pushouts

This file constructs functorial homotopy pushouts of walking spans and compares them with ordinary
span colimits. It also relates the named functorial construction to arbitrary cofibrant span
replacements by an existential weak map over the common colimit.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
variable [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]

private abbrev SpanDiagram := WalkingSpan ⥤ C

private noncomputable def spanFstComposite : SpanDiagram (C := C) ⥤ Arrow C where
  obj F := Arrow.mk
    ((cofibrantReplacementCounit (C := C)).app (F.obj WalkingSpan.zero) ≫
      F.map WalkingSpan.Hom.fst)
  map {F G} η := Arrow.homMk
    ((cofibrantReplacement (C := C)).map (η.app WalkingSpan.zero))
    (η.app WalkingSpan.left) (by
      calc
        (cofibrantReplacement (C := C)).map (η.app WalkingSpan.zero) ≫
              ((cofibrantReplacementCounit (C := C)).app
                (G.obj WalkingSpan.zero) ≫ G.map WalkingSpan.Hom.fst) =
            ((cofibrantReplacement (C := C)).map
                (η.app WalkingSpan.zero) ≫
              (cofibrantReplacementCounit (C := C)).app
                (G.obj WalkingSpan.zero)) ≫ G.map WalkingSpan.Hom.fst :=
          (Category.assoc _ _ _).symm
        _ = ((cofibrantReplacementCounit (C := C)).app
              (F.obj WalkingSpan.zero) ≫ η.app WalkingSpan.zero) ≫
            G.map WalkingSpan.Hom.fst := by
          rw [(cofibrantReplacementCounit (C := C)).naturality
            (η.app WalkingSpan.zero)]
          simp only [Functor.id_map]
        _ = (cofibrantReplacementCounit (C := C)).app
              (F.obj WalkingSpan.zero) ≫
            η.app WalkingSpan.zero ≫ G.map WalkingSpan.Hom.fst :=
          Category.assoc _ _ _
        _ = (cofibrantReplacementCounit (C := C)).app
              (F.obj WalkingSpan.zero) ≫
            F.map WalkingSpan.Hom.fst ≫ η.app WalkingSpan.left := by
          rw [η.naturality WalkingSpan.Hom.fst]
        _ = ((cofibrantReplacementCounit (C := C)).app
              (F.obj WalkingSpan.zero) ≫ F.map WalkingSpan.Hom.fst) ≫
            η.app WalkingSpan.left := (Category.assoc _ _ _).symm)
  map_id F := by
    ext <;> simp
  map_comp η θ := by
    ext <;> simp

private noncomputable def spanSndComposite : SpanDiagram (C := C) ⥤ Arrow C where
  obj F := Arrow.mk
    ((cofibrantReplacementCounit (C := C)).app (F.obj WalkingSpan.zero) ≫
      F.map WalkingSpan.Hom.snd)
  map {F G} η := Arrow.homMk
    ((cofibrantReplacement (C := C)).map (η.app WalkingSpan.zero))
    (η.app WalkingSpan.right) (by
      calc
        (cofibrantReplacement (C := C)).map (η.app WalkingSpan.zero) ≫
              ((cofibrantReplacementCounit (C := C)).app
                (G.obj WalkingSpan.zero) ≫ G.map WalkingSpan.Hom.snd) =
            ((cofibrantReplacement (C := C)).map
                (η.app WalkingSpan.zero) ≫
              (cofibrantReplacementCounit (C := C)).app
                (G.obj WalkingSpan.zero)) ≫ G.map WalkingSpan.Hom.snd :=
          (Category.assoc _ _ _).symm
        _ = ((cofibrantReplacementCounit (C := C)).app
              (F.obj WalkingSpan.zero) ≫ η.app WalkingSpan.zero) ≫
            G.map WalkingSpan.Hom.snd := by
          rw [(cofibrantReplacementCounit (C := C)).naturality
            (η.app WalkingSpan.zero)]
          simp only [Functor.id_map]
        _ = (cofibrantReplacementCounit (C := C)).app
              (F.obj WalkingSpan.zero) ≫
            η.app WalkingSpan.zero ≫ G.map WalkingSpan.Hom.snd :=
          Category.assoc _ _ _
        _ = (cofibrantReplacementCounit (C := C)).app
              (F.obj WalkingSpan.zero) ≫
            F.map WalkingSpan.Hom.snd ≫ η.app WalkingSpan.right := by
          rw [η.naturality WalkingSpan.Hom.snd]
        _ = ((cofibrantReplacementCounit (C := C)).app
              (F.obj WalkingSpan.zero) ≫ F.map WalkingSpan.Hom.snd) ≫
            η.app WalkingSpan.right := (Category.assoc _ _ _).symm)
  map_id F := by
    ext <;> simp
  map_comp η θ := by
    ext <;> simp

set_option backward.isDefEq.respectTransparency false in
private noncomputable def cofibrantSpanReplacementFunctor :
    SpanDiagram (C := C) ⥤ SpanDiagram (C := C) where
  obj F := span
    ((functorialFactorizationData (cofibrations C) (trivialFibrations C)).factorizationData
      (spanFstComposite (C := C) |>.obj F).hom).i
    ((functorialFactorizationData (cofibrations C) (trivialFibrations C)).factorizationData
      (spanSndComposite (C := C) |>.obj F).hom).i
  map {F G} η := spanHomMk
    ((cofibrantReplacement (C := C)).map (η.app WalkingSpan.zero))
    ((functorialFactorizationData (cofibrations C) (trivialFibrations C)).mapZ
        ((spanFstComposite (C := C)).map η))
    ((functorialFactorizationData (cofibrations C) (trivialFibrations C)).mapZ
        ((spanSndComposite (C := C)).map η))
    ((functorialFactorizationData (cofibrations C) (trivialFibrations C)).i_mapZ
        ((spanFstComposite (C := C)).map η))
    ((functorialFactorizationData (cofibrations C) (trivialFibrations C)).i_mapZ
        ((spanSndComposite (C := C)).map η))
  map_id F := by
    ext j
    rcases j with (_ | _ | _)
    · change (cofibrantReplacement (C := C)).map
          ((CategoryStruct.id F).app WalkingSpan.zero) = CategoryStruct.id _
      simp
    · change (functorialFactorizationData (cofibrations C) (trivialFibrations C)).mapZ
          ((spanFstComposite (C := C)).map (CategoryStruct.id F)) =
        CategoryStruct.id _
      rw [← (functorialFactorizationData (cofibrations C) (trivialFibrations C)).mapZ_id]
      exact congrArg (functorialFactorizationData (cofibrations C) (trivialFibrations C)).mapZ
        ((spanFstComposite (C := C)).map_id F)
    · change (functorialFactorizationData (cofibrations C) (trivialFibrations C)).mapZ
          ((spanSndComposite (C := C)).map (CategoryStruct.id F)) =
        CategoryStruct.id _
      rw [← (functorialFactorizationData (cofibrations C) (trivialFibrations C)).mapZ_id]
      exact congrArg (functorialFactorizationData (cofibrations C) (trivialFibrations C)).mapZ
        ((spanSndComposite (C := C)).map_id F)
  map_comp η θ := by
    ext j
    rcases j with (_ | _ | _)
    · change (cofibrantReplacement (C := C)).map
          (η.app WalkingSpan.zero ≫ θ.app WalkingSpan.zero) =
        (cofibrantReplacement (C := C)).map (η.app WalkingSpan.zero) ≫
          (cofibrantReplacement (C := C)).map (θ.app WalkingSpan.zero)
      simp
    · change (functorialFactorizationData (cofibrations C) (trivialFibrations C)).mapZ
          ((spanFstComposite (C := C)).map (η ≫ θ)) =
        (functorialFactorizationData (cofibrations C) (trivialFibrations C)).mapZ
            ((spanFstComposite (C := C)).map η) ≫
          (functorialFactorizationData (cofibrations C) (trivialFibrations C)).mapZ
            ((spanFstComposite (C := C)).map θ)
      rw [Functor.map_comp,
          (functorialFactorizationData (cofibrations C) (trivialFibrations C)).mapZ_comp]
    · change (functorialFactorizationData (cofibrations C) (trivialFibrations C)).mapZ
          ((spanSndComposite (C := C)).map (η ≫ θ)) =
        (functorialFactorizationData (cofibrations C) (trivialFibrations C)).mapZ
            ((spanSndComposite (C := C)).map η) ≫
          (functorialFactorizationData (cofibrations C) (trivialFibrations C)).mapZ
            ((spanSndComposite (C := C)).map θ)
      rw [Functor.map_comp,
          (functorialFactorizationData (cofibrations C) (trivialFibrations C)).mapZ_comp]

private noncomputable def cofibrantSpanReplacementCounit :
    cofibrantSpanReplacementFunctor (C := C) ⟶ 𝟭 (SpanDiagram (C := C)) where
  app F := spanHomMk
    ((cofibrantReplacementCounit (C := C)).app (F.obj WalkingSpan.zero))
    ((functorialFactorizationData (cofibrations C) (trivialFibrations C)).factorizationData
      (spanFstComposite (C := C) |>.obj F).hom).p
    ((functorialFactorizationData (cofibrations C) (trivialFibrations C)).factorizationData
      (spanSndComposite (C := C) |>.obj F).hom).p
    (by
      change ((functorialFactorizationData (cofibrations C) (trivialFibrations C)).factorizationData
          (spanFstComposite (C := C) |>.obj F).hom).i ≫
        ((functorialFactorizationData (cofibrations C) (trivialFibrations C)).factorizationData
          (spanFstComposite (C := C) |>.obj F).hom).p =
        (spanFstComposite (C := C) |>.obj F).hom
      exact (functorialFactorizationData (cofibrations C) (trivialFibrations C)).fac_app)
    (by
      change ((functorialFactorizationData (cofibrations C) (trivialFibrations C)).factorizationData
          (spanSndComposite (C := C) |>.obj F).hom).i ≫
        ((functorialFactorizationData (cofibrations C) (trivialFibrations C)).factorizationData
          (spanSndComposite (C := C) |>.obj F).hom).p =
        (spanSndComposite (C := C) |>.obj F).hom
      exact (functorialFactorizationData (cofibrations C) (trivialFibrations C)).fac_app)
  naturality F G η := by
    ext j
    rcases j with (_ | _ | _)
    · exact (cofibrantReplacementCounit (C := C)).naturality _
    · exact (functorialFactorizationData (cofibrations C) (trivialFibrations C)).mapZ_p
        ((spanFstComposite (C := C)).map η)
    · exact (functorialFactorizationData (cofibrations C) (trivialFibrations C)).mapZ_p
        ((spanSndComposite (C := C)).map η)

private theorem cofibrantSpanReplacement_zero_cofibrant
    (F : SpanDiagram (C := C)) :
    IsCofibrant
      ((cofibrantSpanReplacementFunctor (C := C)).obj F |>.obj WalkingSpan.zero) := by
  change IsCofibrant ((cofibrantReplacement (C := C)).obj (F.obj WalkingSpan.zero))
  infer_instance

private theorem cofibrantSpanReplacement_fst_cofibration
    (F : SpanDiagram (C := C)) :
    Cofibration
      ((cofibrantSpanReplacementFunctor (C := C)).obj F |>.map
        WalkingSpan.Hom.fst) := by
  change Cofibration
    ((functorialFactorizationData (cofibrations C) (trivialFibrations C)).factorizationData
      (spanFstComposite (C := C) |>.obj F).hom).i
  rw [cofibration_iff]
  exact ((functorialFactorizationData (cofibrations C) (trivialFibrations C)).factorizationData
      _).hi

private theorem cofibrantSpanReplacement_snd_cofibration
    (F : SpanDiagram (C := C)) :
    Cofibration
      ((cofibrantSpanReplacementFunctor (C := C)).obj F |>.map
        WalkingSpan.Hom.snd) := by
  change Cofibration
    ((functorialFactorizationData (cofibrations C) (trivialFibrations C)).factorizationData
      (spanSndComposite (C := C) |>.obj F).hom).i
  rw [cofibration_iff]
  exact ((functorialFactorizationData (cofibrations C) (trivialFibrations C)).factorizationData
      _).hi

private theorem cofibrantSpanReplacementCounit_trivialFibration
    (F : SpanDiagram (C := C)) (j : WalkingSpan) :
    trivialFibrations C
      ((cofibrantSpanReplacementCounit (C := C)).app F |>.app j) := by
  rcases j with (_ | _ | _)
  · change trivialFibrations C
      ((cofibrantReplacementCounit (C := C)).app (F.obj WalkingSpan.zero))
    exact mem_trivialFibrations _
  · change trivialFibrations C
      ((functorialFactorizationData (cofibrations C) (trivialFibrations C)).factorizationData
        (spanFstComposite (C := C) |>.obj F).hom).p
    exact ((functorialFactorizationData (cofibrations C) (trivialFibrations C)).factorizationData
        _).hp
  · change trivialFibrations C
      ((functorialFactorizationData (cofibrations C) (trivialFibrations C)).factorizationData
        (spanSndComposite (C := C) |>.obj F).hom).p
    exact ((functorialFactorizationData (cofibrations C) (trivialFibrations C)).factorizationData
        _).hp

private noncomputable def functorialCofibrantSpanReplacement
    (F : SpanDiagram (C := C)) : CofibrantSpanReplacement F :=
  { Q := (cofibrantSpanReplacementFunctor (C := C)).obj F
    counit := (cofibrantSpanReplacementCounit (C := C)).app F
    isCofibrant_zero := cofibrantSpanReplacement_zero_cofibrant F
    cofibration_fst := cofibrantSpanReplacement_fst_cofibration F
    cofibration_snd := cofibrantSpanReplacement_snd_cofibration F
    counit_app_mem_trivialFibrations :=
      cofibrantSpanReplacementCounit_trivialFibration F }

private theorem cofibrantSpanReplacement_map_weakEquivalence
    {F G : SpanDiagram (C := C)} (η : F ⟶ G)
    (hη : ∀ j, WeakEquivalence (η.app j)) (j : WalkingSpan) :
    WeakEquivalence
      ((cofibrantSpanReplacementFunctor (C := C)).map η |>.app j) := by
  have hF := (mem_trivialFibrations_iff _).1
    (cofibrantSpanReplacementCounit_trivialFibration (C := C) F j)
  have hG := (mem_trivialFibrations_iff _).1
    (cofibrantSpanReplacementCounit_trivialFibration (C := C) G j)
  let _ : WeakEquivalence
      ((cofibrantSpanReplacementCounit (C := C)).app F |>.app j) := hF.2
  let _ : WeakEquivalence
      ((cofibrantSpanReplacementCounit (C := C)).app G |>.app j) := hG.2
  let _ : WeakEquivalence (η.app j) := hη j
  have hfac :
      ((cofibrantSpanReplacementFunctor (C := C)).map η |>.app j) ≫
          ((cofibrantSpanReplacementCounit (C := C)).app G |>.app j) =
        ((cofibrantSpanReplacementCounit (C := C)).app F |>.app j) ≫
          η.app j := by
    exact congr_app
      ((cofibrantSpanReplacementCounit (C := C)).naturality η) j
  exact weakEquivalence_of_postcomp_of_fac hfac

private noncomputable def spanColimitIso (F : SpanDiagram (C := C)) :
    colimit F ≅
      pushout (F.map WalkingSpan.Hom.fst) (F.map WalkingSpan.Hom.snd) :=
  HasColimit.isoOfNatIso (diagramIsoSpan F)

omit [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)] in
private theorem spanColimitIso_left (F : SpanDiagram (C := C)) :
    colimit.ι F WalkingSpan.left ≫ (spanColimitIso F).hom =
      pushout.inl (F.map WalkingSpan.Hom.fst)
        (F.map WalkingSpan.Hom.snd) := by
  simp [spanColimitIso]

omit [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)] in
private theorem spanColimitIso_right (F : SpanDiagram (C := C)) :
    colimit.ι F WalkingSpan.right ≫ (spanColimitIso F).hom =
      pushout.inr (F.map WalkingSpan.Hom.fst)
        (F.map WalkingSpan.Hom.snd) := by
  simp [spanColimitIso]

omit [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)] in
private theorem spanColimit_isPushout (F : SpanDiagram (C := C)) :
    IsPushout (F.map WalkingSpan.Hom.fst) (F.map WalkingSpan.Hom.snd)
      (colimit.ι F WalkingSpan.left)
      (colimit.ι F WalkingSpan.right) := by
  apply IsPushout.of_iso
    (IsPushout.of_hasPushout
      (F.map WalkingSpan.Hom.fst) (F.map WalkingSpan.Hom.snd))
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (spanColimitIso F).symm
  · simp
  · simp
  · simpa using
      (Iso.comp_inv_eq (spanColimitIso F)).2 (spanColimitIso_left F).symm
  · simpa using
      (Iso.comp_inv_eq (spanColimitIso F)).2 (spanColimitIso_right F).symm

/-- The colimit of a functorial cofibrant replacement of a span. -/
@[no_expose]
noncomputable def homotopyPushout : (WalkingSpan ⥤ C) ⥤ C :=
  cofibrantSpanReplacementFunctor (C := C) ⋙ colim

/-- The natural comparison from the homotopy pushout to each span's ordinary colimit. -/
@[no_expose]
noncomputable def homotopyPushoutComparison :
    homotopyPushout (C := C) ⟶ colim :=
  { app := fun F => colim.map
      ((cofibrantSpanReplacementCounit (C := C)).app F)
    naturality := fun F G η => by
      change colim.map ((cofibrantSpanReplacementFunctor (C := C)).map η) ≫
          colim.map ((cofibrantSpanReplacementCounit (C := C)).app G) =
        colim.map ((cofibrantSpanReplacementCounit (C := C)).app F) ≫
          colim.map η
      rw [← colim.map_comp, ← colim.map_comp]
      congr 1
      exact (cofibrantSpanReplacementCounit (C := C)).naturality η }

theorem homotopyPushout_map_weakEquivalence
    {F G : WalkingSpan ⥤ C} (η : F ⟶ G)
    (hη : ∀ j, WeakEquivalence (η.app j)) :
    WeakEquivalence ((homotopyPushout (C := C)).map η) := by
  let QF := (cofibrantSpanReplacementFunctor (C := C)).obj F
  let QG := (cofibrantSpanReplacementFunctor (C := C)).obj G
  let ηQ := (cofibrantSpanReplacementFunctor (C := C)).map η
  let _ : Cofibration (QF.map WalkingSpan.Hom.fst) :=
    cofibrantSpanReplacement_fst_cofibration F
  let _ : Cofibration (QG.map WalkingSpan.Hom.fst) :=
    cofibrantSpanReplacement_fst_cofibration G
  let _ : Cofibration (QF.map WalkingSpan.Hom.snd) :=
    cofibrantSpanReplacement_snd_cofibration F
  let _ : Cofibration (QG.map WalkingSpan.Hom.snd) :=
    cofibrantSpanReplacement_snd_cofibration G
  let _ : IsCofibrant (QF.obj WalkingSpan.zero) :=
    cofibrantSpanReplacement_zero_cofibrant F
  let _ : IsCofibrant (QG.obj WalkingSpan.zero) :=
    cofibrantSpanReplacement_zero_cofibrant G
  let _ : IsCofibrant (QF.obj WalkingSpan.right) :=
    isCofibrant_of_cofibration (QF.map WalkingSpan.Hom.snd)
  let _ : IsCofibrant (QG.obj WalkingSpan.right) :=
    isCofibrant_of_cofibration (QG.map WalkingSpan.Hom.snd)
  let _ : WeakEquivalence (ηQ.app WalkingSpan.zero) :=
    cofibrantSpanReplacement_map_weakEquivalence η hη WalkingSpan.zero
  let _ : WeakEquivalence (ηQ.app WalkingSpan.left) :=
    cofibrantSpanReplacement_map_weakEquivalence η hη WalkingSpan.left
  let _ : WeakEquivalence (ηQ.app WalkingSpan.right) :=
    cofibrantSpanReplacement_map_weakEquivalence η hη WalkingSpan.right
  change WeakEquivalence (colim.map ηQ)
  exact weakEquivalence_map_of_isPushouts_of_cofibrant
    (spanColimit_isPushout QF) (spanColimit_isPushout QG)
    (ηQ.naturality WalkingSpan.Hom.fst)
    (ηQ.naturality WalkingSpan.Hom.snd)
    (ι_colimMap ηQ WalkingSpan.left)
    (ι_colimMap ηQ WalkingSpan.right)

theorem weakEquivalence_homotopyPushoutComparison_of_fst
    (F : WalkingSpan ⥤ C)
    [IsCofibrant (F.obj WalkingSpan.zero)]
    [IsCofibrant (F.obj WalkingSpan.right)]
    [Cofibration (F.map WalkingSpan.Hom.fst)] :
    WeakEquivalence ((homotopyPushoutComparison (C := C)).app F) := by
  let QF := (cofibrantSpanReplacementFunctor (C := C)).obj F
  let ε := (cofibrantSpanReplacementCounit (C := C)).app F
  let _ : Cofibration (QF.map WalkingSpan.Hom.fst) :=
    cofibrantSpanReplacement_fst_cofibration F
  let _ : Cofibration (QF.map WalkingSpan.Hom.snd) :=
    cofibrantSpanReplacement_snd_cofibration F
  let _ : IsCofibrant (QF.obj WalkingSpan.zero) :=
    cofibrantSpanReplacement_zero_cofibrant F
  let _ : IsCofibrant (QF.obj WalkingSpan.right) :=
    isCofibrant_of_cofibration (QF.map WalkingSpan.Hom.snd)
  let _ : WeakEquivalence (ε.app WalkingSpan.zero) :=
    ((mem_trivialFibrations_iff _).1
      (cofibrantSpanReplacementCounit_trivialFibration F WalkingSpan.zero)).2
  let _ : WeakEquivalence (ε.app WalkingSpan.left) :=
    ((mem_trivialFibrations_iff _).1
      (cofibrantSpanReplacementCounit_trivialFibration F WalkingSpan.left)).2
  let _ : WeakEquivalence (ε.app WalkingSpan.right) :=
    ((mem_trivialFibrations_iff _).1
      (cofibrantSpanReplacementCounit_trivialFibration F WalkingSpan.right)).2
  change WeakEquivalence (colim.map ε)
  exact weakEquivalence_map_of_isPushouts_of_cofibrant
    (spanColimit_isPushout QF) (spanColimit_isPushout F)
    (ε.naturality WalkingSpan.Hom.fst)
    (ε.naturality WalkingSpan.Hom.snd)
    (ι_colimMap ε WalkingSpan.left)
    (ι_colimMap ε WalkingSpan.right)

theorem weakEquivalence_homotopyPushoutComparison_of_snd
    (F : WalkingSpan ⥤ C)
    [IsCofibrant (F.obj WalkingSpan.zero)]
    [IsCofibrant (F.obj WalkingSpan.left)]
    [Cofibration (F.map WalkingSpan.Hom.snd)] :
    WeakEquivalence ((homotopyPushoutComparison (C := C)).app F) := by
  let QF := (cofibrantSpanReplacementFunctor (C := C)).obj F
  let ε := (cofibrantSpanReplacementCounit (C := C)).app F
  let _ : Cofibration (QF.map WalkingSpan.Hom.fst) :=
    cofibrantSpanReplacement_fst_cofibration F
  let _ : Cofibration (QF.map WalkingSpan.Hom.snd) :=
    cofibrantSpanReplacement_snd_cofibration F
  let _ : IsCofibrant (QF.obj WalkingSpan.zero) :=
    cofibrantSpanReplacement_zero_cofibrant F
  let _ : IsCofibrant (QF.obj WalkingSpan.left) :=
    isCofibrant_of_cofibration (QF.map WalkingSpan.Hom.fst)
  let _ : WeakEquivalence (ε.app WalkingSpan.zero) :=
    ((mem_trivialFibrations_iff _).1
      (cofibrantSpanReplacementCounit_trivialFibration F WalkingSpan.zero)).2
  let _ : WeakEquivalence (ε.app WalkingSpan.left) :=
    ((mem_trivialFibrations_iff _).1
      (cofibrantSpanReplacementCounit_trivialFibration F WalkingSpan.left)).2
  let _ : WeakEquivalence (ε.app WalkingSpan.right) :=
    ((mem_trivialFibrations_iff _).1
      (cofibrantSpanReplacementCounit_trivialFibration F WalkingSpan.right)).2
  change WeakEquivalence (colim.map ε)
  exact weakEquivalence_map_of_isPushouts_of_cofibrant
    (spanColimit_isPushout QF).flip (spanColimit_isPushout F).flip
    (ε.naturality WalkingSpan.Hom.snd)
    (ε.naturality WalkingSpan.Hom.fst)
    (ι_colimMap ε WalkingSpan.right)
    (ι_colimMap ε WalkingSpan.left)

theorem weakEquivalence_homotopyPushoutComparison_of_leftProper_fst
    [IsLeftProper C] (F : WalkingSpan ⥤ C)
    [Cofibration (F.map WalkingSpan.Hom.fst)] :
    WeakEquivalence ((homotopyPushoutComparison (C := C)).app F) := by
  let QF := (cofibrantSpanReplacementFunctor (C := C)).obj F
  let ε := (cofibrantSpanReplacementCounit (C := C)).app F
  let _ : Cofibration (QF.map WalkingSpan.Hom.fst) :=
    cofibrantSpanReplacement_fst_cofibration F
  let _ : WeakEquivalence (ε.app WalkingSpan.zero) :=
    ((mem_trivialFibrations_iff _).1
      (cofibrantSpanReplacementCounit_trivialFibration F WalkingSpan.zero)).2
  let _ : WeakEquivalence (ε.app WalkingSpan.left) :=
    ((mem_trivialFibrations_iff _).1
      (cofibrantSpanReplacementCounit_trivialFibration F WalkingSpan.left)).2
  let _ : WeakEquivalence (ε.app WalkingSpan.right) :=
    ((mem_trivialFibrations_iff _).1
      (cofibrantSpanReplacementCounit_trivialFibration F WalkingSpan.right)).2
  change WeakEquivalence (colim.map ε)
  exact IsLeftProper.weakEquivalence_map_of_isPushouts_of_fst
    (spanColimit_isPushout QF) (spanColimit_isPushout F)
    (ε.naturality WalkingSpan.Hom.fst)
    (ε.naturality WalkingSpan.Hom.snd)
    (ι_colimMap ε WalkingSpan.left)
    (ι_colimMap ε WalkingSpan.right)

theorem weakEquivalence_homotopyPushoutComparison_of_leftProper_snd
    [IsLeftProper C] (F : WalkingSpan ⥤ C)
    [Cofibration (F.map WalkingSpan.Hom.snd)] :
    WeakEquivalence ((homotopyPushoutComparison (C := C)).app F) := by
  let QF := (cofibrantSpanReplacementFunctor (C := C)).obj F
  let ε := (cofibrantSpanReplacementCounit (C := C)).app F
  let _ : Cofibration (QF.map WalkingSpan.Hom.snd) :=
    cofibrantSpanReplacement_snd_cofibration F
  let _ : WeakEquivalence (ε.app WalkingSpan.zero) :=
    ((mem_trivialFibrations_iff _).1
      (cofibrantSpanReplacementCounit_trivialFibration F WalkingSpan.zero)).2
  let _ : WeakEquivalence (ε.app WalkingSpan.left) :=
    ((mem_trivialFibrations_iff _).1
      (cofibrantSpanReplacementCounit_trivialFibration F WalkingSpan.left)).2
  let _ : WeakEquivalence (ε.app WalkingSpan.right) :=
    ((mem_trivialFibrations_iff _).1
      (cofibrantSpanReplacementCounit_trivialFibration F WalkingSpan.right)).2
  change WeakEquivalence (colim.map ε)
  exact IsLeftProper.weakEquivalence_map_of_isPushouts_of_snd
    (spanColimit_isPushout QF) (spanColimit_isPushout F)
    (ε.naturality WalkingSpan.Hom.fst)
    (ε.naturality WalkingSpan.Hom.snd)
    (ι_colimMap ε WalkingSpan.left)
    (ι_colimMap ε WalkingSpan.right)

/-- An arbitrary cofibrant span replacement admits a weak comparison to the
named functorial homotopy pushout over the ordinary span colimit. -/
theorem CofibrantSpanReplacement.exists_weakEquivalence_to_homotopyPushout
    {D : WalkingSpan ⥤ C} (R : CofibrantSpanReplacement D) :
    ∃ f : R.pushoutObj ⟶ (homotopyPushout (C := C)).obj D,
      WeakEquivalence f ∧
        f ≫ (homotopyPushoutComparison (C := C)).app D = R.toPushout := by
  let S := functorialCofibrantSpanReplacement (C := C) D
  obtain ⟨f, hf, hfac⟩ :=
    CofibrantSpanReplacement.exists_weakEquivalence_pushoutObj R S
  refine ⟨f, hf, ?_⟩
  change f ≫ colim.map S.counit = R.toPushout
  exact hfac

/-- Weakness of the named homotopy-pushout comparison is equivalent to
weakness for any arbitrary cofibrant span replacement. -/
theorem CofibrantSpanReplacement.weakEquivalence_homotopyPushoutComparison_iff
    {D : WalkingSpan ⥤ C} (R : CofibrantSpanReplacement D) :
    WeakEquivalence ((homotopyPushoutComparison (C := C)).app D) ↔
      WeakEquivalence R.toPushout := by
  let S := functorialCofibrantSpanReplacement (C := C) D
  have h := CofibrantSpanReplacement.weakEquivalence_toPushout_iff S R
  change WeakEquivalence S.toPushout ↔ WeakEquivalence R.toPushout
  exact h

/-- The chosen cofibrant span replacement functor used by `homotopyPushout`. -/
@[no_expose]
noncomputable abbrev homotopyPushoutReplacementFunctor :
    (WalkingSpan ⥤ C) ⥤ (WalkingSpan ⥤ C) :=
  cofibrantSpanReplacementFunctor (C := C)

/-- The counit of the chosen replacement used by `homotopyPushout`. -/
@[no_expose]
noncomputable abbrev homotopyPushoutReplacementCounit :
    homotopyPushoutReplacementFunctor (C := C) ⟶
      (𝟭 (WalkingSpan ⥤ C) :
        (WalkingSpan ⥤ C) ⥤ (WalkingSpan ⥤ C)) :=
  cofibrantSpanReplacementCounit (C := C)

/-- The actual cofibrant span replacement used by the canonical homotopy pushout. -/
@[no_expose]
noncomputable abbrev homotopyPushoutReplacement (F : WalkingSpan ⥤ C) :
    CofibrantSpanReplacement F :=
  functorialCofibrantSpanReplacement (C := C) F

/-- The replacement record stores the object of the chosen replacement functor. -/
theorem homotopyPushoutReplacement_Q (F : WalkingSpan ⥤ C) :
    (homotopyPushoutReplacement (C := C) F).Q =
      (homotopyPushoutReplacementFunctor (C := C)).obj F := by
  with_unfolding_all rfl

/-- The replacement record stores the component of the chosen replacement counit. -/
theorem homotopyPushoutReplacement_counit (F : WalkingSpan ⥤ C) :
    eqToHom (homotopyPushoutReplacement_Q (C := C) F).symm ≫
      (homotopyPushoutReplacement (C := C) F).counit =
        (homotopyPushoutReplacementCounit (C := C)).app F := by
  with_unfolding_all exact (Category.id_comp
    ((homotopyPushoutReplacementCounit (C := C)).app F))

/-- The canonical homotopy pushout is the colimit of its actual replacement diagram. -/
theorem homotopyPushout_obj (F : WalkingSpan ⥤ C) :
    (homotopyPushout (C := C)).obj F =
      colimit ((homotopyPushoutReplacementFunctor (C := C)).obj F) := by
  with_unfolding_all rfl

/-- The canonical homotopy pushout map is the colimit map of its actual replacement,
with the source and target identified by `homotopyPushout_obj`. -/
theorem homotopyPushout_map {F G : WalkingSpan ⥤ C} (η : F ⟶ G) :
    (homotopyPushout (C := C)).map η =
      eqToHom (homotopyPushout_obj (C := C) F) ≫
        colim.map ((homotopyPushoutReplacementFunctor (C := C)).map η) ≫
          eqToHom (homotopyPushout_obj (C := C) G).symm := by
  with_unfolding_all change (colim.map ((cofibrantSpanReplacementFunctor (C := C)).map η) =
    (𝟙 _) ≫ colim.map ((cofibrantSpanReplacementFunctor (C := C)).map η) ≫ 𝟙 _)
  simp only [Category.id_comp, Category.comp_id]

/-- The canonical homotopy-pushout comparison retains the exact chosen replacement counit. -/
theorem homotopyPushoutComparison_replacement (F : WalkingSpan ⥤ C) :
    eqToHom (homotopyPushout_obj (C := C) F).symm ≫
      (homotopyPushoutComparison (C := C)).app F =
        colim.map ((homotopyPushoutReplacementCounit (C := C)).app F) := by
  with_unfolding_all change ((𝟙 _) ≫
    colim.map ((cofibrantSpanReplacementCounit (C := C)).app F) =
      colim.map ((cofibrantSpanReplacementCounit (C := C)).app F))
  exact Category.id_comp _

end HomotopicalAlgebra
