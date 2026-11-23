/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.AdmissibleMonoSubdivisionIdentity
import MathlibExt.KTheory.Exact.Quillen.QuillenSpanFlagEndpointComposition
import MathlibExt.CategoryTheory.ExactCategory.Bicartesian

/-!
# Composition coherence for admissible-mono subdivision spans

For composable arrows in the Segal subdivision of admissible monomorphisms,
the two consecutive quotient spans compose to the quotient span of the
composite.  The key exact-category calculation identifies the pullback of
the two interval-quotient apices with the long interval quotient.

The raw interval spans are compared before their separately selected source
and target quotients are reconciled.  Passing the resulting span isomorphism
to isomorphism classes proves composition for the quotient-level Quillen
map.  No bundled functor, nerve, realization, or Q/S comparison is introduced.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits Opposite ZeroObject
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace CategoryTheory.Waldhausen.SConstruction.AdmissibleMonoFlag

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- For four nested indices in an admissible-mono flag, the rectangle of
interval quotients is a pullback. -/
theorem intervalRectangle_isPullback {n : ℕ} (F : AdmissibleMonoFlag C n)
    {a b c d : Fin (n + 1)}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    IsPullback
      (F.intervalMap (hab.trans hbc) hbc hab le_rfl)
      (F.intervalMap (hab.trans hbc)
        ((hab.trans hbc).trans hcd) le_rfl hcd)
      (F.intervalMap hbc (hbc.trans hcd) le_rfl hcd)
      (F.intervalMap ((hab.trans hbc).trans hcd)
        (hbc.trans hcd) hab le_rfl) := by
  let _ : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  let wS := F.intervalMap_comp_eq_zero hab hbc
  let wT := F.intervalMap_comp_eq_zero hab (hbc.trans hcd)
  let S : ShortComplex C :=
    ShortComplex.mk
      (F.intervalMap hab (hab.trans hbc) le_rfl hbc)
      (F.intervalMap (hab.trans hbc) hbc hab le_rfl) wS
  let T : ShortComplex C :=
    ShortComplex.mk
      (F.intervalMap hab ((hab.trans hbc).trans hcd)
        le_rfl (hbc.trans hcd))
      (F.intervalMap ((hab.trans hbc).trans hcd)
        (hbc.trans hcd) hab le_rfl) wT
  have hS : IsAdmissibleExact S := by
    simpa only [S, wS] using F.interval_triple_exact hab hbc
  have hT : IsAdmissibleExact T := by
    simpa only [T, wT] using
      F.interval_triple_exact hab (hbc.trans hcd)
  have hFirst :
      F.intervalMap hab (hab.trans hbc) le_rfl hbc ≫
          F.intervalMap (hab.trans hbc)
            ((hab.trans hbc).trans hcd) le_rfl hcd =
        F.intervalMap hab ((hab.trans hbc).trans hcd)
          le_rfl (hbc.trans hcd) := by
    change F.intervalDiagram.map (horiz hab hbc) ≫
        F.intervalDiagram.map (horiz (hab.trans hbc) hcd) =
      F.intervalDiagram.map (horiz hab (hbc.trans hcd))
    rw [← F.intervalDiagram.map_comp]
    apply F.intervalDiagram.congr_map
    apply Arrow.hom_ext <;> exact Subsingleton.elim _ _
  have hRect := F.toStage.property.isPushout_intervalRectangle hab hbc hcd
  change IsPushout
    (F.intervalMap (hab.trans hbc)
      ((hab.trans hbc).trans hcd) le_rfl hcd)
    (F.intervalMap (hab.trans hbc) hbc hab le_rfl)
    (F.intervalMap ((hab.trans hbc).trans hcd)
      (hbc.trans hcd) hab le_rfl)
    (F.intervalMap hbc (hbc.trans hcd) le_rfl hcd) at hRect
  let φ : S ⟶ T :=
    ShortComplex.homMk (𝟙 _)
      (F.intervalMap (hab.trans hbc)
        ((hab.trans hbc).trans hcd) le_rfl hcd)
      (F.intervalMap hbc (hbc.trans hcd) le_rfl hcd)
      (by simpa only [S, T, Category.id_comp] using hFirst.symm)
      (by simpa only [S, T] using hRect.w)
  let _ : IsIso φ.τ₁ := by
    change IsIso (𝟙 _)
    infer_instance
  have hpb :=
    ExactCategory.isPullback_g_of_isAdmissibleExact_of_isIso_left φ hS hT
  change IsPullback
    (F.intervalMap (hab.trans hbc) hbc hab le_rfl)
    (F.intervalMap (hab.trans hbc)
      ((hab.trans hbc).trans hcd) le_rfl hcd)
    (F.intervalMap hbc (hbc.trans hcd) le_rfl hcd)
    (F.intervalMap ((hab.trans hbc).trans hcd)
      (hbc.trans hcd) hab le_rfl) at hpb
  exact hpb

end CategoryTheory.Waldhausen.SConstruction.AdmissibleMonoFlag

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The zero-based flag underlying two composable subdivision arrows. -/
private noncomputable def admissibleMonoSubdivisionCompositionFlag
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) : AdmissibleMonoFlag C 6 where
  chain := (ComposableArrows.mk₅
    z.hom.1.unop.hom w.hom.1.unop.hom x.val.hom
    w.hom.2.hom z.hom.2.hom).precomp (0 : (0 : C) ⟶ _)
  first_isZero := isZero_zero C
  step_admissible := by
    intro i hi
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
      omega
    rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl
    · change IsAdmissibleMono (0 : (0 : C) ⟶ _)
      exact isAdmissibleMono_f
        (isAdmissibleExact_zero_id (C := C) (isZero_zero C))
    · change IsAdmissibleMono z.hom.1.unop.hom
      exact z.hom.1.unop.property
    · change IsAdmissibleMono w.hom.1.unop.hom
      exact w.hom.1.unop.property
    · change IsAdmissibleMono x.val.hom
      exact x.val.property
    · change IsAdmissibleMono w.hom.2.hom
      exact w.hom.2.property
    · change IsAdmissibleMono z.hom.2.hom
      exact z.hom.2.property

private theorem admissibleMonoSubdivisionCompositionFlag_map_three_four
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) (h34 : (3 : Fin 7) ≤ 4) :
    (admissibleMonoSubdivisionCompositionFlag w z).chain.map
        (homOfLE h34) = x.val.hom := by
  rfl

private theorem admissibleMonoSubdivisionCompositionFlag_map_four_five
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) (h45 : (4 : Fin 7) ≤ 5) :
    (admissibleMonoSubdivisionCompositionFlag w z).chain.map
        (homOfLE h45) = w.hom.2.hom := by
  rfl

private theorem admissibleMonoSubdivisionCompositionFlag_map_two_four
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) (h24 : (2 : Fin 7) ≤ 4) :
    (admissibleMonoSubdivisionCompositionFlag w z).chain.map
        (homOfLE h24) = w.hom.1.unop.hom ≫ x.val.hom := by
  change (ComposableArrows.mk₅
    z.hom.1.unop.hom w.hom.1.unop.hom x.val.hom
    w.hom.2.hom z.hom.2.hom).map' 1 3 = _
  rw [ComposableArrows.map'_comp _ 1 2 3]
  dsimp

private theorem admissibleMonoSubdivisionCompositionFlag_map_five_six
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) (h56 : (5 : Fin 7) ≤ 6) :
    (admissibleMonoSubdivisionCompositionFlag w z).chain.map
        (homOfLE h56) = z.hom.2.hom := by
  rfl

private theorem admissibleMonoSubdivisionCompositionFlag_map_four_six
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) (h46 : (4 : Fin 7) ≤ 6) :
    (admissibleMonoSubdivisionCompositionFlag w z).chain.map
        (homOfLE h46) = w.hom.2.hom ≫ z.hom.2.hom := by
  change (ComposableArrows.mk₅
    z.hom.1.unop.hom w.hom.1.unop.hom x.val.hom
    w.hom.2.hom z.hom.2.hom).map' 3 5 = _
  rw [ComposableArrows.map'_comp _ 3 4 5]
  dsimp

private theorem admissibleMonoSubdivisionCompositionFlag_map_two_five
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) (h25 : (2 : Fin 7) ≤ 5) :
    (admissibleMonoSubdivisionCompositionFlag w z).chain.map
        (homOfLE h25) = y.val.hom := by
  change (ComposableArrows.mk₅
    z.hom.1.unop.hom w.hom.1.unop.hom x.val.hom
    w.hom.2.hom z.hom.2.hom).map' 1 4 = y.val.hom
  rw [ComposableArrows.map'_comp _ 1 3 4,
    ComposableArrows.map'_comp _ 1 2 3]
  exact admissibleMonoSubdivisionHom_factorization w

private theorem admissibleMonoSubdivisionCompositionFlag_map_one_six
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) (h16 : (1 : Fin 7) ≤ 6) :
    (admissibleMonoSubdivisionCompositionFlag w z).chain.map
        (homOfLE h16) = t.val.hom := by
  change (ComposableArrows.mk₅
    z.hom.1.unop.hom w.hom.1.unop.hom x.val.hom
    w.hom.2.hom z.hom.2.hom).map' 0 5 = t.val.hom
  rw [ComposableArrows.map'_comp _ 0 4 5,
    ComposableArrows.map'_comp _ 0 3 4,
    ComposableArrows.map'_comp _ 0 2 3,
    ComposableArrows.map'_comp _ 0 1 2]
  dsimp
  calc
    _ = (z.hom.1.unop.hom ≫
        ((w.hom.1.unop.hom ≫ x.val.hom) ≫ w.hom.2.hom)) ≫
          z.hom.2.hom := by simp only [Category.assoc]
    _ = (z.hom.1.unop.hom ≫ y.val.hom) ≫ z.hom.2.hom := by
      rw [admissibleMonoSubdivisionHom_factorization w]
    _ = t.val.hom := admissibleMonoSubdivisionHom_factorization z

private theorem admissibleMonoSubdivisionCompositionFlag_map_one_five
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) (h15 : (1 : Fin 7) ≤ 5) :
    (admissibleMonoSubdivisionCompositionFlag w z).chain.map
        (homOfLE h15) = z.hom.1.unop.hom ≫ y.val.hom := by
  change (ComposableArrows.mk₅
    z.hom.1.unop.hom w.hom.1.unop.hom x.val.hom
    w.hom.2.hom z.hom.2.hom).map' 0 4 = _
  rw [ComposableArrows.map'_comp _ 0 3 4,
    ComposableArrows.map'_comp _ 0 2 3,
    ComposableArrows.map'_comp _ 0 1 2]
  dsimp
  calc
    _ = z.hom.1.unop.hom ≫
        ((w.hom.1.unop.hom ≫ x.val.hom) ≫ w.hom.2.hom) := by
      simp only [Category.assoc]
    _ = _ := congrArg (fun q => z.hom.1.unop.hom ≫ q)
      (admissibleMonoSubdivisionHom_factorization w)

private theorem admissibleMonoSubdivisionCompositionFlag_map_one_four
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) (h14 : (1 : Fin 7) ≤ 4) :
    (admissibleMonoSubdivisionCompositionFlag w z).chain.map
        (homOfLE h14) =
      (z.hom.1.unop.hom ≫ w.hom.1.unop.hom) ≫ x.val.hom := by
  change (ComposableArrows.mk₅
    z.hom.1.unop.hom w.hom.1.unop.hom x.val.hom
    w.hom.2.hom z.hom.2.hom).map' 0 3 = _
  rw [ComposableArrows.map'_comp _ 0 2 3,
    ComposableArrows.map'_comp _ 0 1 2]
  dsimp

private theorem admissibleMonoSubdivisionComposition_comp_left
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) :
    (w ≫ z).hom.1.unop.hom =
      z.hom.1.unop.hom ≫ w.hom.1.unop.hom := by
  rfl

private theorem admissibleMonoSubdivisionComposition_comp_right
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) :
    (w ≫ z).hom.2.hom = w.hom.2.hom ≫ z.hom.2.hom := by
  rfl

/-- Raw combined-flag span representing the first subdivision arrow. -/
private noncomputable def admissibleMonoSubdivisionCompositionLeftRawSpan
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) :
    let F := admissibleMonoSubdivisionCompositionFlag w z
    QuillenSpan
      (F.intervalQuotient (3 : Fin 7) (4 : Fin 7) (by decide))
      (F.intervalQuotient (2 : Fin 7) (5 : Fin 7) (by decide)) := by
  let F := admissibleMonoSubdivisionCompositionFlag w z
  exact F.intervalQuillenSpan
    (show (2 : Fin 7) ≤ 3 by decide)
    (show (3 : Fin 7) ≤ 4 by decide)
    (show (4 : Fin 7) ≤ 5 by decide)

/-- Raw combined-flag span representing the second subdivision arrow. -/
private noncomputable def admissibleMonoSubdivisionCompositionRightRawSpan
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) :
    let F := admissibleMonoSubdivisionCompositionFlag w z
    QuillenSpan
      (F.intervalQuotient (2 : Fin 7) (5 : Fin 7) (by decide))
      (F.intervalQuotient (1 : Fin 7) (6 : Fin 7) (by decide)) := by
  let F := admissibleMonoSubdivisionCompositionFlag w z
  exact F.intervalQuillenSpan
    (show (1 : Fin 7) ≤ 2 by decide)
    (show (2 : Fin 7) ≤ 5 by decide)
    (show (5 : Fin 7) ≤ 6 by decide)

/-- Raw combined-flag span representing the composite subdivision arrow. -/
private noncomputable def admissibleMonoSubdivisionCompositionLongRawSpan
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) :
    let F := admissibleMonoSubdivisionCompositionFlag w z
    QuillenSpan
      (F.intervalQuotient (3 : Fin 7) (4 : Fin 7) (by decide))
      (F.intervalQuotient (1 : Fin 7) (6 : Fin 7) (by decide)) := by
  let F := admissibleMonoSubdivisionCompositionFlag w z
  exact F.intervalQuillenSpan
    (show (1 : Fin 7) ≤ 3 by decide)
    (show (3 : Fin 7) ≤ 4 by decide)
    (show (4 : Fin 7) ≤ 6 by decide)

/-- Before endpoint quotients are transported to their separately selected
models, the long combined-flag span is the pullback composite of the two
short combined-flag spans. -/
private noncomputable def
    admissibleMonoSubdivisionCompositionRawSpanCompIso
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) :
    admissibleMonoSubdivisionCompositionLongRawSpan w z ≅
      Span.comp
        (admissibleMonoSubdivisionCompositionLeftRawSpan w z)
        (admissibleMonoSubdivisionCompositionRightRawSpan w z) := by
  let F := admissibleMonoSubdivisionCompositionFlag w z
  let h12 : (1 : Fin 7) ≤ 2 := by decide
  let h23 : (2 : Fin 7) ≤ 3 := by decide
  let h34 : (3 : Fin 7) ≤ 4 := by decide
  let h45 : (4 : Fin 7) ≤ 5 := by decide
  let h56 : (5 : Fin 7) ≤ 6 := by decide
  let h13 := h12.trans h23
  let h24 := h23.trans h34
  let h35 := h34.trans h45
  let h46 := h45.trans h56
  let h14 := h13.trans h34
  let h25 := h24.trans h45
  let h15 := h14.trans h45
  let h16 := h15.trans h56
  let W := F.intervalQuillenSpan h23 h34 h45
  let Z := F.intervalQuillenSpan h12 h25 h56
  let L := F.intervalQuillenSpan h13 h34 h46
  have hpb := F.intervalRectangle_isPullback h12 h24 h45
  have hpbWZ : IsPullback
      (F.intervalMap h14 h24 h12 le_rfl)
      (F.intervalMap h14 h15 le_rfl h45) W.r Z.l := by
    simpa only [W, Z, AdmissibleMonoFlag.intervalQuillenSpan_l,
      AdmissibleMonoFlag.intervalQuillenSpan_r] using hpb
  letI : HasPullback W.r Z.l := hpbWZ.hasPullback
  have hVert :
      F.intervalMap h14 h24 h12 le_rfl ≫
          F.intervalMap h24 h34 h23 le_rfl =
        F.intervalMap h14 h34 h13 le_rfl := by
    change F.intervalDiagram.map (vert h12 h24) ≫
        F.intervalDiagram.map (vert h23 h34) =
      F.intervalDiagram.map (vert h13 h34)
    rw [← F.intervalDiagram.map_comp]
    apply F.intervalDiagram.congr_map
    apply Arrow.hom_ext <;> exact Subsingleton.elim _ _
  have hHoriz :
      F.intervalMap h14 h15 le_rfl h45 ≫
          F.intervalMap h15 h16 le_rfl h56 =
        F.intervalMap h14 h16 le_rfl h46 := by
    change F.intervalDiagram.map (horiz h14 h45) ≫
        F.intervalDiagram.map (horiz h15 h56) =
      F.intervalDiagram.map (horiz h14 h46)
    rw [← F.intervalDiagram.map_comp]
    apply F.intervalDiagram.congr_map
    apply Arrow.hom_ext <;> exact Subsingleton.elim _ _
  change L ≅ Span.comp W Z
  refine Span.mkIso hpbWZ.isoPullback ?_ ?_
  · change hpbWZ.isoPullback.hom ≫
        (pullback.fst W.r Z.l ≫ W.l) = L.l
    rw [← Category.assoc, hpbWZ.isoPullback_hom_fst]
    exact hVert
  · change hpbWZ.isoPullback.hom ≫
        (pullback.snd W.r Z.l ≫ Z.r) = L.r
    rw [← Category.assoc, hpbWZ.isoPullback_hom_snd]
    exact hHoriz

/-- Quotient projection from the target of the source admissible mono to the
apex of the subdivision span of an arbitrary arrow. -/
private noncomputable def admissibleMonoSubdivisionCompositionApexπ
    {x y : AdmissibleMonoSubdivision (C := C)} (w : x ⟶ y) :
    x.obj.2.obj ⟶ (admissibleMonoSubdivisionQuillenSpan w).apex := by
  let a := w.hom.1.unop
  let b := w.hom.2
  let F := AdmissibleMonoFlag.admissibleMonoTripleFlag
    a.hom a.property x.val.hom x.val.property b.hom b.property
  let h12 : (1 : Fin 5) ≤ (2 : Fin 5) := by decide
  let h23 : (2 : Fin 5) ≤ (3 : Fin 5) := by decide
  let h34 : (3 : Fin 5) ≤ (4 : Fin 5) := by decide
  let h13 := h12.trans h23
  let eApex := F.intervalQuillenSpan_apex h12 h23 h34
  change x.obj.2.obj ⟶ (F.intervalQuillenSpan h12 h23 h34).apex
  exact F.intervalπ (1 : Fin 5) (3 : Fin 5) h13 ≫
    eqToHom eApex.symm

/-- The apex projection followed by the left leg of an arbitrary
subdivision span is the selected source quotient projection. -/
@[reassoc]
private theorem admissibleMonoSubdivisionCompositionApexπ_l
    {x y : AdmissibleMonoSubdivision (C := C)} (w : x ⟶ y) :
    admissibleMonoSubdivisionCompositionApexπ w ≫
        (admissibleMonoSubdivisionQuillenSpan w).l =
      AdmissibleMonoFlag.admissibleMonoQuotientπ
        x.val.hom x.val.property := by
  let F := AdmissibleMonoFlag.admissibleMonoTripleFlag
    w.hom.1.unop.hom w.hom.1.unop.property
    x.val.hom x.val.property w.hom.2.hom w.hom.2.property
  let h12 : (1 : Fin 5) ≤ (2 : Fin 5) := by decide
  let h23 : (2 : Fin 5) ≤ (3 : Fin 5) := by decide
  let h34 : (3 : Fin 5) ≤ (4 : Fin 5) := by decide
  let h13 := h12.trans h23
  have hmap : F.chain.map (homOfLE (le_rfl : (3 : Fin 5) ≤ 3)) =
      𝟙 (F.chain.obj (3 : Fin 5)) := by
    rw [Subsingleton.elim (homOfLE _) (𝟙 _), F.chain.map_id]
  have hSource :=
    AdmissibleMonoFlag.admissibleMonoTripleSourceIso_projection
      w.hom.1.unop.hom w.hom.1.unop.property
      x.val.hom x.val.property w.hom.2.hom w.hom.2.property
  unfold admissibleMonoSubdivisionCompositionApexπ
  unfold admissibleMonoSubdivisionQuillenSpan
  dsimp only
  simp only [AdmissibleMonoFlag.intervalQuillenSpan_apex, eqToHom_refl,
    id_eq, QuillenSpan.endpointTransport_l, Iso.refl_hom,
    Category.comp_id]
  unfold AdmissibleMonoFlag.admissibleMonoTripleQuillenSpan
  simp only [QuillenSpan.endpointTransport_l]
  unfold AdmissibleMonoFlag.admissibleMonoTripleIntervalSpan
  dsimp only
  simp only [AdmissibleMonoFlag.intervalQuillenSpan_l]
  rw [F.intervalπ_naturality_assoc h13 h23 h12 le_rfl, hmap,
    Category.id_comp]
  simpa only using hSource

/-- The apex projection followed by the right leg of an arbitrary
subdivision span is the forward target map followed by the selected target
quotient projection. -/
@[reassoc]
private theorem admissibleMonoSubdivisionCompositionApexπ_r
    {x y : AdmissibleMonoSubdivision (C := C)} (w : x ⟶ y) :
    admissibleMonoSubdivisionCompositionApexπ w ≫
        (admissibleMonoSubdivisionQuillenSpan w).r =
      w.hom.2.hom ≫ AdmissibleMonoFlag.admissibleMonoQuotientπ
        y.val.hom y.val.property := by
  let F := AdmissibleMonoFlag.admissibleMonoTripleFlag
    w.hom.1.unop.hom w.hom.1.unop.property
    x.val.hom x.val.property w.hom.2.hom w.hom.2.property
  let h12 : (1 : Fin 5) ≤ (2 : Fin 5) := by decide
  let h23 : (2 : Fin 5) ≤ (3 : Fin 5) := by decide
  let h34 : (3 : Fin 5) ≤ (4 : Fin 5) := by decide
  let h13 := h12.trans h23
  let h14 := h13.trans h34
  have hmap : F.chain.map (homOfLE h34) = w.hom.2.hom := by
    rfl
  have hTarget :=
    AdmissibleMonoFlag.admissibleMonoTripleTargetIso_projection
      w.hom.1.unop.hom w.hom.1.unop.property
      x.val.hom x.val.property w.hom.2.hom w.hom.2.property
  let hcomp :=
    AdmissibleMonoFlag.admissibleMonoTriple_comp_admissible
      w.hom.1.unop.hom w.hom.1.unop.property
      x.val.hom x.val.property w.hom.2.hom w.hom.2.property
  let eTarget := AdmissibleMonoFlag.admissibleMonoTripleTargetIso
    w.hom.1.unop.hom w.hom.1.unop.property
    x.val.hom x.val.property w.hom.2.hom w.hom.2.property
  let eEqual := AdmissibleMonoFlag.admissibleMonoQuotientIsoOfEq
    hcomp y.val.property (admissibleMonoSubdivisionHom_factorization w)
  have hEqualQuotient :=
    AdmissibleMonoFlag.admissibleMonoQuotientπ_isoOfEq_hom
      hcomp y.val.property (admissibleMonoSubdivisionHom_factorization w)
  have hTargetSelected :
      F.intervalπ (1 : Fin 5) (4 : Fin 5) h14 ≫ eTarget.hom =
        AdmissibleMonoFlag.admissibleMonoQuotientπ
          ((w.hom.1.unop.hom ≫ x.val.hom) ≫ w.hom.2.hom) hcomp := by
    simpa only [eTarget, eqToIso_refl, Iso.refl_hom,
      Category.id_comp] using hTarget
  unfold admissibleMonoSubdivisionCompositionApexπ
  unfold admissibleMonoSubdivisionQuillenSpan
  dsimp only
  simp only [AdmissibleMonoFlag.intervalQuillenSpan_apex, eqToHom_refl,
    id_eq, QuillenSpan.endpointTransport_r, Category.comp_id]
  unfold AdmissibleMonoFlag.admissibleMonoTripleQuillenSpan
  simp only [QuillenSpan.endpointTransport_r, Category.assoc]
  unfold AdmissibleMonoFlag.admissibleMonoTripleIntervalSpan
  dsimp only
  simp only [AdmissibleMonoFlag.intervalQuillenSpan_r]
  rw [F.intervalπ_naturality_assoc h13 h14 le_rfl h34, hmap]
  change w.hom.2.hom ≫ F.intervalπ (1 : Fin 5) (4 : Fin 5) h14 ≫
      eTarget.hom ≫ eEqual.hom = _
  calc
    _ = w.hom.2.hom ≫
        ((F.intervalπ (1 : Fin 5) (4 : Fin 5) h14 ≫ eTarget.hom) ≫
          eEqual.hom) := by simp only [Category.assoc]
    _ = w.hom.2.hom ≫
        (AdmissibleMonoFlag.admissibleMonoQuotientπ
            ((w.hom.1.unop.hom ≫ x.val.hom) ≫ w.hom.2.hom) hcomp ≫
          eEqual.hom) := by rw [hTargetSelected]
    _ = _ := congrArg (fun q => w.hom.2.hom ≫ q) hEqualQuotient

@[reassoc (attr := simp)]
private theorem admissibleMonoSubdivisionComposition_comp_apexπ
    {x y : AdmissibleMonoSubdivision (C := C)} (w : x ⟶ y) :
    (w.hom.1.unop.hom ≫ x.val.hom) ≫
      admissibleMonoSubdivisionCompositionApexπ w = 0 := by
  let F := AdmissibleMonoFlag.admissibleMonoTripleFlag
    w.hom.1.unop.hom w.hom.1.unop.property
    x.val.hom x.val.property w.hom.2.hom w.hom.2.property
  let h12 : (1 : Fin 5) ≤ (2 : Fin 5) := by decide
  let h23 : (2 : Fin 5) ≤ (3 : Fin 5) := by decide
  let h34 : (3 : Fin 5) ≤ (4 : Fin 5) := by decide
  let h13 := h12.trans h23
  have hzero := F.interval_comp_π (1 : Fin 5) (3 : Fin 5) h13
  have hmap : F.chain.map (homOfLE h13) =
      w.hom.1.unop.hom ≫ x.val.hom := by
    change (ComposableArrows.mk₃ w.hom.1.unop.hom x.val.hom
      w.hom.2.hom).map' 0 2 = _
    rw [ComposableArrows.map'_comp _ 0 1 2]
    rfl
  unfold admissibleMonoSubdivisionCompositionApexπ
  dsimp only
  simp only [id_eq]
  rw [← Category.assoc, ← hmap, hzero, zero_comp]

private theorem admissibleMonoSubdivisionComposition_apexπ_exact
    {x y : AdmissibleMonoSubdivision (C := C)} (w : x ⟶ y) :
    IsAdmissibleExact
      (ShortComplex.mk (w.hom.1.unop.hom ≫ x.val.hom)
        (admissibleMonoSubdivisionCompositionApexπ w)
        (admissibleMonoSubdivisionComposition_comp_apexπ w)) := by
  let F := AdmissibleMonoFlag.admissibleMonoTripleFlag
    w.hom.1.unop.hom w.hom.1.unop.property
    x.val.hom x.val.property w.hom.2.hom w.hom.2.property
  let h12 : (1 : Fin 5) ≤ (2 : Fin 5) := by decide
  let h23 : (2 : Fin 5) ≤ (3 : Fin 5) := by decide
  let h34 : (3 : Fin 5) ≤ (4 : Fin 5) := by decide
  let h13 := h12.trans h23
  have hmap : F.chain.map (homOfLE h13) =
      w.hom.1.unop.hom ≫ x.val.hom := by
    change (ComposableArrows.mk₃ w.hom.1.unop.hom x.val.hom
      w.hom.2.hom).map' 0 2 = _
    rw [ComposableArrows.map'_comp _ 0 1 2]
    rfl
  let f := w.hom.1.unop.hom ≫ x.val.hom
  let q := F.intervalπ (1 : Fin 5) (3 : Fin 5) h13
  have wq : f ≫ q = 0 := by
    simpa only [f, ← hmap] using
      F.interval_comp_π (1 : Fin 5) (3 : Fin 5) h13
  let R : ShortComplex C := ShortComplex.mk f q wq
  have hR : IsAdmissibleExact R := by
    simpa only [R, f, q, hmap] using
      F.interval_exact (1 : Fin 5) (3 : Fin 5) h13
  let eApex := F.intervalQuillenSpan_apex h12 h23 h34
  let eQ : F.intervalQuotient (1 : Fin 5) (3 : Fin 5) h13 ≅
      (admissibleMonoSubdivisionQuillenSpan w).apex :=
    eqToIso eApex.symm
  have hp : admissibleMonoSubdivisionCompositionApexπ w = q ≫ eQ.hom := by
    rfl
  let D : ShortComplex C :=
    ShortComplex.mk f (admissibleMonoSubdivisionCompositionApexπ w)
      (admissibleMonoSubdivisionComposition_comp_apexπ w)
  let e : R ≅ D :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) eQ
      (by simp [R, D])
      (by simp [R, D, hp])
  exact isAdmissibleExact_of_iso e hR

/-- The combined flag's source interval is the selected quotient of `x`. -/
private noncomputable def admissibleMonoSubdivisionCompositionSourceIso
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) :
    let F := admissibleMonoSubdivisionCompositionFlag w z
    F.intervalQuotient (3 : Fin 7) (4 : Fin 7) (by decide) ≅
      admissibleMonoSubdivisionQuotient x := by
  let F := admissibleMonoSubdivisionCompositionFlag w z
  let h34 : (3 : Fin 7) ≤ 4 := by decide
  let q := AdmissibleMonoFlag.admissibleMonoQuotientπ
    x.val.hom x.val.property
  have hmap : F.chain.map (homOfLE h34) = x.val.hom :=
    admissibleMonoSubdivisionCompositionFlag_map_three_four w z h34
  have hzero : F.chain.map (homOfLE h34) ≫ q = 0 := by
    rw [hmap]
    exact AdmissibleMonoFlag.comp_admissibleMonoQuotientπ
      x.val.hom x.val.property
  have hExact : IsAdmissibleExact
      (ShortComplex.mk (F.chain.map (homOfLE h34)) q hzero) := by
    simpa only [hmap] using
      AdmissibleMonoFlag.admissibleMonoQuotient_exact
        x.val.hom x.val.property
  exact F.intervalIsoOfExact h34 q hzero hExact

/-- The combined flag's middle interval is the selected quotient of `y`. -/
private noncomputable def admissibleMonoSubdivisionCompositionMiddleIso
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) :
    let F := admissibleMonoSubdivisionCompositionFlag w z
    F.intervalQuotient (2 : Fin 7) (5 : Fin 7) (by decide) ≅
      admissibleMonoSubdivisionQuotient y := by
  let F := admissibleMonoSubdivisionCompositionFlag w z
  let h25 : (2 : Fin 7) ≤ 5 := by decide
  let q := AdmissibleMonoFlag.admissibleMonoQuotientπ
    y.val.hom y.val.property
  have hmap : F.chain.map (homOfLE h25) = y.val.hom :=
    admissibleMonoSubdivisionCompositionFlag_map_two_five w z h25
  have hzero : F.chain.map (homOfLE h25) ≫ q = 0 := by
    rw [hmap]
    exact AdmissibleMonoFlag.comp_admissibleMonoQuotientπ
      y.val.hom y.val.property
  have hExact : IsAdmissibleExact
      (ShortComplex.mk (F.chain.map (homOfLE h25)) q hzero) := by
    simpa only [hmap] using
      AdmissibleMonoFlag.admissibleMonoQuotient_exact
        y.val.hom y.val.property
  exact F.intervalIsoOfExact h25 q hzero hExact

/-- The combined flag's target interval is the selected quotient of `t`. -/
private noncomputable def admissibleMonoSubdivisionCompositionTargetIso
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) :
    let F := admissibleMonoSubdivisionCompositionFlag w z
    F.intervalQuotient (1 : Fin 7) (6 : Fin 7) (by decide) ≅
      admissibleMonoSubdivisionQuotient t := by
  let F := admissibleMonoSubdivisionCompositionFlag w z
  let h16 : (1 : Fin 7) ≤ 6 := by decide
  let q := AdmissibleMonoFlag.admissibleMonoQuotientπ
    t.val.hom t.val.property
  have hmap : F.chain.map (homOfLE h16) = t.val.hom :=
    admissibleMonoSubdivisionCompositionFlag_map_one_six w z h16
  have hzero : F.chain.map (homOfLE h16) ≫ q = 0 := by
    rw [hmap]
    exact AdmissibleMonoFlag.comp_admissibleMonoQuotientπ
      t.val.hom t.val.property
  have hExact : IsAdmissibleExact
      (ShortComplex.mk (F.chain.map (homOfLE h16)) q hzero) := by
    simpa only [hmap] using
      AdmissibleMonoFlag.admissibleMonoQuotient_exact
        t.val.hom t.val.property
  exact F.intervalIsoOfExact h16 q hzero hExact

@[reassoc]
private theorem admissibleMonoSubdivisionCompositionSourceIso_projection
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) :
    let F := admissibleMonoSubdivisionCompositionFlag w z
    F.intervalπ (3 : Fin 7) (4 : Fin 7) (by decide) ≫
        (admissibleMonoSubdivisionCompositionSourceIso w z).hom =
      AdmissibleMonoFlag.admissibleMonoQuotientπ
        x.val.hom x.val.property := by
  let F := admissibleMonoSubdivisionCompositionFlag w z
  let h34 : (3 : Fin 7) ≤ 4 := by decide
  unfold admissibleMonoSubdivisionCompositionSourceIso
  exact F.intervalπ_intervalIsoOfExact_hom h34
    (AdmissibleMonoFlag.admissibleMonoQuotientπ
      x.val.hom x.val.property) _ _

@[reassoc]
private theorem admissibleMonoSubdivisionCompositionMiddleIso_projection
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) :
    let F := admissibleMonoSubdivisionCompositionFlag w z
    F.intervalπ (2 : Fin 7) (5 : Fin 7) (by decide) ≫
        (admissibleMonoSubdivisionCompositionMiddleIso w z).hom =
      AdmissibleMonoFlag.admissibleMonoQuotientπ
        y.val.hom y.val.property := by
  let F := admissibleMonoSubdivisionCompositionFlag w z
  let h25 : (2 : Fin 7) ≤ 5 := by decide
  unfold admissibleMonoSubdivisionCompositionMiddleIso
  exact F.intervalπ_intervalIsoOfExact_hom h25
    (AdmissibleMonoFlag.admissibleMonoQuotientπ
      y.val.hom y.val.property) _ _

@[reassoc]
private theorem admissibleMonoSubdivisionCompositionTargetIso_projection
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) :
    let F := admissibleMonoSubdivisionCompositionFlag w z
    F.intervalπ (1 : Fin 7) (6 : Fin 7) (by decide) ≫
        (admissibleMonoSubdivisionCompositionTargetIso w z).hom =
      AdmissibleMonoFlag.admissibleMonoQuotientπ
        t.val.hom t.val.property := by
  let F := admissibleMonoSubdivisionCompositionFlag w z
  let h16 : (1 : Fin 7) ≤ 6 := by decide
  unfold admissibleMonoSubdivisionCompositionTargetIso
  exact F.intervalπ_intervalIsoOfExact_hom h16
    (AdmissibleMonoFlag.admissibleMonoQuotientπ
      t.val.hom t.val.property) _ _

/-- Comparison from the combined flag's first raw apex to the apex selected
by the final span of `w`. -/
private noncomputable def admissibleMonoSubdivisionCompositionLeftApexIso
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) :
    let F := admissibleMonoSubdivisionCompositionFlag w z
    F.intervalQuotient (2 : Fin 7) (4 : Fin 7) (by decide) ≅
      (admissibleMonoSubdivisionQuillenSpan w).apex := by
  let F := admissibleMonoSubdivisionCompositionFlag w z
  let h24 : (2 : Fin 7) ≤ 4 := by decide
  let q := admissibleMonoSubdivisionCompositionApexπ w
  have hmap : F.chain.map (homOfLE h24) =
      w.hom.1.unop.hom ≫ x.val.hom :=
    admissibleMonoSubdivisionCompositionFlag_map_two_four w z h24
  have hzero : F.chain.map (homOfLE h24) ≫ q = 0 := by
    rw [hmap]
    exact admissibleMonoSubdivisionComposition_comp_apexπ w
  have hExact : IsAdmissibleExact
      (ShortComplex.mk (F.chain.map (homOfLE h24)) q hzero) := by
    simpa only [hmap] using
      admissibleMonoSubdivisionComposition_apexπ_exact w
  exact F.intervalIsoOfExact h24 q hzero hExact

/-- Comparison from the combined flag's second raw apex to the apex selected
by the final span of `z`. -/
private noncomputable def admissibleMonoSubdivisionCompositionRightApexIso
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) :
    let F := admissibleMonoSubdivisionCompositionFlag w z
    F.intervalQuotient (1 : Fin 7) (5 : Fin 7) (by decide) ≅
      (admissibleMonoSubdivisionQuillenSpan z).apex := by
  let F := admissibleMonoSubdivisionCompositionFlag w z
  let h15 : (1 : Fin 7) ≤ 5 := by decide
  let q := admissibleMonoSubdivisionCompositionApexπ z
  have hmap : F.chain.map (homOfLE h15) =
      z.hom.1.unop.hom ≫ y.val.hom :=
    admissibleMonoSubdivisionCompositionFlag_map_one_five w z h15
  have hzero : F.chain.map (homOfLE h15) ≫ q = 0 := by
    rw [hmap]
    exact admissibleMonoSubdivisionComposition_comp_apexπ z
  have hExact : IsAdmissibleExact
      (ShortComplex.mk (F.chain.map (homOfLE h15)) q hzero) := by
    simpa only [hmap] using
      admissibleMonoSubdivisionComposition_apexπ_exact z
  exact F.intervalIsoOfExact h15 q hzero hExact

/-- Comparison from the combined flag's long raw apex to the apex selected
by the final span of `w ≫ z`. -/
private noncomputable def admissibleMonoSubdivisionCompositionLongApexIso
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) :
    let F := admissibleMonoSubdivisionCompositionFlag w z
    F.intervalQuotient (1 : Fin 7) (4 : Fin 7) (by decide) ≅
      (admissibleMonoSubdivisionQuillenSpan (w ≫ z)).apex := by
  let F := admissibleMonoSubdivisionCompositionFlag w z
  let h14 : (1 : Fin 7) ≤ 4 := by decide
  let q := admissibleMonoSubdivisionCompositionApexπ (w ≫ z)
  have hmap : F.chain.map (homOfLE h14) =
      (w ≫ z).hom.1.unop.hom ≫ x.val.hom := by
    rw [admissibleMonoSubdivisionComposition_comp_left w z]
    exact admissibleMonoSubdivisionCompositionFlag_map_one_four w z h14
  have hzero : F.chain.map (homOfLE h14) ≫ q = 0 := by
    rw [hmap]
    exact admissibleMonoSubdivisionComposition_comp_apexπ (w ≫ z)
  have hExact : IsAdmissibleExact
      (ShortComplex.mk (F.chain.map (homOfLE h14)) q hzero) := by
    simpa only [hmap] using
      admissibleMonoSubdivisionComposition_apexπ_exact (w ≫ z)
  exact F.intervalIsoOfExact h14 q hzero hExact

@[reassoc]
private theorem admissibleMonoSubdivisionCompositionLeftApexIso_projection
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) :
    let F := admissibleMonoSubdivisionCompositionFlag w z
    F.intervalπ (2 : Fin 7) (4 : Fin 7) (by decide) ≫
        (admissibleMonoSubdivisionCompositionLeftApexIso w z).hom =
      admissibleMonoSubdivisionCompositionApexπ w := by
  let F := admissibleMonoSubdivisionCompositionFlag w z
  let h24 : (2 : Fin 7) ≤ 4 := by decide
  unfold admissibleMonoSubdivisionCompositionLeftApexIso
  exact F.intervalπ_intervalIsoOfExact_hom h24
    (admissibleMonoSubdivisionCompositionApexπ w) _ _

@[reassoc]
private theorem admissibleMonoSubdivisionCompositionRightApexIso_projection
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) :
    let F := admissibleMonoSubdivisionCompositionFlag w z
    F.intervalπ (1 : Fin 7) (5 : Fin 7) (by decide) ≫
        (admissibleMonoSubdivisionCompositionRightApexIso w z).hom =
      admissibleMonoSubdivisionCompositionApexπ z := by
  let F := admissibleMonoSubdivisionCompositionFlag w z
  let h15 : (1 : Fin 7) ≤ 5 := by decide
  unfold admissibleMonoSubdivisionCompositionRightApexIso
  exact F.intervalπ_intervalIsoOfExact_hom h15
    (admissibleMonoSubdivisionCompositionApexπ z) _ _

@[reassoc]
private theorem admissibleMonoSubdivisionCompositionLongApexIso_projection
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) :
    let F := admissibleMonoSubdivisionCompositionFlag w z
    F.intervalπ (1 : Fin 7) (4 : Fin 7) (by decide) ≫
        (admissibleMonoSubdivisionCompositionLongApexIso w z).hom =
      admissibleMonoSubdivisionCompositionApexπ (w ≫ z) := by
  let F := admissibleMonoSubdivisionCompositionFlag w z
  let h14 : (1 : Fin 7) ≤ 4 := by decide
  unfold admissibleMonoSubdivisionCompositionLongApexIso
  exact F.intervalπ_intervalIsoOfExact_hom h14
    (admissibleMonoSubdivisionCompositionApexπ (w ≫ z)) _ _

/-- Endpoint-compatible comparison from the first combined-flag raw span to
the final selected span of `w`. -/
private noncomputable def admissibleMonoSubdivisionCompositionLeftEndpointIso
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) :
    let W := admissibleMonoSubdivisionCompositionLeftRawSpan w z
    QuillenSpan.EndpointIso W (admissibleMonoSubdivisionQuillenSpan w)
      (admissibleMonoSubdivisionCompositionSourceIso w z)
      (admissibleMonoSubdivisionCompositionMiddleIso w z) := by
  let F := admissibleMonoSubdivisionCompositionFlag w z
  let h23 : (2 : Fin 7) ≤ 3 := by decide
  let h34 : (3 : Fin 7) ≤ 4 := by decide
  let h45 : (4 : Fin 7) ≤ 5 := by decide
  let h24 := h23.trans h34
  let h25 := h24.trans h45
  let W := F.intervalQuillenSpan h23 h34 h45
  let p := F.intervalπ (2 : Fin 7) (4 : Fin 7) h24
  let eA := admissibleMonoSubdivisionCompositionLeftApexIso w z
  let eX := admissibleMonoSubdivisionCompositionSourceIso w z
  let eY := admissibleMonoSubdivisionCompositionMiddleIso w z
  have hWl : p ≫ W.l = F.intervalπ (3 : Fin 7) (4 : Fin 7) h34 := by
    change F.intervalπ (2 : Fin 7) (4 : Fin 7) h24 ≫
        F.intervalMap h24 h34 h23 le_rfl = _
    rw [F.intervalπ_naturality]
    have hid : F.chain.map (homOfLE (le_rfl : (4 : Fin 7) ≤ 4)) =
        𝟙 (F.chain.obj (4 : Fin 7)) := by
      rw [Subsingleton.elim (homOfLE _) (𝟙 _), F.chain.map_id]
    rw [hid, Category.id_comp]
  have hWr : p ≫ W.r = w.hom.2.hom ≫
      F.intervalπ (2 : Fin 7) (5 : Fin 7) h25 := by
    change F.intervalπ (2 : Fin 7) (4 : Fin 7) h24 ≫
        F.intervalMap h24 h25 le_rfl h45 = _
    rw [F.intervalπ_naturality,
      admissibleMonoSubdivisionCompositionFlag_map_four_five w z h45]
  let _ : Epi p :=
    (isAdmissibleEpi_g
      (F.interval_exact (2 : Fin 7) (4 : Fin 7) h24)).epi
  refine ⟨eA, ?_, ?_⟩
  · apply (cancel_epi p).1
    calc
      p ≫ (eA.hom ≫ (admissibleMonoSubdivisionQuillenSpan w).l) =
          (p ≫ eA.hom) ≫
            (admissibleMonoSubdivisionQuillenSpan w).l := by
              rw [Category.assoc]
      _ = admissibleMonoSubdivisionCompositionApexπ w ≫
            (admissibleMonoSubdivisionQuillenSpan w).l := by
              rw [admissibleMonoSubdivisionCompositionLeftApexIso_projection]
      _ = AdmissibleMonoFlag.admissibleMonoQuotientπ
            x.val.hom x.val.property :=
              admissibleMonoSubdivisionCompositionApexπ_l w
      _ = F.intervalπ (3 : Fin 7) (4 : Fin 7) h34 ≫ eX.hom := by
              rw [admissibleMonoSubdivisionCompositionSourceIso_projection]
      _ = (p ≫ W.l) ≫ eX.hom := by rw [hWl]
      _ = p ≫ (W.l ≫ eX.hom) := Category.assoc _ _ _
  · apply (cancel_epi p).1
    calc
      p ≫ (eA.hom ≫ (admissibleMonoSubdivisionQuillenSpan w).r) =
          (p ≫ eA.hom) ≫
            (admissibleMonoSubdivisionQuillenSpan w).r := by
              rw [Category.assoc]
      _ = admissibleMonoSubdivisionCompositionApexπ w ≫
            (admissibleMonoSubdivisionQuillenSpan w).r := by
              rw [admissibleMonoSubdivisionCompositionLeftApexIso_projection]
      _ = w.hom.2.hom ≫
            AdmissibleMonoFlag.admissibleMonoQuotientπ
              y.val.hom y.val.property :=
              admissibleMonoSubdivisionCompositionApexπ_r w
      _ = w.hom.2.hom ≫
            (F.intervalπ (2 : Fin 7) (5 : Fin 7) h25 ≫ eY.hom) := by
              rw [admissibleMonoSubdivisionCompositionMiddleIso_projection]
      _ = (w.hom.2.hom ≫
            F.intervalπ (2 : Fin 7) (5 : Fin 7) h25) ≫ eY.hom := by
              rw [Category.assoc]
      _ = (p ≫ W.r) ≫ eY.hom := by rw [hWr]
      _ = p ≫ (W.r ≫ eY.hom) := Category.assoc _ _ _

/-- Endpoint-compatible comparison from the second combined-flag raw span to
the final selected span of `z`. -/
private noncomputable def admissibleMonoSubdivisionCompositionRightEndpointIso
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) :
    let Z := admissibleMonoSubdivisionCompositionRightRawSpan w z
    QuillenSpan.EndpointIso Z (admissibleMonoSubdivisionQuillenSpan z)
      (admissibleMonoSubdivisionCompositionMiddleIso w z)
      (admissibleMonoSubdivisionCompositionTargetIso w z) := by
  let F := admissibleMonoSubdivisionCompositionFlag w z
  let h12 : (1 : Fin 7) ≤ 2 := by decide
  let h23 : (2 : Fin 7) ≤ 3 := by decide
  let h34 : (3 : Fin 7) ≤ 4 := by decide
  let h45 : (4 : Fin 7) ≤ 5 := by decide
  let h56 : (5 : Fin 7) ≤ 6 := by decide
  let h24 := h23.trans h34
  let h25 := h24.trans h45
  let h15 := h12.trans h25
  let h16 := h15.trans h56
  let Z := F.intervalQuillenSpan h12 h25 h56
  let p := F.intervalπ (1 : Fin 7) (5 : Fin 7) h15
  let eA := admissibleMonoSubdivisionCompositionRightApexIso w z
  let eY := admissibleMonoSubdivisionCompositionMiddleIso w z
  let eT := admissibleMonoSubdivisionCompositionTargetIso w z
  have hZl : p ≫ Z.l = F.intervalπ (2 : Fin 7) (5 : Fin 7) h25 := by
    change F.intervalπ (1 : Fin 7) (5 : Fin 7) h15 ≫
        F.intervalMap h15 h25 h12 le_rfl = _
    rw [F.intervalπ_naturality]
    have hid : F.chain.map (homOfLE (le_rfl : (5 : Fin 7) ≤ 5)) =
        𝟙 (F.chain.obj (5 : Fin 7)) := by
      rw [Subsingleton.elim (homOfLE _) (𝟙 _), F.chain.map_id]
    rw [hid, Category.id_comp]
  have hZr : p ≫ Z.r = z.hom.2.hom ≫
      F.intervalπ (1 : Fin 7) (6 : Fin 7) h16 := by
    change F.intervalπ (1 : Fin 7) (5 : Fin 7) h15 ≫
        F.intervalMap h15 h16 le_rfl h56 = _
    rw [F.intervalπ_naturality,
      admissibleMonoSubdivisionCompositionFlag_map_five_six w z h56]
  let _ : Epi p :=
    (isAdmissibleEpi_g
      (F.interval_exact (1 : Fin 7) (5 : Fin 7) h15)).epi
  refine ⟨eA, ?_, ?_⟩
  · apply (cancel_epi p).1
    calc
      p ≫ (eA.hom ≫ (admissibleMonoSubdivisionQuillenSpan z).l) =
          (p ≫ eA.hom) ≫
            (admissibleMonoSubdivisionQuillenSpan z).l := by
              rw [Category.assoc]
      _ = admissibleMonoSubdivisionCompositionApexπ z ≫
            (admissibleMonoSubdivisionQuillenSpan z).l := by
              rw [admissibleMonoSubdivisionCompositionRightApexIso_projection]
      _ = AdmissibleMonoFlag.admissibleMonoQuotientπ
            y.val.hom y.val.property :=
              admissibleMonoSubdivisionCompositionApexπ_l z
      _ = F.intervalπ (2 : Fin 7) (5 : Fin 7) h25 ≫ eY.hom := by
              rw [admissibleMonoSubdivisionCompositionMiddleIso_projection]
      _ = (p ≫ Z.l) ≫ eY.hom := by rw [hZl]
      _ = p ≫ (Z.l ≫ eY.hom) := Category.assoc _ _ _
  · apply (cancel_epi p).1
    calc
      p ≫ (eA.hom ≫ (admissibleMonoSubdivisionQuillenSpan z).r) =
          (p ≫ eA.hom) ≫
            (admissibleMonoSubdivisionQuillenSpan z).r := by
              rw [Category.assoc]
      _ = admissibleMonoSubdivisionCompositionApexπ z ≫
            (admissibleMonoSubdivisionQuillenSpan z).r := by
              rw [admissibleMonoSubdivisionCompositionRightApexIso_projection]
      _ = z.hom.2.hom ≫
            AdmissibleMonoFlag.admissibleMonoQuotientπ
              t.val.hom t.val.property :=
              admissibleMonoSubdivisionCompositionApexπ_r z
      _ = z.hom.2.hom ≫
            (F.intervalπ (1 : Fin 7) (6 : Fin 7) h16 ≫ eT.hom) := by
              rw [admissibleMonoSubdivisionCompositionTargetIso_projection]
      _ = (z.hom.2.hom ≫
            F.intervalπ (1 : Fin 7) (6 : Fin 7) h16) ≫ eT.hom := by
              rw [Category.assoc]
      _ = (p ≫ Z.r) ≫ eT.hom := by rw [hZr]
      _ = p ≫ (Z.r ≫ eT.hom) := Category.assoc _ _ _

/-- Endpoint-compatible comparison from the long combined-flag raw span to
the final selected span of `w ≫ z`. -/
private noncomputable def admissibleMonoSubdivisionCompositionLongEndpointIso
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) :
    let L := admissibleMonoSubdivisionCompositionLongRawSpan w z
    QuillenSpan.EndpointIso L
      (admissibleMonoSubdivisionQuillenSpan (w ≫ z))
      (admissibleMonoSubdivisionCompositionSourceIso w z)
      (admissibleMonoSubdivisionCompositionTargetIso w z) := by
  let F := admissibleMonoSubdivisionCompositionFlag w z
  let h12 : (1 : Fin 7) ≤ 2 := by decide
  let h23 : (2 : Fin 7) ≤ 3 := by decide
  let h34 : (3 : Fin 7) ≤ 4 := by decide
  let h45 : (4 : Fin 7) ≤ 5 := by decide
  let h56 : (5 : Fin 7) ≤ 6 := by decide
  let h13 := h12.trans h23
  let h46 := h45.trans h56
  let h14 := h13.trans h34
  let h16 := h14.trans h46
  let L := F.intervalQuillenSpan h13 h34 h46
  let p := F.intervalπ (1 : Fin 7) (4 : Fin 7) h14
  let eA := admissibleMonoSubdivisionCompositionLongApexIso w z
  let eX := admissibleMonoSubdivisionCompositionSourceIso w z
  let eT := admissibleMonoSubdivisionCompositionTargetIso w z
  have hLl : p ≫ L.l = F.intervalπ (3 : Fin 7) (4 : Fin 7) h34 := by
    change F.intervalπ (1 : Fin 7) (4 : Fin 7) h14 ≫
        F.intervalMap h14 h34 h13 le_rfl = _
    rw [F.intervalπ_naturality]
    have hid : F.chain.map (homOfLE (le_rfl : (4 : Fin 7) ≤ 4)) =
        𝟙 (F.chain.obj (4 : Fin 7)) := by
      rw [Subsingleton.elim (homOfLE _) (𝟙 _), F.chain.map_id]
    rw [hid, Category.id_comp]
  have hLr : p ≫ L.r = (w.hom.2.hom ≫ z.hom.2.hom) ≫
      F.intervalπ (1 : Fin 7) (6 : Fin 7) h16 := by
    change F.intervalπ (1 : Fin 7) (4 : Fin 7) h14 ≫
        F.intervalMap h14 h16 le_rfl h46 = _
    rw [F.intervalπ_naturality,
      admissibleMonoSubdivisionCompositionFlag_map_four_six w z h46]
  let _ : Epi p :=
    (isAdmissibleEpi_g
      (F.interval_exact (1 : Fin 7) (4 : Fin 7) h14)).epi
  refine ⟨eA, ?_, ?_⟩
  · apply (cancel_epi p).1
    calc
      p ≫ (eA.hom ≫
          (admissibleMonoSubdivisionQuillenSpan (w ≫ z)).l) =
          (p ≫ eA.hom) ≫
            (admissibleMonoSubdivisionQuillenSpan (w ≫ z)).l := by
              rw [Category.assoc]
      _ = admissibleMonoSubdivisionCompositionApexπ (w ≫ z) ≫
            (admissibleMonoSubdivisionQuillenSpan (w ≫ z)).l := by
              rw [admissibleMonoSubdivisionCompositionLongApexIso_projection]
      _ = AdmissibleMonoFlag.admissibleMonoQuotientπ
            x.val.hom x.val.property :=
              admissibleMonoSubdivisionCompositionApexπ_l (w ≫ z)
      _ = F.intervalπ (3 : Fin 7) (4 : Fin 7) h34 ≫ eX.hom := by
              rw [admissibleMonoSubdivisionCompositionSourceIso_projection]
      _ = (p ≫ L.l) ≫ eX.hom := by rw [hLl]
      _ = p ≫ (L.l ≫ eX.hom) := Category.assoc _ _ _
  · apply (cancel_epi p).1
    calc
      p ≫ (eA.hom ≫
          (admissibleMonoSubdivisionQuillenSpan (w ≫ z)).r) =
          (p ≫ eA.hom) ≫
            (admissibleMonoSubdivisionQuillenSpan (w ≫ z)).r := by
              rw [Category.assoc]
      _ = admissibleMonoSubdivisionCompositionApexπ (w ≫ z) ≫
            (admissibleMonoSubdivisionQuillenSpan (w ≫ z)).r := by
              rw [admissibleMonoSubdivisionCompositionLongApexIso_projection]
      _ = (w ≫ z).hom.2.hom ≫
            AdmissibleMonoFlag.admissibleMonoQuotientπ
              t.val.hom t.val.property :=
              admissibleMonoSubdivisionCompositionApexπ_r (w ≫ z)
      _ = (w.hom.2.hom ≫ z.hom.2.hom) ≫
            AdmissibleMonoFlag.admissibleMonoQuotientπ
              t.val.hom t.val.property := by
              rw [admissibleMonoSubdivisionComposition_comp_right w z]
      _ = (w.hom.2.hom ≫ z.hom.2.hom) ≫
            (F.intervalπ (1 : Fin 7) (6 : Fin 7) h16 ≫ eT.hom) := by
              rw [admissibleMonoSubdivisionCompositionTargetIso_projection]
      _ = ((w.hom.2.hom ≫ z.hom.2.hom) ≫
            F.intervalπ (1 : Fin 7) (6 : Fin 7) h16) ≫ eT.hom := by
              exact (Category.assoc _ _ _).symm
      _ = (p ≫ L.r) ≫ eT.hom := by rw [hLr]
      _ = p ≫ (L.r ≫ eT.hom) := Category.assoc _ _ _

/-- The pullback composite of the subdivision spans of two composable arrows
is isomorphic to the subdivision span of their composite. -/
@[no_expose]
noncomputable def admissibleMonoSubdivisionQuillenSpanCompIso
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) :
    Span.comp (admissibleMonoSubdivisionQuillenSpan w)
        (admissibleMonoSubdivisionQuillenSpan z) ≅
      admissibleMonoSubdivisionQuillenSpan (w ≫ z) := by
  let Wraw := admissibleMonoSubdivisionCompositionLeftRawSpan w z
  let Zraw := admissibleMonoSubdivisionCompositionRightRawSpan w z
  let Lraw := admissibleMonoSubdivisionCompositionLongRawSpan w z
  let Sw := admissibleMonoSubdivisionQuillenSpan w
  let Sz := admissibleMonoSubdivisionQuillenSpan z
  let Swz := admissibleMonoSubdivisionQuillenSpan (w ≫ z)
  let eX := admissibleMonoSubdivisionCompositionSourceIso w z
  let eT := admissibleMonoSubdivisionCompositionTargetIso w z
  let cW := admissibleMonoSubdivisionCompositionLeftEndpointIso w z
  let cZ := admissibleMonoSubdivisionCompositionRightEndpointIso w z
  let cLong := admissibleMonoSubdivisionCompositionLongEndpointIso w z
  let rawIso := admissibleMonoSubdivisionCompositionRawSpanCompIso w z
  let cComposite : QuillenSpan.EndpointIso Lraw (Span.comp Sw Sz) eX eT :=
    (cW.comp cZ).rebase rawIso (Iso.refl _)
  let eA : (Span.comp Sw Sz).apex ≅ Swz.apex :=
    cComposite.1.symm.trans cLong.1
  refine Span.mkIso eA ?_ ?_
  · change (cComposite.1.inv ≫ cLong.1.hom) ≫ Swz.l =
      (Span.comp Sw Sz).l
    calc
      _ = cComposite.1.inv ≫ (cLong.1.hom ≫ Swz.l) :=
        Category.assoc _ _ _
      _ = cComposite.1.inv ≫ (Lraw.l ≫ eX.hom) := by
        rw [cLong.hom_l]
      _ = (cComposite.1.inv ≫ Lraw.l) ≫ eX.hom := by
        rw [Category.assoc]
      _ = ((Span.comp Sw Sz).l ≫ eX.inv) ≫ eX.hom := by
        rw [cComposite.inv_l]
      _ = (Span.comp Sw Sz).l := by simp
  · change (cComposite.1.inv ≫ cLong.1.hom) ≫ Swz.r =
      (Span.comp Sw Sz).r
    calc
      _ = cComposite.1.inv ≫ (cLong.1.hom ≫ Swz.r) :=
        Category.assoc _ _ _
      _ = cComposite.1.inv ≫ (Lraw.r ≫ eT.hom) := by
        rw [cLong.hom_r]
      _ = (cComposite.1.inv ≫ Lraw.r) ≫ eT.hom := by
        rw [Category.assoc]
      _ = ((Span.comp Sw Sz).r ≫ eT.inv) ≫ eT.hom := by
        rw [cComposite.inv_r]
      _ = (Span.comp Sw Sz).r := by simp

/-- The quotient-level Quillen map from admissible-mono subdivision arrows
preserves composition. -/
@[simp]
theorem admissibleMonoSubdivisionQuillenHom_comp
    {x y t : AdmissibleMonoSubdivision (C := C)}
    (w : x ⟶ y) (z : y ⟶ t) :
    admissibleMonoSubdivisionQuillenHom w ≫
        admissibleMonoSubdivisionQuillenHom z =
      admissibleMonoSubdivisionQuillenHom (w ≫ z) := by
  unfold admissibleMonoSubdivisionQuillenHom
  change quillenComp
      (QuillenQ.mkHom
        (X := admissibleMonoSubdivisionQuillenObj x)
        (Y := admissibleMonoSubdivisionQuillenObj y)
        (admissibleMonoSubdivisionQuillenSpan w))
      (QuillenQ.mkHom
        (X := admissibleMonoSubdivisionQuillenObj y)
        (Y := admissibleMonoSubdivisionQuillenObj t)
        (admissibleMonoSubdivisionQuillenSpan z)) =
    QuillenQ.mkHom
      (X := admissibleMonoSubdivisionQuillenObj x)
      (Y := admissibleMonoSubdivisionQuillenObj t)
      (admissibleMonoSubdivisionQuillenSpan (w ≫ z))
  rw [mkHom_comp]
  exact QuillenQ.mkHom_sound
    (admissibleMonoSubdivisionQuillenSpanCompIso w z)

end AlgebraicKTheory

end
