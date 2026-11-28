/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Homology.ExactSequenceColimit
import MathlibExt.Algebra.Homology.ShortComplex.MapHomologyLeftExact
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# Torsion coordinates in exact colimits and the degree-zero homology edge

A filtered two-stage diagram scales the split exact five-object sequence on a lifted
copy of `ZMod 6` by two. Its colimit coprojections carry the class of one to two at the
last stage, while the class of three vanishes. The two nonzero middle arrows are checked
on representatives through the general sequence-colimit API.

The natural-number chain complex has incoming differential two in degree zero and zero
outgoing differential there. Its homology edge for the universe-lift functor carries a
class detected as one in `ZMod 2` to a class with the same nonzero coordinate. The source
carrier, target carrier and indexing worlds are distinct where indicated.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows

namespace MathlibExtTest.ExactSequenceColimit

private abbrev E := ModuleCat.{1} ℤ
private abbrev V := ULift.{1} (ZMod 6)
private abbrev N : E := ModuleCat.of ℤ V
private abbrev P : E := ModuleCat.of ℤ (V × V)
private abbrev Z : E := zeroObject E

private def inclusion : N ⟶ P := ModuleCat.ofHom (LinearMap.inl ℤ V V)
private def projection : P ⟶ N := ModuleCat.ofHom (LinearMap.snd ℤ V V)

private instance inclusion_mono : Mono inclusion := by
  rw [ModuleCat.mono_iff_injective]
  intro x y h
  exact congrArg Prod.fst h

private instance projection_epi : Epi projection := by
  rw [ModuleCat.epi_iff_surjective]
  intro y
  exact ⟨(0, y), rfl⟩

private def row : ComposableArrows E 4 :=
  mk₄ (0 : Z ⟶ N) inclusion projection (0 : N ⟶ Z)

private lemma row_complex : row.IsComplex where
  zero i hi := by
    have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases h with rfl | rfl | rfl
    · change (0 : Z ⟶ N) ≫ inclusion = 0
      simp
    · change inclusion ≫ projection = 0
      ext x
      rfl
    · change projection ≫ (0 : N ⟶ Z) = 0
      simp

private lemma row_exact : row.Exact where
  toIsComplex := row_complex
  exact i hi := by
    have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases h with rfl | rfl | rfl
    · change (ShortComplex.mk (0 : Z ⟶ N) inclusion (by simp)).Exact
      exact (ShortComplex.exact_iff_mono _ rfl).2 (by infer_instance)
    · change (ShortComplex.mk inclusion projection (by ext x; rfl)).Exact
      apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
      intro x
      change x.2 = 0 ↔ ∃ y : V, (y, 0) = x
      constructor
      · intro hx
        exact ⟨x.1, Prod.ext rfl hx.symm⟩
      · rintro ⟨y, hy⟩
        exact (congrArg Prod.snd hy).symm
    · change (ShortComplex.mk projection (0 : N ⟶ Z) (by simp)).Exact
      exact (ShortComplex.exact_iff_epi _ rfl).2 (by infer_instance)

private def exactRow : ExactSequences E 4 := ⟨row, row_exact⟩

private def diagram : Fin 2 ⥤ ExactSequences E 4 :=
  mk₁ ((2 : ℕ) • (𝟙 exactRow))

private abbrev terms (i : Fin 5) : Fin 2 ⥤ E :=
  (exactSequenceFourDiagram diagram).flip.obj i

private instance : HasExactColimitsOfShape (Fin 2) E :=
  HasExactColimitsOfShape.domain_of_functor (C := E) (D := AddCommGrpCat.{1})
    (Fin 2) (show E ⥤ AddCommGrpCat.{1} from forget₂ E AddCommGrpCat.{1})

private abbrev sequenceColimit := exactSequenceFourColimit diagram

private abbrev arrow12 : colimit (terms 1) ⟶ colimit (terms 2) :=
  colim.map ((exactSequenceFourDiagram diagram).flip.map
    (homOfLE (show (1 : Fin 5) ≤ 2 from by decide)))

private abbrev arrow23 : colimit (terms 2) ⟶ colimit (terms 3) :=
  colim.map ((exactSequenceFourDiagram diagram).flip.map
    (homOfLE (show (2 : Fin 5) ≤ 3 from by decide)))

private lemma arrow12_is_sequence_map : sequenceColimit.map' 1 2 = arrow12 :=
  exactSequenceFourColimit_map_one_two diagram

private lemma arrow23_is_sequence_map : sequenceColimit.map' 2 3 = arrow23 :=
  exactSequenceFourColimit_map_two_three diagram

private lemma two_apply (x : V) : ((2 : ℕ) • (𝟙 N)).hom x = x + x := by
  simpa only [two_nsmul]

private lemma two_one : ((2 : ℕ) • (𝟙 N)).hom (ULift.up (1 : ZMod 6)) =
    ULift.up (2 : ZMod 6) := by
  calc
    _ = (ULift.up (1 : ZMod 6) : V) + ULift.up (1 : ZMod 6) := two_apply _
    _ = ULift.up (2 : ZMod 6) := by apply ULift.ext; decide

private lemma two_three : ((2 : ℕ) • (𝟙 N)).hom (ULift.up (3 : ZMod 6)) = 0 := by
  calc
    _ = (ULift.up (3 : ZMod 6) : V) + ULift.up (3 : ZMod 6) := two_apply _
    _ = 0 := by apply ULift.ext; decide

private lemma two_pair : ((2 : ℕ) • (𝟙 P)).hom
    (ULift.up (1 : ZMod 6), ULift.up (0 : ZMod 6)) =
      (ULift.up (2 : ZMod 6), ULift.up (0 : ZMod 6)) := by
  calc
    _ = (ULift.up (1 : ZMod 6), ULift.up (0 : ZMod 6)) +
        (ULift.up (1 : ZMod 6), ULift.up (0 : ZMod 6)) := by simpa only [two_nsmul]
    _ = (ULift.up (2 : ZMod 6), ULift.up (0 : ZMod 6)) := by
      apply Prod.ext <;> apply ULift.ext <;> decide

private def atLast (D : Fin 2 ⥤ E) : Cocone D where
  pt := D.obj 1
  ι :=
    { app := fun i => D.map (homOfLE (show i ≤ (1 : Fin 2) from Fin.le_last i))
      naturality := by
        intro i j f
        dsimp
        simp only [Category.comp_id]
        rw [← D.map_comp]
        exact congrArg D.map (Subsingleton.elim _ _) }

private def observe (i : Fin 5) : colimit (terms i) ⟶ (terms i).obj 1 :=
  colimit.desc (terms i) (atLast (terms i))

private lemma observe_coprojection (i : Fin 5) (j : Fin 2) :
    colimit.ι (terms i) j ≫ observe i =
      (terms i).map (homOfLE (show j ≤ (1 : Fin 2) from Fin.le_last j)) :=
  colimit.ι_desc (atLast (terms i)) j

private def one : ↥(colimit (terms 1)) :=
  (colimit.ι (terms 1) 0).hom (ULift.up (1 : ZMod 6))

private def three : ↥(colimit (terms 1)) :=
  (colimit.ι (terms 1) 0).hom (ULift.up (3 : ZMod 6))

private lemma observe_one : (observe 1).hom one = ULift.up (2 : ZMod 6) := by
  have h := congrArg (fun f => f.hom (ULift.up (1 : ZMod 6)))
    (observe_coprojection 1 0)
  change (observe 1).hom one =
    ((2 : ℕ) • (𝟙 N)).hom (ULift.up (1 : ZMod 6)) at h
  exact h.trans two_one

example : sequenceColimit.Exact := exactSequenceFourColimit_exact diagram

example : (observe 1).hom one ≠ 0 ∧ (observe 1).hom one ≠ ULift.up (1 : ZMod 6) := by
  rw [observe_one]
  constructor
  · intro h
    exact (by decide : (2 : ZMod 6) ≠ 0) (congrArg ULift.down h)
  · intro h
    exact (by decide : (2 : ZMod 6) ≠ 1) (congrArg ULift.down h)

example : one ≠ 0 := by
  intro h
  have he := congrArg (observe 1).hom h
  rw [observe_one, map_zero] at he
  exact (by decide : (2 : ZMod 6) ≠ 0) (congrArg ULift.down he)

example : three = 0 := by
  have h := congrArg (fun f => f.hom (ULift.up (3 : ZMod 6)))
    (colimit.w (terms 1) (homOfLE (show (0 : Fin 2) ≤ 1 from by decide)))
  change (colimit.ι (terms 1) 1).hom
      (((2 : ℕ) • (𝟙 N)).hom (ULift.up (3 : ZMod 6))) = three at h
  rw [two_three, map_zero] at h
  exact h.symm

private lemma first_coordinate :
    colimit.ι (terms 1) 0 ≫ arrow12 ≫ observe 2 =
      inclusion ≫ ((2 : ℕ) • (𝟙 P)) := by
  have h := exactSequenceFourColimit_ι_map_one_two diagram 0
  change colimit.ι (terms 1) 0 ≫ arrow12 =
    inclusion ≫ colimit.ι (terms 2) 0 at h
  calc
    _ = (colimit.ι (terms 1) 0 ≫ arrow12) ≫ observe 2 := (Category.assoc _ _ _).symm
    _ = inclusion ≫ colimit.ι (terms 2) 0 ≫ observe 2 := by
      simp only [h, Category.assoc]
    _ = inclusion ≫ (terms 2).map
        (homOfLE (show (0 : Fin 2) ≤ 1 from by decide)) :=
      congrArg (inclusion ≫ ·) (observe_coprojection 2 0)
    _ = inclusion ≫ ((2 : ℕ) • (𝟙 P)) := rfl

example : (observe 2).hom ((sequenceColimit.map' 1 2).hom one) =
    (ULift.up (2 : ZMod 6), ULift.up (0 : ZMod 6)) := by
  change (observe 2).hom (arrow12.hom one) =
    (ULift.up (2 : ZMod 6), ULift.up (0 : ZMod 6))
  have h := congrArg (fun f => f.hom (ULift.up (1 : ZMod 6))) first_coordinate
  change (observe 2).hom (arrow12.hom one) =
    ((2 : ℕ) • (𝟙 P)).hom (ULift.up (1 : ZMod 6), ULift.up (0 : ZMod 6)) at h
  exact h.trans two_pair

private lemma second_coordinate :
    colimit.ι (terms 2) 0 ≫ arrow23 ≫ observe 3 =
      projection ≫ ((2 : ℕ) • (𝟙 N)) := by
  have h := exactSequenceFourColimit_ι_map_two_three diagram 0
  change colimit.ι (terms 2) 0 ≫ arrow23 =
    projection ≫ colimit.ι (terms 3) 0 at h
  calc
    _ = (colimit.ι (terms 2) 0 ≫ arrow23) ≫ observe 3 := (Category.assoc _ _ _).symm
    _ = projection ≫ colimit.ι (terms 3) 0 ≫ observe 3 := by
      simp only [h, Category.assoc]
    _ = projection ≫ (terms 3).map
        (homOfLE (show (0 : Fin 2) ≤ 1 from by decide)) :=
      congrArg (projection ≫ ·) (observe_coprojection 3 0)
    _ = projection ≫ ((2 : ℕ) • (𝟙 N)) := rfl

example : (observe 3).hom ((sequenceColimit.map' 2 3).hom
    ((colimit.ι (terms 2) 0).hom
      (ULift.up (0 : ZMod 6), ULift.up (1 : ZMod 6)))) = ULift.up (2 : ZMod 6) := by
  change (observe 3).hom (arrow23.hom
    ((colimit.ι (terms 2) 0).hom
      (ULift.up (0 : ZMod 6), ULift.up (1 : ZMod 6)))) = ULift.up (2 : ZMod 6)
  have h := congrArg (fun f => f.hom
    (ULift.up (0 : ZMod 6), ULift.up (1 : ZMod 6))) second_coordinate
  change (observe 3).hom (arrow23.hom
    ((colimit.ι (terms 2) 0).hom
      (ULift.up (0 : ZMod 6), ULift.up (1 : ZMod 6)))) =
        ((2 : ℕ) • (𝟙 N)).hom (ULift.up (1 : ZMod 6)) at h
  exact h.trans two_one

section DegreeZero

private def step (n : ℕ) : N ⟶ N := if n = 0 then (2 : ℕ) • 𝟙 N else 0

private abbrev K : ChainComplex E ℕ where
  X _ := N
  d i j := if i = j + 1 then step j else 0
  shape i j hij := by
    exact ite_eq_right hij
  d_comp_d' i j k hij hjk := by
    have hj : j ≠ 0 := by
      change j = k + 1 at hjk
      omega
    simp only [step, ite_eq_right hj, ite_self, zero_comp]

private abbrev S : ShortComplex E :=
  ShortComplex.mk ((2 : ℕ) • 𝟙 N) (0 : N ⟶ N) (by simp)

private lemma degree_zero_window : K.sc' 1 0 0 = S := rfl

private lemma incoming : S.f = (2 : ℕ) • 𝟙 N := by
  rfl

private lemma outgoing : S.g = 0 := by
  rfl

private abbrev N2 : E := ModuleCat.of ℤ (ULift.{1} (ZMod 2))

private def reduction : N ⟶ N2 := ModuleCat.ofHom
  (ULift.moduleEquiv.symm.toLinearMap.comp
    ((ZMod.castHom (by decide : 2 ∣ 6) (ZMod 2)).toAddMonoidHom.toIntLinearMap.comp
      ULift.moduleEquiv.toLinearMap))

private lemma incoming_reduction : S.f ≫ reduction = 0 := by
  rw [incoming]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change reduction.hom ((2 : ℕ) • x) = 0
  rw [map_nsmul]
  apply ULift.ext
  change (2 : ℕ) • (ZMod.castHom (by decide : 2 ∣ 6) (ZMod 2)) x.down = 0
  norm_num [nsmul_eq_mul]

private lemma reduction_one : reduction.hom (ULift.up (1 : ZMod 6)) =
    ULift.up (1 : ZMod 2) := by
  apply ULift.ext
  change (ZMod.castHom (by decide : 2 ∣ 6) (ZMod 2)) (1 : ZMod 6) = 1
  exact RingHom.map_one _

private def liftOne : N ⟶ S.cycles :=
  S.liftCycles (𝟙 N) (by simp only [outgoing, comp_zero])

private lemma liftOne_i : liftOne ≫ S.iCycles = 𝟙 N :=
  S.liftCycles_i _ _

private def detect : S.homology ⟶ N2 :=
  S.descHomology (S.iCycles ≫ reduction) (by
    rw [← Category.assoc, ShortComplex.toCycles_i]
    exact incoming_reduction)

private lemma detect_lift : liftOne ≫ S.homologyπ ≫ detect = reduction := by
  change liftOne ≫ S.homologyπ ≫
    S.descHomology (S.iCycles ≫ reduction) _ = reduction
  rw [ShortComplex.π_descHomology, ← Category.assoc, liftOne_i, Category.id_comp]

private abbrev F : E ⥤ ModuleCat.{2} ℤ := ModuleCat.uliftFunctor.{2, 1} ℤ

private def mappedLift : F.obj N ⟶ (S.map F).cycles :=
  (S.map F).liftCycles (𝟙 (F.obj N)) (by
    change 𝟙 (F.obj N) ≫ F.map S.g = 0
    simp only [outgoing, Functor.map_zero, Category.id_comp])

private lemma mappedLift_i : mappedLift ≫ (S.map F).iCycles = 𝟙 (F.obj N) :=
  (S.map F).liftCycles_i _ _

private lemma mapped_reduction_one : (F.map reduction).hom
    (ULift.up (ULift.up (1 : ZMod 6))) = ULift.up (ULift.up (1 : ZMod 2)) := by
  change ULift.up (reduction.hom (ULift.up (1 : ZMod 6))) = _
  rw [reduction_one]

private def cyclesIso : (S.map F).cycles ≅ F.obj S.cycles :=
  ShortComplex.leftExactCyclesComparisonIso F S

private lemma lift_comparison : mappedLift ≫ cyclesIso.hom = F.map liftOne := by
  change mappedLift ≫ ShortComplex.leftExactCyclesComparison F S = F.map liftOne
  apply (cancel_mono (F.map S.iCycles)).mp
  rw [Category.assoc, ShortComplex.leftExactCyclesComparison_i, mappedLift_i,
    ← F.map_comp, liftOne_i, F.map_id]

private def mappedClass : (S.map F).homology :=
  ((mappedLift ≫ (S.map F).homologyπ).hom)
    (ULift.up (ULift.up (1 : ZMod 6)))

private lemma edge_coordinate_map :
    mappedLift ≫ (S.map F).homologyπ ≫
        ShortComplex.leftExactHomologyEdge F S ≫ F.map detect = F.map reduction := by
  calc
    _ = mappedLift ≫ ((S.map F).homologyπ ≫
        ShortComplex.leftExactHomologyEdge F S) ≫ F.map detect := by
      simp only [Category.assoc]
    _ = mappedLift ≫ (cyclesIso.hom ≫ F.map S.homologyπ) ≫ F.map detect := by
      simpa only [cyclesIso, ShortComplex.leftExactCyclesComparisonIso_hom] using
        congrArg (fun t => mappedLift ≫ t ≫ F.map detect)
          (ShortComplex.leftExactHomologyEdge_characteristic F S)
    _ = (mappedLift ≫ cyclesIso.hom) ≫ F.map (S.homologyπ ≫ detect) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = F.map liftOne ≫ F.map (S.homologyπ ≫ detect) := by rw [lift_comparison]
    _ = F.map (liftOne ≫ S.homologyπ ≫ detect) := (F.map_comp _ _).symm
    _ = F.map reduction := congrArg F.map detect_lift

example : K.d 0 0 = 0 ∧ (K.d 1 0).hom (ULift.up (1 : ZMod 6)) =
    ULift.up (2 : ZMod 6) := by
  constructor
  · exact outgoing
  · change S.f.hom (ULift.up (1 : ZMod 6)) = ULift.up (2 : ZMod 6)
    rw [incoming]
    exact two_one

example : (F.map S.iCycles).hom ((cyclesIso.hom).hom
    (mappedLift.hom (ULift.up (ULift.up (1 : ZMod 6))))) =
      ULift.up (ULift.up (1 : ZMod 6)) := by
  have h : mappedLift ≫ cyclesIso.hom ≫ F.map S.iCycles = 𝟙 (F.obj N) := by
    rw [← Category.assoc, lift_comparison, ← F.map_comp, liftOne_i, F.map_id]
  exact ConcreteCategory.congr_hom h (ULift.up (ULift.up (1 : ZMod 6)))

private lemma edge_value : (F.map detect).hom
    ((ShortComplex.leftExactHomologyEdge F S).hom mappedClass) =
      ULift.up (ULift.up (1 : ZMod 2)) := by
  have h := congrArg (fun f => f.hom (ULift.up (ULift.up (1 : ZMod 6))))
    edge_coordinate_map
  change (F.map detect).hom
    ((ShortComplex.leftExactHomologyEdge F S).hom mappedClass) =
      (F.map reduction).hom (ULift.up (ULift.up (1 : ZMod 6))) at h
  exact h.trans mapped_reduction_one

example : (F.map detect).hom
    ((ShortComplex.leftExactHomologyEdge F S).hom mappedClass) =
      ULift.up (ULift.up (1 : ZMod 2)) := edge_value

example : (ShortComplex.leftExactHomologyEdge F S).hom mappedClass ≠ 0 := by
  intro h
  have hc := congrArg (F.map detect).hom h
  rw [edge_value, map_zero] at hc
  have h' : (1 : ZMod 2) = 0 := congrArg (fun x => x.down.down) hc
  exact (by decide : (1 : ZMod 2) ≠ 0) h'

end DegreeZero

end MathlibExtTest.ExactSequenceColimit
