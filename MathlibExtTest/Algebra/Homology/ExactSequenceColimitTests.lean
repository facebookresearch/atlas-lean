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
  mk₄ (0 : (0 : E) ⟶ N) inclusion projection (0 : N ⟶ (0 : E))

private lemma row_complex : row.IsComplex where
  zero i hi := by
    have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases h with rfl | rfl | rfl
    · change (0 : (0 : E) ⟶ N) ≫ inclusion = 0
      simp
    · change inclusion ≫ projection = 0
      ext x
      rfl
    · change projection ≫ (0 : N ⟶ (0 : E)) = 0
      simp

private lemma row_exact : row.Exact where
  toIsComplex := row_complex
  exact i hi := by
    have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases h with rfl | rfl | rfl
    · change (ShortComplex.mk (0 : (0 : E) ⟶ N) inclusion (by simp)).Exact
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
    · change (ShortComplex.mk projection (0 : N ⟶ (0 : E)) (by simp)).Exact
      exact (ShortComplex.exact_iff_epi _ rfl).2 (by infer_instance)

private def exactRow : ExactSequences E 4 := ⟨row, row_exact⟩

private def diagram : Fin 2 ⥤ ExactSequences E 4 :=
  mk₁ ((2 : ℕ) • (𝟙 exactRow))

private abbrev terms (i : Fin 5) : Fin 2 ⥤ E :=
  (exactSequenceFourDiagram diagram).flip.obj i

private instance : HasExactColimitsOfShape (Fin 2) E :=
  HasExactColimitsOfShape.domain_of_functor (Fin 2) (forget₂ E AddCommGrpCat.{1})

private abbrev sequenceColimit := exactSequenceFourColimit diagram

private def atLast (D : Fin 2 ⥤ E) : Cocone D where
  pt := D.obj 1
  ι :=
    { app := fun i => D.map (homOfLE (show i ≤ (1 : Fin 2) from Fin.le_last i))
      naturality := by
        intro i j f
        dsimp
        simp only [Category.comp_id]
        rw [← D.map_comp]
        congr 1
        apply Subsingleton.elim }

private def observe (i : Fin 5) : colimit (terms i) ⟶ (terms i).obj 1 :=
  colimit.desc (terms i) (atLast (terms i))

private lemma observe_coprojection (i : Fin 5) (j : Fin 2) :
    colimit.ι (terms i) j ≫ observe i =
      (terms i).map (homOfLE (show j ≤ (1 : Fin 2) from Fin.le_last j)) :=
  colimit.ι_desc _ _ _

private def one : colimit (terms 1) :=
  (colimit.ι (terms 1) 0).hom (ULift.up (1 : ZMod 6))

private def three : colimit (terms 1) :=
  (colimit.ι (terms 1) 0).hom (ULift.up (3 : ZMod 6))

private lemma observe_one : (observe 1).hom one = ULift.up (2 : ZMod 6) := by
  have h := congrArg (fun f => f.hom (ULift.up (1 : ZMod 6)))
    (observe_coprojection 1 0)
  change (observe 1).hom one =
    ((2 : ℕ) • (𝟙 N)).hom (ULift.up (1 : ZMod 6)) at h
  simpa using h

example : sequenceColimit.Exact := exactSequenceFourColimit_exact diagram

example : (observe 1).hom one ≠ 0 ∧ (observe 1).hom one ≠ ULift.up (1 : ZMod 6) := by
  rw [observe_one]
  constructor <;> decide

example : one ≠ 0 := by
  intro h
  have he := congrArg (observe 1).hom h
  rw [observe_one, map_zero] at he
  exact (by decide : (ULift.up (2 : ZMod 6) : V) ≠ 0) he

example : three = 0 := by
  have h := congrArg (fun f => f.hom (ULift.up (3 : ZMod 6)))
    (colimit.w (terms 1) (homOfLE (show (0 : Fin 2) ≤ 1 from by decide)))
  change (colimit.ι (terms 1) 1).hom
      (((2 : ℕ) • (𝟙 N)).hom (ULift.up (3 : ZMod 6))) = three at h
  have hz : ((2 : ℕ) • (𝟙 N)).hom (ULift.up (3 : ZMod 6)) = 0 := by decide
  rw [hz, map_zero] at h
  exact h.symm

private lemma first_coordinate :
    colimit.ι (terms 1) 0 ≫ sequenceColimit.map' 1 2 ≫ observe 2 =
      inclusion ≫ ((2 : ℕ) • (𝟙 P)) := by
  rw [← Category.assoc, exactSequenceFourColimit_ι_map_one_two]
  rw [Category.assoc, observe_coprojection]
  rfl

example : (observe 2).hom ((sequenceColimit.map' 1 2).hom one) =
    (ULift.up (2 : ZMod 6), ULift.up (0 : ZMod 6)) := by
  have h := congrArg (fun f => f.hom (ULift.up (1 : ZMod 6))) first_coordinate
  change (observe 2).hom ((sequenceColimit.map' 1 2).hom one) = _ at h
  simpa using h

private lemma second_coordinate :
    colimit.ι (terms 2) 0 ≫ sequenceColimit.map' 2 3 ≫ observe 3 =
      projection ≫ ((2 : ℕ) • (𝟙 N)) := by
  rw [← Category.assoc, exactSequenceFourColimit_ι_map_two_three]
  rw [Category.assoc, observe_coprojection]
  rfl

example : (observe 3).hom ((sequenceColimit.map' 2 3).hom
    ((colimit.ι (terms 2) 0).hom
      (ULift.up (0 : ZMod 6), ULift.up (1 : ZMod 6)))) = ULift.up (2 : ZMod 6) := by
  have h := congrArg (fun f => f.hom
    (ULift.up (0 : ZMod 6), ULift.up (1 : ZMod 6))) second_coordinate
  simpa using h

section DegreeZero

private def step (n : ℕ) : N ⟶ N := if n = 0 then (2 : ℕ) • 𝟙 N else 0

private def K : ChainComplex E ℕ :=
  ChainComplex.of (fun _ => N) step (by intro n; simp [step])

private abbrev S : ShortComplex E := K.sc' 1 0 0

private lemma incoming : S.f = (2 : ℕ) • 𝟙 N := by
  change K.d 1 0 = (2 : ℕ) • 𝟙 N
  simp [K, step]

private lemma outgoing : S.g = 0 := by
  change K.d 0 0 = 0
  exact K.shape 0 0 (by decide)

private abbrev N2 : E := ModuleCat.of ℤ (ULift.{1} (ZMod 2))

private def reduction : N ⟶ N2 := ModuleCat.ofHom
  (ULift.moduleEquiv.symm.toLinearMap.comp
    ((ZMod.castHom (by decide : 2 ∣ 6) (ZMod 2)).toAddMonoidHom.toIntLinearMap.comp
      ULift.moduleEquiv.toLinearMap))

private lemma incoming_reduction : S.f ≫ reduction = 0 := by
  rw [incoming]
  ext x
  change reduction.hom ((2 : ℕ) • x) = 0
  rw [map_nsmul]
  apply ULift.ext
  change (2 : ℕ) • (ZMod.castHom (by decide : 2 ∣ 6) (ZMod 2)) x.down = 0
  rw [nsmul_eq_mul]
  norm_num

private def liftOne : N ⟶ S.cycles := S.liftCycles (𝟙 N) (by rw [outgoing]; simp)

private def detect : S.homology ⟶ N2 :=
  S.descHomology (S.iCycles ≫ reduction) (by
    rw [← Category.assoc, ShortComplex.toCycles_i]
    exact incoming_reduction)

private lemma detect_lift : liftOne ≫ S.homologyπ ≫ detect = reduction := by
  simp only [detect, ShortComplex.π_descHomology]
  simp [liftOne]

private abbrev F : E ⥤ ModuleCat.{2} ℤ := ModuleCat.uliftFunctor.{2, 1} ℤ

private def mappedLift : F.obj N ⟶ (S.map F).cycles :=
  (S.map F).liftCycles (𝟙 (F.obj N)) (by
    change 𝟙 (F.obj N) ≫ F.map S.g = 0
    rw [outgoing]
    simp)

private def cyclesIso : (S.map F).cycles ≅ F.obj S.cycles :=
  ShortComplex.leftExactCyclesComparisonIso F S

private lemma lift_comparison : mappedLift ≫ cyclesIso.hom = F.map liftOne := by
  change mappedLift ≫ ShortComplex.leftExactCyclesComparison F S = F.map liftOne
  apply (cancel_mono (F.map S.iCycles)).mp
  rw [Category.assoc, ShortComplex.leftExactCyclesComparison_i]
  simp only [mappedLift, ShortComplex.liftCycles_i]
  rw [← F.map_comp]
  simp [liftOne]

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
      rw [ShortComplex.leftExactHomologyEdge_characteristic]
      rfl
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
    decide

example : (F.map S.iCycles).hom ((cyclesIso.hom).hom
    (mappedLift.hom (ULift.up (ULift.up (1 : ZMod 6))))) =
      ULift.up (ULift.up (1 : ZMod 6)) := by
  have h := congrArg (fun f => f.hom (ULift.up (ULift.up (1 : ZMod 6))))
    (congrArg (fun f => f ≫ F.map S.iCycles) lift_comparison)
  simpa [liftOne, mappedLift, ← F.map_comp] using h

private lemma edge_value : (F.map detect).hom
    ((ShortComplex.leftExactHomologyEdge F S).hom mappedClass) =
      ULift.up (ULift.up (1 : ZMod 2)) := by
  have h := congrArg (fun f => f.hom (ULift.up (ULift.up (1 : ZMod 6))))
    edge_coordinate_map
  change (F.map detect).hom
    ((ShortComplex.leftExactHomologyEdge F S).hom mappedClass) = _ at h
  simpa [F, reduction] using h

example : (F.map detect).hom
    ((ShortComplex.leftExactHomologyEdge F S).hom mappedClass) =
      ULift.up (ULift.up (1 : ZMod 2)) := edge_value

example : (ShortComplex.leftExactHomologyEdge F S).hom mappedClass ≠ 0 := by
  intro h
  have hc := congrArg (F.map detect).hom h
  rw [edge_value, map_zero] at hc
  exact (by decide : (ULift.up (ULift.up (1 : ZMod 2)) : F.obj N2) ≠ 0) hc

end DegreeZero

end MathlibExtTest.ExactSequenceColimit
