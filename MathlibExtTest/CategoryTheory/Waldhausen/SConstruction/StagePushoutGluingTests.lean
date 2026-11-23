/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenGluing

/-!
# Tests for general stage pushouts and gluing

The pushout constructor supplies its whole square, each interval square,
and its cobase cofibration in arbitrary finite degree. The induced map
between two constructed pushouts is weak when the three maps of spans
are weak and the base category satisfies the gluing axiom.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.Waldhausen.SConstruction

universe u v

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
namespace StagePushoutGluingTests

variable {C : Type u} [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategory C]

/-- The general constructor supplies all three pushout properties. -/
example {n : ℕ} {A B D : Stage C n} (i : A ⟶ B) (f : A ⟶ D)
    (hi : stageCofibrations C n i) :
    let P := GeneralStagePushoutPresentation.ofStageCofibration i f hi
    IsPushout f i P.inl P.inr ∧ stageCofibrations C n P.inl ∧
      ∀ x : Ar n, IsPushout (f.hom.app x) (i.hom.app x)
        (P.inl.hom.app x) (P.inr.hom.app x) := by
  let P := GeneralStagePushoutPresentation.ofStageCofibration i f hi
  change IsPushout f i P.inl P.inr ∧ stageCofibrations C n P.inl ∧
    ∀ x : Ar n, IsPushout (f.hom.app x) (i.hom.app x)
      (P.inl.hom.app x) (P.inr.hom.app x)
  exact ⟨P.isPushout, P.inlCofibration, P.appIsPushout⟩

/-- Degree zero obtains the cofibration proof from the empty condition. -/
example {A B D : Stage C 0} (i : A ⟶ B) (f : A ⟶ D) :
    ∃ (P : Stage C 0) (inD : D ⟶ P) (inB : B ⟶ P),
      IsPushout f i inD inB ∧ stageCofibrations C 0 inD := by
  have hi : stageCofibrations C 0 i := by
    intro j
    exact Fin.elim0 j
  let P := GeneralStagePushoutPresentation.ofStageCofibration i f hi
  exact ⟨P.apex, P.inl, P.inr, P.isPushout, P.inlCofibration⟩

/-- In every positive degree the constructed apex retains all triples. -/
example {n : ℕ} {A B D : Stage C (n + 1)}
    (i : A ⟶ B) (f : A ⟶ D) (hi : stageCofibrations C (n + 1) i) :
    let P := GeneralStagePushoutPresentation.ofStageCofibration i f hi
    ∀ {a b c : Fin (n + 2)} (hab : a ≤ b) (hbc : b ≤ c),
      IsCofibrationSequence (P.apex.obj.map (horiz hab hbc))
        (P.apex.obj.map (vert hab hbc)) := by
  let P := GeneralStagePushoutPresentation.ofStageCofibration i f hi
  change ∀ {a b c : Fin (n + 2)} (hab : a ≤ b) (hbc : b ≤ c),
    IsCofibrationSequence (P.apex.obj.map (horiz hab hbc))
      (P.apex.obj.map (vert hab hbc))
  intro a b c hab hbc
  exact P.apex.property.cofiber_triple hab hbc

/-- Degree two reads the source, middle and quotient of the new apex. -/
example {A B D : Stage C 2} (i : A ⟶ B) (f : A ⟶ D)
    (hi : stageCofibrations C 2 i) :
    let P := GeneralStagePushoutPresentation.ofStageCofibration i f hi
    let a : Fin 3 := ⟨0, by decide⟩
    let b : Fin 3 := ⟨1, by decide⟩
    let c : Fin 3 := ⟨2, by decide⟩
    IsCofibrationSequence
      (P.apex.obj.map
        (horiz (show a ≤ b by decide) (show b ≤ c by decide)))
      (P.apex.obj.map
        (vert (show a ≤ b by decide) (show b ≤ c by decide))) := by
  let P := GeneralStagePushoutPresentation.ofStageCofibration i f hi
  exact P.apex.property.cofiber_triple
    (show (⟨0, by decide⟩ : Fin 3) ≤ ⟨1, by decide⟩ by decide)
    (show (⟨1, by decide⟩ : Fin 3) ≤ ⟨2, by decide⟩ by decide)

/-- Base gluing proves the induced pushout map weak in every degree. -/
example (hGlue : WaldhausenGluingAxiom (C := C)) {n : ℕ}
    {A B D A' B' D' : Stage C n}
    (i : A ⟶ B) (f : A ⟶ D) (i' : A' ⟶ B') (f' : A' ⟶ D')
    (hi : stageCofibrations C n i) (hi' : stageCofibrations C n i')
    (a : A ⟶ A') (b : B ⟶ B') (d : D ⟶ D')
    (hI : i ≫ b = a ≫ i') (hF : f ≫ d = a ≫ f')
    (ha : stageWeak C n a) (hb : stageWeak C n b)
    (hd : stageWeak C n d) :
    let P := GeneralStagePushoutPresentation.ofStageCofibration i f hi
    let P' := GeneralStagePushoutPresentation.ofStageCofibration i' f' hi'
    ∃ (p : P.apex ⟶ P'.apex),
      P.inr ≫ p = b ≫ P'.inr ∧ P.inl ≫ p = d ≫ P'.inl ∧
        stageWeak C n p := by
  let P := GeneralStagePushoutPresentation.ofStageCofibration i f hi
  let P' := GeneralStagePushoutPresentation.ofStageCofibration i' f' hi'
  change ∃ (p : P.apex ⟶ P'.apex),
    P.inr ≫ p = b ≫ P'.inr ∧ P.inl ≫ p = d ≫ P'.inl ∧
      stageWeak C n p
  have w : f ≫ (d ≫ P'.inl) = i ≫ (b ≫ P'.inr) := by
    calc
      f ≫ (d ≫ P'.inl) = (f ≫ d) ≫ P'.inl :=
        (Category.assoc _ _ _).symm
      _ = (a ≫ f') ≫ P'.inl :=
        congrArg (fun q => q ≫ P'.inl) hF
      _ = a ≫ (f' ≫ P'.inl) := Category.assoc _ _ _
      _ = a ≫ (i' ≫ P'.inr) :=
        congrArg (fun q => a ≫ q) P'.isPushout.w
      _ = (a ≫ i') ≫ P'.inr := (Category.assoc _ _ _).symm
      _ = (i ≫ b) ≫ P'.inr :=
        congrArg (fun q => q ≫ P'.inr) hI.symm
      _ = i ≫ (b ≫ P'.inr) := Category.assoc _ _ _
  let p : P.apex ⟶ P'.apex :=
    P.isPushout.desc (d ≫ P'.inl) (b ≫ P'.inr) w
  have hD : P.inl ≫ p = d ≫ P'.inl :=
    P.isPushout.inl_desc (d ≫ P'.inl) (b ≫ P'.inr) w
  have hB : P.inr ≫ p = b ≫ P'.inr :=
    P.isPushout.inr_desc (d ≫ P'.inl) (b ≫ P'.inr) w
  let : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
  let : WaldhausenCategory (Stage C n) :=
    generalStageWaldhausenCategory C n
  have hStage : WaldhausenGluingAxiom (C := Stage C n) :=
    generalStageWaldhausenGluingAxiom C hGlue n
  have hp : IsWeakEquivalence p :=
    hStage.gluing P.isPushout.flip P'.isPushout.flip a b d p
      ((isCofibration_generalStageWaldhausenCategory_iff C n i).mpr hi)
      ((isCofibration_generalStageWaldhausenCategory_iff C n i').mpr hi')
      hI hF hB hD
      ((isWeakEquivalence_generalStageWaldhausenCategory_iff C n a).mpr ha)
      ((isWeakEquivalence_generalStageWaldhausenCategory_iff C n b).mpr hb)
      ((isWeakEquivalence_generalStageWaldhausenCategory_iff C n d).mpr hd)
  exact ⟨p, hB, hD,
    (isWeakEquivalence_generalStageWaldhausenCategory_iff C n p).mp hp⟩

end StagePushoutGluingTests
end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
