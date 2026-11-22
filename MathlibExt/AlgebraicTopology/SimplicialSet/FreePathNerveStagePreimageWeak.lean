/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreePathNerveStagePushout
import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexOuterFacesWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceCoproducts
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure

/-!
# The full actual original stage preimage inclusion is weak

Each actual original path label retains its SAME two outer-face cell
preimage. The entire native indexed preimage is their complete labelled
coproduct. Both full original inclusions and inverse coefficient maps
are retained. Actual outer-face weakness and native coproduct stability
prove weakness of the SAME original preimage inclusion.
-/

noncomputable section
universe u v
open CategoryTheory Limits Opposite
open scoped Simplicial SSet.modelCategoryQuillen
namespace CategoryTheory.FreePathNerveCoordinates
variable (V : Type u) [Quiver.{v} V]

/-- The SAME two original outer faces at each full original word label. -/
def labelOuterFaces (k : ℕ) (a : WordLabel V (k + 2)) : (labelSimplex V (k + 2) a).Subcomplex :=
  SSet.stdSimplex.face {(0 : Fin (a.path.length + 1))}ᶜ ⊔
    SSet.stdSimplex.face {Fin.last a.path.length}ᶜ

/-- Every SAME full original labelled outer-face inclusion is weak. -/
lemma labelOuterFaces_weak (k : ℕ) (a : WordLabel V (k + 2)) :
    SSet.realizationWeakEquivalences (labelOuterFaces V k a).ι := by
  exact SSet.stdSimplex.outerFaces_union_weak_of_two_le a.path.length (by
    have h := a.length_eq
    omega)

/-- The full native sum of all SAME original outer-face subcomplexes. -/
abbrev outerFaceCells (k : ℕ) : SSet.{max u v} :=
  SSet.IndexedSums.object (fun a : WordLabel V (k + 2) => (labelOuterFaces V k a : SSet.{max u v}))

/-- The whole original indexed outer-face coefficient maps to the SAME native old-stage preimage. -/
def outerFacesToPreimage (k : ℕ) : outerFaceCells V k ⟶
    ((lengthStage V (k + 1)).preimage (stageCellMap V (k + 2)) : SSet.{max u v}) where
  app q := ↾fun a => ⟨⟨a.1, a.2.val⟩, by
    have he := congrArg (fun K => K.obj q) (wordCell_preimage_lengthStage V a.1.path (k + 1)
      (by simpa only [Nat.add_assoc] using a.1.length_eq))
    change (wordCell V a.1.path).app q a.2.val ∈ (lengthStage V (k + 1)).obj q
    exact (congrArg (fun S => a.2.val ∈ S) he).mpr a.2.property⟩
  naturality q r f := by
    apply ConcreteCategory.hom_ext
    intro a
    rfl

/-- The whole original preimage map retains the SAME original label and full simplex coefficient. -/
lemma outerFacesToPreimage_ι (k : ℕ) :
    outerFacesToPreimage V k ≫ ((lengthStage V (k + 1)).preimage (stageCellMap V (k + 2))).ι =
      SSet.IndexedSums.map (fun a : WordLabel V (k + 2) => (labelOuterFaces V k a : SSet.{max u v}))
        (fun a => (labelOuterFaces V k a).ι) := rfl

/-- Both full original coefficient operations recover every labelled native preimage simplex. -/
instance outerFacesToPreimage_isIso (k : ℕ) : IsIso (outerFacesToPreimage V k) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro q
  rw [isIso_iff_bijective]
  constructor
  · intro a b h
    have he := congrArg Subtype.val h
    have hl := Sigma.mk.inj_iff.mp he
    cases a with
    | mk a c =>
      cases b with
      | mk b d =>
        dsimp at hl
        obtain ⟨rfl, hc⟩ := hl
        have hcd : c = d := Subtype.ext (eq_of_heq hc)
        subst d
        rfl
  · rintro ⟨⟨a, c⟩, hc⟩
    have he := congrArg (fun K => K.obj q) (wordCell_preimage_lengthStage V a.path (k + 1)
      (by simpa only [Nat.add_assoc] using a.length_eq))
    have hm : c ∈ (labelOuterFaces V k a).obj q :=
      (congrArg (fun S => c ∈ S) he).mp hc
    exact ⟨⟨a, ⟨c, hm⟩⟩, rfl⟩

/-- The SAME whole native original preimage inclusion is genuinely weak,
with all full path labels and complete original outer-face coefficients retained. -/
theorem original_stage_preimage_weak (k : ℕ) :
    SSet.realizationWeakEquivalences ((lengthStage V (k + 1)).preimage (stageCellMap V (k + 2))).ι := by
  apply SSet.realizationWeakEquivalences.of_precomp (outerFacesToPreimage V k) _
    (SSet.realizationWeakEquivalences.of_isIso _)
  rw [outerFacesToPreimage_ι]
  exact SSet.IndexedSums.map_property _ SSet.realizationWeakEquivalences _ (labelOuterFaces_weak V k)

/-- EVERY same original nonzero word-length stage inclusion is weak by its actual native all-word pushout. -/
theorem original_stage_inclusion_weak (k : ℕ) :
    SSet.realizationWeakEquivalences (SSet.Subcomplex.homOfLE
      (lengthStage_mono V (Nat.le_succ (k + 1)))) := by
  let _ : HomotopicalAlgebra.ModelCategory SSet.{max u v} := SSet.modelCategoryQuillen.modelCategory
  let q := ((lengthStage V (k + 1)).preimage (stageCellMap V (k + 2))).ι
  have hc : HomotopicalAlgebra.Cofibration q := SSet.modelCategoryQuillen.cofibration_of_mono q
  have hw : HomotopicalAlgebra.WeakEquivalence q :=
    (HomotopicalAlgebra.weakEquivalence_iff q).mpr (original_stage_preimage_weak V k)
  have htc : HomotopicalAlgebra.trivialCofibrations SSet.{max u v} q :=
    (HomotopicalAlgebra.mem_trivialCofibrations_iff q).mpr ⟨hc, hw⟩
  have hnew := (HomotopicalAlgebra.trivialCofibrations SSet.{max u v}).of_isPushout
    (original_stage_isPushout V (k + 1)) htc
  exact (HomotopicalAlgebra.weakEquivalence_iff _).mp
    ((HomotopicalAlgebra.mem_trivialCofibrations_iff _).mp hnew).2

end CategoryTheory.FreePathNerveCoordinates
