/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageCofibrationStability
public import MathlibExt.CategoryTheory.Waldhausen.CofibrationCornerHorizontal
public import MathlibExt.CategoryTheory.Waldhausen.CofiberCornerQuotient

/-!
# All zero-row corners and interval components of stage cofibrations

The successive relative-corner condition of a genuine finite-stage
cofibration implies the same condition for every pair of columns in the
zero row. Finite induction uses horizontal pasting of actual corners.
The original cofiber row from `(0,i)` through `(0,j)` to `(i,j)` then
identifies every interval component as a cobase change of such a corner.

These are named theorem values over the general Waldhausen axioms.
No global Waldhausen structure on stages is installed.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

namespace Stage

/-- The original zero-row map for an arbitrary pair of ordered columns. -/
def zeroRowPairMap {n : ℕ} (A : Stage C n) {i j : Fin (n + 1)} (hij : i ≤ j) :
    A.zeroRowObj i ⟶ A.zeroRowObj j :=
  A.obj.map (horiz (Fin.zero_le i) hij)

private theorem zeroRowPairMap_eq_aux {n : ℕ} (A : Stage C n)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    A.zeroRowPairMap hij = A.obj.map (horiz (Fin.zero_le i) hij) := rfl

/-- Public computation of the canonical pair map in the original diagram. -/
theorem zeroRowPairMap_eq {n : ℕ} (A : Stage C n)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    A.zeroRowPairMap hij = A.obj.map (horiz (Fin.zero_le i) hij) :=
  zeroRowPairMap_eq_aux A hij

private theorem zeroRowPairMap_isCofibration_aux {n : ℕ} (A : Stage C n)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    IsCofibration (A.zeroRowPairMap hij) := by
  rw [zeroRowPairMap_eq]
  exact (A.property.cofiber_triple (Fin.zero_le i) hij).1

/-- Every original zero-row pair map is a base cofibration of its stage. -/
theorem zeroRowPairMap_isCofibration {n : ℕ} (A : Stage C n)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    IsCofibration (A.zeroRowPairMap hij) :=
  zeroRowPairMap_isCofibration_aux A hij

/-- Scalar naturality of an original zero-row pair map. -/
theorem zeroRowPairMap_naturality {n : ℕ} {A B : Stage C n}
    (φ : A ⟶ B) {i j : Fin (n + 1)} (hij : i ≤ j) :
    A.zeroRowPairMap hij ≫ Stage.zeroRowApp φ j =
      Stage.zeroRowApp φ i ≫ B.zeroRowPairMap hij := by
  simpa only [zeroRowPairMap_eq, zeroRowApp, zeroRowObj] using
    φ.hom.naturality (horiz (Fin.zero_le i) hij)

/-- An equal-endpoint zero-row map is the identity of the original object. -/
theorem zeroRowPairMap_refl {n : ℕ} (A : Stage C n) (i : Fin (n + 1)) :
    A.zeroRowPairMap (le_refl i) = 𝟙 (A.zeroRowObj i) := by
  have hId : horiz (Fin.zero_le i) (le_refl i) =
      𝟙 (interval 0 i (Fin.zero_le i)) := by
    apply Arrow.hom_ext <;> exact Subsingleton.elim _ _
  change A.obj.map (horiz (Fin.zero_le i) (le_refl i)) = 𝟙 _
  rw [hId, A.obj.map_id]

/-- Zero-row maps compose as the original diagram maps. -/
theorem zeroRowPairMap_comp {n : ℕ} (A : Stage C n)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    A.zeroRowPairMap hij ≫ A.zeroRowPairMap hjk =
      A.zeroRowPairMap (hij.trans hjk) := by
  have hcomp : horiz (Fin.zero_le i) hij ≫ horiz (Fin.zero_le j) hjk =
      horiz (Fin.zero_le i) (hij.trans hjk) := by
    apply Arrow.hom_ext <;> exact Subsingleton.elim _ _
  change A.obj.map (horiz (Fin.zero_le i) hij) ≫
    A.obj.map (horiz (Fin.zero_le j) hjk) =
      A.obj.map (horiz (Fin.zero_le i) (hij.trans hjk))
  calc
    A.obj.map (horiz (Fin.zero_le i) hij) ≫
        A.obj.map (horiz (Fin.zero_le j) hjk) =
      A.obj.map (horiz (Fin.zero_le i) hij ≫ horiz (Fin.zero_le j) hjk) :=
        (A.obj.map_comp _ _).symm
    _ = A.obj.map (horiz (Fin.zero_le i) (hij.trans hjk)) :=
      congrArg (fun f => A.obj.map f) hcomp

end Stage

variable (C)

/-- An arbitrary original zero-row arrow as a cofibration-arrow functor. -/
def zeroRowPairArrow (n : ℕ) (i j : Fin (n + 1)) (hij : i ≤ j) :
    Stage C n ⥤ Waldhausen.CofibrationArrow C where
  obj A := MorphismProperty.Arrow.mk (A.zeroRowPairMap hij)
    (A.property.cofiber_triple (Fin.zero_le i) hij).1
  map φ := MorphismProperty.Arrow.homMk
    (Stage.zeroRowApp φ i) (Stage.zeroRowApp φ j)
    (φ.hom.naturality (horiz (Fin.zero_le i) hij)).symm
  map_id A := by
    apply MorphismProperty.Arrow.Hom.ext <;> rfl
  map_comp φ ψ := by
    apply MorphismProperty.Arrow.Hom.ext <;> rfl

/-- Every pair of zero-row columns of a genuine stage cofibration has an
actual relative corner whose map to the target column is a cofibration. -/
theorem Stage.zeroRowPair_corner {n : ℕ} {A B : Stage C n}
    (φ : A ⟶ B) (hφ : stageCofibrations C n φ)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    ∃ (P : C) (inl : A.zeroRowObj j ⟶ P) (inr : B.zeroRowObj i ⟶ P)
      (d : P ⟶ B.zeroRowObj j),
      IsPushout (A.zeroRowPairMap hij) (Stage.zeroRowApp φ i) inl inr ∧
        inl ≫ d = Stage.zeroRowApp φ j ∧
        inr ≫ d = B.zeroRowPairMap hij ∧ IsCofibration d := by
  revert i
  induction j using Fin.induction with
  | zero =>
      intro i hij
      have hieq : i = 0 := le_antisymm hij (Fin.zero_le i)
      subst i
      simp only [Stage.zeroRowPairMap_refl]
      refine ⟨B.zeroRowObj 0, Stage.zeroRowApp φ 0, 𝟙 _, 𝟙 _,
        IsPushout.of_id_fst, ?_, ?_, ?_⟩
      · exact Category.comp_id _
      · exact Category.id_comp _
      · exact (WaldhausenCategoryWithoutGluing.cofibrations (C := C)).id_mem _
  | succ j ih =>
      intro i hij
      by_cases heq : i = j.succ
      · subst i
        simp only [Stage.zeroRowPairMap_refl]
        refine ⟨B.zeroRowObj j.succ, Stage.zeroRowApp φ j.succ, 𝟙 _, 𝟙 _,
          IsPushout.of_id_fst, ?_, ?_, ?_⟩
        · exact Category.comp_id _
        · exact Category.id_comp _
        · exact (WaldhausenCategoryWithoutGluing.cofibrations (C := C)).id_mem _
      · have hip : i ≤ j.castSucc := by
          have hilt : i < j.succ := lt_of_le_of_ne hij heq
          have hval : i.val < j.val + 1 := by
            simpa only [Fin.lt_def, Fin.val_succ] using hilt
          rw [Fin.le_iff_val_le_val]
          exact Nat.lt_succ_iff.mp hval
        obtain ⟨P, p₁, p₀, dP, hP, hp₁, hp₀, hdP⟩ := ih hip
        obtain ⟨Q, q₂, q₁, dQ, hQ, hq₂, hq₁, hdQ⟩ := hφ j
        have hTop : IsCofibration (A.zeroRowSuccMap j) :=
          (A.property.cofiber_triple (Fin.zero_le j.castSucc)
            j.castSucc_le_succ).1
        obtain ⟨R, r₂, r₀, dR, hR, hr₂, hr₀, hdR⟩ :=
          Waldhausen.cofibrationCorner_paste_horiz C hTop
            hP hp₁ hp₀ hdP hQ hq₂ hq₁ hdQ
        change IsPushout
          (A.zeroRowPairMap hip ≫ A.zeroRowPairMap j.castSucc_le_succ)
          (Stage.zeroRowApp φ i) r₂ r₀ at hR
        change r₀ ≫ dR =
          B.zeroRowPairMap hip ≫ B.zeroRowPairMap j.castSucc_le_succ at hr₀
        refine ⟨R, r₂, r₀, dR, ?_, hr₂, ?_, hdR⟩
        · simpa only [Stage.zeroRowPairMap_comp] using hR
        · simpa only [Stage.zeroRowPairMap_comp] using hr₀

/-- Genuine stage cofibrations are relative cofibrations of every
original zero-row arrow, including pairs with equal endpoints. -/
theorem stageCofibrations_relativeZeroRowPair {n : ℕ} {A B : Stage C n}
    (φ : A ⟶ B) (hφ : stageCofibrations C n φ)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    Waldhausen.IsRelativeCofibration C ((zeroRowPairArrow C n i j hij).map φ) := by
  constructor
  · exact Stage.zeroRowApp_isCofibration C φ hφ i
  · exact Stage.zeroRowPair_corner C φ hφ hij

/-- Every original interval component of a genuine stage cofibration is
a base cofibration, through its original cofiber row and relative corner. -/
theorem Stage.intervalApp_isCofibration {n : ℕ} {A B : Stage C n}
    (φ : A ⟶ B) (hφ : stageCofibrations C n φ)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    IsCofibration (φ.hom.app (interval i j hij)) := by
  obtain ⟨P, inl, inr, d, hP, hinl, hinr, hd⟩ :=
    Stage.zeroRowPair_corner C φ hφ hij
  have hSeq : IsCofiberSequence (A.zeroRowPairMap hij)
      (A.obj.map (vert (Fin.zero_le i) hij)) :=
    A.property.cofiber_triple (Fin.zero_le i) hij
  have hSeq' : IsCofiberSequence (B.zeroRowPairMap hij)
      (B.obj.map (vert (Fin.zero_le i) hij)) :=
    B.property.cofiber_triple (Fin.zero_le i) hij
  have hqc : A.obj.map (vert (Fin.zero_le i) hij) ≫
      φ.hom.app (interval i j hij) =
        Stage.zeroRowApp φ j ≫ B.obj.map (vert (Fin.zero_le i) hij) :=
    φ.hom.naturality (vert (Fin.zero_le i) hij)
  exact Waldhausen.cofiberCorner_quotient_isCofibration C hSeq hSeq'
    (Stage.zeroRowApp φ i) (Stage.zeroRowApp φ j)
    (φ.hom.app (interval i j hij)) hP hinl hinr hqc hd

end CategoryTheory.Waldhausen.SConstruction
