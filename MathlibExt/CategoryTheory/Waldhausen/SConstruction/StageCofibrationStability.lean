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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageCofibrationEverywhere
public import MathlibExt.CategoryTheory.Waldhausen.CofibrationArrow

/-!
# Algebra of genuine finite-stage cofibrations

Finite induction proves that every zero-row component of a genuine stage
cofibration is a base cofibration. Its successive zero-row squares are then
the existing relative cofibrations of cofibration arrows. This identifies
the original stage morphism property and derives identity, composition and
isomorphism closure under the general Waldhausen axioms.

This module publicly imports the canonical every-cell cofibration API,
including its `ContainsIdentities`, `RespectsIso`, and `IsMultiplicative`
instances. The named proof values below also supply the corresponding
structure fields. A stage Waldhausen structure is chosen separately.

The canonical identity, composition, and isomorphism helpers infer the
degree from their stage objects. Clients of the former explicit-degree
signatures should replace `stageCofibrations_id C n A` with
`stageCofibrations_id C (n := n) A`, `stageCofibrations_comp C n f g hf hg`
with `stageCofibrations_comp C (n := n) f g hf hg`, and
`stageCofibrations_of_isIso C n f` with
`stageCofibrations_of_isIso C (n := n) f`. Omitting `(n := n)` also works.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Every zero-row component of an actual stage cofibration is a base
cofibration, by the zero-column case and successive cobase changes. -/
theorem Stage.zeroRowApp_isCofibration {n : ℕ} {A B : Stage C n}
    (φ : A ⟶ B) (hφ : stageCofibrations C n φ) (j : Fin (n + 1)) :
    IsCofibration (Stage.zeroRowApp φ j) := by
  have hzero : IsCofibration (Stage.zeroRowApp φ 0) := by
    let : HasZeroMorphisms C := (isZero_zero C).hasZeroMorphisms
    have hA : IsZero (A.zeroRowObj 0) := by
      change IsZero (A.obj.obj (diag (0 : Fin (n + 1))))
      exact A.property.diag_isZero 0
    have hB : IsZero (B.zeroRowObj 0) := by
      change IsZero (B.obj.obj (diag (0 : Fin (n + 1))))
      exact B.property.diag_isZero 0
    let : IsIso (Stage.zeroRowApp φ 0) := IsZero.isIso hA hB _
    exact (WaldhausenCategoryWithoutGluing.cofibrations (C := C)).of_isIso _
  have hstep : ∀ i : Fin n,
      IsCofibration (Stage.zeroRowApp φ i.castSucc) →
        IsCofibration (Stage.zeroRowApp φ i.succ) := by
    intro i hprev
    obtain ⟨P, inl, inr, d, hP, hinl, hinr, hd⟩ := hφ i
    have hInl : IsCofibration inl :=
      MorphismProperty.IsStableUnderCobaseChange.of_isPushout hP hprev
    have hcomp : IsCofibration (inl ≫ d) :=
      (WaldhausenCategoryWithoutGluing.cofibrations (C := C)).comp_mem inl d hInl hd
    rwa [hinl] at hcomp
  exact Fin.induction hzero hstep j

/-- The original successive zero-row cofibration as a functor to the
existing cofibration-arrow category. -/
def zeroRowSuccessorArrow (n : ℕ) (i : Fin n) :
    Stage C n ⥤ Waldhausen.CofibrationArrow C where
  obj A := MorphismProperty.Arrow.mk (A.zeroRowSuccMap i)
    (A.property.cofiber_triple (Fin.zero_le i.castSucc) i.castSucc_le_succ).1
  map φ := MorphismProperty.Arrow.homMk
    (Stage.zeroRowApp φ i.castSucc) (Stage.zeroRowApp φ i.succ)
    (φ.hom.naturality (horiz (Fin.zero_le i.castSucc) i.castSucc_le_succ)).symm
  map_id A := by
    apply MorphismProperty.Arrow.Hom.ext <;> rfl
  map_comp φ ψ := by
    apply MorphismProperty.Arrow.Hom.ext <;> rfl

private theorem stageCofibrations_relativeSuccessors_aux (n : ℕ)
    {A B : Stage C n} (φ : A ⟶ B) :
    stageCofibrations C n φ ↔ ∀ i : Fin n,
      Waldhausen.IsRelativeCofibration C ((zeroRowSuccessorArrow C n i).map φ) := by
  unfold zeroRowSuccessorArrow
  constructor
  · intro hφ i
    refine ⟨Stage.zeroRowApp_isCofibration C φ hφ i.castSucc, ?_⟩
    exact hφ i
  · intro hφ i
    exact (hφ i).2

/-- The original stage cofibration property is exactly relative
cofibration of every original successive zero-row square. -/
theorem stageCofibrations_iff_relativeSuccessors (n : ℕ)
    {A B : Stage C n} (φ : A ⟶ B) :
    stageCofibrations C n φ ↔ ∀ i : Fin n,
      Waldhausen.IsRelativeCofibration C ((zeroRowSuccessorArrow C n i).map φ) :=
  stageCofibrations_relativeSuccessors_aux C n φ

/-- Maps from any actual zero stage are genuine stage cofibrations.
The successor corner is the target's previous zero-row object. -/
theorem stageCofibrations_of_isZero_source (n : ℕ) {A B : Stage C n}
    (φ : A ⟶ B) (hA : IsZero A) : stageCofibrations C n φ := by
  let : HasZeroMorphisms C := (isZero_zero C).hasZeroMorphisms
  have hDiagram : IsZero A.obj := (forget C n).map_isZero hA
  intro i
  have hPrev : IsZero (A.zeroRowObj i.castSucc) :=
    ((evaluation (Ar n) C).obj (interval 0 i.castSucc (Fin.zero_le _))).map_isZero hDiagram
  have hNext : IsZero (A.zeroRowObj i.succ) :=
    ((evaluation (Ar n) C).obj (interval 0 i.succ (Fin.zero_le _))).map_isZero hDiagram
  let : IsIso (A.zeroRowSuccMap i) := IsZero.isIso hPrev hNext _
  let inl : A.zeroRowObj i.succ ⟶ B.zeroRowObj i.castSucc :=
    hNext.to_ (B.zeroRowObj i.castSucc)
  refine ⟨B.zeroRowObj i.castSucc, inl, 𝟙 _, B.zeroRowSuccMap i, ?_, ?_, ?_, ?_⟩
  · exact IsPushout.of_horiz_isIso ⟨hPrev.eq_of_src _ _⟩
  · exact hNext.eq_of_src _ _
  · exact Category.id_comp _
  · exact (B.property.cofiber_triple (Fin.zero_le i.castSucc) i.castSucc_le_succ).1

/-- Named multiplicativity proof for the original stage cofibrations,
using the canonical identity and composition helpers. -/
theorem stageCofibrationsMultiplicative (n : ℕ) :
    (stageCofibrations C n).IsMultiplicative where
  id_mem A := stageCofibrations_id C A
  comp_mem φ ψ := stageCofibrations_comp C φ ψ

/-- Named isomorphism-respecting proof for the original stage
cofibrations, with no chosen stage Waldhausen witness. -/
theorem stageCofibrationsRespectsIso (n : ℕ) :
    (stageCofibrations C n).RespectsIso :=
  stageCofibrations_respectsIso C n

end CategoryTheory.Waldhausen.SConstruction
