/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopPair.ClosedBall
public import MathlibExt.Topology.Sphere.ContinuousLinearEquiv
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Category.TopCat.Sphere

/-!
# Topology facts for `TopPair.closedBallPair`

Reusable facts for `closedBallPair` with classical-cell specializations
to `TopCat.sphere`.
-/

@[expose] public section

universe u v w x

namespace TopPair

/-- Homeomorphism between the spheres of `closedBallPair` at `0` radius `1`
induced by a continuous linear equivalence. -/
noncomputable def closedBallPairUnitSphereHomeomorph
    {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) :
    (closedBallPair.{u} (0 : E) 1).snd ≃ₜ
      (closedBallPair.{u} (0 : F) 1).snd :=
  (Homeomorph.ulift.trans (ContinuousLinearEquiv.unitSphereHomeomorph e)).trans
    Homeomorph.ulift.symm

/-- Identity coherence for the boundary homeomorphism: `refl` maps to the identity. -/
@[simp] theorem closedBallPairUnitSphereHomeomorph_refl
    (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    closedBallPairUnitSphereHomeomorph.{u}
        (ContinuousLinearEquiv.refl ℝ E) =
      Homeomorph.refl (closedBallPair.{u} (0 : E) 1).snd := by
  unfold closedBallPairUnitSphereHomeomorph
  rw [ContinuousLinearEquiv.unitSphereHomeomorph_refl]
  apply Homeomorph.ext
  intro x
  rfl

/-- Composition coherence for the boundary homeomorphism: composition of equivalences
maps to composition of homeomorphisms. -/
theorem closedBallPairUnitSphereHomeomorph_trans
    {E : Type v} {F : Type w} {G : Type x}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (e : E ≃L[ℝ] F) (f : F ≃L[ℝ] G) :
    closedBallPairUnitSphereHomeomorph.{u} (e.trans f) =
      (closedBallPairUnitSphereHomeomorph.{u} e).trans
        (closedBallPairUnitSphereHomeomorph.{u} f) := by
  unfold closedBallPairUnitSphereHomeomorph
  rw [ContinuousLinearEquiv.unitSphereHomeomorph_trans]
  apply Homeomorph.ext
  intro x
  rfl

/-- Inverse coherence for the boundary homeomorphism: the inverse equivalence maps to
the inverse homeomorphism. -/
@[simp] theorem closedBallPairUnitSphereHomeomorph_symm
    {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) :
    (closedBallPairUnitSphereHomeomorph.{u} e).symm =
      closedBallPairUnitSphereHomeomorph.{u} e.symm := by
  unfold closedBallPairUnitSphereHomeomorph
  apply Homeomorph.ext
  intro x
  cases x with
  | up x =>
    change ULift.up ((ContinuousLinearEquiv.unitSphereHomeomorph e).symm x) =
        ULift.up ((ContinuousLinearEquiv.unitSphereHomeomorph e.symm) x)
    rw [ContinuousLinearEquiv.unitSphereHomeomorph_symm]

/-- The `fst` of a closed-ball pair is contractible. -/
theorem contractibleSpace_closedBallPair_fst
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (r : ℝ) (hr : 0 ≤ r) :
    ContractibleSpace (closedBallPair.{u} x r).fst := by
  have h_eq :
      (closedBallPair.{u} (x : E) r).fst =
        TopCat.of (ULift.{u} (Metric.closedBall x r)) :=
    rfl
  have h_contr : ContractibleSpace (Metric.closedBall x r) :=
    Metric.contractibleSpace_closedBall hr
  have h_ulift : ContractibleSpace (ULift.{u} (Metric.closedBall x r)) :=
    let _ : ContractibleSpace (Metric.closedBall x r) := h_contr
    (Homeomorph.ulift (X := Metric.closedBall x r)).contractibleSpace
  rw [h_eq]
  exact h_ulift

/-- The `snd` of a closed-ball pair is empty for subsingleton spaces
with nonzero radius. -/
theorem isEmpty_closedBallPair_snd_of_subsingleton
    {E : Type v} [PseudoMetricSpace E] [Subsingleton E]
    (x : E) (r : ℝ) [NeZero r] :
    IsEmpty (closedBallPair.{u} x r).snd := by
  have h_eq :
      (closedBallPair.{u} (x : E) r).snd =
        TopCat.of (ULift.{u} (Metric.sphere x r)) :=
    rfl
  have h_empty : IsEmpty (Metric.sphere (x : E) r) := inferInstance
  have h_ulift : IsEmpty (ULift.{u} (Metric.sphere x r)) :=
    let _ : IsEmpty (Metric.sphere x r) := h_empty
    (Homeomorph.ulift (X := Metric.sphere x r)).isEmpty
  rw [h_eq]
  exact h_ulift

/-- The `snd` of a closed-ball pair is nonempty for nontrivial normed spaces. -/
theorem nonempty_closedBallPair_snd
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    (x : E) (r : ℝ) (hr : 0 ≤ r) :
    Nonempty (closedBallPair.{u} x r).snd := by
  have h_eq :
      (closedBallPair.{u} (x : E) r).snd =
        TopCat.of (ULift.{u} (Metric.sphere x r)) :=
    rfl
  have h_set : (Metric.sphere x r).Nonempty :=
    (NormedSpace.sphere_nonempty (x := x) (r := r)).mpr hr
  have h_sphere : Nonempty (Metric.sphere x r) := by
    obtain ⟨y, hy⟩ := h_set
    exact ⟨⟨y, hy⟩⟩
  have h_ulift : Nonempty (ULift.{u} (Metric.sphere x r)) :=
    Nonempty.map Homeomorph.ulift.symm.toEquiv h_sphere
  rw [h_eq]
  exact h_ulift

end TopPair

namespace Topology.CWComplex

/-- Homeomorphism from the boundary of the classical `(m+1)`-disk to `𝕊 m`. -/
noncomputable def classicalCellBoundarySphereHomeomorph (m : ℕ) :
    (classicalCellDiskPair.{u} (m + 1)).snd ≃ₜ TopCat.sphere.{u} m :=
  TopPair.closedBallPairUnitSphereHomeomorph
    (E := Fin (m + 1) → ℝ) (F := EuclideanSpace ℝ (Fin (m + 1)))
    (e := (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm)

noncomputable instance contractibleSpace_classicalCellDiskPair_fst
    (n : ℕ) : ContractibleSpace (classicalCellDiskPair.{u} n).fst :=
  TopPair.contractibleSpace_closedBallPair_fst (0 : Fin n → ℝ) 1 (by positivity)

noncomputable instance isEmpty_classicalCellDiskPair_zero_snd :
    IsEmpty (classicalCellDiskPair.{u} 0).snd :=
  TopPair.isEmpty_closedBallPair_snd_of_subsingleton
    (E := Fin 0 → ℝ) 0 1

noncomputable instance nonempty_classicalCellDiskPair_succ_snd
    (m : ℕ) : Nonempty (classicalCellDiskPair.{u} (m + 1)).snd :=
  TopPair.nonempty_closedBallPair_snd (E := Fin (m + 1) → ℝ) 0 1 (by positivity)

end Topology.CWComplex
