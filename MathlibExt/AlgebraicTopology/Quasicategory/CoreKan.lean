/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.Core
public import MathlibExt.AlgebraicTopology.Quasicategory.EdgeEquivalenceInv
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
# The maximal core of a quasicategory, special outer horns, and Kan-ness

This file is the T17 follow-up to the former TODO recorded in
`MathlibExt/AlgebraicTopology/Quasicategory/Core.lean`: if `X` is a
quasicategory, then its maximal core `SSet.core X` should be a Kan
complex. The mathematical input was Joyal's special outer horn
filling: fillers for `Λ[n, 0]` resp. `Λ[n, n]` whose
`(0, 1)`-edge resp. `(n - 1, n)`-edge is an equivalence. That filling
is not proved in this file in general dimensions; it is proved in
`MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHornGeneral`
(`SSet.hasSpecialOuterHornFilling_of_quasicategory`, packet T21),
which also proves `SSet.kanComplex_core_of_quasicategory` from the
reduction in this file. Packet T08 (`EdgeEquivalenceInv.lean`) landed
`Edge.IsEquivalence → Nonempty Edge.InvStruct` for quasicategories,
by `2`-truncated methods only.

What is proved in this file:

* an inner-horn lifting lemma for a quasicategory in
  `horn.IsCompatible` form (`horn.IsCompatible.exists_lift_of_quasicategory`,
  with the chosen filler `horn.IsCompatible.liftOfQuasicategory`),
  mirroring the Kan-complex API `liftOfKanComplex`;
* extraction of the distinguished edges of outer horns
  (`SSet.leftHornEdge`, `SSet.rightHornEdge`), and the observation
  that they are equivalences for a horn factoring through the core
  (`leftHornEdge_isEquivalence_of_factor_core`,
  `rightHornEdge_isEquivalence_of_factor_core`);
* special outer horn filling in dimension `2`, in edge form
  (`Edge.exists_compStruct_of_isEquivalence_left`,
  `Edge.exists_compStruct_of_isEquivalence_right`: the missing edge
  is the composite, in the homotopy category, of an inverse edge
  with the given long edge, and the composition relation is lifted
  to a `CompStruct` by
  `Edge.nonempty_compStruct_of_homMk_comp_eq` of T08) and in horn
  form (`exists_fill_horn_two_zero_of_isEquivalence`,
  `exists_fill_horn_two_last_of_isEquivalence`);
* the complete reduction of Kan-ness of the core to special outer
  horn filling (`kanComplex_core_of_special_horn_filling`): under
  the explicitly stated filling hypotheses in dimensions at least
  `2`, the core of a quasicategory is a Kan complex. Inner horns of
  the core are filled because the core is a quasicategory
  (`Core.lean`); a `1`-dimensional outer horn is filled by a
  degenerate identity edge; an outer horn of dimension at least `2`
  in the core is an outer horn in `X` whose distinguished edge is
  an equivalence, a filler in `X` is supplied by the hypothesis,
  and the filler is lifted to the core by
  `SSet.hasLiftingProperty_horn_core_ι` of `Core.lean`. In
  particular the core of a Kan complex is a Kan complex
  (`kanComplex_core_of_kanComplex`, also an instance), with no extra
  hypothesis, because a Kan complex fills every horn.

## Not proved in this file

* Discharging the hypotheses of
  `kanComplex_core_of_special_horn_filling` in dimensions `n ≥ 3`
  is not proved in this file; it is proved in
  `MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHornGeneral`
  (packet T21: `SSet.hasSpecialOuterHornFilling_of_quasicategory`,
  by Dugger's filtration after Joyal; Dugger–Spivak, *Mapping
  spaces in quasi-categories*, Appendix B.9). That module applies
  the reduction above to obtain `KanComplex (core X : SSet)` for
  `[Quasicategory X]` (`SSet.kanComplex_core_of_quasicategory`).
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite
open scoped Simplicial

universe v u

namespace SSet

variable {X : SSet.{u}}

namespace horn.IsCompatible

variable {n : ℕ} {i : Fin (n + 2)}
  {f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), Δ[n] ⟶ X}

/-- A quasicategory fills every inner horn presented as a compatible
family of face maps. This is the quasicategory analogue of
`horn.IsCompatible.exists_lift_of_kanComplex`. -/
lemma exists_lift_of_quasicategory [Quasicategory X]
    (h0 : 0 < i) (hn : i < Fin.last (n + 1)) (hf : horn.IsCompatible f) :
    ∃ (φ : Δ[n + 1] ⟶ X),
      ∀ (j : Fin (n + 2)) (hj : j ≠ i), stdSimplex.δ j ≫ φ = f j hj := by
  obtain ⟨φ, hφ⟩ := Quasicategory.hornFilling h0 hn hf.desc
  refine ⟨φ, fun j hj ↦ ?_⟩
  rw [← horn.ι_ι i j hj, Category.assoc, ← hφ]
  exact horn.IsCompatible.ι_desc hf j hj

/-- A chosen filler, in a quasicategory, of an inner horn presented
as a compatible family of face maps. This is the quasicategory
analogue of `horn.IsCompatible.liftOfKanComplex`. -/
noncomputable def liftOfQuasicategory [Quasicategory X]
    (h0 : 0 < i) (hn : i < Fin.last (n + 1)) (hf : horn.IsCompatible f) :
    Δ[n + 1] ⟶ X :=
  (exists_lift_of_quasicategory h0 hn hf).choose

/-- The faces of the chosen quasicategory filler of an inner horn
are the prescribed face maps. -/
@[reassoc]
lemma δ_liftOfQuasicategory [Quasicategory X]
    (h0 : 0 < i) (hn : i < Fin.last (n + 1)) (hf : horn.IsCompatible f)
    (j : Fin (n + 2)) (hj : j ≠ i) :
    stdSimplex.δ j ≫ hf.liftOfQuasicategory h0 hn = f j hj :=
  (exists_lift_of_quasicategory h0 hn hf).choose_spec j hj

end horn.IsCompatible

section HornEdges

/-- The `(0, 1)`-edge of the left outer horn `Λ[n + 2, 0]`, as a
`1`-simplex of the horn. The numerical hypothesis of
`SSet.horn.edge` holds because the finset `{0, 0, 1}` has
cardinality at most `2`. -/
def leftHornEdgeSimplex (n : ℕ) :
    (Λ[n + 2, (0 : Fin (n + 3))] : SSet.{u}) _⦋1⦌ :=
  horn.edge (n + 2) 0 0 ⟨1, by omega⟩ (Fin.zero_le _) (by
    have hsub : ({(0 : Fin (n + 3)), (0 : Fin (n + 3)),
        (⟨1, by omega⟩ : Fin (n + 3))} : Finset (Fin (n + 3))) ⊆
        {0, ⟨1, by omega⟩} := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      tauto
    exact (Finset.card_le_card hsub).trans
      ((Finset.card_le_two).trans (by omega)))

/-- The `(n + 1, n + 2)`-edge of the right outer horn
`Λ[n + 2, n + 2]`, as a `1`-simplex of the horn. The numerical
hypothesis of `SSet.horn.edge` holds because the finset
`{n + 2, n + 1, n + 2}` has cardinality at most `2`. -/
def rightHornEdgeSimplex (n : ℕ) :
    (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) _⦋1⦌ :=
  horn.edge (n + 2) (Fin.last (n + 2)) ⟨n + 1, by omega⟩ (Fin.last (n + 2))
    (by simp [Fin.le_def]) (by
    have hsub : ({Fin.last (n + 2), (⟨n + 1, by omega⟩ : Fin (n + 3)),
        Fin.last (n + 2)} : Finset (Fin (n + 3))) ⊆
        {⟨n + 1, by omega⟩, Fin.last (n + 2)} := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      tauto
    exact (Finset.card_le_card hsub).trans
      ((Finset.card_le_two).trans (by omega)))

/-- The `(0, 1)`-edge of a left outer horn `σ₀ : Λ[n + 2, 0] ⟶ X`:
the first edge of the horn, whose being an equivalence is the
hypothesis of Joyal's special outer horn filling. -/
def leftHornEdge {n : ℕ} (σ₀ : (Λ[n + 2, (0 : Fin (n + 3))] : SSet.{u}) ⟶ X) :
    Edge (X.δ 1 (σ₀.app _ (leftHornEdgeSimplex.{u} n)))
      (X.δ 0 (σ₀.app _ (leftHornEdgeSimplex.{u} n))) :=
  Edge.mk' (σ₀.app _ (leftHornEdgeSimplex.{u} n))

/-- The underlying `1`-simplex of the `(0, 1)`-edge of a left outer
horn is the image of `leftHornEdgeSimplex`. -/
@[simp]
lemma leftHornEdge_edge {n : ℕ}
    (σ₀ : (Λ[n + 2, (0 : Fin (n + 3))] : SSet.{u}) ⟶ X) :
    (leftHornEdge σ₀).edge = σ₀.app _ (leftHornEdgeSimplex.{u} n) :=
  rfl

/-- The `(n + 1, n + 2)`-edge of a right outer horn
`σ₀ : Λ[n + 2, n + 2] ⟶ X`: the last edge of the horn, whose being
an equivalence is the hypothesis of the dual special outer horn
filling. -/
def rightHornEdge {n : ℕ}
    (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ X) :
    Edge (X.δ 1 (σ₀.app _ (rightHornEdgeSimplex.{u} n)))
      (X.δ 0 (σ₀.app _ (rightHornEdgeSimplex.{u} n))) :=
  Edge.mk' (σ₀.app _ (rightHornEdgeSimplex.{u} n))

/-- The underlying `1`-simplex of the last edge of a right outer
horn is the image of `rightHornEdgeSimplex`. -/
@[simp]
lemma rightHornEdge_edge {n : ℕ}
    (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ X) :
    (rightHornEdge σ₀).edge = σ₀.app _ (rightHornEdgeSimplex.{u} n) :=
  rfl

/-- If a left outer horn `Λ[n + 2, 0] ⟶ X` factors through the
core of `X`, then its `(0, 1)`-edge is an equivalence: it is a
`1`-simplex of the core. -/
theorem leftHornEdge_isEquivalence_of_factor_core {n : ℕ}
    (τ : (Λ[n + 2, (0 : Fin (n + 3))] : SSet.{u}) ⟶ (core X : SSet.{u})) :
    (leftHornEdge (τ ≫ (core X).ι)).IsEquivalence := by
  have hmem : (τ ≫ (core X).ι).app _ (leftHornEdgeSimplex.{u} n) ∈
      (core X).obj (op ⦋1⦌) :=
    (τ.app _ (leftHornEdgeSimplex.{u} n)).2
  exact mem_core_obj_one_iff.mp hmem

/-- If a right outer horn `Λ[n + 2, n + 2] ⟶ X` factors through the
core of `X`, then its last edge is an equivalence: it is a
`1`-simplex of the core. -/
theorem rightHornEdge_isEquivalence_of_factor_core {n : ℕ}
    (τ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ (core X : SSet.{u})) :
    (rightHornEdge (τ ≫ (core X).ι)).IsEquivalence := by
  have hmem : (τ ≫ (core X).ι).app _ (rightHornEdgeSimplex.{u} n) ∈
      (core X).obj (op ⦋1⦌) :=
    (τ.app _ (rightHornEdgeSimplex.{u} n)).2
  exact mem_core_obj_one_iff.mp hmem

end HornEdges

namespace Edge

variable {x₀ x₁ x₂ : X _⦋0⦌}

/-- Special outer horn filling for `Λ[2, 0]`, in edge form: in a
quasicategory, given an equivalence edge `e₀₁` and a long edge
`e₀₂` with the same source, there is an edge `e₁₂` and a
`2`-simplex witnessing it as a composite of `e₀₁` and `e₁₂`. The
edge `e₁₂` represents, in the homotopy category, the composite of
an inverse of `e₀₁` with `e₀₂`; the composition relation is then
lifted to a `CompStruct`. -/
theorem exists_compStruct_of_isEquivalence_left [Quasicategory X]
    {e₀₁ : Edge x₀ x₁} (h : e₀₁.IsEquivalence) (e₀₂ : Edge x₀ x₂) :
    ∃ e₁₂ : Edge x₁ x₂, Nonempty (CompStruct e₀₁ e₁₂ e₀₂) := by
  obtain ⟨I⟩ := h.nonempty_invStruct
  obtain ⟨e₁₂, he₁₂⟩ :=
    exists_homMk_eq (HomotopyCategory.homMk I.inv ≫ HomotopyCategory.homMk e₀₂)
  refine ⟨e₁₂, nonempty_compStruct_of_homMk_comp_eq ?_⟩
  rw [he₁₂, ← Category.assoc, HomotopyCategory.homMk_comp_homMk I.homInvId,
    HomotopyCategory.homMk_id, Category.id_comp]

/-- Special outer horn filling for `Λ[2, 2]`, in edge form: in a
quasicategory, given an equivalence edge `e₁₂` and a long edge
`e₀₂` with the same target, there is an edge `e₀₁` and a
`2`-simplex witnessing `e₀₂` as a composite of `e₀₁` and `e₁₂`.
The edge `e₀₁` represents, in the homotopy category, the composite
of `e₀₂` with an inverse of `e₁₂`; the composition relation is
then lifted to a `CompStruct`. -/
theorem exists_compStruct_of_isEquivalence_right [Quasicategory X]
    {e₁₂ : Edge x₁ x₂} (h : e₁₂.IsEquivalence) (e₀₂ : Edge x₀ x₂) :
    ∃ e₀₁ : Edge x₀ x₁, Nonempty (CompStruct e₀₁ e₁₂ e₀₂) := by
  obtain ⟨I⟩ := h.nonempty_invStruct
  obtain ⟨e₀₁, he₀₁⟩ :=
    exists_homMk_eq (HomotopyCategory.homMk e₀₂ ≫ HomotopyCategory.homMk I.inv)
  refine ⟨e₀₁, nonempty_compStruct_of_homMk_comp_eq ?_⟩
  rw [he₀₁, Category.assoc, HomotopyCategory.homMk_comp_homMk I.invHomId,
    HomotopyCategory.homMk_id, Category.comp_id]

end Edge

section TwoDimensionalHorns

/-- The `2`-face (`(0, 1)`-edge face) of `Λ[2, 0]` is the
`1`-simplex `leftHornEdgeSimplex 0`, by finite computation. -/
private lemma horn_face_two_eq_leftHornEdgeSimplex :
    horn.face (0 : Fin 3) 2 (by decide) = leftHornEdgeSimplex.{u} 0 := by
  decide

/-- The `0`-face (`(1, 2)`-edge face) of `Λ[2, 2]` is the
`1`-simplex `rightHornEdgeSimplex 0`, by finite computation. -/
private lemma horn_face_zero_eq_rightHornEdgeSimplex :
    horn.face (2 : Fin 3) 0 (by decide) = rightHornEdgeSimplex.{u} 0 := by
  decide

/-- Special outer horn filling for `Λ[2, 0]` in a quasicategory: a
horn whose `(0, 1)`-edge is an equivalence extends to `Δ[2]`. This
is `Edge.exists_compStruct_of_isEquivalence_left` read through the
face maps of the horn. -/
theorem exists_fill_horn_two_zero_of_isEquivalence [Quasicategory X]
    (σ₀ : (Λ[2, (0 : Fin 3)] : SSet.{u}) ⟶ X)
    (h : (leftHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[2] ⟶ X, σ₀ = Λ[2, (0 : Fin 3)].ι ≫ σ := by
  set s₀₂ := σ₀.app _ (horn.face (0 : Fin 3) 1 (by decide)) with hs₀₂
  set s₀₁ := σ₀.app _ (horn.face (0 : Fin 3) 2 (by decide)) with hs₀₁
  have hcompat : X.δ 1 s₀₂ = X.δ 1 s₀₁ := by
    have hf₁ : horn.ι (0 : Fin 3) 1 (by decide) ≫ σ₀ =
        yonedaEquiv.symm s₀₂ := by
      rw [horn.ι, yonedaEquiv_symm_comp, hs₀₂]
    have hf₂ : horn.ι (0 : Fin 3) 2 (by decide) ≫ σ₀ =
        yonedaEquiv.symm s₀₁ := by
      rw [horn.ι, yonedaEquiv_symm_comp, hs₀₁]
    have hc := (horn.IsCompatible.of_hom σ₀).δ_pred_comp
      (1 : Fin 3) (2 : Fin 3) (by decide) (by decide) (by decide)
    rw [hf₁, hf₂, stdSimplex.δ_comp_yonedaEquiv_symm,
      stdSimplex.δ_comp_yonedaEquiv_symm] at hc
    exact yonedaEquiv.symm.injective hc
  have hed : (leftHornEdge σ₀).edge = s₀₁ := by
    rw [leftHornEdge_edge, hs₀₁, horn_face_two_eq_leftHornEdgeSimplex]
  have h₀₁ : (Edge.mk' s₀₁).IsEquivalence :=
    (Edge.isEquivalence_iff_of_edge_eq (show
      (leftHornEdge σ₀).edge = (Edge.mk' s₀₁).edge from hed)).mp h
  obtain ⟨e₁₂, ⟨c⟩⟩ := Edge.exists_compStruct_of_isEquivalence_left h₀₁
    (Edge.mk s₀₂ hcompat rfl)
  refine ⟨yonedaEquiv.symm c.simplex, horn.hom_ext' fun j hj ↦ ?_⟩
  rw [← Category.assoc, horn.ι_ι, horn.ι, yonedaEquiv_symm_comp,
    stdSimplex.δ_comp_yonedaEquiv_symm]
  fin_cases j
  · exact absurd rfl hj
  · exact congr_arg yonedaEquiv.symm c.d₁.symm
  · exact congr_arg yonedaEquiv.symm c.d₂.symm

/-- Special outer horn filling for `Λ[2, 2]` in a quasicategory: a
horn whose `(1, 2)`-edge is an equivalence extends to `Δ[2]`. This
is `Edge.exists_compStruct_of_isEquivalence_right` read through
the face maps of the horn. -/
theorem exists_fill_horn_two_last_of_isEquivalence [Quasicategory X]
    (σ₀ : (Λ[2, Fin.last 2] : SSet.{u}) ⟶ X)
    (h : (rightHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[2] ⟶ X, σ₀ = Λ[2, Fin.last 2].ι ≫ σ := by
  set s₁₂ := σ₀.app _ (horn.face (Fin.last 2) 0 (by decide)) with hs₁₂
  set s₀₂ := σ₀.app _ (horn.face (Fin.last 2) 1 (by decide)) with hs₀₂
  have hcompat : X.δ 0 s₀₂ = X.δ 0 s₁₂ := by
    have hf₀ : horn.ι (Fin.last 2) 0 (by decide) ≫ σ₀ =
        yonedaEquiv.symm s₁₂ := by
      rw [horn.ι, yonedaEquiv_symm_comp, hs₁₂]
    have hf₁ : horn.ι (Fin.last 2) 1 (by decide) ≫ σ₀ =
        yonedaEquiv.symm s₀₂ := by
      rw [horn.ι, yonedaEquiv_symm_comp, hs₀₂]
    have hc := (horn.IsCompatible.of_hom σ₀).δ_pred_comp
      (0 : Fin 3) (1 : Fin 3) (by decide) (by decide) (by decide)
    rw [hf₀, hf₁, stdSimplex.δ_comp_yonedaEquiv_symm,
      stdSimplex.δ_comp_yonedaEquiv_symm] at hc
    exact (yonedaEquiv.symm.injective hc).symm
  have hed : (rightHornEdge σ₀).edge = s₁₂ := by
    have hface : horn.face (Fin.last 2) 0 (by decide) =
        rightHornEdgeSimplex.{u} 0 := horn_face_zero_eq_rightHornEdgeSimplex
    rw [rightHornEdge_edge, hs₁₂, hface]
  have h₁₂ : (Edge.mk' s₁₂).IsEquivalence :=
    (Edge.isEquivalence_iff_of_edge_eq (show
      (rightHornEdge σ₀).edge = (Edge.mk' s₁₂).edge from hed)).mp h
  obtain ⟨e₀₁, ⟨c⟩⟩ := Edge.exists_compStruct_of_isEquivalence_right h₁₂
    (Edge.mk s₀₂ rfl hcompat)
  refine ⟨yonedaEquiv.symm c.simplex, horn.hom_ext' fun j hj ↦ ?_⟩
  rw [← Category.assoc, horn.ι_ι, horn.ι, yonedaEquiv_symm_comp,
    stdSimplex.δ_comp_yonedaEquiv_symm]
  fin_cases j
  · exact congr_arg yonedaEquiv.symm c.d₀.symm
  · exact congr_arg yonedaEquiv.symm c.d₁.symm
  · exact absurd rfl hj

end TwoDimensionalHorns

/-- Joyal's special outer horn filling property for a simplicial
set `X`, in dimensions at least `2`: every left outer horn
`Λ[n + 2, 0] ⟶ X` whose `(0, 1)`-edge is an equivalence extends to
`Δ[n + 2]`, and every right outer horn `Λ[n + 2, n + 2] ⟶ X` whose
last edge is an equivalence extends to `Δ[n + 2]`. For `n = 0` this
is proved for every quasicategory in this file
(`exists_fill_horn_two_zero_of_isEquivalence`,
`exists_fill_horn_two_last_of_isEquivalence`); for `n ≥ 1` it is
proved in
`MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHornGeneral`
(`SSet.hasSpecialOuterHornFilling_of_quasicategory`). -/
def HasSpecialOuterHornFilling (X : SSet.{u}) : Prop :=
  (∀ {n : ℕ} (σ₀ : (Λ[n + 2, (0 : Fin (n + 3))] : SSet.{u}) ⟶ X),
    (leftHornEdge σ₀).IsEquivalence →
      ∃ σ : Δ[n + 2] ⟶ X, σ₀ = Λ[n + 2, (0 : Fin (n + 3))].ι ≫ σ) ∧
  (∀ {n : ℕ} (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ X),
    (rightHornEdge σ₀).IsEquivalence →
      ∃ σ : Δ[n + 2] ⟶ X, σ₀ = Λ[n + 2, Fin.last (n + 2)].ι ≫ σ)

/-- The left outer horn filling component of
`HasSpecialOuterHornFilling`. -/
theorem HasSpecialOuterHornFilling.left {X : SSet.{u}}
    (h : HasSpecialOuterHornFilling X) {n : ℕ}
    (σ₀ : (Λ[n + 2, (0 : Fin (n + 3))] : SSet.{u}) ⟶ X)
    (hσ : (leftHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[n + 2] ⟶ X, σ₀ = Λ[n + 2, (0 : Fin (n + 3))].ι ≫ σ :=
  h.1 σ₀ hσ

/-- The right outer horn filling component of
`HasSpecialOuterHornFilling`. -/
theorem HasSpecialOuterHornFilling.right {X : SSet.{u}}
    (h : HasSpecialOuterHornFilling X) {n : ℕ}
    (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ X)
    (hσ : (rightHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[n + 2] ⟶ X, σ₀ = Λ[n + 2, Fin.last (n + 2)].ι ≫ σ :=
  h.2 σ₀ hσ

/-- A Kan complex has special outer horn filling, because it fills
every horn. -/
theorem hasSpecialOuterHornFilling_of_kanComplex (X : SSet.{u})
    [KanComplex X] : HasSpecialOuterHornFilling X :=
  ⟨fun σ₀ _ ↦ KanComplex.hornFilling σ₀,
    fun σ₀ _ ↦ KanComplex.hornFilling σ₀⟩

section CoreKan

variable [Quasicategory X]

/-- The reduction of Kan-ness of the core to special outer horn
filling: if a quasicategory `X` fills its special outer horns in
dimensions at least `2`, then its maximal core is a Kan complex.
Inner horns of the core are filled because the core is a
quasicategory; a `1`-dimensional outer horn of the core is filled
by the degenerate edge at its vertex; an outer horn of dimension
at least `2` in the core is an outer horn in `X` whose
distinguished edge lies in the core, hence is an equivalence, a
filler in `X` is supplied by the hypothesis, and that filler is
lifted to the core by `SSet.hasLiftingProperty_horn_core_ι`. -/
theorem kanComplex_core_of_special_horn_filling
    (hsp : HasSpecialOuterHornFilling X) :
    KanComplex (core X : SSet.{u}) := by
  rw [KanComplex.iff]
  intro n i f hf
  rcases n with _ | k
  · fin_cases i
    · refine ⟨yonedaEquiv.symm ((core X : SSet.{u}).σ 0
        (yonedaEquiv (f 1 (by decide)))), fun j hj ↦ ?_⟩
      fin_cases j
      · exact absurd rfl hj
      · apply yonedaEquiv.injective
        rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
        change (core X : SSet.{u}).δ 1 _ = _
        simpa using ConcreteCategory.congr_hom
          (SimplicialObject.δ_comp_σ_succ' (core X : SSet.{u})
            (show (1 : Fin 2) = Fin.succ 0 from rfl))
          (yonedaEquiv (f 1 (by decide)))
    · refine ⟨yonedaEquiv.symm ((core X : SSet.{u}).σ 0
        (yonedaEquiv (f 0 (by decide)))), fun j hj ↦ ?_⟩
      fin_cases j
      · apply yonedaEquiv.injective
        rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
        change (core X : SSet.{u}).δ 0 _ = _
        simpa using ConcreteCategory.congr_hom
          (SimplicialObject.δ_comp_σ_self' (core X : SSet.{u})
            (show (0 : Fin 2) = Fin.castSucc 0 from rfl))
          (yonedaEquiv (f 0 (by decide)))
      · exact absurd rfl hj
  · by_cases hi0 : i = 0
    · subst hi0
      obtain ⟨σ, hσ⟩ := hsp.left (hf.desc ≫ (core X).ι)
        (leftHornEdge_isEquivalence_of_factor_core hf.desc)
      have sq : CommSq hf.desc Λ[k + 2, (0 : Fin (k + 3))].ι
          (core X).ι σ := by
        constructor
        exact hσ
      obtain ⟨l, hl, -⟩ :=
        (hasLiftingProperty_horn_core_ι (0 : Fin (k + 3))).sq_hasLift sq
      refine ⟨l, fun j hj ↦ ?_⟩
      calc stdSimplex.δ j ≫ l
          = horn.ι (0 : Fin (k + 3)) j hj ≫
            (Λ[k + 2, (0 : Fin (k + 3))].ι ≫ l) := by
            rw [← Category.assoc, horn.ι_ι]
        _ = horn.ι (0 : Fin (k + 3)) j hj ≫ hf.desc := by
            rw [hl]
        _ = f j hj := horn.IsCompatible.ι_desc hf j hj
    · by_cases hilast : i = Fin.last (k + 2)
      · subst hilast
        obtain ⟨σ, hσ⟩ := hsp.right (hf.desc ≫ (core X).ι)
          (rightHornEdge_isEquivalence_of_factor_core hf.desc)
        have sq : CommSq hf.desc Λ[k + 2, Fin.last (k + 2)].ι
            (core X).ι σ := by
          constructor
          exact hσ
        obtain ⟨l, hl, -⟩ :=
          (hasLiftingProperty_horn_core_ι
            (Fin.last (k + 2))).sq_hasLift sq
        refine ⟨l, fun j hj ↦ ?_⟩
        calc stdSimplex.δ j ≫ l
            = horn.ι (Fin.last (k + 2)) j hj ≫
              (Λ[k + 2, Fin.last (k + 2)].ι ≫ l) := by
              rw [← Category.assoc, horn.ι_ι]
          _ = horn.ι (Fin.last (k + 2)) j hj ≫ hf.desc := by
              rw [hl]
          _ = f j hj := horn.IsCompatible.ι_desc hf j hj
      · exact hf.exists_lift_of_quasicategory
          (Fin.pos_iff_ne_zero.mpr hi0)
          (Fin.lt_last_iff_ne_last.mpr hilast)

/-- The core of a Kan complex is a Kan complex: a Kan complex fills
every horn, in particular its special outer horns. (By
`SSet.core_eq_top_of_kanComplex` the core is in fact the whole
simplicial set.) -/
theorem kanComplex_core_of_kanComplex (X : SSet.{u}) [KanComplex X] :
    KanComplex (core X : SSet.{u}) :=
  kanComplex_core_of_special_horn_filling
    (hasSpecialOuterHornFilling_of_kanComplex X)

/-- The core of a Kan complex is a Kan complex, as an instance. -/
instance (priority := low) [KanComplex X] :
    KanComplex (core X : SSet.{u}) :=
  kanComplex_core_of_kanComplex X

end CoreKan

end SSet
