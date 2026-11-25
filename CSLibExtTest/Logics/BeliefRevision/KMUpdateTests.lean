/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.BeliefRevision.KMUpdate

/-!
# Boundary and non-vacuity probes for KM update

Empty-input behavior of any (U1)–(U8) operator, incomparability in Winslett's order on the
two-atom example, and a trivial order that is not an update assignment.
-/

@[expose] public section

namespace Cslib.BeliefRevision


/-- Boundary (KM Lemma 3.1): by (U2), updating the empty (inconsistent) model set gives the
empty set. -/
theorem SatisfiesKMUpdate.update_empty_left {σ : Type*} [Fintype σ] [DecidableEq σ]
    {upd : Finset (Interp σ) → Finset (Interp σ) → Finset (Interp σ)}
    (h : SatisfiesKMUpdate upd) (B : Finset (Interp σ)) : upd ∅ B = ∅ := by
  exact h.u2 ∅ B (Finset.empty_subset B)

/-- Boundary: by (U1), updating by the empty model set gives the empty set. -/
theorem SatisfiesKMUpdate.update_empty_right {σ : Type*} [Fintype σ] [DecidableEq σ]
    {upd : Finset (Interp σ) → Finset (Interp σ) → Finset (Interp σ)}
    (h : SatisfiesKMUpdate upd) (A : Finset (Interp σ)) : upd A ∅ = ∅ := by
  exact Finset.subset_empty.mp (h.u1 A ∅)

/-- Non-totality probe: relative to `00`, the PMA order does not compare `10` and `01`, whose
`Diff` sets are `{0}` and `{1}`, so a totality requirement would exclude PMA. -/
theorem pmaLe_incomparable :
    ¬ pmaLe (σ := Fin 2) ![false, false] ![true, false] ![false, true] ∧
      ¬ pmaLe (σ := Fin 2) ![false, false] ![false, true] ![true, false] := by
  constructor
  · unfold pmaLe; decide
  · unfold pmaLe; decide

/-- Min-set probe: relative to `00`, both `10` and `01` are minimal in `{10, 01}`. Minimality
means having no strictly better member, not being below every member. -/
theorem pma_minSet_incomparable :
    minSet (pmaLe (σ := Fin 2) ![false, false])
        ({![true, false], ![false, true]} : Finset (Interp (Fin 2))) =
      {![true, false], ![false, true]} := by
  have nle1 : ¬ pmaLe (σ := Fin 2) ![false, false] ![true, false] ![false, true] := by
    unfold pmaLe; decide
  have nle2 : ¬ pmaLe (σ := Fin 2) ![false, false] ![false, true] ![true, false] := by
    unfold pmaLe; decide
  ext X
  simp only [mem_minSet, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hX, -⟩; exact hX
  · intro hX
    refine ⟨hX, ?_⟩
    intro J hJ
    rcases hX with rfl | rfl <;> rcases hJ with rfl | rfl
    · exact fun hcon => hcon.2 hcon.1
    · exact fun hcon => nle2 hcon.1
    · exact fun hcon => nle1 hcon.1
    · exact fun hcon => hcon.2 hcon.1

/-- Strictness probe: with the trivial preorder, under which `I` is below but not strictly
below the other interpretations, the induced operator fails (U2) on one atom. The strict
clause of faithfulness is needed. -/
theorem trivialOrder_not_satisfiesKMUpdate :
    ¬ SatisfiesKMUpdate (σ := Fin 1)
      (fun A B => A.biUnion fun _ => minSet (fun _ _ => True) B) := by
  intro h
  have h2 := h.u2 {![true]} {![true], ![false]} (by decide)
  have hmin : minSet (fun _ _ : Interp (Fin 1) => True) {![true], ![false]} =
      {![true], ![false]} := by
    ext X
    simp only [mem_minSet, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hX, -⟩; exact hX
    · intro hX
      refine ⟨hX, ?_⟩
      intro J hJ hcon
      exact hcon.2 hcon.1
  simp only [Finset.singleton_biUnion] at h2
  have hcon := hmin.symm.trans h2
  revert hcon
  decide


end Cslib.BeliefRevision
