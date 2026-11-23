/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Setoid.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-! # Common knowledge in partition models

Aumann's partition model of differential information (Aumann 1976, p. 1236–1237; Aumann
1987, §3): a set `Ω` of states of the world and, for each agent `i`, an information partition,
here a `Setoid Ω` `r i`. At state `ω` agent `i` is told the cell `cell (r i) ω` that contains
`ω`; agent `i` *knows* an event `E` at `ω` when that cell is contained in `E`.

In Mathlib's order on `Setoid Ω` (`r ≤ s` when `r` is finer than `s`), the supremum
`⨆ i, r i` is the finest common coarsening of the partitions, which Aumann calls their *meet*
(Aumann 1976, footnote 6). An event is *common knowledge* at `ω` when it contains the cell of
the meet that contains `ω` (Aumann 1976, p. 1237).

## Main results

* `isCommonKnowledgeAt_iff_forall_knowsChain`: an event is common knowledge at `ω` exactly
  when every finite statement "`i₁` knows that `i₂` knows that … `iₖ` knows `E`" holds at
  `ω`. This is the equivalence between the formal and the informal definitions argued in
  Aumann 1976, p. 1237 (there for two agents; here for any family of agents).
* `isCommonKnowledgeAt_level_set`: a function that every agent knows (constant on each agent's
  cells) is constant on the cells of the meet, so its value is common knowledge.
* `sum_nonpos_of_forall_sum_cell_nonpos`: on a finite state space, a sum is nonpositive as soon
  as its restriction to every cell of one partition is; this is the "sum over the cells"
  step of the proofs of the agreement theorem (Aumann 1976, p. 1237) and of the Main Theorem
  of Aumann 1987 (p. 7–8).

## References

* R. J. Aumann, "Agreeing to disagree", Ann. Statist. 4(6) (1976), 1236–1239.
* R. J. Aumann, "Correlated equilibrium as an expression of Bayesian rationality",
  Econometrica 55(1) (1987), 1–18, §3.
-/

namespace MathlibExt.GameTheory.InteractiveEpistemology

variable {Ω : Type*}

/-- **Information cell.** The cell of the partition `r` that contains `ω`: the set of states
that the agent with information partition `r` cannot distinguish from `ω` (Aumann 1976,
p. 1237: "if the true state of the world is `ω`, then `i` is informed of that element
`𝒫ᵢ(ω)` of `𝒫ᵢ` that contains `ω`"). -/
def cell (r : Setoid Ω) (ω : Ω) : Set Ω := {ω' | r ω' ω}

/-- **Knowledge operator.** The event "the agent with partition `r` knows `E`": the set of
states whose cell is contained in `E` (Aumann 1976, p. 1237: "to say that 1 'knows' `E`
means that `E` includes `P₁`"). -/
def knows (r : Setoid Ω) (E : Set Ω) : Set Ω := {ω | cell r ω ⊆ E}

/-- **Common knowledge.** The event `E` is common knowledge at `ω` among agents with
information partitions `r i` when `E` includes the cell of the meet `⨆ i, r i` (finest common
coarsening) that contains `ω` (Aumann 1976, p. 1237, with footnote 6 for the meet). -/
def IsCommonKnowledgeAt {ι : Type*} (r : ι → Setoid Ω) (E : Set Ω) (ω : Ω) : Prop :=
  cell (⨆ i, r i) ω ⊆ E

/-- **Iterated knowledge along a chain of agents.** For a list `[i₁, …, iₖ]`, the event
"`i₁` knows that `i₂` knows that … `iₖ` knows `E`"; the empty list gives `E` itself
(Aumann 1976, p. 1237). -/
def knowsChain {ι : Type*} (r : ι → Setoid Ω) (l : List ι) (E : Set Ω) : Set Ω :=
  l.foldr (fun i F => knows (r i) F) E

@[simp] theorem mem_cell {r : Setoid Ω} {ω ω' : Ω} : ω' ∈ cell r ω ↔ r ω' ω := Iff.rfl

theorem mem_cell_self (r : Setoid Ω) (ω : Ω) : ω ∈ cell r ω := r.refl ω

theorem cell_eq_of_rel {r : Setoid Ω} {ω ω' : Ω} (h : r ω' ω) : cell r ω' = cell r ω := by
  ext x
  exact ⟨fun hx => r.trans hx h, fun hx => r.trans hx (r.symm h)⟩

theorem cell_mono {r s : Setoid Ω} (h : r ≤ s) (ω : Ω) : cell r ω ⊆ cell s ω :=
  fun _ hx => Setoid.le_def.mp h hx

/-- **What is known is true.** `knows r E ⊆ E` (the truth axiom of knowledge). -/
theorem knows_subset (r : Setoid Ω) (E : Set Ω) : knows r E ⊆ E :=
  fun ω h => h (mem_cell_self r ω)

/-- **Common knowledge is constant on the cells of the meet.** If `E` is common knowledge at
`ω`, it is common knowledge at every state that the meet does not distinguish from `ω`. -/
theorem isCommonKnowledgeAt_of_meet_rel {ι : Type*} {r : ι → Setoid Ω} {E : Set Ω} {ω ω' : Ω}
    (h : IsCommonKnowledgeAt r E ω) (h' : (⨆ i, r i) ω' ω) : IsCommonKnowledgeAt r E ω' := by
  unfold IsCommonKnowledgeAt
  rwa [cell_eq_of_rel h']

/-- **Common knowledge is known by everyone.** If `E` is common knowledge at `ω`, then every
agent knows at `ω` that `E` is common knowledge. -/
theorem isCommonKnowledgeAt_mem_knows {ι : Type*} {r : ι → Setoid Ω} {E : Set Ω} {ω : Ω}
    (h : IsCommonKnowledgeAt r E ω) (i : ι) :
    ω ∈ knows (r i) {ω' | IsCommonKnowledgeAt r E ω'} :=
  fun _ hω' => isCommonKnowledgeAt_of_meet_rel h (Setoid.le_def.mp (le_iSup r i) hω')

/-- **Common knowledge as iterated knowledge.** The event `E` is common knowledge at `ω`
(it contains the cell of the meet that contains `ω`) if and only if, for every finite chain
of agents `i₁, …, iₖ`, it is true at `ω` that `i₁` knows that `i₂` knows that … `iₖ` knows
`E`. This is the equivalence of the formal and the informal definitions of common knowledge
argued in Aumann 1976, p. 1237 (for two agents, via chains of cells that alternately belong
to the two partitions); here the family of agents is arbitrary. -/
theorem isCommonKnowledgeAt_iff_forall_knowsChain {ι : Type*} (r : ι → Setoid Ω) (E : Set Ω)
    (ω : Ω) : IsCommonKnowledgeAt r E ω ↔ ∀ l : List ι, ω ∈ knowsChain r l E := by
  constructor
  · intro h l
    induction l generalizing ω with
    | nil => exact h (mem_cell_self _ ω)
    | cons i l ih =>
      intro ω' hω'
      exact ih _ (isCommonKnowledgeAt_of_meet_rel h (Setoid.le_def.mp (le_iSup r i) hω'))
  · intro h ω' hω'
    let R : Ω → Ω → Prop := fun a b => ∃ i, r i a b
    have hle : (⨆ i, r i) ≤ Relation.EqvGen.setoid R :=
      iSup_le fun i => Setoid.le_def.mpr fun hab => Relation.EqvGen.rel _ _ ⟨i, hab⟩
    have hgen : Relation.EqvGen R ω' ω := Setoid.le_def.mp hle hω'
    have : Std.Symm R := ⟨fun _ _ ⟨i, hab⟩ => ⟨i, (r i).symm hab⟩⟩
    rw [Relation.EqvGen.eqvGen_eq_reflTransGen] at hgen
    have key : ∀ b, Relation.ReflTransGen R ω' b →
        ∃ l : List ι, ∀ F : Set Ω, b ∈ knowsChain r l F → ω' ∈ F := by
      intro b hb
      induction hb with
      | refl => exact ⟨[], fun _ hF => hF⟩
      | tail _ hbc ih =>
        obtain ⟨l, hl⟩ := ih
        obtain ⟨i, hi⟩ := hbc
        exact ⟨i :: l, fun F hF => hl F (hF hi)⟩
    obtain ⟨l, hl⟩ := key ω hgen
    exact hl E (h l)

/-- **Values of commonly known functions are common knowledge.** If a function `f` is known by
every agent (each partition `r i` is finer than the partition `Setoid.ker f` into level sets of
`f`), then `f` is constant on the cells of the meet (Mathlib's `iSup_le`), so the event
`{f = f ω}` is common knowledge at `ω`. -/
theorem isCommonKnowledgeAt_level_set {ι β : Type*} {r : ι → Setoid Ω} {f : Ω → β}
    (h : ∀ i, r i ≤ Setoid.ker f) (ω : Ω) : IsCommonKnowledgeAt r {ω' | f ω' = f ω} ω :=
  fun _ hω' => Setoid.ker_def.mp (Setoid.le_def.mp (iSup_le h) hω')

section Finite

variable [Fintype Ω]

open Classical in
/-- **Information cell as a finset.** On a finite state space, the cell `cell r ω` as a
`Finset`. -/
noncomputable def cellFinset (r : Setoid Ω) (ω : Ω) : Finset Ω :=
  Finset.univ.filter fun ω' => r ω' ω

open Classical in
@[simp] theorem mem_cellFinset {r : Setoid Ω} {ω ω' : Ω} : ω' ∈ cellFinset r ω ↔ r ω' ω := by
  simp [cellFinset]

@[simp] theorem coe_cellFinset (r : Setoid Ω) (ω : Ω) : (cellFinset r ω : Set Ω) = cell r ω := by
  ext; simp

theorem cellFinset_eq_of_rel {r : Setoid Ω} {ω ω' : Ω} (h : r ω' ω) :
    cellFinset r ω' = cellFinset r ω := by
  ext x
  simp only [mem_cellFinset]
  exact ⟨fun hx => r.trans hx h, fun hx => r.trans hx (r.symm h)⟩

/-- **Averaging cell sums.** On a finite state space, the total sum of `f` equals the sum over
all states `ω` of the sum of `f` over the cell of `ω`, divided by the size of that cell: each
cell is counted once in total. -/
theorem sum_eq_sum_inv_card_mul_sum_cell (r : Setoid Ω) (f : Ω → ℝ) :
    ∑ x, f x = ∑ ω, ((cellFinset r ω).card : ℝ)⁻¹ * ∑ x ∈ cellFinset r ω, f x := by
  classical
  have hcard : ∀ x, ((cellFinset r x).card : ℝ) ≠ 0 := fun x => by
    have : x ∈ cellFinset r x := mem_cellFinset.mpr (r.refl x)
    exact_mod_cast (Finset.card_pos.mpr ⟨x, this⟩).ne'
  calc ∑ x, f x = ∑ x, ∑ ω ∈ cellFinset r x, ((cellFinset r ω).card : ℝ)⁻¹ * f x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_congr rfl fun ω hω => by
          rw [cellFinset_eq_of_rel (mem_cellFinset.mp hω)]]
        rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (hcard x), one_mul]
    _ = ∑ x, ∑ ω, if r x ω then ((cellFinset r ω).card : ℝ)⁻¹ * f x else 0 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext ω
        simp only [mem_cellFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => r.symm h, fun h => r.symm h⟩
    _ = ∑ ω, ∑ x, if r x ω then ((cellFinset r ω).card : ℝ)⁻¹ * f x else 0 := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [Finset.mul_sum, ← Finset.sum_filter]
        rfl

/-- **Summing over the cells (inequality).** On a finite state space, if the sum of `f` over
every cell of the partition `r` is nonpositive, then the total sum of `f` is nonpositive. This
is the step "multiplying by `Prob P` and summing over all `P` in `𝒫ⁱ`" of Aumann 1987, p. 8. -/
theorem sum_nonpos_of_forall_sum_cell_nonpos (r : Setoid Ω) {f : Ω → ℝ}
    (h : ∀ ω, ∑ x ∈ cellFinset r ω, f x ≤ 0) : ∑ x, f x ≤ 0 := by
  rw [sum_eq_sum_inv_card_mul_sum_cell r f]
  exact Finset.sum_nonpos fun ω _ =>
    mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (Nat.cast_nonneg _)) (h ω)

/-- **Summing over the cells (equality).** On a finite state space, if the sum of `f` over every
cell of the partition `r` vanishes, then the total sum of `f` vanishes ("summing over `j`",
Aumann 1976, p. 1237). -/
theorem sum_eq_zero_of_forall_sum_cell_eq_zero (r : Setoid Ω) {f : Ω → ℝ}
    (h : ∀ ω, ∑ x ∈ cellFinset r ω, f x = 0) : ∑ x, f x = 0 := by
  rw [sum_eq_sum_inv_card_mul_sum_cell r f]
  exact Finset.sum_eq_zero fun ω _ => by rw [h ω, mul_zero]

end Finite

end MathlibExt.GameTheory.InteractiveEpistemology
