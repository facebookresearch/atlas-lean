/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Adaptive.HierarchicalTesting
public import MathlibExt.Probability.Statistics.MultipleTesting.BenjaminiHochberg
public import Mathlib.Probability.ConditionalProbability

/-!
# Hierarchical FDR control (Yekutieli): Benjamini–Hochberg along a tree

Yekutieli (2008) tests hypotheses arranged in a tree of *families*. The root family is tested by
the Benjamini–Hochberg (BH) procedure at level `q`; whenever a hypothesis is rejected, the family
of its children is tested by BH at level `q`, and so on down the tree. A family is tested only if
its parent hypothesis was rejected.

## Setting

We reuse the cluster trees of `MultipleTesting.Adaptive.HierarchicalTesting` (Meinshausen's
hierarchical FWER procedure, `hierRejections`). The nodes are clusters `C ⊆ Fin m` collected in a
finite family `T`; `p C` is the p-value of node `C`. The strict ancestors of `C` are the members
of `T` strictly containing it (`strictAncestors`), and the *sibling family* of `C` is the set of
nodes with the same strict ancestors (`siblingFamily`). In a laminar tree a nonempty node with a
parent `D` (`IsParent`) has as siblings the other children of `D`; the root family consists of
the nodes with no strict ancestor.

Each family `S` is tested by BH on the p-values of its members, enumerated by `S.equivFin`
(`familyPValues`), and the BH cutoff `q k / |S|` of the family (`familyBHLevel`) is the level of
every member (`yekutieliLevel`). Yekutieli's procedure is then Meinshausen's hierarchical
procedure with these *data-dependent* levels:

`yekutieliRejections q T p = hierRejections T (yekutieliLevel q T p) p`.

`mem_yekutieliRejections_iff` and `mem_yekutieliRejections_iff_parent` show that this is the
top-down procedure: a node is rejected iff its family is tested (every strict ancestor was
rejected, `IsTested`, equivalently the parent was rejected, `isTested_iff_parent`) and BH rejects
it within its family (`mem_yekutieliRejections_equivFin_iff`).

## FDR control

* **Per-family selective FDR** (`integral_familyFDP_yekutieliRejections_le`). Write `V_S, R_S` for
  the false and total discoveries in family `S` and `FDP_S = V_S / max R_S 1` (`familyFDP`).
  If the p-values of `S` are mutually independent, its true-null p-values are valid, and the
  p-value vector of `S` is independent of the p-values of the other nodes of the tree
  (`outsideFamily`), then `E[FDP_S] ≤ q |S ∩ H0| / |S| · P(S is tested)`: BH controls the FDR of
  a family at `q m₀ / m` *conditionally on the family being tested*. The proof conditions on the
  event that `S` is tested, which depends only on the p-values of the tree nodes outside `S`
  (`isTested_iff_outsideFamily`), so under the conditional measure the family's p-values keep
  their joint law and BH's FDR theorem applies
  (`setIntegral_falseDiscoveryProportion_bhRejections_le`).
* **Full-tree FDR** (`integral_treeFDP_yekutieliRejections_le`). The full-tree false discovery
  proportion `V / max R 1` is at most the sum of the family FDPs (`treeFDP_le_sum_familyFDP`), so
  `E[FDP_tree] ≤ q ∑_S (|S ∩ H0| / |S|) P(S tested) ≤ q · E[#families tested]`
  (`integral_treeFDP_yekutieliRejections_le_expected_tested`).
* **Mutual independence** (`..._of_iIndepFun`): both bounds hold when the p-values of the nodes
  of `T` are mutually independent (`iIndepFun` indexed by the nodes of `T`) and the true-null ones
  are valid.

## Conditions, stated explicitly

* **Validity**: every true-null p-value is super-uniform (`IsValidPValue`).
* **Independence**: within each family the p-values are mutually independent, and each family's
  p-value vector is independent of the p-values of the other nodes of the tree. Both follow from
  mutual independence of the node p-values. Nothing is assumed about false-null p-values beyond
  measurability, and nothing at all about the values `p C` of clusters `C ∉ T`.
* **Tree structure**: none is needed for the FDR bounds: sibling families are defined for any
  finite family of clusters, and an ancestor's family never meets the family itself
  (`not_mem_siblingFamily_of_mem_strictAncestors`). Laminarity is used only to identify the
  gating event with "the parent was rejected" (`isTested_iff_parent`).
* **Level**: `q ∈ [0, 1]`, the same in every family.

## Not covered

Yekutieli's sharper full-tree bound `FDR_tree ≤ 2 δ* q`, with `δ*` an upper bound on the
expected number of discoveries in subtrees below false discoveries, and his level-restricted FDR
bounds are not formalized. The full-tree bound proved here charges `q m₀ / m` for every tested
family; it is tight for a single family (where it is BH's theorem) but grows with the number of
families tested. Selection-adjusted levels (Benjamini–Bogomolov) and dependent p-values (PRDS)
are also not covered.

## References

* D. Yekutieli, *Hierarchical false discovery rate-controlling methodology*, J. Amer. Statist.
  Assoc. 103 (2008), 309–316.
* Y. Benjamini and Y. Hochberg, *Controlling the false discovery rate: a practical and powerful
  approach to multiple testing*, J. Roy. Statist. Soc. Ser. B 57 (1995), 289–300.
* N. Meinshausen, *Hierarchical testing of variable importance*, Biometrika 95 (2008), 265–278.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.MultipleTesting

open MeasureTheory ProbabilityTheory

variable {m : ℕ}

/-! ### Sibling families -/

/-- The strict ancestors of `C` in `T`: the members of `T` strictly containing `C`. -/
noncomputable def strictAncestors (T : Finset (Finset (Fin m))) (C : Finset (Fin m)) :
    Finset (Finset (Fin m)) := by
  classical
  exact T.filter fun D => C ⊂ D

/-- The sibling family of `C` in `T`: the members of `T` with the same strict ancestors as `C`.
The hypotheses of one family are tested together by BH. -/
noncomputable def siblingFamily (T : Finset (Finset (Fin m))) (C : Finset (Fin m)) :
    Finset (Finset (Fin m)) := by
  classical
  exact T.filter fun D => strictAncestors T D = strictAncestors T C

theorem mem_strictAncestors {T : Finset (Finset (Fin m))} {C D : Finset (Fin m)} :
    D ∈ strictAncestors T C ↔ D ∈ T ∧ C ⊂ D := by
  classical
  unfold strictAncestors
  convert Finset.mem_filter (s := T) (p := fun D => C ⊂ D)

theorem mem_siblingFamily {T : Finset (Finset (Fin m))} {C D : Finset (Fin m)} :
    D ∈ siblingFamily T C ↔ D ∈ T ∧ strictAncestors T D = strictAncestors T C := by
  classical
  unfold siblingFamily
  convert Finset.mem_filter (s := T) (p := fun D => strictAncestors T D = strictAncestors T C)

/-- A node of the tree belongs to its own family. -/
theorem self_mem_siblingFamily {T : Finset (Finset (Fin m))} {C : Finset (Fin m)} (hC : C ∈ T) :
    C ∈ siblingFamily T C :=
  mem_siblingFamily.mpr ⟨hC, rfl⟩

/-- The family of a node is a set of nodes of the tree. -/
theorem siblingFamily_subset (T : Finset (Finset (Fin m))) (C : Finset (Fin m)) :
    siblingFamily T C ⊆ T :=
  fun _ hD => (mem_siblingFamily.mp hD).1

/-- Siblings have the same family. -/
theorem siblingFamily_eq_of_mem {T : Finset (Finset (Fin m))} {C D : Finset (Fin m)}
    (hD : D ∈ siblingFamily T C) : siblingFamily T D = siblingFamily T C := by
  have h := (mem_siblingFamily.mp hD).2
  ext E
  rw [mem_siblingFamily, mem_siblingFamily, h]

/-- The family of a node of the tree is nonempty. -/
theorem card_siblingFamily_pos {T : Finset (Finset (Fin m))} {C : Finset (Fin m)} (hC : C ∈ T) :
    0 < (siblingFamily T C).card :=
  Finset.card_pos.mpr ⟨C, self_mem_siblingFamily hC⟩

/-- **The family of a strict ancestor never meets the family.** If `E` strictly contains `C`,
no sibling of `E` is a sibling of `C`. No tree structure is needed. -/
theorem not_mem_siblingFamily_of_mem_strictAncestors {T : Finset (Finset (Fin m))}
    {C E F : Finset (Fin m)} (hE : E ∈ strictAncestors T C) (hF : F ∈ siblingFamily T E) :
    F ∉ siblingFamily T C := by
  intro hFC
  have h1 := (mem_siblingFamily.mp hF).2
  have h2 := (mem_siblingFamily.mp hFC).2
  have hEE : E ∈ strictAncestors T E := by rw [← h1, h2]; exact hE
  exact ssubset_irrefl E (mem_strictAncestors.mp hEE).2

/-- Two families of the tree are equal or disjoint. -/
theorem disjoint_siblingFamily {T : Finset (Finset (Fin m))} {C D : Finset (Fin m)}
    (hne : siblingFamily T C ≠ siblingFamily T D) :
    Disjoint (siblingFamily T C) (siblingFamily T D) :=
  Finset.disjoint_left.mpr fun _ hE hE' =>
    hne ((siblingFamily_eq_of_mem hE).symm.trans (siblingFamily_eq_of_mem hE'))

/-! ### The procedure -/

/-- The p-values of the family `S`, enumerated by `S.equivFin`. -/
noncomputable def familyPValues (p : Finset (Fin m) → ℝ) (S : Finset (Finset (Fin m))) :
    Fin S.card → ℝ :=
  fun i => p (S.equivFin.symm i).1

/-- The BH cutoff `q k / |S|` of the family `S`, with `k` the BH step-up index of its p-values. -/
noncomputable def familyBHLevel (q : ℝ) (p : Finset (Fin m) → ℝ)
    (S : Finset (Finset (Fin m))) : ℝ :=
  q * bhIndex q (familyPValues p S) / S.card

/-- The level of node `C` in Yekutieli's procedure: the BH cutoff of its family. -/
noncomputable def yekutieliLevel (q : ℝ) (T : Finset (Finset (Fin m))) (p : Finset (Fin m) → ℝ)
    (C : Finset (Fin m)) : ℝ :=
  familyBHLevel q p (siblingFamily T C)

/-- **Yekutieli's hierarchical BH procedure**: Meinshausen's hierarchical procedure
(`hierRejections`) with every node tested at the BH cutoff of its family. -/
noncomputable def yekutieliRejections (q : ℝ) (T : Finset (Finset (Fin m)))
    (p : Finset (Fin m) → ℝ) : Finset (Finset (Fin m)) :=
  hierRejections T (yekutieliLevel q T p) p

/-- The family of `C` is *tested*: every strict ancestor of `C` passed its level. -/
def IsTested (q : ℝ) (T : Finset (Finset (Fin m))) (p : Finset (Fin m) → ℝ)
    (C : Finset (Fin m)) : Prop :=
  ∀ E ∈ strictAncestors T C, p E ≤ yekutieliLevel q T p E

/-- The family `S` is tested: every member is tested (for a family of the tree, equivalently one
member is, `isTestedFamily_siblingFamily_iff`). -/
def IsTestedFamily (q : ℝ) (T : Finset (Finset (Fin m))) (p : Finset (Fin m) → ℝ)
    (S : Finset (Finset (Fin m))) : Prop :=
  ∀ C ∈ S, IsTested q T p C

/-- All members of a family have the family's BH cutoff as their level. -/
theorem yekutieliLevel_of_mem {q : ℝ} {T : Finset (Finset (Fin m))} {p : Finset (Fin m) → ℝ}
    {C D : Finset (Fin m)} (hD : D ∈ siblingFamily T C) :
    yekutieliLevel q T p D = familyBHLevel q p (siblingFamily T C) := by
  unfold yekutieliLevel
  rw [siblingFamily_eq_of_mem hD]

/-- Siblings are tested together. -/
theorem isTested_iff_of_mem {q : ℝ} {T : Finset (Finset (Fin m))} {p : Finset (Fin m) → ℝ}
    {C D : Finset (Fin m)} (hD : D ∈ siblingFamily T C) :
    IsTested q T p D ↔ IsTested q T p C := by
  unfold IsTested
  rw [(mem_siblingFamily.mp hD).2]

theorem isTestedFamily_siblingFamily_iff {q : ℝ} {T : Finset (Finset (Fin m))}
    {p : Finset (Fin m) → ℝ} {C : Finset (Fin m)} (hC : C ∈ T) :
    IsTestedFamily q T p (siblingFamily T C) ↔ IsTested q T p C :=
  ⟨fun h => h C (self_mem_siblingFamily hC), fun h _ hD => (isTested_iff_of_mem hD).mpr h⟩

/-- **Top-down form of the procedure.** A node of the tree is rejected iff its family is tested
and it passes its family's BH cutoff. -/
theorem mem_yekutieliRejections_iff {q : ℝ} {T : Finset (Finset (Fin m))}
    {p : Finset (Fin m) → ℝ} {C : Finset (Fin m)} (hC : C ∈ T) :
    C ∈ yekutieliRejections q T p ↔ p C ≤ yekutieliLevel q T p C ∧ IsTested q T p C := by
  unfold yekutieliRejections IsTested
  rw [mem_hierRejections]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨h C hC subset_rfl, fun E hE =>
      h E (mem_strictAncestors.mp hE).1 (mem_strictAncestors.mp hE).2.subset⟩
  · rintro ⟨hCp, h⟩
    refine ⟨hC, fun D hD hCD => ?_⟩
    rcases eq_or_ne C D with rfl | hne
    · exact hCp
    · exact h D (mem_strictAncestors.mpr ⟨hD, Finset.ssubset_iff_subset_ne.mpr ⟨hCD, hne⟩⟩)

/-- **A family is tested iff the parent was rejected.** If `D` is the parent of `C` in the tree
(`IsParent`), the family of `C` is tested exactly when `D` is rejected. -/
theorem isTested_iff_parent {q : ℝ} {T : Finset (Finset (Fin m))} {p : Finset (Fin m) → ℝ}
    {C D : Finset (Fin m)} (hpar : IsParent T C D) :
    IsTested q T p C ↔ D ∈ yekutieliRejections q T p := by
  obtain ⟨-, hD, hCD, hmin⟩ := hpar
  unfold IsTested yekutieliRejections
  rw [mem_hierRejections]
  constructor
  · intro h
    exact ⟨hD, fun E hE hDE => h E (mem_strictAncestors.mpr ⟨hE, hCD.trans_subset hDE⟩)⟩
  · rintro ⟨-, h⟩ E hE
    obtain ⟨hET, hCE⟩ := mem_strictAncestors.mp hE
    exact h E hET (hmin E hET hCE)

/-- **A node is tested only if its parent rejected** (Meinshausen's
`mem_hierRejections_iff_parent` for the BH levels). -/
theorem mem_yekutieliRejections_iff_parent {q : ℝ} {T : Finset (Finset (Fin m))}
    {p : Finset (Fin m) → ℝ} {C D : Finset (Fin m)} (hpar : IsParent T C D) :
    C ∈ yekutieliRejections q T p ↔
      p C ≤ yekutieliLevel q T p C ∧ D ∈ yekutieliRejections q T p :=
  mem_hierRejections_iff_parent hpar

/-- The root family is always tested. -/
theorem isTested_of_root {q : ℝ} {T : Finset (Finset (Fin m))} {p : Finset (Fin m) → ℝ}
    {C : Finset (Fin m)} (hroot : ∀ E ∈ T, ¬ C ⊂ E) : IsTested q T p C :=
  fun E hE => absurd (mem_strictAncestors.mp hE).2 (hroot E (mem_strictAncestors.mp hE).1)

/-- **Within a tested family the procedure is BH.** The `i`-th member of the family of `C` is
rejected iff the family is tested and BH on the family's p-values rejects `i`. -/
theorem mem_yekutieliRejections_equivFin_iff {q : ℝ} {T : Finset (Finset (Fin m))}
    {p : Finset (Fin m) → ℝ} {C : Finset (Fin m)} (i : Fin (siblingFamily T C).card) :
    ((siblingFamily T C).equivFin.symm i).1 ∈ yekutieliRejections q T p ↔
      IsTested q T p C ∧ i ∈ bhRejections q (familyPValues p (siblingFamily T C)) := by
  have hD : ((siblingFamily T C).equivFin.symm i).1 ∈ siblingFamily T C :=
    ((siblingFamily T C).equivFin.symm i).2
  rw [mem_yekutieliRejections_iff (mem_siblingFamily.mp hD).1, isTested_iff_of_mem hD,
    yekutieliLevel_of_mem hD]
  have hbh : i ∈ bhRejections q (familyPValues p (siblingFamily T C)) ↔
      p ((siblingFamily T C).equivFin.symm i).1 ≤ familyBHLevel q p (siblingFamily T C) := by
    unfold bhRejections familyBHLevel familyPValues
    exact ⟨fun h => (Finset.mem_filter.mp h).2,
      fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  rw [hbh]
  exact and_comm

/-! ### False discovery proportions of a family and of the tree -/

/-- The false discovery proportion of the rejection set `R` within the family `S`:
`|R ∩ S ∩ H0| / max |R ∩ S| 1`. -/
noncomputable def familyFDP (H0 R S : Finset (Finset (Fin m))) : ℝ :=
  ((R ∩ S ∩ H0).card : ℝ) / max ((R ∩ S).card : ℝ) 1

/-- The false discovery proportion of the rejection set `R` over the whole tree:
`|R ∩ H0| / max |R| 1`. -/
noncomputable def treeFDP (H0 R : Finset (Finset (Fin m))) : ℝ :=
  ((R ∩ H0).card : ℝ) / max (R.card : ℝ) 1

/-- The true nulls of the family `S`, as indices of `S.equivFin`. -/
noncomputable def familyNulls (H0 S : Finset (Finset (Fin m))) : Finset (Fin S.card) :=
  Finset.univ.filter fun i => (S.equivFin.symm i).1 ∈ H0

theorem familyFDP_nonneg (H0 R S : Finset (Finset (Fin m))) : 0 ≤ familyFDP H0 R S := by
  unfold familyFDP
  positivity

theorem familyFDP_le_one (H0 R S : Finset (Finset (Fin m))) : familyFDP H0 R S ≤ 1 := by
  unfold familyFDP
  rw [div_le_one (by positivity)]
  exact le_max_of_le_left (by exact_mod_cast Finset.card_le_card Finset.inter_subset_left)

theorem treeFDP_nonneg (H0 R : Finset (Finset (Fin m))) : 0 ≤ treeFDP H0 R := by
  unfold treeFDP
  positivity

/-- Counting the members of `S` in `t` through the enumeration `S.equivFin`. -/
theorem card_inter_eq_card_filter_equivFin {α : Type*} [DecidableEq α] (S t : Finset α) :
    (S ∩ t).card = (Finset.univ.filter fun i : Fin S.card => (S.equivFin.symm i).1 ∈ t).card := by
  refine Finset.card_bij' (fun a ha => S.equivFin ⟨a, (Finset.mem_inter.mp ha).1⟩)
    (fun i _ => (S.equivFin.symm i).1) ?_ ?_ ?_ ?_
  · intro a ha
    simpa using (Finset.mem_inter.mp ha).2
  · intro i hi
    exact Finset.mem_inter.mpr ⟨(S.equivFin.symm i).2, (Finset.mem_filter.mp hi).2⟩
  · intro a ha
    simp
  · intro i hi
    simp

/-- The family has as many true nulls as `familyNulls` has indices. -/
theorem card_familyNulls (H0 S : Finset (Finset (Fin m))) :
    (familyNulls H0 S).card = (S ∩ H0).card :=
  (card_inter_eq_card_filter_equivFin S H0).symm

open Classical in
/-- **The family FDP of Yekutieli's procedure is BH's FDP on a tested family, and `0` on an
untested one.** -/
theorem familyFDP_yekutieliRejections_eq {q : ℝ} {T : Finset (Finset (Fin m))}
    (p : Finset (Fin m) → ℝ) (H0 : Finset (Finset (Fin m))) (C : Finset (Fin m)) :
    familyFDP H0 (yekutieliRejections q T p) (siblingFamily T C) =
      if IsTested q T p C then
        falseDiscoveryProportion (familyNulls H0 (siblingFamily T C))
          (bhRejections q (familyPValues p (siblingFamily T C)))
      else 0 := by
  set S := siblingFamily T C with hS
  set R := yekutieliRejections q T p with hR
  set bh := bhRejections q (familyPValues p S) with hbh
  have hcorr : ∀ i : Fin S.card, (S.equivFin.symm i).1 ∈ R ↔ IsTested q T p C ∧ i ∈ bh :=
    fun i => mem_yekutieliRejections_equivFin_iff i
  have h1 : (R ∩ S).card = (S ∩ R).card := by rw [Finset.inter_comm]
  have h2 : (R ∩ S ∩ H0).card = (S ∩ (R ∩ H0)).card := by
    rw [Finset.inter_comm R S, Finset.inter_assoc]
  unfold familyFDP
  rw [h1, h2, card_inter_eq_card_filter_equivFin, card_inter_eq_card_filter_equivFin]
  by_cases ht : IsTested q T p C
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ht)]
    have e1 : (Finset.univ.filter fun i : Fin S.card => (S.equivFin.symm i).1 ∈ R) = bh := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hcorr i]
      simp [ht]
    have e2 : (Finset.univ.filter fun i : Fin S.card => (S.equivFin.symm i).1 ∈ R ∩ H0) =
        bh ∩ familyNulls H0 S := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter, familyNulls]
      rw [hcorr i]
      simp [ht]
    rw [e1, e2]
    rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false ht)]
    have e1 : (Finset.univ.filter fun i : Fin S.card => (S.equivFin.symm i).1 ∈ R ∩ H0) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
        Finset.notMem_empty, iff_false, not_and]
      intro hi
      exact absurd ((hcorr i).mp hi).1 ht
    rw [e1]
    simp

/-- **The full-tree FDP is at most the sum of the family FDPs.** For any rejection set inside
the tree, `V / max R 1 ≤ ∑_S V_S / max R_S 1`, the sum over the families of the tree. -/
theorem treeFDP_le_sum_familyFDP {T R : Finset (Finset (Fin m))} (hR : R ⊆ T)
    (H0 : Finset (Finset (Fin m))) :
    treeFDP H0 R ≤ ∑ S ∈ T.image (siblingFamily T), familyFDP H0 R S := by
  classical
  set F := T.image (siblingFamily T) with hF
  have hdisj : ∀ S ∈ F, ∀ S' ∈ F, S ≠ S' → Disjoint S S' := by
    intro S hS S' hS' hne
    obtain ⟨C, -, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨C', -, rfl⟩ := Finset.mem_image.mp hS'
    exact disjoint_siblingFamily hne
  have hcover : R ∩ H0 = F.biUnion fun S => R ∩ S ∩ H0 := by
    ext D
    simp only [Finset.mem_biUnion, Finset.mem_inter, hF, Finset.mem_image]
    constructor
    · rintro ⟨hDR, hDH⟩
      exact ⟨siblingFamily T D, ⟨D, hR hDR, rfl⟩, ⟨hDR, self_mem_siblingFamily (hR hDR)⟩, hDH⟩
    · rintro ⟨_, _, ⟨hDR, _⟩, hDH⟩
      exact ⟨hDR, hDH⟩
  have hcard : ((R ∩ H0).card : ℝ) = ∑ S ∈ F, ((R ∩ S ∩ H0).card : ℝ) := by
    rw [hcover, Finset.card_biUnion]
    · push_cast
      rfl
    · intro S hS S' hS' hne
      refine Finset.disjoint_left.mpr fun D hD hD' => ?_
      exact Finset.disjoint_left.mp (hdisj S hS S' hS' hne)
        (Finset.mem_inter.mp (Finset.mem_inter.mp hD).1).2
        (Finset.mem_inter.mp (Finset.mem_inter.mp hD').1).2
  unfold treeFDP
  rw [hcard, Finset.sum_div]
  refine Finset.sum_le_sum fun S _ => ?_
  unfold familyFDP
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  exact max_le_max (by exact_mod_cast Finset.card_le_card Finset.inter_subset_left) le_rfl

/-! ### BH under conditioning on an independent event -/

/-- **BH controls the FDR on an independent event.** Let the p-values `x` be mutually independent
with valid true-null p-values, and let `G = Y⁻¹ B` be an event determined by a random variable
`Y` independent of the p-value vector. Then
`∫_G FDP(BH) dμ ≤ q |H0| / k · P(G)`: conditionally on `G`, BH still controls the FDR at
`q |H0| / k`. -/
theorem setIntegral_falseDiscoveryProportion_bhRejections_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ} (x : Fin k → Ω → ℝ)
    (hx : ∀ i, Measurable (x i)) (hindep : iIndepFun x μ) (H0 : Finset (Fin k))
    (hnull : ∀ i ∈ H0, IsValidPValue μ (x i)) {β : Type*} [MeasurableSpace β] (Y : Ω → β)
    (hY : Measurable Y) (hXY : IndepFun (fun ω i => x i ω) Y μ) {B : Set β}
    (hB : MeasurableSet B) (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω in Y ⁻¹' B, falseDiscoveryProportion H0 (bhRejections q fun i => x i ω) ∂μ ≤
      q * H0.card / k * μ.real (Y ⁻¹' B) := by
  have hG : MeasurableSet (Y ⁻¹' B) := hY hB
  by_cases hG0 : μ (Y ⁻¹' B) = 0
  · rw [setIntegral_measure_zero _ hG0, measureReal_def, hG0, ENNReal.toReal_zero, mul_zero]
  have : IsProbabilityMeasure (μ[|Y ⁻¹' B]) := cond_isProbabilityMeasure hG0
  -- the conditional measure does not change the law of the p-value vector
  have hpres : ∀ A : Set (Fin k → ℝ), MeasurableSet A →
      μ[|Y ⁻¹' B] ((fun ω i => x i ω) ⁻¹' A) = μ ((fun ω i => x i ω) ⁻¹' A) := by
    intro A hA
    rw [cond_apply hG, Set.inter_comm, hXY.measure_inter_preimage_eq_mul A B hA hB,
      mul_comm (μ ((fun ω i => x i ω) ⁻¹' A)), ← mul_assoc,
      ENNReal.inv_mul_cancel hG0 (measure_ne_top μ _), one_mul]
  have hindep' : iIndepFun x (μ[|Y ⁻¹' B]) := by
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hindep ⊢
    intro S sets hsets
    have hinter : (⋂ i ∈ S, x i ⁻¹' sets i) =
        (fun ω i => x i ω) ⁻¹' (⋂ i ∈ S, (fun v : Fin k → ℝ => v i) ⁻¹' sets i) := by
      ext ω
      simp
    have hmeas : MeasurableSet (⋂ i ∈ S, (fun v : Fin k → ℝ => v i) ⁻¹' sets i) :=
      Finset.measurableSet_biInter _ fun i hi => measurable_pi_apply i (hsets i hi)
    rw [hinter, hpres _ hmeas, ← hinter, hindep S hsets]
    refine Finset.prod_congr rfl fun i hi => ?_
    exact (hpres ((fun v : Fin k → ℝ => v i) ⁻¹' sets i)
      (measurable_pi_apply i (hsets i hi))).symm
  have hnull' : ∀ i ∈ H0, IsValidPValue (μ[|Y ⁻¹' B]) (x i) := by
    intro i hi t ht
    have h := hpres {v | v i ≤ t} (measurableSet_le (measurable_pi_apply i) measurable_const)
    calc μ[|Y ⁻¹' B] {ω | x i ω ≤ t} = μ {ω | x i ω ≤ t} := h
      _ ≤ ENNReal.ofReal t := hnull i hi t ht
  have hbh := integral_falseDiscoveryProportion_bhRejections_le_of_isValidPValue (μ[|Y ⁻¹' B]) x
    hx hindep' H0 hnull' q hq₀ hq₁
  have hcond : ∫ ω, falseDiscoveryProportion H0 (bhRejections q fun i => x i ω) ∂(μ[|Y ⁻¹' B]) =
      (μ.real (Y ⁻¹' B))⁻¹ *
        ∫ ω in Y ⁻¹' B, falseDiscoveryProportion H0 (bhRejections q fun i => x i ω) ∂μ := by
    rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul,
      measureReal_def]
  have hpos : 0 < μ.real (Y ⁻¹' B) := ENNReal.toReal_pos hG0 (measure_ne_top _ _)
  rw [hcond, inv_mul_le_iff₀ hpos] at hbh
  calc _ ≤ μ.real (Y ⁻¹' B) * (q * H0.card / k) := hbh
    _ = _ := by ring

/-! ### Measurability -/

theorem measurable_familyBHLevel {Ω : Type*} [MeasurableSpace Ω] (q : ℝ)
    (p : Finset (Fin m) → Ω → ℝ) (S : Finset (Finset (Fin m))) (hp : ∀ D ∈ S, Measurable (p D)) :
    Measurable fun ω => familyBHLevel q (fun D => p D ω) S := by
  unfold familyBHLevel familyPValues
  exact (measurable_const.mul (measurable_from_nat.comp
    (measurable_bhIndex (fun i ω => p (S.equivFin.symm i).1 ω)
      (fun i => hp _ (S.equivFin.symm i).2) q))).div_const _

theorem measurableSet_isTested {Ω : Type*} [MeasurableSpace Ω] (q : ℝ)
    (T : Finset (Finset (Fin m))) (p : Finset (Fin m) → Ω → ℝ) (hp : ∀ D ∈ T, Measurable (p D))
    (C : Finset (Fin m)) : MeasurableSet {ω | IsTested q T (fun D => p D ω) C} := by
  have h : {ω | IsTested q T (fun D => p D ω) C} =
      ⋂ E ∈ strictAncestors T C, {ω | p E ω ≤ yekutieliLevel q T (fun D => p D ω) E} := by
    ext ω
    simp [IsTested]
  rw [h]
  exact Finset.measurableSet_biInter _ fun E hE =>
    measurableSet_le (hp E (mem_strictAncestors.mp hE).1)
      (measurable_familyBHLevel q p _ fun D hD => hp D (siblingFamily_subset T E hD))

/-! ### The gating event depends only on the other nodes' p-values -/

/-- The p-values of the nodes of `T` outside the family `S`: `p D` for `D ∈ T \ S`, and `0` for
the members of `S` and for clusters that are not nodes of `T`. -/
def outsideFamily (T : Finset (Finset (Fin m))) (p : Finset (Fin m) → ℝ)
    (S : Finset (Finset (Fin m))) : Finset (Fin m) → ℝ :=
  fun D => if D ∈ T \ S then p D else 0

/-- **Whether a family is tested depends only on the p-values of the other nodes.** -/
theorem isTested_iff_outsideFamily {q : ℝ} {T : Finset (Finset (Fin m))}
    (p : Finset (Fin m) → ℝ) {C : Finset (Fin m)} :
    IsTested q T p C ↔ IsTested q T (outsideFamily T p (siblingFamily T C)) C := by
  unfold IsTested
  refine forall₂_congr fun E hE => ?_
  have hET : E ∈ T := (mem_strictAncestors.mp hE).1
  have hEout : outsideFamily T p (siblingFamily T C) E = p E :=
    ite_eq_left_of_eq_true _ _ (eq_true (Finset.mem_sdiff.mpr ⟨hET,
      not_mem_siblingFamily_of_mem_strictAncestors hE (self_mem_siblingFamily hET)⟩))
  have hfun : familyPValues (outsideFamily T p (siblingFamily T C)) (siblingFamily T E) =
      familyPValues p (siblingFamily T E) := by
    funext i
    have hi := ((siblingFamily T E).equivFin.symm i).2
    exact ite_eq_left_of_eq_true _ _ (eq_true (Finset.mem_sdiff.mpr ⟨siblingFamily_subset T E hi,
      not_mem_siblingFamily_of_mem_strictAncestors hE hi⟩))
  simp only [yekutieliLevel, familyBHLevel, hfun, hEout]

/-! ### FDR control -/

theorem measurable_familyFDP_yekutieliRejections {Ω : Type*} [MeasurableSpace Ω] (q : ℝ)
    (T : Finset (Finset (Fin m))) (p : Finset (Fin m) → Ω → ℝ)
    (hp : ∀ D ∈ T, Measurable (p D)) (H0 : Finset (Finset (Fin m))) (C : Finset (Fin m)) :
    Measurable fun ω => familyFDP H0 (yekutieliRejections q T fun D => p D ω)
      (siblingFamily T C) := by
  classical
  simp_rw [familyFDP_yekutieliRejections_eq]
  exact Measurable.ite (measurableSet_isTested q T p hp C)
    (measurable_falseDiscoveryProportion_bhRejections
      (fun i ω => p ((siblingFamily T C).equivFin.symm i).1 ω)
      (fun i => hp _ (siblingFamily_subset T C ((siblingFamily T C).equivFin.symm i).2)) _ q)
    measurable_const

theorem integrable_familyFDP_yekutieliRejections {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (q : ℝ) (T : Finset (Finset (Fin m)))
    (p : Finset (Fin m) → Ω → ℝ) (hp : ∀ D ∈ T, Measurable (p D)) (H0 : Finset (Finset (Fin m)))
    (C : Finset (Fin m)) :
    Integrable (fun ω => familyFDP H0 (yekutieliRejections q T fun D => p D ω)
      (siblingFamily T C)) μ :=
  Integrable.of_bound (measurable_familyFDP_yekutieliRejections q T p hp H0 C).aestronglyMeasurable
    1 (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (familyFDP_nonneg _ _ _)]
      exact familyFDP_le_one _ _ _)

/-- **Per-family FDR control of Yekutieli's procedure.** Let `S` be the family of the node `C`.
Suppose the p-values of `S` are mutually independent, the true-null ones are valid, and the
p-value vector of `S` is independent of the p-values of the other nodes of the tree
(`outsideFamily`). Then the expected FDP of the discoveries in `S` is at most
`q |S ∩ H0| / |S|` times the probability that `S` is tested: BH controls the FDR of the family
conditionally on the family being tested.

Source: Yekutieli (2008), the per-family step of the FDR analysis; the within-family bound is
Benjamini & Hochberg (1995), Theorem 1. -/
theorem integral_familyFDP_yekutieliRejections_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {T : Finset (Finset (Fin m))}
    (p : Finset (Fin m) → Ω → ℝ) (hp : ∀ D ∈ T, Measurable (p D)) (H0 : Finset (Finset (Fin m)))
    {C : Finset (Fin m)}
    (hindep : iIndepFun
      (fun i : Fin (siblingFamily T C).card => p ((siblingFamily T C).equivFin.symm i).1) μ)
    (hnull : ∀ D ∈ siblingFamily T C, D ∈ H0 → IsValidPValue μ (p D))
    (hout : IndepFun
      (fun ω (i : Fin (siblingFamily T C).card) => p ((siblingFamily T C).equivFin.symm i).1 ω)
      (fun ω => outsideFamily T (fun D => p D ω) (siblingFamily T C)) μ)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, familyFDP H0 (yekutieliRejections q T fun D => p D ω) (siblingFamily T C) ∂μ ≤
      q * ((siblingFamily T C ∩ H0).card : ℝ) / (siblingFamily T C).card *
        μ.real {ω | IsTested q T (fun D => p D ω) C} := by
  classical
  set S := siblingFamily T C with hS
  set Y : Ω → (Finset (Fin m) → ℝ) := fun ω => outsideFamily T (fun D => p D ω) S with hYdef
  set B : Set (Finset (Fin m) → ℝ) := {y | IsTested q T y C} with hBdef
  have hY : Measurable Y := Measurable.of_eval fun D => by
    by_cases hD : D ∈ T \ S
    · simp only [Y, outsideFamily, hD, ite_true]
      exact hp D (Finset.mem_sdiff.mp hD).1
    · simp only [Y, outsideFamily, hD, ite_false]
      exact measurable_const
  have hB : MeasurableSet B :=
    measurableSet_isTested q T (fun D (y : Finset (Fin m) → ℝ) => y D)
      (fun D _ => measurable_pi_apply D) C
  have hGset : {ω | IsTested q T (fun D => p D ω) C} = Y ⁻¹' B := by
    ext ω
    exact isTested_iff_outsideFamily (fun D => p D ω)
  have heq : ∀ ω, familyFDP H0 (yekutieliRejections q T fun D => p D ω) S =
      (Y ⁻¹' B).indicator (fun ω => falseDiscoveryProportion (familyNulls H0 S)
        (bhRejections q fun i => p (S.equivFin.symm i).1 ω)) ω := by
    intro ω
    rw [hS, familyFDP_yekutieliRejections_eq]
    have hmem : ω ∈ Y ⁻¹' B ↔ IsTested q T (fun D => p D ω) C := by
      simp only [← hGset, Set.mem_ofPred_eq]
    by_cases ht : IsTested q T (fun D => p D ω) C
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ht), Set.indicator_of_mem (hmem.mpr ht)]
      rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false ht), Set.indicator_of_notMem (mt hmem.mp ht)]
  rw [integral_congr_ae (Filter.Eventually.of_forall heq), integral_indicator (hY hB), hGset,
    ← card_familyNulls]
  refine setIntegral_falseDiscoveryProportion_bhRejections_le μ
    (fun i ω => p (S.equivFin.symm i).1 ω)
    (fun i => hp _ (siblingFamily_subset T C (S.equivFin.symm i).2)) hindep (familyNulls H0 S) ?_
    Y hY hout hB q hq₀ hq₁
  intro i hi
  exact hnull _ (S.equivFin.symm i).2 (Finset.mem_filter.mp hi).2

/-- **Full-tree FDR control of Yekutieli's procedure.** Under the per-family hypotheses of
`integral_familyFDP_yekutieliRejections_le` for every family of the tree, the full-tree FDR is at
most `q ∑_S (|S ∩ H0| / |S|) P(S is tested)`, the sum over the families `S` of the tree.

Source: Yekutieli (2008); the sharper `2 δ* q` bound is not formalized. -/
theorem integral_treeFDP_yekutieliRejections_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {T : Finset (Finset (Fin m))}
    (p : Finset (Fin m) → Ω → ℝ) (hp : ∀ D ∈ T, Measurable (p D)) (H0 : Finset (Finset (Fin m)))
    (hindep : ∀ C ∈ T, iIndepFun
      (fun i : Fin (siblingFamily T C).card => p ((siblingFamily T C).equivFin.symm i).1) μ)
    (hnull : ∀ D ∈ T, D ∈ H0 → IsValidPValue μ (p D))
    (hout : ∀ C ∈ T, IndepFun
      (fun ω (i : Fin (siblingFamily T C).card) => p ((siblingFamily T C).equivFin.symm i).1 ω)
      (fun ω => outsideFamily T (fun D => p D ω) (siblingFamily T C)) μ)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, treeFDP H0 (yekutieliRejections q T fun D => p D ω) ∂μ ≤
      ∑ S ∈ T.image (siblingFamily T),
        q * ((S ∩ H0).card : ℝ) / S.card * μ.real {ω | IsTestedFamily q T (fun D => p D ω) S} := by
  have hint : ∀ S ∈ T.image (siblingFamily T), Integrable
      (fun ω => familyFDP H0 (yekutieliRejections q T fun D => p D ω) S) μ := by
    intro S hS
    obtain ⟨C, -, rfl⟩ := Finset.mem_image.mp hS
    exact integrable_familyFDP_yekutieliRejections μ q T p hp H0 C
  calc ∫ ω, treeFDP H0 (yekutieliRejections q T fun D => p D ω) ∂μ
      ≤ ∫ ω, ∑ S ∈ T.image (siblingFamily T),
          familyFDP H0 (yekutieliRejections q T fun D => p D ω) S ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => treeFDP_nonneg _ _)
          (integrable_finsetSum _ hint) (Filter.Eventually.of_forall fun ω =>
            treeFDP_le_sum_familyFDP (hierRejections_subset _ _ _) H0)
    _ = ∑ S ∈ T.image (siblingFamily T),
          ∫ ω, familyFDP H0 (yekutieliRejections q T fun D => p D ω) S ∂μ :=
        integral_finsetSum _ hint
    _ ≤ _ := by
        refine Finset.sum_le_sum fun S hS => ?_
        obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hS
        have hset : {ω | IsTestedFamily q T (fun D => p D ω) (siblingFamily T C)} =
            {ω | IsTested q T (fun D => p D ω) C} := by
          ext ω
          exact isTestedFamily_siblingFamily_iff hC
        rw [hset]
        exact integral_familyFDP_yekutieliRejections_le μ p hp H0 (hindep C hC)
          (fun D hD hDH => hnull D (siblingFamily_subset T C hD) hDH) (hout C hC) q hq₀ hq₁

/-! ### Mutually independent node p-values -/

/-- Mutual independence of the p-values of the nodes of `T` gives the within-family independence
used by the FDR bounds, for every family `S ⊆ T`. -/
theorem iIndepFun_familyPValues {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {T : Finset (Finset (Fin m))} {p : Finset (Fin m) → Ω → ℝ}
    (hindep : iIndepFun (fun D : T => p D) μ) {S : Finset (Finset (Fin m))} (hST : S ⊆ T) :
    iIndepFun (fun i : Fin S.card => p (S.equivFin.symm i).1) μ :=
  hindep.precomp
    (g := fun i : Fin S.card => (⟨(S.equivFin.symm i).1, hST (S.equivFin.symm i).2⟩ : T))
    fun _ _ h => S.equivFin.symm.injective (Subtype.ext (by
      have h' := congrArg (fun d : T => (d : Finset (Fin m))) h
      exact h'))

/-- Mutual independence of the p-values of the nodes of `T` makes the p-value vector of a family
`S ⊆ T` independent of the p-values of the other nodes (`outsideFamily`). -/
theorem indepFun_familyPValues_outsideFamily {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {T : Finset (Finset (Fin m))} {p : Finset (Fin m) → Ω → ℝ}
    (hp : ∀ D ∈ T, Measurable (p D)) (hindep : iIndepFun (fun D : T => p D) μ)
    {S : Finset (Finset (Fin m))} (hST : S ⊆ T) :
    IndepFun (fun ω (i : Fin S.card) => p (S.equivFin.symm i).1 ω)
      (fun ω => outsideFamily T (fun D => p D ω) S) μ := by
  classical
  set A : Finset T := Finset.univ.filter fun D => D.1 ∈ S with hA
  have h := hindep.indepFun_finset A Aᶜ disjoint_compl_right fun D => hp D.1 D.2
  let φ : (A → ℝ) → (Fin S.card → ℝ) := fun v i =>
    v ⟨⟨(S.equivFin.symm i).1, hST (S.equivFin.symm i).2⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (S.equivFin.symm i).2⟩⟩
  let ψ : (↥(Aᶜ) → ℝ) → (Finset (Fin m) → ℝ) := fun w D =>
    if hD : D ∈ T \ S then
      w ⟨⟨D, (Finset.mem_sdiff.mp hD).1⟩,
        Finset.mem_compl.mpr fun h => (Finset.mem_sdiff.mp hD).2 (Finset.mem_filter.mp h).2⟩
    else 0
  have hφ : Measurable φ := Measurable.of_eval fun i => measurable_pi_apply _
  have hψ : Measurable ψ := Measurable.of_eval fun D => by
    by_cases hD : D ∈ T \ S
    · simp only [ψ, hD, dite_true]
      exact measurable_pi_apply _
    · simp only [ψ, hD, dite_false]
      exact measurable_const
  have e2 : (fun ω => outsideFamily T (fun D => p D ω) S) =
      ψ ∘ fun ω (i : ↥(Aᶜ)) => p i.1.1 ω := by
    funext ω D
    simp only [Function.comp_apply, outsideFamily, ψ]
    split_ifs <;> rfl
  rw [e2]
  exact h.comp hφ hψ

/-- **Per-family FDR control for mutually independent node p-values.** If the p-values of the
nodes of `T` are mutually independent and the true-null ones are valid, the expected FDP of the
discoveries in the family of `C` is at most `q |S ∩ H0| / |S| · P(S is tested)`. Nothing is
assumed about the values `p D` of clusters `D ∉ T`.

Source: Yekutieli (2008). -/
theorem integral_familyFDP_yekutieliRejections_le_of_iIndepFun {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {T : Finset (Finset (Fin m))}
    (p : Finset (Fin m) → Ω → ℝ) (hp : ∀ D ∈ T, Measurable (p D))
    (hindep : iIndepFun (fun D : T => p D) μ) (H0 : Finset (Finset (Fin m)))
    (hnull : ∀ D ∈ T, D ∈ H0 → IsValidPValue μ (p D))
    (C : Finset (Fin m)) (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, familyFDP H0 (yekutieliRejections q T fun D => p D ω) (siblingFamily T C) ∂μ ≤
      q * ((siblingFamily T C ∩ H0).card : ℝ) / (siblingFamily T C).card *
        μ.real {ω | IsTested q T (fun D => p D ω) C} :=
  integral_familyFDP_yekutieliRejections_le μ p hp H0
    (iIndepFun_familyPValues hindep (siblingFamily_subset T C))
    (fun D hD hDH => hnull D (siblingFamily_subset T C hD) hDH)
    (indepFun_familyPValues_outsideFamily hp hindep (siblingFamily_subset T C)) q hq₀ hq₁

/-- **Full-tree FDR control for mutually independent node p-values.** If the p-values of the
nodes of `T` are mutually independent and the true-null ones are valid, Yekutieli's procedure has
full-tree FDR at most `q ∑_S (|S ∩ H0| / |S|) P(S is tested)`.

Source: Yekutieli (2008). -/
theorem integral_treeFDP_yekutieliRejections_le_of_iIndepFun {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {T : Finset (Finset (Fin m))}
    (p : Finset (Fin m) → Ω → ℝ) (hp : ∀ D ∈ T, Measurable (p D))
    (hindep : iIndepFun (fun D : T => p D) μ) (H0 : Finset (Finset (Fin m)))
    (hnull : ∀ D ∈ T, D ∈ H0 → IsValidPValue μ (p D))
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, treeFDP H0 (yekutieliRejections q T fun D => p D ω) ∂μ ≤
      ∑ S ∈ T.image (siblingFamily T),
        q * ((S ∩ H0).card : ℝ) / S.card * μ.real {ω | IsTestedFamily q T (fun D => p D ω) S} :=
  integral_treeFDP_yekutieliRejections_le μ p hp H0
    (fun C _ => iIndepFun_familyPValues hindep (siblingFamily_subset T C)) hnull
    (fun C _ => indepFun_familyPValues_outsideFamily hp hindep (siblingFamily_subset T C))
    q hq₀ hq₁

/-- **Full-tree FDR is at most `q` times the expected number of families tested.** -/
theorem integral_treeFDP_yekutieliRejections_le_expected_tested {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {T : Finset (Finset (Fin m))}
    (p : Finset (Fin m) → Ω → ℝ) (hp : ∀ D ∈ T, Measurable (p D))
    (hindep : iIndepFun (fun D : T => p D) μ) (H0 : Finset (Finset (Fin m)))
    (hnull : ∀ D ∈ T, D ∈ H0 → IsValidPValue μ (p D))
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, treeFDP H0 (yekutieliRejections q T fun D => p D ω) ∂μ ≤
      q * ∑ S ∈ T.image (siblingFamily T), μ.real {ω | IsTestedFamily q T (fun D => p D ω) S} := by
  refine (integral_treeFDP_yekutieliRejections_le_of_iIndepFun μ p hp hindep H0 hnull q hq₀
    hq₁).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun S hS => ?_
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hS
  have hpos : (0 : ℝ) < (siblingFamily T C).card := by exact_mod_cast card_siblingFamily_pos hC
  have hratio : ((siblingFamily T C ∩ H0).card : ℝ) / (siblingFamily T C).card ≤ 1 := by
    rw [div_le_one hpos]
    exact_mod_cast Finset.card_le_card Finset.inter_subset_left
  have hP : 0 ≤ μ.real {ω | IsTestedFamily q T (fun D => p D ω) (siblingFamily T C)} :=
    measureReal_nonneg
  calc q * ((siblingFamily T C ∩ H0).card : ℝ) / (siblingFamily T C).card *
        μ.real {ω | IsTestedFamily q T (fun D => p D ω) (siblingFamily T C)}
      = q * (((siblingFamily T C ∩ H0).card : ℝ) / (siblingFamily T C).card) *
        μ.real {ω | IsTestedFamily q T (fun D => p D ω) (siblingFamily T C)} := by ring
    _ ≤ q * 1 * μ.real {ω | IsTestedFamily q T (fun D => p D ω) (siblingFamily T C)} := by
        gcongr
    _ = _ := by ring

end MathlibExt.Probability.Statistics.MultipleTesting
