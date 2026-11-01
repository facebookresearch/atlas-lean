/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.List.FinRange

import Mathlib.Data.List.Pairwise
import Mathlib.Tactic.Choose

/-!
# Hudson and Kaplan's lower bound `R_m` on the number of recombination events

A sample of `n` haplotypes is scored at `s` biallelic segregating sites, listed in chromosomal
order; `M r i : Bool` is the allele of haplotype `r` at site `i`. Under the infinite-sites
model each site mutated once in the history of the sample, so in a stretch of sequence without
recombination all sites share one genealogy and the haplotypes carrying the derived allele at a
site form a clade of that tree. Two clades of one tree are nested or disjoint, so at most three
of the four gametes `00, 01, 10, 11` occur at two such sites (`not_fourGametes_iff`). Hence
every pair of sites `i < j` showing all four gametes needs a recombination breakpoint between
`i` and `j` (Hudson–Kaplan 1985).

A breakpoint `g : Fin s` cuts the sequence immediately to the left of site `g`; it separates
sites `i < j` when `i < g ≤ j`. A set of breakpoints is *valid* (`IsBreakpointSet`) when it
separates every four-gamete pair. `R_m` is computed by Hudson and Kaplan's sweep: scan the right
endpoints `j` from left to right and keep the interval `(i, j)` whenever some four-gamete pair
`(i, j)` starts at or after the right end of the last kept interval. (Hudson and Kaplan first
delete every interval containing another and then sweep from the left, which keeps the same
number of intervals; see Durrett 2008, §3.5.)

## Main results

* `card_le_card_of_isBreakpointSet`: every valid breakpoint set has at least as many points as
  any family of pairwise disjoint four-gamete intervals. This is the validity of the bound.
* `rm_le_card_of_isBreakpointSet`, `exists_isBreakpointSet_card_eq_rm`: `R_m` is the minimum
  size of a valid breakpoint set.
* `card_le_rm`, `exists_isDisjointFamily_card_eq_rm`: `R_m` is the maximum number of pairwise
  disjoint four-gamete intervals (greedy optimality, an exchange argument).
* `rm_le_card_of_nested_or_disjoint`: if between consecutive breakpoints the derived-allele
  clades of every two sites are nested or disjoint for some choice of ancestral alleles (as for
  clades of one tree), then there are at least `R_m` breakpoints.

The statement that pairwise compatible sites have one common perfect phylogeny (the four-gamete
theorem) and Hudson and Kaplan's formulas for the mean and variance of the number `R` of
recombination events under the coalescent with recombination are not covered.

## References

* R. R. Hudson, N. L. Kaplan, *Statistical properties of the number of recombination events in
  the history of a sample of DNA sequences*, Genetics 111 (1985), 147–164.
* R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed., Springer, 2008, §3.5.
-/

@[expose] public section

namespace Cslib.Bioinformatics.PopulationGenetics.HudsonKaplan

variable {n s : ℕ} (M : Fin n → Fin s → Bool)

/-- Sites `i` and `j` show all four gametes: for every pair of alleles `(a, b)` some haplotype
carries `a` at `i` and `b` at `j`. -/
def FourGametes (i j : Fin s) : Prop :=
  ∀ a b : Bool, ∃ r : Fin n, M r i = a ∧ M r j = b

instance (i j : Fin s) : Decidable (FourGametes M i j) := by
  unfold FourGametes; infer_instance

/-- The haplotypes carrying allele `a` at site `i`; when `a` is the derived allele this is the
clade defined by the mutation at `i`. -/
def carriers (i : Fin s) (a : Bool) : Finset (Fin n) :=
  Finset.univ.filter fun r => M r i = a

/-- A breakpoint `g` (a cut immediately to the left of site `g`) separates sites `i` and `j`
when `i < g ≤ j`. -/
def Separates (g i j : Fin s) : Prop := i < g ∧ g ≤ j

/-- A set `B` of breakpoints is valid for the sample `M` when it separates every pair of sites
`i < j` showing all four gametes. -/
def IsBreakpointSet (B : Finset (Fin s)) : Prop :=
  ∀ i j : Fin s, i < j → FourGametes M i j → ∃ g ∈ B, Separates g i j

/-- A family `F` of site pairs `(i, j)` consists of four-gamete intervals (`i < j`, all four
gametes at `i` and `j`) that are pairwise disjoint: of two distinct intervals, one ends at or
before the start of the other, so no breakpoint separates both. -/
def IsDisjointFamily (F : Finset (Fin s × Fin s)) : Prop :=
  (∀ x ∈ F, x.1 < x.2 ∧ FourGametes M x.1 x.2) ∧
    ∀ x ∈ F, ∀ y ∈ F, x ≠ y → x.2 ≤ y.1 ∨ y.2 ≤ x.1

/-- One step of the sweep at right endpoint `j`. The list `acc` holds the intervals kept so far,
most recent first; the next interval must start at or after the right end of the most recent
one (at or after site `0` if none was kept). Among the admissible four-gamete intervals ending
at `j`, the shortest one is kept. -/
def sweepStep (acc : List (Fin s × Fin s)) (j : Fin s) : List (Fin s × Fin s) :=
  let last : ℕ := (acc.head?.map fun x => (x.2 : ℕ)).getD 0
  let cands := Finset.univ.filter fun i : Fin s => last ≤ (i : ℕ) ∧ i < j ∧ FourGametes M i j
  if h : cands.Nonempty then (cands.max' h, j) :: acc else acc

/-- The intervals kept by Hudson and Kaplan's left-to-right sweep, most recent first. -/
def sweep : List (Fin s × Fin s) :=
  (List.finRange s).foldl (sweepStep M) []

/-- **Hudson and Kaplan's `R_m`**: the number of intervals kept by the sweep. -/
def rm : ℕ := (sweep M).length

private def SweepInvariant {n s : ℕ} (M : Fin n → Fin s → Bool)
    (acc : List (Fin s × Fin s)) : Prop :=
  (∀ x ∈ acc, x.1 < x.2 ∧ FourGametes M x.1 x.2) ∧
    acc.Pairwise (fun x y => y.2 ≤ x.1)

private theorem sweepStep_invariant {n s : ℕ} (M : Fin n → Fin s → Bool)
    (acc : List (Fin s × Fin s)) (j : Fin s) (hacc : SweepInvariant M acc)
    (hbefore : ∀ x ∈ acc, x.2 < j) :
    SweepInvariant M (sweepStep M acc j) ∧
      (∀ x ∈ acc, x ∈ sweepStep M acc j) ∧
      (∀ x ∈ sweepStep M acc j, x ∈ acc ∨ x.2 = j) ∧
      (∀ i : Fin s, i < j → FourGametes M i j →
        ∃ x ∈ sweepStep M acc j, Separates x.2 i j) := by
  classical
  unfold sweepStep
  dsimp only
  split
  · rename_i h
    have hc := (Finset.mem_filter.mp (Finset.max'_mem _ h)).2
    refine ⟨⟨?_, List.pairwise_cons.mpr ⟨?_, hacc.2⟩⟩, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hc.2
      · exact hacc.1 x hx
    · intro x hx
      cases acc with
      | nil => simp at hx
      | cons a tail =>
        have hlast := hc.1
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hlast
        · have hxa := (List.pairwise_cons.mp hacc.2).1 x hx
          exact le_trans hxa (le_trans (le_of_lt (hacc.1 a (by simp)).1) hlast)
    · intro x hx
      exact List.mem_cons_of_mem _ hx
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inr rfl
      · exact Or.inl hx
    · intro i hij hfour
      exact ⟨_, List.mem_cons_self, hij, le_rfl⟩
  · rename_i hempty
    refine ⟨hacc, fun _ hx => hx, fun _ hx => Or.inl hx, ?_⟩
    intro i hij hfour
    cases acc with
    | nil =>
      apply False.elim
      apply hempty
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.zero_le _, hij, hfour⟩⟩
    | cons a tail =>
      have hnot : ¬ (a.2 : ℕ) ≤ (i : ℕ) := by
        intro hle
        apply hempty
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle, hij, hfour⟩⟩
      exact ⟨a, List.mem_cons_self, Nat.lt_of_not_ge hnot,
        le_of_lt (hbefore a List.mem_cons_self)⟩

private theorem sweep_fold_invariant {n s : ℕ} (M : Fin n → Fin s → Bool)
    (l : List (Fin s)) (acc : List (Fin s × Fin s))
    (hl : l.Pairwise (· < ·)) (hacc : SweepInvariant M acc)
    (hbefore : ∀ x ∈ acc, ∀ j ∈ l, x.2 < j) :
    SweepInvariant M (l.foldl (sweepStep M) acc) ∧
      (∀ x ∈ acc, x ∈ l.foldl (sweepStep M) acc) ∧
      (∀ i j : Fin s, j ∈ l → i < j → FourGametes M i j →
        ∃ x ∈ l.foldl (sweepStep M) acc, Separates x.2 i j) := by
  induction l generalizing acc with
  | nil => exact ⟨hacc, fun _ hx => hx, by simp⟩
  | cons j l ih =>
    obtain ⟨hstep, hkeep, hends, hcover⟩ :=
      sweepStep_invariant M acc j hacc (fun x hx => hbefore x hx j List.mem_cons_self)
    have hsorted := List.pairwise_cons.mp hl
    have hnext : ∀ x ∈ sweepStep M acc j, ∀ k ∈ l, x.2 < k := by
      intro x hx k hk
      rcases hends x hx with hx | heq
      · exact hbefore x hx k (List.mem_cons_of_mem _ hk)
      · rw [heq]
        exact hsorted.1 k hk
    obtain ⟨hfinal, hremain, hcovered⟩ := ih _ hsorted.2 hstep hnext
    refine ⟨hfinal, fun x hx => hremain x (hkeep x hx), ?_⟩
    intro i k hk hik hfour
    rcases List.mem_cons.mp hk with rfl | hk
    · obtain ⟨x, hx, hsep⟩ := hcover i hik hfour
      exact ⟨x, hremain x hx, hsep⟩
    · exact hcovered i k hk hik hfour

private theorem sweep_invariant {n s : ℕ} (M : Fin n → Fin s → Bool) :
    SweepInvariant M (sweep M) ∧
      (∀ i j : Fin s, i < j → FourGametes M i j →
        ∃ x ∈ sweep M, Separates x.2 i j) := by
  have hsorted : (List.finRange s).Pairwise (· < ·) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simpa using hij
  have h := sweep_fold_invariant M (List.finRange s) [] hsorted
    ⟨by simp, List.Pairwise.nil⟩ (by simp)
  exact ⟨h.1, fun i j hij hfour => h.2.2 i j (List.mem_finRange j) hij hfour⟩

private theorem sweep_snd_nodup {n s : ℕ} (M : Fin n → Fin s → Bool) :
    ((sweep M).map Prod.snd).Nodup := by
  have h := (sweep_invariant M).1
  have hstrict : (sweep M).Pairwise (fun x y => y.2 < x.2) :=
    h.2.imp_of_mem fun {x y} hx _ hxy =>
      lt_of_le_of_lt hxy (h.1 x hx).1
  have hm : ((sweep M).map Prod.snd).Pairwise (fun x y => y < x) :=
    List.pairwise_map.mpr hstrict
  exact hm.nodup

/-- The intervals kept by the sweep are distinct. -/
theorem nodup_sweep : (sweep M).Nodup := by
  exact List.Nodup.of_map Prod.snd (sweep_snd_nodup M)

/-- The intervals kept by the sweep are pairwise disjoint four-gamete intervals. -/
theorem isDisjointFamily_sweep : IsDisjointFamily M (sweep M).toFinset := by
  have h := (sweep_invariant M).1
  refine ⟨?_, ?_⟩
  · intro x hx
    exact h.1 x (List.mem_toFinset.mp hx)
  · have hp : (sweep M).Pairwise
        (fun x y => x.2 ≤ y.1 ∨ y.2 ≤ x.1) :=
      h.2.imp fun hxy => Or.inr hxy
    let instSymm : Std.Symm (fun x y : Fin s × Fin s => x.2 ≤ y.1 ∨ y.2 ≤ x.1) :=
      ⟨fun _ _ hxy => hxy.symm⟩
    intro x hx y hy hne
    exact hp.forall (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy) hne

/-- Cutting immediately to the left of the right endpoint of every kept interval gives a valid
breakpoint set. -/
theorem isBreakpointSet_sweep : IsBreakpointSet M ((sweep M).map Prod.snd).toFinset := by
  intro i j hij hfour
  obtain ⟨x, hx, hsep⟩ := (sweep_invariant M).2 i j hij hfour
  exact ⟨x.2, List.mem_toFinset.mpr (List.mem_map.mpr ⟨x, hx, rfl⟩), hsep⟩

/-- The right endpoints of the kept intervals are distinct, so there are `R_m` of them. -/
theorem card_sweep_snd : ((sweep M).map Prod.snd).toFinset.card = rm M := by
  rw [List.toFinset_card_of_nodup (sweep_snd_nodup M), List.length_map]
  rfl

/-- **Validity of the bound** (Hudson–Kaplan 1985): a valid breakpoint set has at least as
many points as any family of pairwise disjoint four-gamete intervals, since each interval needs
its own breakpoint. -/
theorem card_le_card_of_isBreakpointSet {F : Finset (Fin s × Fin s)} {B : Finset (Fin s)}
    (hF : IsDisjointFamily M F) (hB : IsBreakpointSet M B) : F.card ≤ B.card := by
  classical
  have hex : ∀ x : ↥F, ∃ g : ↥B, Separates g x.val.1 x.val.2 := by
    intro x
    obtain ⟨g, hg, hsep⟩ := hB x.val.1 x.val.2
      (hF.1 x.val x.property).1 (hF.1 x.val x.property).2
    exact ⟨⟨g, hg⟩, hsep⟩
  choose f hf using hex
  apply Finset.card_le_card_of_injective (f := f)
  intro x y heq
  apply Subtype.ext
  by_contra hne
  have hx := hf x
  have hy := hf y
  rw [← heq] at hy
  rcases hF.2 x.val x.property y.val y.property hne with hxy | hyx
  · exact (not_lt_of_ge (le_trans hx.2 hxy)) hy.1
  · exact (not_lt_of_ge (le_trans hy.2 hyx)) hx.1

/-- **`R_m` is a lower bound** (Hudson–Kaplan 1985): every valid breakpoint set has at least
`R_m` points. -/
theorem rm_le_card_of_isBreakpointSet {B : Finset (Fin s)} (hB : IsBreakpointSet M B) :
    rm M ≤ B.card := by
  have h := card_le_card_of_isBreakpointSet M (isDisjointFamily_sweep M) hB
  rwa [List.toFinset_card_of_nodup (nodup_sweep M)] at h

/-- The bound is attained: some valid breakpoint set has exactly `R_m` points, so `R_m` is the
minimum size of a valid breakpoint set. -/
theorem exists_isBreakpointSet_card_eq_rm :
    ∃ B : Finset (Fin s), IsBreakpointSet M B ∧ B.card = rm M :=
  ⟨_, isBreakpointSet_sweep M, card_sweep_snd M⟩

/-- **Greedy optimality**: no family of pairwise disjoint four-gamete intervals has more than
`R_m` members. -/
theorem card_le_rm {F : Finset (Fin s × Fin s)} (hF : IsDisjointFamily M F) : F.card ≤ rm M :=
  (card_le_card_of_isBreakpointSet M hF (isBreakpointSet_sweep M)).trans (card_sweep_snd M).le

/-- The sweep attains the maximum: `R_m` is the largest size of a family of pairwise disjoint
four-gamete intervals. -/
theorem exists_isDisjointFamily_card_eq_rm :
    ∃ F : Finset (Fin s × Fin s), IsDisjointFamily M F ∧ F.card = rm M :=
  ⟨_, isDisjointFamily_sweep M, List.toFinset_card_of_nodup (nodup_sweep M)⟩

/-- Two sites miss one of the four gametes exactly when, for some choice of the alleles `a` at
`i` and `b` at `j` (the derived alleles), the carrier sets are nested or disjoint, as two clades
of one rooted tree are. -/
theorem not_fourGametes_iff (i j : Fin s) :
    ¬FourGametes M i j ↔ ∃ a b : Bool,
      carriers M i a ⊆ carriers M j b ∨ Disjoint (carriers M i a) (carriers M j b) := by
  constructor
  · intro h
    simp only [FourGametes, not_forall, not_exists] at h
    obtain ⟨a, b, hab⟩ := h
    refine ⟨a, b, Or.inr (Finset.disjoint_left.2 fun r hri hrj => hab r ?_)⟩
    simp only [carriers, Finset.mem_filter, Finset.mem_univ, true_and] at hri hrj
    exact ⟨hri, hrj⟩
  · rintro ⟨a, b, hsub | hdis⟩ h
    · obtain ⟨r, hri, hrj⟩ := h a (!b)
      have : r ∈ carriers M j b := hsub (by simp [carriers, hri])
      simp only [carriers, Finset.mem_filter, Finset.mem_univ, true_and] at this
      rw [this] at hrj
      cases b <;> simp at hrj
    · obtain ⟨r, hri, hrj⟩ := h a b
      have h1 : r ∈ carriers M i a := by simp [carriers, hri]
      have h2 : r ∈ carriers M j b := by simp [carriers, hrj]
      exact Finset.disjoint_left.1 hdis h1 h2

/-- **Hudson and Kaplan's bound for tree-like blocks.** Suppose the breakpoints `B` cut the
sequence into blocks such that, within a block, the derived-allele clades of every two sites are
nested or disjoint for some choice of the derived alleles (as for sites whose mutations sit on
one tree under the infinite-sites model). Then there are at least `R_m` breakpoints. -/
theorem rm_le_card_of_nested_or_disjoint {B : Finset (Fin s)}
    (h : ∀ i j : Fin s, i < j → (∀ g ∈ B, ¬Separates g i j) → ∃ a b : Bool,
      carriers M i a ⊆ carriers M j b ∨ Disjoint (carriers M i a) (carriers M j b)) :
    rm M ≤ B.card := by
  refine rm_le_card_of_isBreakpointSet M fun i j hij h4 => ?_
  by_contra hno
  exact (not_fourGametes_iff M i j).2 (h i j hij fun g hg hs => hno ⟨g, hg, hs⟩) h4

end Cslib.Bioinformatics.PopulationGenetics.HudsonKaplan
