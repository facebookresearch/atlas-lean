/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.RNA.PartitionFunction

/-!
# Zuker's minimum free energy algorithm under a loop energy model

In the nearest-neighbor (loop) energy model the free energy of an RNA secondary structure is
not a sum over base pairs but a sum over the **loops** of the structure (Tinoco et al. 1971;
Zuker and Stiegler 1981; Zuker and Sankoff 1984). The pairs of a structure `P` that are not
enclosed by any other pair are its exterior branches; for a pair `(i, j) ∈ P`, its branches
(`branches P (i, j)`) are the pairs of `P` strictly inside `(i, j)` that are not enclosed by
another pair strictly inside `(i, j)`. The loop closed by `(i, j)` is

* a **hairpin** if it has no branch,
* a **stack, bulge or interior loop** if it has exactly one branch `(k, l)` (a stack when
  `k = i + 1` and `l = j - 1`),
* a **multiloop** if it has at least two branches.

A `LoopEnergy` assigns an energy to each kind of loop: `hairpin i j`, `interior i j k l`
(stacks, bulges and interior loops alike), and the affine multiloop energy
`a + b · (number of branches) + c · (number of unpaired bases in the loop)` (the multiloop model
of Jaeger, Turner and Zuker 1989, also used by McCaskill 1990). The exterior loop
has energy `0`. The energy of a structure is the sum of the energies of the loops closed by its
pairs (`freeEnergy`).

`zukerVW` is the Zuker recursion for an interval `[i, i + len)`: the minimum energy `V` of a
structure on the interval closed by the pair `(i, i + len - 1)`, and the minimum energy `WM` of
a multiloop fragment with at least one branch; `zukerExterior` adds the exterior loop on a
prefix. Values live in `WithTop ℝ` (`⊤` when no structure is possible).

## Main results

* `existsUnique_closing_pair`: every pair of a structure is either an exterior branch or a
  branch of exactly one pair, so each pair is shared by the loop it closes and exactly one
  enclosing loop (possibly the exterior loop).
* `existsUnique_loop_of_pos`: every position lies in the exterior loop or in the loop closed by
  exactly one pair; with the previous result, the loops (one per pair, plus the exterior loop)
  decompose the structure uniquely.
* `loopEnergy_eq_hairpin`, `loopEnergy_eq_interior`, `loopEnergy_eq_multiloop`: the energy of
  the loop closed by a pair, by number of branches.
* `zukerMFE_eq_inf`: Zuker's recursion computes the minimum free energy over all secondary
  structures with minimum hairpin `m`, for arbitrary real loop energies.
* `zukerMFE_le_zero`: the minimum free energy is at most that of the open chain.

## Scope

The energy parameters are arbitrary functions of the closing and inner positions, so any
sequence-dependent table (such as the Turner rules of the Nearest Neighbor Database) fits;
the parameter values are data, not theorems. Dangling-end, terminal-mismatch and coaxial
stacking terms are not modeled (the exterior loop has energy `0`). `loopEnergy` is meant for a
pair of a secondary structure; for other inputs its natural-number subtraction truncates.

## Cost model

`zukerVW` and `zukerExterior` are specifications by recursion on interval lengths and take
exponential time if evaluated directly. Memoized on the `O(n²)` intervals they give an `O(n⁴)`
algorithm, because interior loops of unbounded size are allowed; the usual `O(n³)` bound needs
a cap on interior-loop size, which is not formalized here.

## References

* M. Zuker and P. Stiegler, *Optimal computer folding of large RNA sequences using
  thermodynamics and auxiliary information*, Nucleic Acids Res. 9 (1981), 133–148.
* M. Zuker and D. Sankoff, *RNA secondary structures and their prediction*, Bull. Math. Biol.
  46 (1984), 591–621.
* J. A. Jaeger, D. H. Turner and M. Zuker, *Improved predictions of secondary structures for
  RNA*, Proc. Natl. Acad. Sci. USA 86 (1989), 7706–7710.
* J. S. McCaskill, *The equilibrium partition function and base pair binding probabilities
  for RNA secondary structure*, Biopolymers 29 (1990), 1105–1119.
* I. Tinoco, O. C. Uhlenbeck and M. D. Levine, *Estimation of secondary structure in
  ribonucleic acids*, Nature 230 (1971), 362–367.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.RNA.Zuker

open Cslib.Bioinformatics.RNA.Nussinov Cslib.Bioinformatics.RNA.PartitionFunction

variable {B : Type*} (pair : B → B → Prop) (m : ℕ) (s : List B)

/-- A loop (nearest-neighbor) energy model: energies of hairpin loops closed by `(i, j)`, of
stacks, bulges and interior loops closed by `(i, j)` with inner pair `(k, l)`, and the affine
multiloop parameters `a` (per multiloop), `b` (per branch) and `c` (per unpaired base). The
exterior loop has energy `0`. Units: free energy, e.g. kcal/mol. -/
structure LoopEnergy where
  /-- Energy of the hairpin loop closed by the pair `(i, j)`. -/
  hairpin : ℕ → ℕ → ℝ
  /-- Energy of the stack, bulge or interior loop closed by `(i, j)` with inner pair `(k, l)`. -/
  interior : ℕ → ℕ → ℕ → ℕ → ℝ
  /-- Multiloop initiation energy `a`. -/
  multiA : ℝ
  /-- Multiloop energy per branch `b`. -/
  multiB : ℝ
  /-- Multiloop energy per unpaired base `c`. -/
  multiC : ℝ

/-- `q` lies strictly inside the pair `p`: `p.1 < q.1` and `q.2 < p.2`. -/
def Encloses (p q : ℕ × ℕ) : Prop :=
  p.1 < q.1 ∧ q.2 < p.2

/-- `Encloses` is decidable. -/
instance (p q : ℕ × ℕ) : Decidable (Encloses p q) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The branches of the loop closed by `p` in `P`: the pairs of `P` strictly inside `p` that
are not strictly inside another pair of `P` strictly inside `p`. -/
def branches (P : Finset (ℕ × ℕ)) (p : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  P.filter fun q => Encloses p q ∧ ∀ r ∈ P, Encloses p r → ¬ Encloses r q

/-- The exterior branches of `P`: the pairs not strictly inside any pair of `P`. -/
def exteriorBranches (P : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  P.filter fun q => ∀ r ∈ P, ¬ Encloses r q

/-- **Unique loop decomposition**: in a secondary structure every pair is either an exterior
branch or a branch of exactly one pair of the structure (and not both): each pair is shared by
the loop it closes and exactly one enclosing loop, possibly the exterior loop. -/
theorem existsUnique_closing_pair (P : Finset (ℕ × ℕ)) (hP : IsStructure pair m s P)
    (q : ℕ × ℕ) (hq : q ∈ P) :
    (q ∈ exteriorBranches P ∧ ∀ p ∈ P, q ∉ branches P p) ∨
      (q ∉ exteriorBranches P ∧ ∃! p, p ∈ P ∧ q ∈ branches P p) := by
  classical
  have hql := hP.loop q hq
  by_cases hext : q ∈ exteriorBranches P
  · refine Or.inl ⟨hext, fun p hp hqb => ?_⟩
    simp only [exteriorBranches, branches, Finset.mem_filter] at hext hqb
    exact hext.2 p hp hqb.2.1
  · refine Or.inr ⟨hext, ?_⟩
    have hS : (P.filter fun r => Encloses r q).Nonempty := by
      simp only [exteriorBranches, Finset.mem_filter, not_and, not_forall, not_not] at hext
      obtain ⟨r, hr, hrq⟩ := hext hq
      exact ⟨r, Finset.mem_filter.mpr ⟨hr, hrq⟩⟩
    obtain ⟨p, hpS, hmin⟩ := Finset.exists_min_image _ (fun r : ℕ × ℕ => r.2 - r.1) hS
    rw [Finset.mem_filter] at hpS
    have key : ∀ p₁ ∈ P, ∀ p₂ ∈ P, Encloses p₁ q → Encloses p₂ q →
        p₁ = p₂ ∨ Encloses p₁ p₂ ∨ Encloses p₂ p₁ := by
      intro p₁ h₁ p₂ h₂ e₁ e₂
      by_cases hne : p₁ = p₂
      · exact Or.inl hne
      have hd := hP.disjoint p₁ h₁ p₂ h₂ hne
      have hc₁ := hP.noncrossing p₁ h₁ p₂ h₂
      have hc₂ := hP.noncrossing p₂ h₂ p₁ h₁
      right
      unfold Encloses at *
      omega
    refine ⟨p, ⟨hpS.1, ?_⟩, ?_⟩
    · refine Finset.mem_filter.mpr ⟨hq, hpS.2, fun r hr hpr hrq => ?_⟩
      have := hmin r (Finset.mem_filter.mpr ⟨hr, hrq⟩)
      unfold Encloses at hpr hrq
      omega
    · rintro p' ⟨hp', hqb⟩
      simp only [branches, Finset.mem_filter] at hqb
      rcases key p' hp' p hpS.1 hqb.2.1 hpS.2 with h | h | h
      · exact h
      · exact absurd hpS.2 (hqb.2.2 p hpS.1 h)
      · exfalso
        have := hmin p' (Finset.mem_filter.mpr ⟨hp', hqb.2.1⟩)
        unfold Encloses at h hqb
        omega

/-- The energy of the loop closed by `p = (i, j)` in `P`: a hairpin with no branch, a stack,
bulge or interior loop with one branch `(k, l)`, and the affine multiloop energy
`a + b · r + c · u` with `r ≥ 2` branches and `u = (j - i - 1) - ∑ (l - k + 1)` unpaired
bases. -/
noncomputable def loopEnergy (E : LoopEnergy) (P : Finset (ℕ × ℕ)) (p : ℕ × ℕ) : ℝ :=
  let br := branches P p
  if br.card = 0 then E.hairpin p.1 p.2
  else if h : br.card = 1 then
    let q := (Finset.card_eq_one.mp h).choose
    E.interior p.1 p.2 q.1 q.2
  else
    E.multiA + E.multiB * br.card +
      E.multiC * ((p.2 - p.1 - 1 - ∑ q ∈ br, (q.2 - q.1 + 1) : ℕ) : ℝ)

/-- The free energy of a structure in the loop model: the sum of the energies of the loops
closed by its pairs (the exterior loop contributes `0`). -/
noncomputable def freeEnergy (E : LoopEnergy) (P : Finset (ℕ × ℕ)) : ℝ :=
  ∑ p ∈ P, loopEnergy E P p

section Structures

variable {pair m s}

/-- All pairs of `P` lie in the half-open interval `[lo, hi)`. -/
private def Rng (lo hi : ℕ) (P : Finset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ P, lo ≤ p.1 ∧ p.2 < hi

private theorem mem_structuresIn {i len : ℕ} {P : Finset (ℕ × ℕ)} :
    P ∈ structuresIn pair m s i len ↔ IsStructure pair m s P ∧ Rng i (i + len) P := by
  classical
  simp only [structuresIn, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hsub, hP⟩
    refine ⟨hP, fun p hp => ?_⟩
    have := hsub hp
    simp only [Finset.mem_product, Finset.mem_Ico] at this
    omega
  · rintro ⟨hP, hR⟩
    refine ⟨fun p hp => ?_, hP⟩
    have := hR p hp
    have := hP.loop p hp
    simp only [Finset.mem_product, Finset.mem_Ico]
    omega

private theorem _root_.Cslib.Bioinformatics.RNA.Nussinov.IsStructure.lt
    {P : Finset (ℕ × ℕ)} (hP : IsStructure pair m s P)
    {p : ℕ × ℕ} (hp : p ∈ P) : p.1 < p.2 := by
  have := hP.loop p hp; omega

private theorem _root_.Cslib.Bioinformatics.RNA.Nussinov.IsStructure.mono
    {P Q : Finset (ℕ × ℕ)} (hP : IsStructure pair m s P)
    (hQ : Q ⊆ P) : IsStructure pair m s Q where
  loop p hp := hP.loop p (hQ hp)
  compl p hp := hP.compl p (hQ hp)
  disjoint p hp q hq := hP.disjoint p (hQ hp) q (hQ hq)
  noncrossing p hp q hq := hP.noncrossing p (hQ hp) q (hQ hq)

private theorem _root_.Cslib.Bioinformatics.RNA.Nussinov.IsStructure.union
    {P₁ P₂ : Finset (ℕ × ℕ)} {lo u hi : ℕ}
    (h₁ : IsStructure pair m s P₁) (h₂ : IsStructure pair m s P₂)
    (r₁ : Rng lo u P₁) (r₂ : Rng u hi P₂) : IsStructure pair m s (P₁ ∪ P₂) where
  loop p hp := by
    rcases Finset.mem_union.mp hp with hp | hp
    · exact h₁.loop p hp
    · exact h₂.loop p hp
  compl p hp := by
    rcases Finset.mem_union.mp hp with hp | hp
    · exact h₁.compl p hp
    · exact h₂.compl p hp
  disjoint p hp q hq hne := by
    rcases Finset.mem_union.mp hp with hp | hp <;> rcases Finset.mem_union.mp hq with hq | hq
    · exact h₁.disjoint p hp q hq hne
    · have := r₁ p hp; have := r₂ q hq; have := h₁.lt hp; have := h₂.lt hq; omega
    · have := r₂ p hp; have := r₁ q hq; have := h₂.lt hp; have := h₁.lt hq; omega
    · exact h₂.disjoint p hp q hq hne
  noncrossing p hp q hq := by
    rcases Finset.mem_union.mp hp with hp | hp <;> rcases Finset.mem_union.mp hq with hq | hq
    · exact h₁.noncrossing p hp q hq
    · have := r₁ p hp; have := r₂ q hq; have := h₁.lt hp; have := h₂.lt hq; omega
    · have := r₂ p hp; have := r₁ q hq; have := h₂.lt hp; have := h₁.lt hq; omega
    · exact h₂.noncrossing p hp q hq

private theorem _root_.Cslib.Bioinformatics.RNA.Nussinov.IsStructure.insert
    {Q : Finset (ℕ × ℕ)} {i j : ℕ}
    (hQ : IsStructure pair m s Q) (hr : Rng (i + 1) j Q) (hij : i + m < j)
    (hc : CanPair pair s i j) : IsStructure pair m s (insert (i, j) Q) where
  loop p hp := by
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hij
    · exact hQ.loop p hp
  compl p hp := by
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hc
    · exact hQ.compl p hp
  disjoint p hp q hq hne := by
    rcases Finset.mem_insert.mp hp with rfl | hp <;> rcases Finset.mem_insert.mp hq with rfl | hq
    · exact absurd rfl hne
    · have := hr q hq; have := hQ.lt hq; dsimp only; omega
    · have := hr p hp; have := hQ.lt hp; dsimp only; omega
    · exact hQ.disjoint p hp q hq hne
  noncrossing p hp q hq := by
    rcases Finset.mem_insert.mp hp with rfl | hp <;> rcases Finset.mem_insert.mp hq with rfl | hq
    · dsimp only; omega
    · have := hr q hq; have := hQ.lt hq; dsimp only; omega
    · have := hr p hp; have := hQ.lt hp; dsimp only; omega
    · exact hQ.noncrossing p hp q hq

private theorem Rng.mono {lo hi lo' hi' : ℕ} {P : Finset (ℕ × ℕ)} (h : Rng lo hi P)
    (h₁ : lo' ≤ lo) (h₂ : hi ≤ hi') : Rng lo' hi' P := fun p hp => by
  have := h p hp; omega

private theorem Rng.union {lo hi : ℕ} {P₁ P₂ : Finset (ℕ × ℕ)} (h₁ : Rng lo hi P₁)
    (h₂ : Rng lo hi P₂) : Rng lo hi (P₁ ∪ P₂) := fun p hp => by
  rcases Finset.mem_union.mp hp with hp | hp
  · exact h₁ p hp
  · exact h₂ p hp

private theorem rng_empty (lo hi : ℕ) : Rng lo hi (∅ : Finset (ℕ × ℕ)) := by
  intro p hp; simp at hp

private theorem isStructure_empty : IsStructure pair m s (∅ : Finset (ℕ × ℕ)) where
  loop p hp := by simp at hp
  compl p hp := by simp at hp
  disjoint p hp := by simp at hp
  noncrossing p hp := by simp at hp

/-! ### Locality of loop energies -/

private theorem branches_congr {P Q : Finset (ℕ × ℕ)} {p : ℕ × ℕ}
    (h : P.filter (Encloses p) = Q.filter (Encloses p)) : branches P p = branches Q p := by
  ext q
  have key : ∀ r, (r ∈ P ∧ Encloses p r) ↔ (r ∈ Q ∧ Encloses p r) := fun r => by
    rw [← Finset.mem_filter, ← Finset.mem_filter, h]
  simp only [branches, Finset.mem_filter]
  constructor
  · rintro ⟨hq, he, hall⟩
    refine ⟨((key q).mp ⟨hq, he⟩).1, he, fun r hr hpr => hall r ((key r).mpr ⟨hr, hpr⟩).1 hpr⟩
  · rintro ⟨hq, he, hall⟩
    refine ⟨((key q).mpr ⟨hq, he⟩).1, he, fun r hr hpr => hall r ((key r).mp ⟨hr, hpr⟩).1 hpr⟩

private theorem loopEnergy_congr (E : LoopEnergy) {P Q : Finset (ℕ × ℕ)} {p : ℕ × ℕ}
    (h : P.filter (Encloses p) = Q.filter (Encloses p)) :
    loopEnergy E P p = loopEnergy E Q p := by
  simp only [loopEnergy, branches_congr h]

/-- A pair with no branch closes a hairpin loop. -/
theorem loopEnergy_eq_hairpin (E : LoopEnergy) {P : Finset (ℕ × ℕ)} {p : ℕ × ℕ}
    (h : branches P p = ∅) : loopEnergy E P p = E.hairpin p.1 p.2 := by
  simp [loopEnergy, h]

/-- A pair with exactly one branch `q` closes a stack, bulge or interior loop with inner pair
`q`. -/
theorem loopEnergy_eq_interior (E : LoopEnergy) {P : Finset (ℕ × ℕ)} {p q : ℕ × ℕ}
    (h : branches P p = {q}) : loopEnergy E P p = E.interior p.1 p.2 q.1 q.2 := by
  have h1 : (branches P p).card = 1 := by rw [h]; rfl
  have hc : q = (Finset.card_eq_one.mp h1).choose :=
    Finset.singleton_inj.mp (h.symm.trans (Finset.card_eq_one.mp h1).choose_spec)
  simp only [loopEnergy, h1, one_ne_zero, ↓reduceIte, ↓reduceDIte]
  rw [← hc]

/-- A pair with at least two branches closes a multiloop with the affine energy. -/
theorem loopEnergy_eq_multiloop (E : LoopEnergy) {P : Finset (ℕ × ℕ)} {p : ℕ × ℕ}
    (h : 2 ≤ (branches P p).card) : loopEnergy E P p = E.multiA + E.multiB * (branches P p).card +
      E.multiC * ((p.2 - p.1 - 1 - ∑ q ∈ branches P p, (q.2 - q.1 + 1) : ℕ) : ℝ) := by
  have h0 : (branches P p).card ≠ 0 := by omega
  have h1 : (branches P p).card ≠ 1 := by omega
  simp only [loopEnergy, h0, h1, ↓reduceIte, ↓reduceDIte]

private theorem structuresIn_zero (i : ℕ) : structuresIn pair m s i 0 = {∅} := by
  ext P
  rw [mem_structuresIn, Finset.mem_singleton]
  constructor
  · rintro ⟨hPs, hPr⟩
    refine Finset.eq_empty_of_forall_notMem fun q hq => ?_
    have := hPr q hq; have := hPs.lt hq; omega
  · rintro rfl; exact ⟨isStructure_empty, rng_empty _ _⟩

end Structures

section Locality

variable {pair m s}

private theorem filter_encloses_eq_empty_left {P₂ : Finset (ℕ × ℕ)} {u hi : ℕ} {p : ℕ × ℕ}
    (h₂ : IsStructure pair m s P₂) (r₂ : Rng u hi P₂) (hp : p.2 < u) :
    P₂.filter (Encloses p) = ∅ := by
  refine Finset.filter_eq_empty_iff.mpr fun q hq he => ?_
  have := r₂ q hq; have := h₂.lt hq; unfold Encloses at he; omega

private theorem filter_encloses_eq_empty_right {P₁ : Finset (ℕ × ℕ)} {lo u : ℕ} {p : ℕ × ℕ}
    (h₁ : IsStructure pair m s P₁) (r₁ : Rng lo u P₁) (hp : u ≤ p.1) :
    P₁.filter (Encloses p) = ∅ := by
  refine Finset.filter_eq_empty_iff.mpr fun q hq he => ?_
  have := r₁ q hq; have := h₁.lt hq; unfold Encloses at he; omega

private theorem disjoint_of_rng {P₁ P₂ : Finset (ℕ × ℕ)} {lo u hi : ℕ}
    (r₁ : Rng lo u P₁) (r₂ : Rng u hi P₂) (h₁ : IsStructure pair m s P₁) :
    Disjoint P₁ P₂ := by
  refine Finset.disjoint_left.mpr fun q hq hq' => ?_
  have := r₁ q hq; have := r₂ q hq'; have := h₁.lt hq; omega

private theorem freeEnergy_union (E : LoopEnergy) {P₁ P₂ : Finset (ℕ × ℕ)} {lo u hi : ℕ}
    (h₁ : IsStructure pair m s P₁) (h₂ : IsStructure pair m s P₂)
    (r₁ : Rng lo u P₁) (r₂ : Rng u hi P₂) :
    freeEnergy E (P₁ ∪ P₂) = freeEnergy E P₁ + freeEnergy E P₂ := by
  unfold freeEnergy
  rw [Finset.sum_union (disjoint_of_rng r₁ r₂ h₁)]
  congr 1
  · refine Finset.sum_congr rfl fun p hp => loopEnergy_congr E ?_
    have := r₁ p hp
    rw [Finset.filter_union, filter_encloses_eq_empty_left h₂ r₂ (by omega), Finset.union_empty]
  · refine Finset.sum_congr rfl fun p hp => loopEnergy_congr E ?_
    have := r₂ p hp
    rw [Finset.filter_union, filter_encloses_eq_empty_right h₁ r₁ (by omega), Finset.empty_union]

private theorem exteriorBranches_subset (P : Finset (ℕ × ℕ)) : exteriorBranches P ⊆ P :=
  Finset.filter_subset _ _

private theorem exteriorBranches_union {P₁ P₂ : Finset (ℕ × ℕ)} {lo u hi : ℕ}
    (h₁ : IsStructure pair m s P₁) (h₂ : IsStructure pair m s P₂)
    (r₁ : Rng lo u P₁) (r₂ : Rng u hi P₂) :
    exteriorBranches (P₁ ∪ P₂) = exteriorBranches P₁ ∪ exteriorBranches P₂ := by
  ext q
  simp only [exteriorBranches, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hq | hq, hall⟩
    · exact Or.inl ⟨hq, fun r hr => hall r (Or.inl hr)⟩
    · exact Or.inr ⟨hq, fun r hr => hall r (Or.inr hr)⟩
  · rintro (⟨hq, hall⟩ | ⟨hq, hall⟩)
    · refine ⟨Or.inl hq, fun r hr => ?_⟩
      rcases hr with hr | hr
      · exact hall r hr
      · have := r₁ q hq; have := r₂ r hr; have := h₁.lt hq; have := h₂.lt hr
        unfold Encloses; omega
    · refine ⟨Or.inr hq, fun r hr => ?_⟩
      rcases hr with hr | hr
      · have := r₂ q hq; have := r₁ r hr; have := h₂.lt hq; have := h₁.lt hr
        unfold Encloses; omega
      · exact hall r hr

private theorem not_mem_of_rng {Q : Finset (ℕ × ℕ)} {i j : ℕ} (hr : Rng (i + 1) j Q) :
    (i, j) ∉ Q := fun h => by have := hr _ h; dsimp only at this; omega

private theorem freeEnergy_insert (E : LoopEnergy) {Q : Finset (ℕ × ℕ)} {i j : ℕ}
    (hr : Rng (i + 1) j Q) :
    freeEnergy E (insert (i, j) Q) = loopEnergy E (insert (i, j) Q) (i, j) + freeEnergy E Q := by
  unfold freeEnergy
  rw [Finset.sum_insert (not_mem_of_rng hr)]
  congr 1
  refine Finset.sum_congr rfl fun p hp => loopEnergy_congr E ?_
  have := hr p hp
  have hne : ¬ Encloses p (i, j) := by unfold Encloses; dsimp only; omega
  rw [Finset.filter_insert]
  simp only [hne, ↓reduceIte]

private theorem branches_insert {Q : Finset (ℕ × ℕ)} {i j : ℕ} (hr : Rng (i + 1) j Q) :
    branches (insert (i, j) Q) (i, j) = exteriorBranches Q := by
  ext q
  simp only [branches, exteriorBranches, Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hq | hq, he, hall⟩
    · subst hq; unfold Encloses at he; dsimp only at he; omega
    · refine ⟨hq, fun r hr' => hall r (Or.inr hr') ?_⟩
      have := hr r hr'; unfold Encloses; omega
  · rintro ⟨hq, hall⟩
    refine ⟨Or.inr hq, ?_, ?_⟩
    · have := hr q hq; unfold Encloses; omega
    · rintro r (rfl | hr') hpr
      · unfold Encloses at hpr; omega
      · exact hall r hr'

private theorem exteriorBranches_insert {Q : Finset (ℕ × ℕ)} {i j : ℕ} (hr : Rng (i + 1) j Q) :
    exteriorBranches (insert (i, j) Q) = {(i, j)} := by
  ext q
  simp only [exteriorBranches, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨rfl | hq, hall⟩
    · rfl
    · exfalso
      have := hr q hq
      exact hall (i, j) (Or.inl rfl) (by unfold Encloses; dsimp only; omega)
  · rintro rfl
    refine ⟨Or.inl rfl, ?_⟩
    rintro r (rfl | hr')
    · unfold Encloses; omega
    · have := hr r hr'; unfold Encloses; omega

private theorem exists_exterior_cover {Q : Finset (ℕ × ℕ)} (q : ℕ × ℕ) (hq : q ∈ Q) :
    ∃ e ∈ exteriorBranches Q, e = q ∨ Encloses e q := by
  classical
  obtain ⟨e, he, hmin⟩ := Finset.exists_min_image (Q.filter fun r => r = q ∨ Encloses r q)
    (fun r : ℕ × ℕ => r.1) ⟨q, Finset.mem_filter.mpr ⟨hq, Or.inl rfl⟩⟩
  rw [Finset.mem_filter] at he
  refine ⟨e, Finset.mem_filter.mpr ⟨he.1, fun r hr hre => ?_⟩, he.2⟩
  have hrq : r = q ∨ Encloses r q := by
    right
    rcases he.2 with rfl | heq
    · exact hre
    · unfold Encloses at *; omega
  have := hmin r (Finset.mem_filter.mpr ⟨hr, hrq⟩)
  unfold Encloses at hre; omega

private theorem exteriorBranches_nonempty {Q : Finset (ℕ × ℕ)} (hQ : Q.Nonempty) :
    (exteriorBranches Q).Nonempty := by
  obtain ⟨q, hq⟩ := hQ
  obtain ⟨e, he, -⟩ := exists_exterior_cover q hq
  exact ⟨e, he⟩

private theorem branches_eq_exteriorBranches_filter (P : Finset (ℕ × ℕ)) (p : ℕ × ℕ) :
    branches P p = exteriorBranches (P.filter (Encloses p)) := by
  ext q
  simp only [branches, exteriorBranches, Finset.mem_filter]
  constructor
  · rintro ⟨hq, he, hall⟩
    exact ⟨⟨hq, he⟩, fun r ⟨hr, hpr⟩ => hall r hr hpr⟩
  · rintro ⟨⟨hq, he⟩, hall⟩
    exact ⟨hq, he, fun r hr hpr => hall r ⟨hr, hpr⟩⟩

end Locality

/-- **Every position lies in exactly one loop**: a position `x` either lies strictly inside no
pair (it is in the exterior loop) or lies in the loop closed by exactly one pair `p`, the one
with `p.1 < x < p.2` such that no branch of `p` has `x` strictly inside it. For an unpaired
position this is the unique loop containing it. For an endpoint of a pair `q` it is the loop of
which `q` is a branch; the same base also closes the loop of `q`, as in the usual convention
that a base pair is shared by two loops (see `existsUnique_closing_pair`). -/
theorem existsUnique_loop_of_pos (P : Finset (ℕ × ℕ)) (hP : IsStructure pair m s P) (x : ℕ) :
    (∀ p ∈ P, ¬ (p.1 < x ∧ x < p.2)) ∨
      ∃! p, p ∈ P ∧ (p.1 < x ∧ x < p.2) ∧ ∀ q ∈ branches P p, ¬ (q.1 < x ∧ x < q.2) := by
  classical
  by_cases h : ∀ p ∈ P, ¬ (p.1 < x ∧ x < p.2)
  · exact Or.inl h
  right
  push Not at h
  obtain ⟨p₀, hp₀, hxp₀⟩ := h
  obtain ⟨p, hpS, hmin⟩ := Finset.exists_min_image (P.filter fun r => r.1 < x ∧ x < r.2)
    (fun r : ℕ × ℕ => r.2 - r.1) ⟨p₀, Finset.mem_filter.mpr ⟨hp₀, hxp₀⟩⟩
  rw [Finset.mem_filter] at hpS
  refine ⟨p, ⟨hpS.1, hpS.2, fun q hq hxq => ?_⟩, ?_⟩
  · simp only [branches, Finset.mem_filter] at hq
    have := hmin q (Finset.mem_filter.mpr ⟨hq.1, hxq⟩)
    unfold Encloses at hq; omega
  · rintro p' ⟨hp', hxp', hbr⟩
    by_contra hne
    have hd := hP.disjoint p' hp' p hpS.1 hne
    have hc₁ := hP.noncrossing p' hp' p hpS.1
    have hc₂ := hP.noncrossing p hpS.1 p' hp'
    have hx₁ := hpS.2
    by_cases hout : Encloses p' p
    · obtain ⟨b, hb, hbp⟩ := exists_exterior_cover (Q := P.filter (Encloses p')) p
        (Finset.mem_filter.mpr ⟨hpS.1, hout⟩)
      rw [← branches_eq_exteriorBranches_filter] at hb
      refine hbr b hb ?_
      rcases hbp with rfl | hbp
      · exact hx₁
      · unfold Encloses at hbp; omega
    · have := hmin p' (Finset.mem_filter.mpr ⟨hp', hxp'⟩)
      unfold Encloses at hout; omega

section Unpaired

variable {pair m s}

open Classical in
/-- The positions of `[lo, hi)` covered by no exterior branch of `P`. -/
private noncomputable def unp (lo hi : ℕ) (P : Finset (ℕ × ℕ)) : ℕ :=
  ((Finset.Ico lo hi).filter fun x => ∀ q ∈ exteriorBranches P, ¬ (q.1 ≤ x ∧ x ≤ q.2)).card

private theorem unp_union {P₁ P₂ : Finset (ℕ × ℕ)} {lo u hi : ℕ}
    (h₁ : IsStructure pair m s P₁) (h₂ : IsStructure pair m s P₂)
    (r₁ : Rng lo u P₁) (r₂ : Rng u hi P₂) (hlo : lo ≤ u) (hhi : u ≤ hi) :
    unp lo hi (P₁ ∪ P₂) = unp lo u P₁ + unp u hi P₂ := by
  classical
  unfold unp
  rw [exteriorBranches_union h₁ h₂ r₁ r₂, ← Finset.Ico_union_Ico_eq_Ico hlo hhi,
    Finset.filter_union, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive lo u hi))]
  congr 1
  · refine congrArg Finset.card (Finset.filter_congr fun x hx => ?_)
    rw [Finset.mem_Ico] at hx
    constructor
    · exact fun h q hq => h q (Finset.mem_union_left _ hq)
    · intro h q hq
      rcases Finset.mem_union.mp hq with hq | hq
      · exact h q hq
      · have := r₂ q (exteriorBranches_subset _ hq); omega
  · refine congrArg Finset.card (Finset.filter_congr fun x hx => ?_)
    rw [Finset.mem_Ico] at hx
    constructor
    · exact fun h q hq => h q (Finset.mem_union_right _ hq)
    · intro h q hq
      rcases Finset.mem_union.mp hq with hq | hq
      · have := r₁ q (exteriorBranches_subset _ hq); omega
      · exact h q hq

private theorem unp_empty (lo hi : ℕ) : unp lo hi (∅ : Finset (ℕ × ℕ)) = hi - lo := by
  classical
  unfold unp
  rw [Finset.filter_true_of_mem (fun x _ q hq => by simp [exteriorBranches] at hq),
    Nat.card_Ico]

private theorem erase_rng {P : Finset (ℕ × ℕ)} {i j : ℕ} (hP : IsStructure pair m s P)
    (hr : Rng i (j + 1) P) (hij : (i, j) ∈ P) : Rng (i + 1) j (P.erase (i, j)) := by
  intro q hq
  obtain ⟨hne, hq⟩ := Finset.mem_erase.mp hq
  have := hr q hq; have := hP.lt hq
  have := hP.disjoint q hq (i, j) hij hne
  dsimp only at this; omega

private theorem exteriorBranches_closed {P : Finset (ℕ × ℕ)} {i j : ℕ}
    (hP : IsStructure pair m s P) (hr : Rng i (j + 1) P) (hij : (i, j) ∈ P) :
    exteriorBranches P = {(i, j)} := by
  conv_lhs => rw [← Finset.insert_erase hij]
  exact exteriorBranches_insert (erase_rng hP hr hij)

private theorem unp_closed {P : Finset (ℕ × ℕ)} {i j : ℕ}
    (hP : IsStructure pair m s P) (hr : Rng i (j + 1) P) (hij : (i, j) ∈ P) :
    unp i (j + 1) P = 0 := by
  classical
  unfold unp
  rw [exteriorBranches_closed hP hr hij, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx h
  rw [Finset.mem_Ico] at hx
  exact h (i, j) (Finset.mem_singleton_self _) ⟨hx.1, by dsimp only; omega⟩

private theorem pairwiseDisjoint_exterior {Q : Finset (ℕ × ℕ)} (hQ : IsStructure pair m s Q) :
    (↑(exteriorBranches Q) : Set (ℕ × ℕ)).PairwiseDisjoint fun q => Finset.Icc q.1 q.2 := by
  intro q hq q' hq' hne
  simp only [Finset.coe_filter, exteriorBranches, Set.mem_ofPred_eq] at hq hq'
  refine Finset.disjoint_left.mpr fun x hx hx' => ?_
  rw [Finset.mem_Icc] at hx hx'
  have h1 := hQ.disjoint q hq.1 q' hq'.1 hne
  have h2 := hQ.noncrossing q hq.1 q' hq'.1
  have h3 := hQ.noncrossing q' hq'.1 q hq.1
  have h4 := hq.2 q' hq'.1
  have h5 := hq'.2 q hq.1
  have := hQ.lt hq.1; have := hQ.lt hq'.1
  unfold Encloses at h4 h5
  omega

private theorem sum_span_add_unp {Q : Finset (ℕ × ℕ)} {lo hi : ℕ}
    (hQ : IsStructure pair m s Q) (hr : Rng lo hi Q) :
    ∑ q ∈ exteriorBranches Q, (q.2 - q.1 + 1) + unp lo hi Q = hi - lo := by
  classical
  set C := (exteriorBranches Q).biUnion fun q => Finset.Icc q.1 q.2 with hC
  have hcard : C.card = ∑ q ∈ exteriorBranches Q, (q.2 - q.1 + 1) := by
    rw [hC, Finset.card_biUnion (pairwiseDisjoint_exterior hQ)]
    refine Finset.sum_congr rfl fun q hq => ?_
    have := hQ.lt (exteriorBranches_subset _ hq)
    rw [Nat.card_Icc]; omega
  have hsub : C ⊆ Finset.Ico lo hi := by
    intro x hx
    simp only [hC, Finset.mem_biUnion, Finset.mem_Icc] at hx
    obtain ⟨q, hq, hx⟩ := hx
    have := hr q (exteriorBranches_subset _ hq)
    rw [Finset.mem_Ico]; omega
  have hunp : unp lo hi Q = (Finset.Ico lo hi \ C).card := by
    unfold unp
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_sdiff, hC, Finset.mem_biUnion, Finset.mem_Icc,
      not_exists, not_and]
  rw [← hcard, hunp, add_comm, Finset.card_sdiff_add_card_eq_card hsub, Nat.card_Ico]

end Unpaired

section Costs

variable {pair m s}

private theorem le_add_inf {ι : Type*} {T : Finset ι} {g : ι → WithTop ℝ} {X c : WithTop ℝ}
    (h : ∀ Q ∈ T, X ≤ c + g Q) : X ≤ c + T.inf g := by
  rcases T.eq_empty_or_nonempty with rfl | hT
  · simp
  · obtain ⟨Q, hQ, he⟩ := Finset.exists_mem_eq_inf T hT g
    rw [he]; exact h Q hQ

private theorem le_inf_add {ι : Type*} {T : Finset ι} {g : ι → WithTop ℝ} {X c : WithTop ℝ}
    (h : ∀ Q ∈ T, X ≤ g Q + c) : X ≤ T.inf g + c := by
  rw [add_comm]; exact le_add_inf fun Q hQ => by rw [add_comm]; exact h Q hQ

private theorem le_inf_add_inf {ι κ : Type*} {T₁ : Finset ι} {T₂ : Finset κ}
    {g₁ : ι → WithTop ℝ} {g₂ : κ → WithTop ℝ} {X : WithTop ℝ}
    (h : ∀ Q₁ ∈ T₁, ∀ Q₂ ∈ T₂, X ≤ g₁ Q₁ + g₂ Q₂) : X ≤ T₁.inf g₁ + T₂.inf g₂ := by
  rcases T₁.eq_empty_or_nonempty with rfl | hT
  · simp
  · obtain ⟨Q, hQ, he⟩ := Finset.exists_mem_eq_inf T₁ hT g₁
    rw [he]; exact le_add_inf fun Q₂ hQ₂ => h Q hQ Q₂ hQ₂

private theorem le_add_inf_add_inf {ι κ : Type*} {T₁ : Finset ι} {T₂ : Finset κ}
    {g₁ : ι → WithTop ℝ} {g₂ : κ → WithTop ℝ} {X c : WithTop ℝ}
    (h : ∀ Q₁ ∈ T₁, ∀ Q₂ ∈ T₂, X ≤ c + g₁ Q₁ + g₂ Q₂) : X ≤ c + T₁.inf g₁ + T₂.inf g₂ := by
  rcases T₁.eq_empty_or_nonempty with rfl | hT
  · simp
  · obtain ⟨Q, hQ, he⟩ := Finset.exists_mem_eq_inf T₁ hT g₁
    rw [he]; exact le_add_inf fun Q₂ hQ₂ => h Q hQ Q₂ hQ₂

/-- The cost of a multiloop fragment on `[lo, hi)`: `b` per exterior branch, `c` per
uncovered position, plus the free energy. -/
private noncomputable def fragCost (E : LoopEnergy) (lo hi : ℕ) (P : Finset (ℕ × ℕ)) : ℝ :=
  E.multiB * (exteriorBranches P).card + E.multiC * (unp lo hi P : ℝ) + freeEnergy E P

private theorem fragCost_union (E : LoopEnergy) {P₁ P₂ : Finset (ℕ × ℕ)} {lo u hi : ℕ}
    (h₁ : IsStructure pair m s P₁) (h₂ : IsStructure pair m s P₂)
    (r₁ : Rng lo u P₁) (r₂ : Rng u hi P₂) (hlo : lo ≤ u) (hhi : u ≤ hi) :
    fragCost E lo hi (P₁ ∪ P₂) = fragCost E lo u P₁ + fragCost E u hi P₂ := by
  have hd : Disjoint (exteriorBranches P₁) (exteriorBranches P₂) :=
    Finset.disjoint_of_subset_left (exteriorBranches_subset _)
      (Finset.disjoint_of_subset_right (exteriorBranches_subset _) (disjoint_of_rng r₁ r₂ h₁))
  unfold fragCost
  rw [exteriorBranches_union h₁ h₂ r₁ r₂, Finset.card_union_of_disjoint hd,
    unp_union h₁ h₂ r₁ r₂ hlo hhi, freeEnergy_union E h₁ h₂ r₁ r₂]
  push_cast; ring

private theorem fragCost_empty (E : LoopEnergy) (lo hi : ℕ) :
    fragCost E lo hi ∅ = E.multiC * ((hi - lo : ℕ) : ℝ) := by
  simp [fragCost, unp_empty, exteriorBranches, freeEnergy]

private theorem fragCost_closed (E : LoopEnergy) {P : Finset (ℕ × ℕ)} {i j : ℕ}
    (hP : IsStructure pair m s P) (hr : Rng i (j + 1) P) (hij : (i, j) ∈ P) :
    fragCost E i (j + 1) P = E.multiB + freeEnergy E P := by
  simp [fragCost, exteriorBranches_closed hP hr hij, unp_closed hP hr hij]

private theorem freeEnergy_hairpin (E : LoopEnergy) (i j : ℕ) :
    freeEnergy E {(i, j)} = E.hairpin i j := by
  have hb : branches {(i, j)} (i, j) = ∅ := by
    ext q
    simp only [branches, Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
    rintro ⟨rfl, h, -⟩
    exact absurd h.1 (lt_irrefl _)
  simp [freeEnergy, loopEnergy_eq_hairpin E hb]

private theorem freeEnergy_interior (E : LoopEnergy) {Q : Finset (ℕ × ℕ)} {i j k l : ℕ}
    (hQ : IsStructure pair m s Q) (hr : Rng k (l + 1) Q) (hkl : (k, l) ∈ Q)
    (hik : i < k) (hlj : l < j) :
    freeEnergy E (insert (i, j) Q) = E.interior i j k l + freeEnergy E Q := by
  have hr' : Rng (i + 1) j Q := hr.mono (by omega) (by omega)
  rw [freeEnergy_insert E hr',
    loopEnergy_eq_interior E ((branches_insert hr').trans (exteriorBranches_closed hQ hr hkl))]

private theorem freeEnergy_multi (E : LoopEnergy) {Q₁ Q₂ : Finset (ℕ × ℕ)} {i u j : ℕ}
    (h₁ : IsStructure pair m s Q₁) (h₂ : IsStructure pair m s Q₂)
    (r₁ : Rng (i + 1) u Q₁) (r₂ : Rng u j Q₂) (n₁ : Q₁.Nonempty) (n₂ : Q₂.Nonempty)
    (hiu : i + 1 ≤ u) (huj : u ≤ j) :
    freeEnergy E (insert (i, j) (Q₁ ∪ Q₂)) =
      E.multiA + fragCost E (i + 1) u Q₁ + fragCost E u j Q₂ := by
  have hQ := h₁.union h₂ r₁ r₂
  have hr : Rng (i + 1) j (Q₁ ∪ Q₂) := (r₁.mono le_rfl huj).union (r₂.mono hiu le_rfl)
  have hd : Disjoint (exteriorBranches Q₁) (exteriorBranches Q₂) :=
    Finset.disjoint_of_subset_left (exteriorBranches_subset _)
      (Finset.disjoint_of_subset_right (exteriorBranches_subset _) (disjoint_of_rng r₁ r₂ h₁))
  have hcard : (branches (insert (i, j) (Q₁ ∪ Q₂)) (i, j)).card =
      (exteriorBranches Q₁).card + (exteriorBranches Q₂).card := by
    rw [branches_insert hr, exteriorBranches_union h₁ h₂ r₁ r₂, Finset.card_union_of_disjoint hd]
  have c₁ := (exteriorBranches_nonempty n₁).card_pos
  have c₂ := (exteriorBranches_nonempty n₂).card_pos
  have hspan := sum_span_add_unp hQ hr
  rw [freeEnergy_insert E hr, loopEnergy_eq_multiloop E (by omega), hcard,
    branches_insert hr, freeEnergy_union E h₁ h₂ r₁ r₂]
  have hu : (j - i - 1 - ∑ q ∈ exteriorBranches (Q₁ ∪ Q₂), (q.2 - q.1 + 1) : ℕ) =
      unp (i + 1) u Q₁ + unp u j Q₂ := by
    rw [← unp_union h₁ h₂ r₁ r₂ hiu huj]; omega
  rw [hu]
  unfold fragCost
  push_cast; ring

private theorem split_union (P : Finset (ℕ × ℕ)) (u : ℕ) (h : ∀ q ∈ P, q.2 < u ∨ u ≤ q.1) :
    P = P.filter (fun q => q.2 < u) ∪ P.filter (fun q => u ≤ q.1) := by
  ext q
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · intro hq; rcases h q hq with h' | h'
    · exact Or.inl ⟨hq, h'⟩
    · exact Or.inr ⟨hq, h'⟩
  · rintro (⟨hq, -⟩ | ⟨hq, -⟩) <;> exact hq

private theorem rng_filter_left {P : Finset (ℕ × ℕ)} {lo hi : ℕ} (u : ℕ) (hr : Rng lo hi P) :
    Rng lo u (P.filter fun q => q.2 < u) := fun q hq => by
  rw [Finset.mem_filter] at hq; exact ⟨(hr q hq.1).1, hq.2⟩

private theorem rng_filter_right {P : Finset (ℕ × ℕ)} {lo hi : ℕ} (u : ℕ) (hr : Rng lo hi P) :
    Rng u hi (P.filter fun q => u ≤ q.1) := fun q hq => by
  rw [Finset.mem_filter] at hq; exact ⟨hq.2, (hr q hq.1).2⟩

private theorem rng_insert {Q : Finset (ℕ × ℕ)} {i j hi : ℕ} (hr : Rng (i + 1) j Q)
    (hj : j < hi) : Rng i hi (insert (i, j) Q) := fun q hq => by
  rcases Finset.mem_insert.mp hq with rfl | hq
  · exact ⟨le_rfl, hj⟩
  · have := hr q hq; omega

private theorem fragCost_unpaired_right (E : LoopEnergy) {P : Finset (ℕ × ℕ)} {lo j : ℕ}
    (hP : IsStructure pair m s P) (hr : Rng lo j P) (hlo : lo ≤ j) :
    fragCost E lo (j + 1) P = fragCost E lo j P + E.multiC := by
  have := fragCost_union E hP isStructure_empty hr (rng_empty j (j + 1)) hlo (by omega)
  rw [Finset.union_empty] at this
  rw [this, fragCost_empty, show j + 1 - j = 1 by omega]
  simp

private theorem fragCost_unpaired_left (E : LoopEnergy) {P : Finset (ℕ × ℕ)} {i hi : ℕ}
    (hP : IsStructure pair m s P) (hr : Rng (i + 1) hi P) (hhi : i + 1 ≤ hi) :
    fragCost E i hi P = E.multiC + fragCost E (i + 1) hi P := by
  have := fragCost_union E isStructure_empty hP (rng_empty i (i + 1)) hr (by omega) hhi
  rw [Finset.empty_union] at this
  rw [this, fragCost_empty, show i + 1 - i = 1 by omega]
  simp

end Costs

section IntervalSets

open Classical in
/-- Structures on `[i, i + len)` closed by the pair `(i, i + len - 1)`. -/
private noncomputable def SV (i len : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (structuresIn pair m s i len).filter fun P => (i, i + len - 1) ∈ P

open Classical in
/-- Nonempty structures on `[i, i + len)`. -/
private noncomputable def SW (i len : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (structuresIn pair m s i len).filter fun P => P.Nonempty

variable {pair m s}

private theorem mem_SV {i len : ℕ} {P : Finset (ℕ × ℕ)} :
    P ∈ SV pair m s i len ↔
      IsStructure pair m s P ∧ Rng i (i + len) P ∧ (i, i + len - 1) ∈ P := by
  classical
  simp only [SV, Finset.mem_filter, mem_structuresIn, and_assoc]

private theorem mem_SW {i len : ℕ} {P : Finset (ℕ × ℕ)} :
    P ∈ SW pair m s i len ↔ IsStructure pair m s P ∧ Rng i (i + len) P ∧ P.Nonempty := by
  classical
  simp only [SW, Finset.mem_filter, mem_structuresIn, and_assoc]

end IntervalSets

variable [DecidableRel pair]

/-- **Zuker's recursion** on the interval `[i, i + len)`, with `j = i + len - 1`, returning
`(V, WM)`:
* `V = ⊤` unless `(i, j)` can close a loop (`i + m < j`, `CanPair pair s i j`); otherwise `V` is
  the least of the hairpin energy `hairpin i j`, the interior-loop energies
  `interior i j k l + V(k, l)` over `i < k < l < j`, and the multiloop energies
  `a + WM(i + 1, u) + WM(u + 1, j - 1)` over `i < u < j - 1`;
* `WM` (a multiloop fragment with at least one branch, charging `b` per branch and `c` per
  unpaired base) is the least of `V + b`, `WM(i + 1, j) + c` (base `i` unpaired),
  `WM(i, j - 1) + c` (base `j` unpaired) and `WM(i, u) + WM(u + 1, j)` over `i ≤ u < j`.
Intervals are written by start and length. -/
noncomputable def zukerVW (E : LoopEnergy) : ℕ → ℕ → WithTop ℝ × WithTop ℝ
  | i, len =>
    let j := i + len - 1
    let V : WithTop ℝ :=
      if i + m < j ∧ CanPair pair s i j then
        min (E.hairpin i j : WithTop ℝ)
          (min
            (Finset.univ.inf fun a : Fin len => Finset.univ.inf fun b : Fin len =>
              if 1 ≤ a.val ∧ a.val + b.val < len ∧ 1 ≤ b.val then
                (E.interior i j (i + a.val) (i + a.val + b.val - 1) : WithTop ℝ) +
                  (zukerVW E (i + a.val) b.val).1
              else ⊤)
            (Finset.univ.inf fun a : Fin len =>
              if 1 ≤ a.val ∧ a.val + 2 < len then
                (E.multiA : WithTop ℝ) + (zukerVW E (i + 1) a.val).2 +
                  (zukerVW E (i + a.val + 1) (len - a.val - 2)).2
              else ⊤))
      else ⊤
    let WM : WithTop ℝ :=
      if len = 0 then ⊤
      else
        min (V + (E.multiB : WithTop ℝ))
          (min ((zukerVW E (i + 1) (len - 1)).2 + (E.multiC : WithTop ℝ))
            (min ((zukerVW E i (len - 1)).2 + (E.multiC : WithTop ℝ))
              (Finset.univ.inf fun a : Fin len =>
                if 1 ≤ a.val then (zukerVW E i a.val).2 + (zukerVW E (i + a.val) (len - a.val)).2
                else ⊤)))
    (V, WM)
  termination_by _ len => len
  decreasing_by all_goals omega

/-- The exterior-loop recursion on the prefix `[0, len)`: `W(0) = 0` and
`W(len + 1) = min (W(len), min_{i ≤ len} W(i) + V(i, len + 1 - i))` (the last base is unpaired,
or closes an exterior branch `(i, len)`). -/
noncomputable def zukerExterior (E : LoopEnergy) : ℕ → WithTop ℝ
  | 0 => 0
  | len + 1 =>
    min (zukerExterior E len)
      (Finset.univ.inf fun i : Fin (len + 1) =>
        zukerExterior E i.val + (zukerVW pair m s E i.val (len + 1 - i.val)).1)
  termination_by len => len
  decreasing_by all_goals omega

/-- Zuker's minimum free energy of `s`: the exterior recursion on the whole sequence. -/
noncomputable def zukerMFE (E : LoopEnergy) : WithTop ℝ :=
  zukerExterior pair m s E s.length

section Unfolding

variable {pair m s}

private theorem zukerVW_fst (E : LoopEnergy) (i len : ℕ) :
    (zukerVW pair m s E i len).1 =
      if i + m < i + len - 1 ∧ CanPair pair s i (i + len - 1) then
        min (E.hairpin i (i + len - 1) : WithTop ℝ)
          (min
            (Finset.univ.inf fun a : Fin len => Finset.univ.inf fun b : Fin len =>
              if 1 ≤ a.val ∧ a.val + b.val < len ∧ 1 ≤ b.val then
                (E.interior i (i + len - 1) (i + a.val) (i + a.val + b.val - 1) : WithTop ℝ) +
                  (zukerVW pair m s E (i + a.val) b.val).1
              else ⊤)
            (Finset.univ.inf fun a : Fin len =>
              if 1 ≤ a.val ∧ a.val + 2 < len then
                (E.multiA : WithTop ℝ) + (zukerVW pair m s E (i + 1) a.val).2 +
                  (zukerVW pair m s E (i + a.val + 1) (len - a.val - 2)).2
              else ⊤))
      else ⊤ := by
  rw [zukerVW]

private theorem zukerVW_snd (E : LoopEnergy) (i len : ℕ) :
    (zukerVW pair m s E i len).2 =
      if len = 0 then ⊤
      else
        min ((zukerVW pair m s E i len).1 + (E.multiB : WithTop ℝ))
          (min ((zukerVW pair m s E (i + 1) (len - 1)).2 + (E.multiC : WithTop ℝ))
            (min ((zukerVW pair m s E i (len - 1)).2 + (E.multiC : WithTop ℝ))
              (Finset.univ.inf fun a : Fin len =>
                if 1 ≤ a.val then
                  (zukerVW pair m s E i a.val).2 + (zukerVW pair m s E (i + a.val) (len - a.val)).2
                else ⊤))) := by
  conv_lhs => rw [zukerVW]
  conv_rhs => rw [zukerVW]

private theorem zukerExterior_zero (E : LoopEnergy) : zukerExterior pair m s E 0 = 0 := by
  rw [zukerExterior]

private theorem zukerExterior_succ (E : LoopEnergy) (len : ℕ) :
    zukerExterior pair m s E (len + 1) =
      min (zukerExterior pair m s E len)
        (Finset.univ.inf fun i : Fin (len + 1) =>
          zukerExterior pair m s E i.val + (zukerVW pair m s E i.val (len + 1 - i.val)).1) := by
  rw [zukerExterior]

end Unfolding

section Intervals

variable {pair m s}

/-- The joint characterization of `V` and `WM` on intervals of length `len`. -/
private def Char (E : LoopEnergy) (len : ℕ) : Prop :=
  ∀ i, (zukerVW pair m s E i len).1 =
      (SV pair m s i len).inf (fun P => ((freeEnergy E P : ℝ) : WithTop ℝ)) ∧
    (zukerVW pair m s E i len).2 =
      (SW pair m s i len).inf (fun P => ((fragCost E i (i + len) P : ℝ) : WithTop ℝ))

private theorem V_step (E : LoopEnergy) (len i : ℕ)
    (ih : ∀ len' < len, Char (pair := pair) (m := m) (s := s) E len') :
    (zukerVW pair m s E i len).1 =
      (SV pair m s i len).inf (fun P => ((freeEnergy E P : ℝ) : WithTop ℝ)) := by
  rw [zukerVW_fst]
  apply le_antisymm
  · refine Finset.le_inf fun P hP => ?_
    obtain ⟨hPs, hPr, hij⟩ := mem_SV.mp hP
    have hlt := hPs.loop _ hij
    have hcp : CanPair pair s i (i + len - 1) := hPs.compl _ hij
    dsimp only at hlt
    rw [ite_eq_left ⟨hlt, hcp⟩]
    set j := i + len - 1 with hj
    have hlen : i + len = j + 1 := by omega
    have hr : Rng i (j + 1) P := hlen ▸ hPr
    have hQs : IsStructure pair m s (P.erase (i, j)) := hPs.mono (Finset.erase_subset _ _)
    have hQr : Rng (i + 1) j (P.erase (i, j)) := erase_rng hPs hr hij
    have hPQ : P = insert (i, j) (P.erase (i, j)) := (Finset.insert_erase hij).symm
    generalize P.erase (i, j) = Q at hQs hQr hPQ
    subst hPQ
    rcases (exteriorBranches Q).eq_empty_or_nonempty with he | hne
    · have hQe : Q = ∅ := by
        by_contra h
        exact (exteriorBranches_nonempty (Finset.nonempty_iff_ne_empty.mpr h)).ne_empty he
      subst hQe
      have : freeEnergy E (insert (i, j) ∅) = E.hairpin i j := by
        simpa using freeEnergy_hairpin E i j
      rw [this]; exact min_le_left _ _
    by_cases h1 : (exteriorBranches Q).card = 1
    · obtain ⟨⟨k, l⟩, hkl⟩ := Finset.card_eq_one.mp h1
      have hklQ : (k, l) ∈ Q := exteriorBranches_subset _ (hkl ▸ Finset.mem_singleton_self _)
      have hQr' : Rng k (l + 1) Q := by
        intro q hq
        obtain ⟨e, he, heq⟩ := exists_exterior_cover q hq
        rw [hkl, Finset.mem_singleton] at he
        subst he
        rcases heq with rfl | henc
        · dsimp only; omega
        · unfold Encloses at henc; dsimp only at henc ⊢; omega
      have hkl' := hQr _ hklQ
      have hkl2 := hQs.lt hklQ
      dsimp only at hkl' hkl2
      have hFE : freeEnergy E (insert (i, j) Q) = E.interior i j k l + freeEnergy E Q :=
        freeEnergy_interior E hQs hQr' hklQ (by omega) (by omega)
      have hlt' : l - k + 1 < len := by omega
      have hVkl := ((ih (l - k + 1) hlt') k).1
      have hmem : Q ∈ SV pair m s k (l - k + 1) := by
        refine mem_SV.mpr ⟨hQs, ?_, ?_⟩
        · rwa [show k + (l - k + 1) = l + 1 by omega]
        · rwa [show k + (l - k + 1) - 1 = l by omega]
      refine (min_le_right _ _).trans ((min_le_left _ _).trans ?_)
      refine (Finset.inf_le (Finset.mem_univ (⟨k - i, by omega⟩ : Fin len))).trans
        ((Finset.inf_le (Finset.mem_univ (⟨l - k + 1, hlt'⟩ : Fin len))).trans ?_)
      dsimp only
      rw [ite_eq_left (by omega), show i + (k - i) = k by omega,
        show k + (l - k + 1) - 1 = l by omega, hVkl, hFE, WithTop.coe_add]
      gcongr
      exact Finset.inf_le hmem
    · have h2 : 2 ≤ (exteriorBranches Q).card := by have := hne.card_pos; omega
      obtain ⟨⟨k, l⟩, hklE, hmin⟩ :=
        Finset.exists_min_image (exteriorBranches Q) (fun q => q.1) hne
      have hklQ := exteriorBranches_subset _ hklE
      have hext : ∀ r ∈ Q, ¬ Encloses r (k, l) := (Finset.mem_filter.mp hklE).2
      have hkl' := hQr _ hklQ
      have hkl2 := hQs.lt hklQ
      dsimp only at hkl' hkl2
      have hsplit : ∀ q ∈ Q, q.2 < l + 1 ∨ l + 1 ≤ q.1 := by
        intro q hq
        by_contra hc
        push Not at hc
        have hne' : q ≠ (k, l) := by rintro rfl; dsimp only at hc; omega
        have hd := hQs.disjoint q hq _ hklQ hne'
        have hc1 := hQs.noncrossing _ hklQ q hq
        have he := hext q hq
        have := hQs.lt hq
        unfold Encloses at he; dsimp only at hd hc1 he; omega
      have hQ12 := split_union Q (l + 1) hsplit
      have r₁ : Rng (i + 1) (l + 1) (Q.filter fun q => q.2 < l + 1) := rng_filter_left _ hQr
      have r₂ : Rng (l + 1) j (Q.filter fun q => l + 1 ≤ q.1) := rng_filter_right _ hQr
      have s₁ := hQs.mono (Finset.filter_subset (fun q : ℕ × ℕ => q.2 < l + 1) Q)
      have s₂ := hQs.mono (Finset.filter_subset (fun q : ℕ × ℕ => l + 1 ≤ q.1) Q)
      have n₁ : (Q.filter fun q => q.2 < l + 1).Nonempty :=
        ⟨(k, l), Finset.mem_filter.mpr ⟨hklQ, by dsimp only; omega⟩⟩
      obtain ⟨e, he, hne'⟩ :=
        Finset.exists_mem_ne (show 1 < (exteriorBranches Q).card by omega) (k, l)
      have heQ := exteriorBranches_subset _ he
      have he1 : l + 1 ≤ e.1 := by
        have := hmin e he
        have hd := hQs.disjoint e heQ _ hklQ hne'
        have hc1 := hQs.noncrossing _ hklQ e heQ
        have hx := (Finset.mem_filter.mp he).2 _ hklQ
        have := hQs.lt heQ
        have := hQr e heQ
        unfold Encloses at hx; dsimp only at hd hc1 hx this ⊢; omega
      have n₂ : (Q.filter fun q => l + 1 ≤ q.1).Nonempty :=
        ⟨e, Finset.mem_filter.mpr ⟨heQ, he1⟩⟩
      have hej := hQr e heQ
      have hej2 := hQs.lt heQ
      have hFE := freeEnergy_multi E s₁ s₂ r₁ r₂ n₁ n₂ (by omega) (by omega)
      rw [← hQ12] at hFE
      refine (min_le_right _ _).trans ((min_le_right _ _).trans ?_)
      refine (Finset.inf_le (Finset.mem_univ (⟨l - i, by omega⟩ : Fin len))).trans ?_
      dsimp only
      rw [ite_eq_left (by omega), ((ih (l - i) (by omega)) (i + 1)).2,
        ((ih (len - (l - i) - 2) (by omega)) (i + (l - i) + 1)).2, hFE,
        show i + (l - i) + 1 = l + 1 by omega, show i + 1 + (l - i) = l + 1 by omega,
        show l + 1 + (len - (l - i) - 2) = j by omega, WithTop.coe_add, WithTop.coe_add]
      gcongr
      · refine Finset.inf_le (mem_SW.mpr ⟨s₁, ?_, n₁⟩)
        rwa [show i + 1 + (l - i) = l + 1 by omega]
      · refine Finset.inf_le (mem_SW.mpr ⟨s₂, ?_, n₂⟩)
        rwa [show l + 1 + (len - (l - i) - 2) = j by omega]
  · split_ifs with hc
    · obtain ⟨hlt, hcp⟩ := hc
      set j := i + len - 1 with hj
      have hlen : i + len = j + 1 := by omega
      refine le_min ?_ (le_min ?_ ?_)
      · have hPs := isStructure_empty.insert (rng_empty (i + 1) j) hlt hcp
        have hmem : insert (i, j) ∅ ∈ SV pair m s i len :=
          mem_SV.mpr ⟨hPs, rng_insert (rng_empty _ _) (by omega), Finset.mem_insert_self _ _⟩
        refine (Finset.inf_le hmem).trans (le_of_eq ?_)
        simpa using freeEnergy_hairpin E i j
      · refine Finset.le_inf fun a _ => Finset.le_inf fun b _ => ?_
        split_ifs with hab
        · rw [((ih b.val (by omega)) (i + a.val)).1]
          refine le_add_inf fun Q hQ => ?_
          obtain ⟨hQs, hQr, hkl⟩ := mem_SV.mp hQ
          have hQr' : Rng (i + a.val) (i + a.val + b.val - 1 + 1) Q := by
            rwa [show i + a.val + b.val - 1 + 1 = i + a.val + b.val by omega]
          have hQr2 : Rng (i + 1) j Q := hQr'.mono (by omega) (by omega)
          have hPs := hQs.insert hQr2 hlt hcp
          have hmem : insert (i, j) Q ∈ SV pair m s i len :=
            mem_SV.mpr ⟨hPs, rng_insert hQr2 (by omega), Finset.mem_insert_self _ _⟩
          refine (Finset.inf_le hmem).trans (le_of_eq ?_)
          rw [freeEnergy_interior E hQs hQr' hkl (by omega) (by omega), WithTop.coe_add]
        · exact le_top
      · refine Finset.le_inf fun a _ => ?_
        split_ifs with ha
        · rw [((ih a.val (by omega)) (i + 1)).2,
            ((ih (len - a.val - 2) (by omega)) (i + a.val + 1)).2]
          refine le_add_inf_add_inf fun Q₁ h₁ Q₂ h₂ => ?_
          obtain ⟨s₁, r₁, n₁⟩ := mem_SW.mp h₁
          obtain ⟨s₂, r₂, n₂⟩ := mem_SW.mp h₂
          rw [show i + 1 + a.val = i + a.val + 1 by omega] at r₁ ⊢
          rw [show i + a.val + 1 + (len - a.val - 2) = j by omega] at r₂ ⊢
          have hQr : Rng (i + 1) j (Q₁ ∪ Q₂) :=
            (r₁.mono le_rfl (by omega)).union (r₂.mono (by omega) le_rfl)
          have hPs := (s₁.union s₂ r₁ r₂).insert hQr hlt hcp
          have hmem : insert (i, j) (Q₁ ∪ Q₂) ∈ SV pair m s i len :=
            mem_SV.mpr ⟨hPs, rng_insert hQr (by omega), Finset.mem_insert_self _ _⟩
          refine (Finset.inf_le hmem).trans (le_of_eq ?_)
          rw [freeEnergy_multi E s₁ s₂ r₁ r₂ n₁ n₂ (by omega) (by omega), WithTop.coe_add,
            WithTop.coe_add]
        · exact le_top
    · exact le_top

end Intervals

section Recursion

variable {pair m s}

private theorem WM_step (E : LoopEnergy) (len i : ℕ)
    (ih : ∀ len' < len, Char (pair := pair) (m := m) (s := s) E len')
    (hV : (zukerVW pair m s E i len).1 =
      (SV pair m s i len).inf (fun P => ((freeEnergy E P : ℝ) : WithTop ℝ))) :
    (zukerVW pair m s E i len).2 =
      (SW pair m s i len).inf (fun P => ((fragCost E i (i + len) P : ℝ) : WithTop ℝ)) := by
  rw [zukerVW_snd]
  split_ifs with h0
  · subst h0
    have : SW pair m s i 0 = ∅ := by
      ext P
      simp only [mem_SW, Finset.notMem_empty, iff_false]
      rintro ⟨hPs, hPr, ⟨q, hq⟩⟩
      have := hPr q hq; have := hPs.lt hq; omega
    rw [this, Finset.inf_empty]
  set j := i + len - 1 with hj
  have hlen : i + len = j + 1 := by omega
  apply le_antisymm
  · refine Finset.le_inf fun P hP => ?_
    obtain ⟨hPs, hPr, hne⟩ := mem_SW.mp hP
    have hr : Rng i (j + 1) P := hlen ▸ hPr
    by_cases hij : (i, j) ∈ P
    · refine (min_le_left _ _).trans ?_
      rw [hV, hlen, fragCost_closed E hPs hr hij, WithTop.coe_add,
        add_comm (E.multiB : WithTop ℝ)]
      gcongr
      exact Finset.inf_le (mem_SV.mpr ⟨hPs, hPr, hij⟩)
    by_cases hjf : ∀ q ∈ P, q.2 ≠ j
    · have hr' : Rng i j P := fun q hq => by
        have h1 := hr q hq; have h2 := hjf q hq; exact ⟨h1.1, by omega⟩
      refine (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_left _ _).trans ?_))
      rw [((ih (len - 1) (by omega)) i).2, hlen,
        fragCost_unpaired_right E hPs hr' (by omega), WithTop.coe_add,
        show i + (len - 1) = j by omega]
      gcongr
      refine Finset.inf_le (mem_SW.mpr ⟨hPs, ?_, hne⟩)
      rwa [show i + (len - 1) = j by omega]
    by_cases hif : ∀ q ∈ P, q.1 ≠ i
    · have hr' : Rng (i + 1) (j + 1) P := fun q hq => by
        have h1 := hr q hq; have h2 := hif q hq; exact ⟨by omega, h1.2⟩
      refine (min_le_right _ _).trans ((min_le_left _ _).trans ?_)
      rw [((ih (len - 1) (by omega)) (i + 1)).2, hlen,
        fragCost_unpaired_left E hPs hr' (by omega), WithTop.coe_add,
        show i + 1 + (len - 1) = j + 1 by omega, add_comm (E.multiC : WithTop ℝ)]
      gcongr
      refine Finset.inf_le (mem_SW.mpr ⟨hPs, ?_, hne⟩)
      rwa [show i + 1 + (len - 1) = j + 1 by omega]
    push Not at hjf hif
    obtain ⟨⟨i', l⟩, hil, hi'⟩ := hif
    dsimp only at hi'; rw [hi'] at hil
    obtain ⟨⟨k, j'⟩, hkj, hj'⟩ := hjf
    dsimp only at hj'; rw [hj'] at hkj
    have hil2 := hr _ hil
    have hkj2 := hr _ hkj
    have hilt := hPs.lt hil
    have hklt := hPs.lt hkj
    dsimp only at hil2 hkj2 hilt hklt
    have hlj : l ≠ j := by rintro rfl; exact hij hil
    have hd := hPs.disjoint _ hil _ hkj (by intro h; simp only [Prod.ext_iff] at h; omega)
    have hnc := hPs.noncrossing _ hil _ hkj
    dsimp only at hd hnc
    have hsplit : ∀ q ∈ P, q.2 < l + 1 ∨ l + 1 ≤ q.1 := by
      intro q hq
      by_contra hc
      push Not at hc
      have hne' : q ≠ (i, l) := by rintro rfl; dsimp only at hc; omega
      have h1 := hPs.disjoint q hq _ hil hne'
      have h2 := hPs.noncrossing _ hil q hq
      have := hr q hq; have := hPs.lt hq
      dsimp only at h1 h2 this; omega
    have hP12 := split_union P (l + 1) hsplit
    have r₁ : Rng i (l + 1) (P.filter fun q => q.2 < l + 1) := rng_filter_left _ hr
    have r₂ : Rng (l + 1) (j + 1) (P.filter fun q => l + 1 ≤ q.1) := rng_filter_right _ hr
    have s₁ := hPs.mono (Finset.filter_subset (fun q : ℕ × ℕ => q.2 < l + 1) P)
    have s₂ := hPs.mono (Finset.filter_subset (fun q : ℕ × ℕ => l + 1 ≤ q.1) P)
    have n₁ : (P.filter fun q => q.2 < l + 1).Nonempty :=
      ⟨(i, l), Finset.mem_filter.mpr ⟨hil, by dsimp only; omega⟩⟩
    have n₂ : (P.filter fun q => l + 1 ≤ q.1).Nonempty :=
      ⟨(k, j), Finset.mem_filter.mpr ⟨hkj, by dsimp only; omega⟩⟩
    refine (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ?_))
    refine (Finset.inf_le (Finset.mem_univ (⟨l - i + 1, by omega⟩ : Fin len))).trans ?_
    dsimp only
    rw [ite_eq_left (by omega), ((ih (l - i + 1) (by omega)) i).2,
      ((ih (len - (l - i + 1)) (by omega)) (i + (l - i + 1))).2,
      show i + (l - i + 1) = l + 1 by omega, show l + 1 + (len - (l - i + 1)) = j + 1 by omega,
      hlen, hP12, fragCost_union E s₁ s₂ r₁ r₂ (by omega) (by omega), WithTop.coe_add]
    gcongr
    · exact Finset.inf_le (mem_SW.mpr ⟨s₁, by rwa [show i + (l - i + 1) = l + 1 by omega], n₁⟩)
    · refine Finset.inf_le (mem_SW.mpr ⟨s₂, ?_, n₂⟩)
      rwa [show l + 1 + (len - (l - i + 1)) = j + 1 by omega]
  · refine le_min ?_ (le_min ?_ (le_min ?_ ?_))
    · rw [hV]
      refine le_inf_add fun P hP => ?_
      obtain ⟨hPs, hPr, hij⟩ := mem_SV.mp hP
      have hr : Rng i (j + 1) P := hlen ▸ hPr
      refine (Finset.inf_le (mem_SW.mpr ⟨hPs, hPr, ⟨_, hij⟩⟩)).trans (le_of_eq ?_)
      rw [hlen, fragCost_closed E hPs hr hij, WithTop.coe_add, add_comm]
    · rw [((ih (len - 1) (by omega)) (i + 1)).2]
      refine le_inf_add fun P hP => ?_
      obtain ⟨hPs, hPr, hne⟩ := mem_SW.mp hP
      rw [show i + 1 + (len - 1) = j + 1 by omega] at hPr ⊢
      refine (Finset.inf_le (mem_SW.mpr ⟨hPs, hlen ▸ hPr.mono (by omega) le_rfl, hne⟩)).trans
        (le_of_eq ?_)
      rw [hlen, fragCost_unpaired_left E hPs hPr (by omega), WithTop.coe_add, add_comm]
    · rw [((ih (len - 1) (by omega)) i).2]
      refine le_inf_add fun P hP => ?_
      obtain ⟨hPs, hPr, hne⟩ := mem_SW.mp hP
      rw [show i + (len - 1) = j by omega] at hPr ⊢
      refine (Finset.inf_le (mem_SW.mpr ⟨hPs, hlen ▸ hPr.mono le_rfl (by omega), hne⟩)).trans
        (le_of_eq ?_)
      rw [hlen, fragCost_unpaired_right E hPs hPr (by omega), WithTop.coe_add]
    · refine Finset.le_inf fun a _ => ?_
      split_ifs with ha
      · rw [((ih a.val (by omega)) i).2, ((ih (len - a.val) (by omega)) (i + a.val)).2]
        refine le_inf_add_inf fun P₁ h₁ P₂ h₂ => ?_
        obtain ⟨s₁, r₁, n₁⟩ := mem_SW.mp h₁
        obtain ⟨s₂, r₂, n₂⟩ := mem_SW.mp h₂
        rw [show i + a.val + (len - a.val) = i + len by omega] at r₂ ⊢
        have hmem : P₁ ∪ P₂ ∈ SW pair m s i len :=
          mem_SW.mpr ⟨s₁.union s₂ r₁ r₂,
            (r₁.mono le_rfl (by omega)).union (r₂.mono (by omega) le_rfl),
            n₁.mono Finset.subset_union_left⟩
        refine (Finset.inf_le hmem).trans (le_of_eq ?_)
        rw [fragCost_union E s₁ s₂ r₁ r₂ (by omega) (by omega), WithTop.coe_add]
      · exact le_top

private theorem char (E : LoopEnergy) (len : ℕ) : Char (pair := pair) (m := m) (s := s) E len := by
  induction len using Nat.strong_induction_on with
  | _ len ih =>
    intro i
    have hV := V_step E len i ih
    exact ⟨hV, WM_step E len i ih hV⟩

private theorem exterior_char (E : LoopEnergy) (len : ℕ) :
    zukerExterior pair m s E len =
      (structuresIn pair m s 0 len).inf (fun P => ((freeEnergy E P : ℝ) : WithTop ℝ)) := by
  induction len using Nat.strong_induction_on with
  | _ len ih =>
    rcases len with _ | len
    · rw [zukerExterior_zero, structuresIn_zero, Finset.inf_singleton]
      simp [freeEnergy]
    rw [zukerExterior_succ]
    apply le_antisymm
    · refine Finset.le_inf fun P hP => ?_
      obtain ⟨hPs, hPr⟩ := mem_structuresIn.mp hP
      by_cases hl : ∀ q ∈ P, q.2 ≠ len
      · refine (min_le_left _ _).trans ?_
        rw [ih len (by omega)]
        refine Finset.inf_le (mem_structuresIn.mpr ⟨hPs, fun q hq => ?_⟩)
        have := hPr q hq; have := hl q hq; omega
      push Not at hl
      obtain ⟨⟨i, l⟩, hil, hl'⟩ := hl
      dsimp only at hl'; subst hl'
      have hil2 := hPr _ hil
      have hilt := hPs.lt hil
      dsimp only at hil2 hilt
      have hsplit : ∀ q ∈ P, q.2 < i ∨ i ≤ q.1 := by
        intro q hq
        by_contra hc
        push Not at hc
        have hne' : q ≠ (i, l) := by rintro rfl; dsimp only at hc; omega
        have h1 := hPs.disjoint q hq _ hil hne'
        have h2 := hPs.noncrossing q hq _ hil
        have := hPr q hq; have := hPs.lt hq
        dsimp only at h1 h2 this; omega
      have hP12 := split_union P i hsplit
      have r₁ : Rng 0 i (P.filter fun q => q.2 < i) := rng_filter_left _ hPr
      have r₂ : Rng i (0 + (l + 1)) (P.filter fun q => i ≤ q.1) := rng_filter_right _ hPr
      have s₁ := hPs.mono (Finset.filter_subset (fun q : ℕ × ℕ => q.2 < i) P)
      have s₂ := hPs.mono (Finset.filter_subset (fun q : ℕ × ℕ => i ≤ q.1) P)
      refine (min_le_right _ _).trans ?_
      refine (Finset.inf_le (Finset.mem_univ (⟨i, by omega⟩ : Fin (l + 1)))).trans ?_
      dsimp only
      rw [ih i (by omega), ((char E (l + 1 - i)) i).1, hP12,
        freeEnergy_union E s₁ s₂ r₁ r₂, WithTop.coe_add]
      gcongr
      · exact Finset.inf_le (mem_structuresIn.mpr ⟨s₁, by simpa using r₁⟩)
      · refine Finset.inf_le (mem_SV.mpr ⟨s₂, ?_, ?_⟩)
        · rwa [show i + (l + 1 - i) = 0 + (l + 1) by omega]
        · rw [show i + (l + 1 - i) - 1 = l by omega]
          exact Finset.mem_filter.mpr ⟨hil, le_rfl⟩
    · refine le_min ?_ ?_
      · rw [ih len (by omega)]
        refine Finset.inf_mono fun P hP => ?_
        obtain ⟨hPs, hPr⟩ := mem_structuresIn.mp hP
        exact mem_structuresIn.mpr ⟨hPs, hPr.mono le_rfl (by omega)⟩
      · refine Finset.le_inf fun i _ => ?_
        rw [ih i.val (by omega), ((char E (len + 1 - i.val)) i.val).1]
        refine le_inf_add_inf fun P₁ h₁ P₂ h₂ => ?_
        obtain ⟨s₁, r₁⟩ := mem_structuresIn.mp h₁
        obtain ⟨s₂, r₂, -⟩ := mem_SV.mp h₂
        rw [Nat.zero_add] at r₁
        have r₂' : Rng i.val (0 + (len + 1)) P₂ := by
          rwa [show i.val + (len + 1 - i.val) = 0 + (len + 1) by omega] at r₂
        have hmem : P₁ ∪ P₂ ∈ structuresIn pair m s 0 (len + 1) :=
          mem_structuresIn.mpr ⟨s₁.union s₂ r₁ r₂',
            (r₁.mono le_rfl (by omega)).union (r₂'.mono (by omega) le_rfl)⟩
        refine (Finset.inf_le hmem).trans (le_of_eq ?_)
        rw [freeEnergy_union E s₁ s₂ r₁ r₂', WithTop.coe_add]

end Recursion

/-- **Zuker's algorithm** (Zuker and Stiegler 1981; Zuker and Sankoff 1984), here with the affine
multiloop energy of Jaeger, Turner and Zuker (1989): the Zuker recursion computes the minimum
free energy over all secondary structures on `s` with minimum hairpin `m`, for any real loop
energies (of either sign). The minimum ranges over a finite set that contains the empty
structure, so it is never `⊤`. -/
theorem zukerMFE_eq_inf (E : LoopEnergy) :
    zukerMFE pair m s E =
      (structures pair m s).inf fun P => ((freeEnergy E P : ℝ) : WithTop ℝ) :=
  exterior_char E s.length

/-- The minimum free energy is at most `0`, the energy of the open chain (the empty
structure). -/
theorem zukerMFE_le_zero (E : LoopEnergy) : zukerMFE pair m s E ≤ 0 := by
  rw [zukerMFE_eq_inf]
  refine (Finset.inf_le ((mem_structures pair m s ∅).mpr isStructure_empty)).trans ?_
  simp [freeEnergy]

end Cslib.Bioinformatics.RNA.Zuker
