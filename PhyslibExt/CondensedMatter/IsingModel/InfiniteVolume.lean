/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Probability.Configuration.WeakConvergence
public import PhyslibExt.CondensedMatter.IsingModel.Gibbs

/-!
# Finite-volume Ising measures on ℤ^d and their infinite-volume limits

Box Gibbs measures with boundary conditions on the hypercubic lattice and their weak subsequential
limits.

## i. Overview

For a boundary condition `η`, a box `Λ_n = [-n, n]^d`, and a finite set of bonds `B`, the
finite-volume measure `fvMeasure η n B β h` is the probability measure on configurations of `ℤ^d`
that agrees with `η` outside `Λ_n` and gives the inside configuration `τ` probability proportional
to `exp (-β H(η τ))`, where `H = -∑_{e ∈ B} σ_e - h ∑_{x ∈ Λ_n} σ_x`. The plus and minus measures
use all bonds touching `Λ_n` and the constant boundary conditions `+` and `-`; the free measure uses
only bonds inside `Λ_n`.

Since the configuration space is compact, every sequence of probability measures has a weakly
convergent subsequence (Prokhorov). An *infinite-volume state* of a sequence is such a subsequential
weak limit, and `plusState`, `minusState`, `freeState` are subsequential limits selected by choice.
That the plus state is in fact the full weak limit, translation invariant, and a DLR state is proved
in other files of this directory.

## ii. Key results

- `StatMech.Ising.fvMeasure` : the finite-volume Gibbs measure with boundary condition
- `StatMech.Ising.plusMeasure` : the plus-boundary box measure
- `StatMech.Ising.InfiniteVolumeState` : subsequential weak limits
- `StatMech.Ising.exists_infiniteVolumeState` : every sequence of box measures has an
  infinite-volume state
- `StatMech.Ising.plusState` : the plus state

## iii. Table of contents

- A. Boxes and bonds
- B. Boundary conditions
- C. Finite-volume Gibbs measures
- D. Plus, minus and free measures
- E. Infinite-volume states

## iv. References

- S. Friedli and Y. Velenik, *Statistical Mechanics of Lattice Systems: A Concrete Mathematical
  Introduction*, Cambridge University Press (2017), Chapters 3 and 6
- H.-O. Georgii, *Gibbs Measures and Phase Transitions*, de Gruyter (1988; 2nd ed. 2011)
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}

/-! ## A. Boxes and bonds -/

/-- Membership in the box `Λ_n` is decidable. -/
instance instDecidableMemBox (d n : ℕ) (x : Site d) :
    Decidable (x ∈ box d n) := by
  rw [mem_box]; infer_instance

/-- Adjacency in the hypercubic lattice is decidable. -/
instance instDecidableAdj (d : ℕ) (x y : Site d) :
    Decidable ((hypercubicLattice d).Adj x y) := by
  rw [hypercubicLattice_adj]; infer_instance

/-- The box `Λ_n = [-n, n]^d` as a finite set of sites. -/
noncomputable def boxFinset (d n : ℕ) : Finset (Site d) :=
  (box_finite d n).toFinset

@[simp] lemma mem_boxFinset {d n : ℕ} {x : Site d} :
    x ∈ boxFinset d n ↔ x ∈ box d n := by
  rw [boxFinset, Set.Finite.mem_toFinset]

/-- The sites of a box form a finite type. -/
noncomputable instance instFintypeBox (d n : ℕ) : Fintype {x // x ∈ box d n} :=
  (box_finite d n).fintype

/-- Spin assignments on a box form a finite type. -/
noncomputable instance instFintypeBoxAssign (d n : ℕ) :
    Fintype ({x // x ∈ box d n} → Bool) := inferInstance

/-- Ordered nearest-neighbour pairs with at least one endpoint in `Λ_n`. -/
noncomputable def bondPairsTouch (d n : ℕ) : Finset (Site d × Site d) :=
  ((boxFinset d (n + 1)) ×ˢ (boxFinset d (n + 1))).filter
    (fun p => (hypercubicLattice d).Adj p.1 p.2 ∧ (p.1 ∈ box d n ∨ p.2 ∈ box d n))

/-- Ordered nearest-neighbour pairs with both endpoints in `Λ_n`. -/
noncomputable def bondPairsInternal (d n : ℕ) : Finset (Site d × Site d) :=
  ((boxFinset d n) ×ˢ (boxFinset d n)).filter
    (fun p => (hypercubicLattice d).Adj p.1 p.2)

/-- The bonds with at least one endpoint in `Λ_n` (used for plus and minus boundary conditions). -/
noncomputable def bondFinsetTouch (d n : ℕ) : Finset (Sym2 (Site d)) :=
  (bondPairsTouch d n).image (fun p => s(p.1, p.2))

/-- The bonds with both endpoints in `Λ_n` (used for the free boundary condition). -/
noncomputable def bondFinsetInternal (d n : ℕ) : Finset (Sym2 (Site d)) :=
  (bondPairsInternal d n).image (fun p => s(p.1, p.2))

/-! ## B. Boundary conditions -/

/-- The configuration equal to `τ` inside the box `Λ_n` and to the boundary condition `η`
outside. -/
noncomputable def glue (η : ConfigSpace (Site d)) {n : ℕ}
    (τ : {x // x ∈ box d n} → Bool) : ConfigSpace (Site d) :=
  fun x => if h : x ∈ box d n then τ ⟨x, h⟩ else η x

@[simp] lemma glue_mem (η : ConfigSpace (Site d)) {n : ℕ}
    (τ : {x // x ∈ box d n} → Bool) {x : Site d} (hx : x ∈ box d n) :
    glue η τ x = τ ⟨x, hx⟩ := by
  simp [glue, hx]

@[simp] lemma glue_not_mem (η : ConfigSpace (Site d)) {n : ℕ}
    (τ : {x // x ∈ box d n} → Bool) {x : Site d} (hx : x ∉ box d n) :
    glue η τ x = η x := by
  simp [glue, hx]

/-! ## C. Finite-volume Gibbs measures -/

/-- The box energy `-∑_{e ∈ B} σ_e - h ∑_{x ∈ Λ_n} σ_x` of the configuration `glue η τ`. -/
noncomputable def fvEnergy (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (h : ℝ) (τ : {x // x ∈ box d n} → Bool) : ℝ :=
  - (∑ e ∈ B, bond (glue η τ) e) - h * ∑ x ∈ boxFinset d n, spin (glue η τ) x

/-- The Boltzmann weight `exp (-β H)` of an inside configuration `τ` with boundary condition `η`. -/
noncomputable def fvWeight (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) (τ : {x // x ∈ box d n} → Bool) : ℝ :=
  Real.exp (-β * fvEnergy η n B h τ)

lemma fvWeight_pos (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) (τ : {x // x ∈ box d n} → Bool) :
    0 < fvWeight η n B β h τ := Real.exp_pos _

lemma fvWeight_nonneg (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) (τ : {x // x ∈ box d n} → Bool) :
    0 ≤ fvWeight η n B β h τ := (fvWeight_pos η n B β h τ).le

/-- The finite-volume partition function with boundary condition `η`. -/
noncomputable def fvZ (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) : ℝ :=
  ∑ τ : {x // x ∈ box d n} → Bool, fvWeight η n B β h τ

lemma fvZ_pos (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) : 0 < fvZ η n B β h := by
  unfold fvZ
  apply Finset.sum_pos
  · intro τ _; exact fvWeight_pos η n B β h τ
  · exact Finset.univ_nonempty

lemma fvZ_ne_zero (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) : fvZ η n B β h ≠ 0 :=
  (fvZ_pos η n B β h).ne'

/-- The finite-volume Gibbs probability of an inside configuration `τ` with boundary condition
`η`. -/
noncomputable def fvProb (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) (τ : {x // x ∈ box d n} → Bool) : ℝ :=
  fvWeight η n B β h τ / fvZ η n B β h

lemma fvProb_nonneg (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) (τ : {x // x ∈ box d n} → Bool) :
    0 ≤ fvProb η n B β h τ :=
  div_nonneg (fvWeight_nonneg η n B β h τ) (fvZ_pos η n B β h).le

lemma fvProb_sum_eq_one (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    ∑ τ : {x // x ∈ box d n} → Bool, fvProb η n B β h τ = 1 := by
  unfold fvProb
  rw [← Finset.sum_div, div_eq_one_iff_eq (fvZ_ne_zero η n B β h)]
  rfl

/-- The finite-volume Gibbs measure in `Λ_n` with boundary condition `η` and bond set `B`, as a
measure on configurations of `ℤ^d`. -/
noncomputable def fvMeasure (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    Measure (ConfigSpace (Site d)) :=
  ∑ τ : {x // x ∈ box d n} → Bool,
    ENNReal.ofReal (fvProb η n B β h τ) • Measure.dirac (glue η τ)

lemma fvMeasure_univ (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    (fvMeasure η n B β h) Set.univ = 1 := by
  unfold fvMeasure
  rw [Measure.finsetSum_apply _ _ _]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ MeasurableSet.univ, Set.mem_univ,
    Set.indicator_of_mem, Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun τ _ => fvProb_nonneg η n B β h τ),
    fvProb_sum_eq_one η n B β h, ENNReal.ofReal_one]

/-- The finite-volume Gibbs measure is a probability measure. -/
instance fvMeasure_isProbabilityMeasure (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    IsProbabilityMeasure (fvMeasure η n B β h) :=
  ⟨fvMeasure_univ η n B β h⟩

/-- The finite-volume Gibbs measure as a `ProbabilityMeasure`. -/
noncomputable def fvProbabilityMeasure (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  ⟨fvMeasure η n B β h, fvMeasure_isProbabilityMeasure η n B β h⟩

/-! ## D. Plus, minus and free measures -/

/-- The all-plus configuration. -/
def plusField (d : ℕ) : ConfigSpace (Site d) := fun _ => true

/-- The all-minus configuration. -/
def minusField (d : ℕ) : ConfigSpace (Site d) := fun _ => false

/-- The Ising measure in `Λ_n` with plus boundary condition. -/
noncomputable def plusMeasure (d n : ℕ) (β h : ℝ) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  fvProbabilityMeasure (plusField d) n (bondFinsetTouch d n) β h

/-- The Ising measure in `Λ_n` with minus boundary condition. -/
noncomputable def minusMeasure (d n : ℕ) (β h : ℝ) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  fvProbabilityMeasure (minusField d) n (bondFinsetTouch d n) β h

/-- The Ising measure in `Λ_n` with free boundary condition (internal bonds only). -/
noncomputable def freeMeasure (d n : ℕ) (β h : ℝ) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  fvProbabilityMeasure (minusField d) n (bondFinsetInternal d n) β h

/-! ## E. Infinite-volume states -/

/-- `μ` is an infinite-volume state of the sequence `ρ`: some subsequence of `ρ` converges weakly to
`μ`. -/
def InfiniteVolumeState (ρ : ℕ → ProbabilityMeasure (ConfigSpace (Site d)))
    (μ : ProbabilityMeasure (ConfigSpace (Site d))) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ WeakConvergesTo (ρ ∘ φ) μ

/-- Every sequence of probability measures on configurations has an infinite-volume state, by
Prokhorov compactness. -/
lemma exists_infiniteVolumeState
    (ρ : ℕ → ProbabilityMeasure (ConfigSpace (Site d))) :
    ∃ μ : ProbabilityMeasure (ConfigSpace (Site d)), InfiniteVolumeState ρ μ := by
  obtain ⟨ν, φ, hφ, htends⟩ := CompactSpace.tendsto_subseq ρ
  exact ⟨ν, φ, hφ, htends⟩

/-- A subsequential weak limit of `ρ`, chosen by `exists_infiniteVolumeState`. -/
noncomputable def limitState (ρ : ℕ → ProbabilityMeasure (ConfigSpace (Site d))) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  (exists_infiniteVolumeState ρ).choose

lemma limitState_isInfiniteVolumeState
    (ρ : ℕ → ProbabilityMeasure (ConfigSpace (Site d))) :
    InfiniteVolumeState ρ (limitState ρ) :=
  (exists_infiniteVolumeState ρ).choose_spec

/-- The plus state: a weak subsequential limit of the plus-boundary box measures.
Full-sequence convergence is not claimed here: the library only provides this state as a
chosen subsequential limit (see `plusState_isInfiniteVolumeState`). -/
noncomputable def plusState (d : ℕ) (β h : ℝ) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  limitState (fun n => plusMeasure d n β h)

/-- The minus state: a weak subsequential limit of the minus-boundary box measures. -/
noncomputable def minusState (d : ℕ) (β h : ℝ) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  limitState (fun n => minusMeasure d n β h)

/-- The free state: a weak subsequential limit of the free-boundary box measures. -/
noncomputable def freeState (d : ℕ) (β h : ℝ) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  limitState (fun n => freeMeasure d n β h)

lemma plusState_isInfiniteVolumeState (d : ℕ) (β h : ℝ) :
    InfiniteVolumeState (fun n => plusMeasure d n β h) (plusState d β h) :=
  limitState_isInfiniteVolumeState _

lemma minusState_isInfiniteVolumeState (d : ℕ) (β h : ℝ) :
    InfiniteVolumeState (fun n => minusMeasure d n β h) (minusState d β h) :=
  limitState_isInfiniteVolumeState _

lemma freeState_isInfiniteVolumeState (d : ℕ) (β h : ℝ) :
    InfiniteVolumeState (fun n => freeMeasure d n β h) (freeState d β h) :=
  limitState_isInfiniteVolumeState _

end Ising

end StatMech
