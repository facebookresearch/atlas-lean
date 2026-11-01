/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Phylogenetics.SubstitutionModels
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The Goldman–Yang codon model and `dN / dS = ω`

A codon is a word of three nucleotides (`Codon = Fin 3 → Fin 4`, order `A, C, G, T` as in
`SubstitutionModels`, so a nucleotide change is a transition iff the two indices have the same
parity). The state space is any finite type `ι` of codons (in practice the sense codons of a
genetic code) with a labelling `nuc : ι → Codon` and an amino-acid map `aa : ι → α`. The
**Goldman–Yang model** (Goldman & Yang 1994) is the GTR chain (`gtrRate`) on `ι` with codon
frequencies `π` and exchangeability

* `0` unless the two codons differ at exactly one position;
* times `κ` if that change is a transition;
* times `ω` if it changes the amino acid (nonsynonymous).

At stationarity the rates of synonymous and nonsynonymous substitutions per codon are
`ρ_S(ω) = ∑_{i ≠ j, aa i = aa j} π_i Q_ij` and `ρ_N(ω) = ∑_{aa i ≠ aa j} π_i Q_ij`. Only the
nonsynonymous exchangeabilities involve `ω`, so `ρ_S(ω) = ρ_S(1)` and `ρ_N(ω) = ω ρ_N(1)`.

**Site definition.** `dN / dS = ω` holds exactly when synonymous and nonsynonymous *sites* are
counted under the same model with `ω = 1`: `S = 3 ρ_S(1) / (ρ_S(1) + ρ_N(1))`,
`N = 3 ρ_N(1) / (ρ_S(1) + ρ_N(1))` per codon, with `dS = ρ_S(ω) / S` and `dN = ρ_N(ω) / N`.
Other site definitions (for example counting sites with `κ = 1`, as in the Nei–Gojobori
method, while substitutions follow `κ ≠ 1`) do not give `ω` in general. The rates are per unit
time; for a stationary chain the expected numbers of synonymous and nonsynonymous
substitutions along a branch of length `t` are `t` times these rates (not proved here), so the
ratio is the same for every branch length. Consistency of the Nei–Gojobori counting estimator
is not covered.

The parameter domain is `π_i ≥ 0`, `κ ≥ 0`, `ω ≥ 0`; the algebraic identities hold for all
real `κ`, `ω`, `π`.

## Main results

* `gyExchange`, `gyRate`: the Goldman–Yang exchangeabilities and rate matrix.
* `isRateMatrix_gyRate`, `isDetailedBalance_gyRate`: it is a reversible rate matrix.
* `synRate_eq`, `nonsynRate_eq`: `ρ_S(ω) = ρ_S(1)`, `ρ_N(ω) = ω ρ_N(1)`.
* `synSites_add_nonsynSites`: `S + N = 3`.
* `dN_div_dS`: `dN / dS = ω` when `ρ_S(1) > 0` and `ρ_N(1) > 0`.
* `synRate_pos_of_mem`, `nonsynRate_pos_of_mem`: sufficient conditions for these positivity
  hypotheses.

## References

* N. Goldman and Z. Yang, *A codon-based model of nucleotide substitution for protein-coding
  DNA sequences*, Mol. Biol. Evol. 11 (1994), 725–736.
* Z. Yang, *Computational Molecular Evolution*, Oxford University Press (2006), ch. 2.
-/

@[expose] public section

open Finset Matrix ProbabilityTheory MathlibExt.Biology.Phylogenetics.SubstitutionModels

noncomputable section

namespace MathlibExt.Biology.Phylogenetics.CodonModel

/-- A codon: three nucleotides, each in `Fin 4` (order `A, C, G, T`). -/
abbrev Codon := Fin 3 → Fin 4

/-- The positions at which two codons differ. -/
def diffPositions (c c' : Codon) : Finset (Fin 3) := univ.filter fun k => c k ≠ c' k

/-- Two codons differ at exactly one position. -/
def IsSingleChange (c c' : Codon) : Prop := (diffPositions c c').card = 1

/-- Every differing position is a transition (same parity: `A ↔ G` or `C ↔ T`). -/
def IsTransitionChange (c c' : Codon) : Prop :=
  ∀ k, c k ≠ c' k → (c k : ℕ) % 2 = (c' k : ℕ) % 2

instance (c c' : Codon) : Decidable (IsSingleChange c c') := by
  unfold IsSingleChange
  infer_instance

instance (c c' : Codon) : Decidable (IsTransitionChange c c') := by
  unfold IsTransitionChange
  infer_instance

/-- Differing at exactly one position is symmetric. -/
theorem isSingleChange_comm (c c' : Codon) : IsSingleChange c c' ↔ IsSingleChange c' c := by
  unfold IsSingleChange diffPositions
  simp_rw [ne_comm]

/-- Being a transition change is symmetric. -/
theorem isTransitionChange_comm (c c' : Codon) :
    IsTransitionChange c c' ↔ IsTransitionChange c' c := by
  unfold IsTransitionChange
  exact ⟨fun h k hk => (h k (Ne.symm hk)).symm, fun h k hk => (h k (Ne.symm hk)).symm⟩

variable {ι α : Type*} [DecidableEq α]

/-- The **Goldman–Yang exchangeability** between codons `i` and `j`: `0` unless they differ at
one position; otherwise `κ` for a transition (`1` for a transversion), times `ω` if the amino
acid changes. -/
def gyExchange (nuc : ι → Codon) (aa : ι → α) (κ ω : ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j =>
    if IsSingleChange (nuc i) (nuc j) then
      (if IsTransitionChange (nuc i) (nuc j) then κ else 1) * (if aa i = aa j then 1 else ω)
    else 0

/-- The Goldman–Yang exchangeabilities are symmetric. -/
theorem gyExchange_symm (nuc : ι → Codon) (aa : ι → α) (κ ω : ℝ) (i j : ι) :
    gyExchange nuc aa κ ω i j = gyExchange nuc aa κ ω j i := by
  simp only [gyExchange, Matrix.of_apply, isSingleChange_comm (nuc i),
    isTransitionChange_comm (nuc i), eq_comm (a := aa i)]

/-- The nonsynonymous exchangeabilities are linear in `ω`, the synonymous ones do not
involve it. -/
theorem gyExchange_eq (nuc : ι → Codon) (aa : ι → α) (κ ω : ℝ) (i j : ι) :
    gyExchange nuc aa κ ω i j =
      (if aa i = aa j then 1 else ω) * gyExchange nuc aa κ 1 i j := by
  simp only [gyExchange, Matrix.of_apply]
  split_ifs <;> ring

variable [Fintype ι] [DecidableEq ι]

/-- The **Goldman–Yang rate matrix** (Goldman & Yang 1994): the GTR matrix with codon
frequencies `π` and exchangeabilities `gyExchange`. -/
def gyRate (π : ι → ℝ) (nuc : ι → Codon) (aa : ι → α) (κ ω : ℝ) : Matrix ι ι ℝ :=
  gtrRate π (gyExchange nuc aa κ ω)

/-- The stationary **rate of synonymous substitutions** per codon,
`ρ_S = ∑_{i ≠ j, aa i = aa j} π_i Q_ij`. -/
def synRate (π : ι → ℝ) (nuc : ι → Codon) (aa : ι → α) (κ ω : ℝ) : ℝ :=
  ∑ i, ∑ j ∈ univ.filter fun j => j ≠ i ∧ aa j = aa i, π i * gyRate π nuc aa κ ω i j

/-- The stationary **rate of nonsynonymous substitutions** per codon,
`ρ_N = ∑_{aa i ≠ aa j} π_i Q_ij`. -/
def nonsynRate (π : ι → ℝ) (nuc : ι → Codon) (aa : ι → α) (κ ω : ℝ) : ℝ :=
  ∑ i, ∑ j ∈ univ.filter fun j => aa j ≠ aa i, π i * gyRate π nuc aa κ ω i j

/-- The number of **synonymous sites** per codon, counted under `ω = 1`:
`S = 3 ρ_S(1) / (ρ_S(1) + ρ_N(1))`. -/
def synSites (π : ι → ℝ) (nuc : ι → Codon) (aa : ι → α) (κ : ℝ) : ℝ :=
  3 * synRate π nuc aa κ 1 / (synRate π nuc aa κ 1 + nonsynRate π nuc aa κ 1)

/-- The number of **nonsynonymous sites** per codon, counted under `ω = 1`:
`N = 3 ρ_N(1) / (ρ_S(1) + ρ_N(1))`. -/
def nonsynSites (π : ι → ℝ) (nuc : ι → Codon) (aa : ι → α) (κ : ℝ) : ℝ :=
  3 * nonsynRate π nuc aa κ 1 / (synRate π nuc aa κ 1 + nonsynRate π nuc aa κ 1)

/-- The synonymous rate per synonymous site, `dS = ρ_S(ω) / S`. -/
def dS (π : ι → ℝ) (nuc : ι → Codon) (aa : ι → α) (κ ω : ℝ) : ℝ :=
  synRate π nuc aa κ ω / synSites π nuc aa κ

/-- The nonsynonymous rate per nonsynonymous site, `dN = ρ_N(ω) / N`. -/
def dN (π : ι → ℝ) (nuc : ι → Codon) (aa : ι → α) (κ ω : ℝ) : ℝ :=
  nonsynRate π nuc aa κ ω / nonsynSites π nuc aa κ

variable (π : ι → ℝ) (nuc : ι → Codon) (aa : ι → α) (κ ω : ℝ)

/-- Off the diagonal the Goldman–Yang rate is `gyExchange i j * π j`. -/
theorem gyRate_of_ne {i j : ι} (h : i ≠ j) :
    gyRate π nuc aa κ ω i j = gyExchange nuc aa κ ω i j * π j := by
  simp [gyRate, gtrRate, h]

/-- With nonnegative frequencies, `κ ≥ 0` and `ω ≥ 0`, the Goldman–Yang matrix is a rate
matrix. -/
theorem isRateMatrix_gyRate {π : ι → ℝ} (hπ : ∀ i, 0 ≤ π i) {κ ω : ℝ} (hκ : 0 ≤ κ)
    (hω : 0 ≤ ω) : IsRateMatrix (gyRate π nuc aa κ ω) := by
  refine isRateMatrix_gtrRate hπ fun i j => ?_
  simp only [gyExchange, Matrix.of_apply]
  split_ifs <;> positivity

/-- **The Goldman–Yang chain is reversible**: it is in detailed balance with its codon
frequencies. -/
theorem isDetailedBalance_gyRate : IsDetailedBalance π (gyRate π nuc aa κ ω) :=
  isDetailedBalance_gtrRate π (gyExchange_symm nuc aa κ ω)

/-- The synonymous rate does not depend on `ω`: `ρ_S(ω) = ρ_S(1)`. -/
theorem synRate_eq : synRate π nuc aa κ ω = synRate π nuc aa κ 1 := by
  refine sum_congr rfl fun i _ => sum_congr rfl fun j hj => ?_
  obtain ⟨hji, haa⟩ := (mem_filter.mp hj).2
  rw [gyRate_of_ne _ _ _ _ _ (Ne.symm hji), gyRate_of_ne _ _ _ _ _ (Ne.symm hji),
    gyExchange_eq]
  simp only [haa.symm, ↓reduceIte, one_mul]

/-- The nonsynonymous rate is linear in `ω`: `ρ_N(ω) = ω ρ_N(1)`. -/
theorem nonsynRate_eq : nonsynRate π nuc aa κ ω = ω * nonsynRate π nuc aa κ 1 := by
  rw [nonsynRate, nonsynRate, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have haa := (mem_filter.mp hj).2
  have hij : i ≠ j := fun h => haa (h ▸ rfl)
  rw [gyRate_of_ne _ _ _ _ _ hij, gyRate_of_ne _ _ _ _ _ hij, gyExchange_eq]
  simp only [Ne.symm haa, ↓reduceIte]
  ring

/-- There are three sites per codon: `S + N = 3` when `ρ_S(1) + ρ_N(1) ≠ 0`. -/
theorem synSites_add_nonsynSites (h : synRate π nuc aa κ 1 + nonsynRate π nuc aa κ 1 ≠ 0) :
    synSites π nuc aa κ + nonsynSites π nuc aa κ = 3 := by
  unfold synSites nonsynSites
  rw [← add_div, ← mul_add, mul_div_assoc, div_self h, mul_one]

/-- **`dN / dS = ω`** in the Goldman–Yang model with sites counted under `ω = 1` (derived;
see the module docstring for the site definition), provided `ρ_S(1) > 0` and `ρ_N(1) > 0`. -/
theorem dN_div_dS (hS : 0 < synRate π nuc aa κ 1) (hN : 0 < nonsynRate π nuc aa κ 1) :
    dN π nuc aa κ ω / dS π nuc aa κ ω = ω := by
  unfold dN dS nonsynSites synSites
  rw [synRate_eq π nuc aa κ ω, nonsynRate_eq π nuc aa κ ω]
  have hsum : 0 < synRate π nuc aa κ 1 + nonsynRate π nuc aa κ 1 := add_pos hS hN
  field_simp

/-- `ρ_S(1) > 0` if the frequencies are nonnegative, `κ > 0`, and some synonymous single
change joins two codons of positive frequency. -/
theorem synRate_pos_of_mem {π : ι → ℝ} (hπ : ∀ i, 0 ≤ π i) {κ : ℝ} (hκ : 0 < κ) {i j : ι}
    (hij : i ≠ j) (haa : aa i = aa j) (hs : IsSingleChange (nuc i) (nuc j)) (hi : 0 < π i)
    (hj : 0 < π j) : 0 < synRate π nuc aa κ 1 := by
  have hterm : ∀ i' j' : ι, i' ≠ j' → 0 ≤ π i' * gyRate π nuc aa κ 1 i' j' := by
    intro i' j' hne
    rw [gyRate_of_ne _ _ _ _ _ hne]
    have : 0 ≤ gyExchange nuc aa κ 1 i' j' := by
      simp only [gyExchange, Matrix.of_apply]
      split_ifs <;> positivity
    exact mul_nonneg (hπ i') (mul_nonneg this (hπ j'))
  have hij' : 0 < π i * gyRate π nuc aa κ 1 i j := by
    rw [gyRate_of_ne _ _ _ _ _ hij]
    simp only [gyExchange, Matrix.of_apply, hs, haa, ↓reduceIte]
    split_ifs <;> positivity
  refine sum_pos' (fun i' _ => sum_nonneg fun j' hj' =>
    hterm i' j' (Ne.symm (mem_filter.mp hj').2.1)) ⟨i, mem_univ i, ?_⟩
  exact sum_pos' (fun j' hj' => hterm i j' (Ne.symm (mem_filter.mp hj').2.1))
    ⟨j, mem_filter.mpr ⟨mem_univ j, Ne.symm hij, haa.symm⟩, hij'⟩

/-- `ρ_N(1) > 0` if the frequencies are nonnegative, `κ > 0`, and some nonsynonymous single
change joins two codons of positive frequency. -/
theorem nonsynRate_pos_of_mem {π : ι → ℝ} (hπ : ∀ i, 0 ≤ π i) {κ : ℝ} (hκ : 0 < κ) {i j : ι}
    (haa : aa i ≠ aa j) (hs : IsSingleChange (nuc i) (nuc j)) (hi : 0 < π i)
    (hj : 0 < π j) : 0 < nonsynRate π nuc aa κ 1 := by
  have hne : ∀ {i' j' : ι}, aa j' ≠ aa i' → i' ≠ j' := fun h hij => h (hij ▸ rfl)
  have hterm : ∀ i' j' : ι, i' ≠ j' → 0 ≤ π i' * gyRate π nuc aa κ 1 i' j' := by
    intro i' j' hne
    rw [gyRate_of_ne _ _ _ _ _ hne]
    have : 0 ≤ gyExchange nuc aa κ 1 i' j' := by
      simp only [gyExchange, Matrix.of_apply]
      split_ifs <;> positivity
    exact mul_nonneg (hπ i') (mul_nonneg this (hπ j'))
  have hij : i ≠ j := hne (Ne.symm haa)
  have hij' : 0 < π i * gyRate π nuc aa κ 1 i j := by
    rw [gyRate_of_ne _ _ _ _ _ hij]
    simp only [gyExchange, Matrix.of_apply, hs, haa, ↓reduceIte]
    split_ifs <;> positivity
  refine sum_pos' (fun i' _ => sum_nonneg fun j' hj' =>
    hterm i' j' (hne (mem_filter.mp hj').2)) ⟨i, mem_univ i, ?_⟩
  exact sum_pos' (fun j' hj' => hterm i j' (hne (mem_filter.mp hj').2))
    ⟨j, mem_filter.mpr ⟨mem_univ j, Ne.symm haa⟩, hij'⟩

end MathlibExt.Biology.Phylogenetics.CodonModel
