/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Phylogenetics.JukesCantor
public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Stationary

/-!
# Time-reversible nucleotide substitution models: GTR, HKY85, F81, K80

The **general time-reversible model** (GTR, Tavaré 1986) on a finite alphabet `ι` has
equilibrium base frequencies `π : ι → ℝ` and symmetric exchangeabilities `s i j = s j i`; its
rate matrix is

`gtrRate π s i j = s i j * π j` for `i ≠ j`, and `gtrRate π s i i = -∑_{k ≠ i} s i k * π k`.

On the nucleotides `Fin 4` we use the index order `0 = A`, `1 = C`, `2 = G`, `3 = T`, so the
purines `A, G` have even indices and the pyrimidines `C, T` odd ones; a substitution is a
**transition** (`A ↔ G` or `C ↔ T`) exactly when the two indices have the same parity, and a
**transversion** otherwise. The classical special cases are:

* HKY85 (Hasegawa–Kishino–Yano 1985): exchangeability `κ` for transitions and `1` for
  transversions, `hkyRate π κ`;
* F81 (Felsenstein 1981): all exchangeabilities `1`, `f81Rate π = hkyRate π 1`;
* K80 (Kimura 1980): equal base frequencies `1/4` and transition/transversion ratio `κ`,
  `k80Rate κ`;
* JC69 (Jukes–Cantor 1969): equal frequencies and equal exchangeabilities; with
  exchangeability `4 μ / 3` this is the seed matrix `JukesCantor.jcRateMatrix μ`.

Rates are not normalized: an overall rate `μ` only rescales time
(`ProbabilityTheory.ctmcTransition_smul`), so HKY85, F81 and K80 are stated with transversion
exchangeability `1`, and time is measured in expected transversion events per unit frequency.

The biological parameter domain is `π i > 0` with `∑ i, π i = 1`, `s i j > 0`, `κ > 0` and
`μ > 0`, with branch lengths `t ≥ 0`. The algebraic identities below hold for all real
parameters; each rate-matrix statement assumes only the nonnegativity it needs, and the
probabilistic reading of `exp (t • Q)` needs `t ≥ 0`.

With nonnegative parameters each matrix is a rate matrix. With symmetric exchangeabilities
the GTR matrix is in detailed balance with `π` (whatever the signs of the parameters), so `π`
is stationary for every transition matrix `exp (t • Q)`, and `π i P t i j = π j P t j i`
(the matrix form of time-reversibility when `π` is a probability vector).

## Main definitions

* `gtrRate`, `hkyExchangeability`, `hkyRate`, `f81Rate`, `k80Rate`.

## Main results

* `isRateMatrix_gtrRate`, `isRateMatrix_hkyRate`, `isRateMatrix_f81Rate`,
  `isRateMatrix_k80Rate`, `isRateMatrix_jcRateMatrix`: the models' matrices are rate matrices.
* `isDetailedBalance_gtrRate`: GTR is in detailed balance with its base frequencies.
* `vecMul_ctmcTransition_gtrRate`, `isDetailedBalance_ctmcTransition_gtrRate`: `π` is
  stationary and in detailed balance with `exp (t • Q)` at every time.
* `gtrRate_jukesCantor`, `ctmcTransition_gtrRate_jukesCantor`: JC69 is the equal-rates case,
  and its transition function is `JukesCantor.jcProb` (via `JukesCantor.jcProb_eq_exp`).
* `hkyRate_one`, `k80Rate_one`: HKY85 with `κ = 1` is F81, and K80 with `κ = 1` is JC69.

## References

* S. Tavaré, *Some probabilistic and statistical problems in the analysis of DNA sequences*,
  Lectures on Mathematics in the Life Sciences 17 (1986), 57–86.
* M. Hasegawa, H. Kishino and T. Yano, *Dating of the human–ape splitting by a molecular clock
  of mitochondrial DNA*, J. Mol. Evol. 22 (1985), 160–174.
* M. Kimura, *A simple method for estimating evolutionary rates of base substitutions through
  comparative studies of nucleotide sequences*, J. Mol. Evol. 16 (1980), 111–120.
* J. Felsenstein, *Evolutionary trees from DNA sequences: a maximum likelihood approach*,
  J. Mol. Evol. 17 (1981), 368–376.
* J. Felsenstein, *Inferring Phylogenies*, Sinauer, 2004, chapter 13.
-/

@[expose] public section

open Finset Matrix ProbabilityTheory MathlibExt.Biology.Phylogenetics.JukesCantor

namespace MathlibExt.Biology.Phylogenetics.SubstitutionModels

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **GTR rate matrix** (Tavaré 1986) with base frequencies `π` and exchangeabilities `s`:
`s i j * π j` off the diagonal and minus the off-diagonal row sum on it. The diagonal of `s` is
not used. -/
noncomputable def gtrRate (π : ι → ℝ) (s : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => if i = j then -∑ k ∈ univ.erase i, s i k * π k else s i j * π j

/-- The rows of the GTR matrix sum to `0`, for all parameters. -/
theorem sum_gtrRate (π : ι → ℝ) (s : Matrix ι ι ℝ) (i : ι) : ∑ j, gtrRate π s i j = 0 := by
  have h : ∑ j ∈ univ.erase i, gtrRate π s i j = ∑ k ∈ univ.erase i, s i k * π k :=
    sum_congr rfl fun j hj => by simp [gtrRate, (ne_of_mem_erase hj).symm]
  rw [← add_sum_erase _ _ (mem_univ i), h]
  simp [gtrRate]

/-- With nonnegative base frequencies and exchangeabilities, the GTR matrix is a rate
matrix. -/
theorem isRateMatrix_gtrRate {π : ι → ℝ} {s : Matrix ι ι ℝ} (hπ : ∀ i, 0 ≤ π i)
    (hs : ∀ i j, 0 ≤ s i j) : IsRateMatrix (gtrRate π s) := by
  refine ⟨fun i j hij => ?_, sum_gtrRate π s⟩
  simpa [gtrRate, hij] using mul_nonneg (hs i j) (hπ j)

/-- **GTR is reversible**: with symmetric exchangeabilities, the GTR matrix is in detailed
balance with its base frequencies, `π i Q i j = π j Q j i` (Tavaré 1986). -/
theorem isDetailedBalance_gtrRate (π : ι → ℝ) {s : Matrix ι ι ℝ} (hs : ∀ i j, s i j = s j i) :
    IsDetailedBalance π (gtrRate π s) := by
  intro i j
  by_cases h : i = j
  · subst h
    rfl
  · simp only [gtrRate, of_apply, ite_eq_right h, ite_eq_right (Ne.symm h)]
    rw [hs i j]
    ring

/-- The base frequencies are invariant for the GTR generator: `π Q = 0`. -/
theorem vecMul_gtrRate (π : ι → ℝ) {s : Matrix ι ι ℝ} (hs : ∀ i j, s i j = s j i) :
    π ᵥ* gtrRate π s = 0 :=
  (isDetailedBalance_gtrRate π hs).vecMul_eq_zero (sum_gtrRate π s)

/-- The base frequencies are stationary for the GTR transition function at every time. -/
theorem vecMul_ctmcTransition_gtrRate (π : ι → ℝ) {s : Matrix ι ι ℝ}
    (hs : ∀ i j, s i j = s j i) (t : ℝ) : π ᵥ* ctmcTransition (gtrRate π s) t = π :=
  (isDetailedBalance_gtrRate π hs).vecMul_ctmcTransition (sum_gtrRate π s) t

/-- Detailed balance of the GTR transition function with the base frequencies,
`π i P t i j = π j P t j i` for every `t` (time-reversibility of the GTR chain). -/
theorem isDetailedBalance_ctmcTransition_gtrRate (π : ι → ℝ) {s : Matrix ι ι ℝ}
    (hs : ∀ i j, s i j = s j i) (t : ℝ) :
    IsDetailedBalance π (ctmcTransition (gtrRate π s) t) :=
  (isDetailedBalance_gtrRate π hs).ctmcTransition t

/-! ## Nucleotide models on `Fin 4` (order `A, C, G, T`) -/

/-- The HKY85 exchangeabilities: `κ` for a transition (indices of equal parity: `A ↔ G`,
`C ↔ T` in the order `A, C, G, T`), `1` for a transversion. The diagonal (also `κ`) is not
used by `gtrRate`. -/
def hkyExchangeability (κ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => if (i : ℕ) % 2 = (j : ℕ) % 2 then κ else 1

/-- The **HKY85 rate matrix** (Hasegawa–Kishino–Yano 1985) with base frequencies `π` and
transition/transversion ratio `κ`: rate `κ π j` for a transition to `j`, `π j` for a
transversion. -/
noncomputable def hkyRate (π : Fin 4 → ℝ) (κ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  gtrRate π (hkyExchangeability κ)

/-- The **F81 rate matrix** (Felsenstein 1981): rate `π j` to every other base `j`. -/
noncomputable def f81Rate (π : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  gtrRate π (Matrix.of fun _ _ => 1)

/-- The **K80 rate matrix** (Kimura 1980): equal base frequencies `1/4`, rate `κ / 4` for a
transition and `1 / 4` for each transversion. -/
noncomputable def k80Rate (κ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  hkyRate (fun _ => 1 / 4) κ

/-- With nonnegative base frequencies and `κ ≥ 0`, the HKY85 matrix is a rate matrix. -/
theorem isRateMatrix_hkyRate {π : Fin 4 → ℝ} {κ : ℝ} (hπ : ∀ i, 0 ≤ π i) (hκ : 0 ≤ κ) :
    IsRateMatrix (hkyRate π κ) := by
  refine isRateMatrix_gtrRate hπ fun i j => ?_
  simp only [hkyExchangeability, of_apply]
  split_ifs <;> linarith

/-- With nonnegative base frequencies, the F81 matrix is a rate matrix. -/
theorem isRateMatrix_f81Rate {π : Fin 4 → ℝ} (hπ : ∀ i, 0 ≤ π i) : IsRateMatrix (f81Rate π) :=
  isRateMatrix_gtrRate hπ fun _ _ => zero_le_one

/-- With `κ ≥ 0`, the K80 matrix is a rate matrix. -/
theorem isRateMatrix_k80Rate {κ : ℝ} (hκ : 0 ≤ κ) : IsRateMatrix (k80Rate κ) :=
  isRateMatrix_hkyRate (fun _ => by norm_num) hκ

/-- HKY85 is in detailed balance with its base frequencies. -/
theorem isDetailedBalance_hkyRate (π : Fin 4 → ℝ) (κ : ℝ) :
    IsDetailedBalance π (hkyRate π κ) := by
  refine isDetailedBalance_gtrRate π fun i j => ?_
  simp only [hkyExchangeability, of_apply, eq_comm]

/-- F81 is in detailed balance with its base frequencies. -/
theorem isDetailedBalance_f81Rate (π : Fin 4 → ℝ) : IsDetailedBalance π (f81Rate π) :=
  isDetailedBalance_gtrRate π fun _ _ => rfl

/-- HKY85 with `κ = 1` is F81. -/
theorem hkyRate_one (π : Fin 4 → ℝ) : hkyRate π 1 = f81Rate π := by
  unfold hkyRate f81Rate hkyExchangeability
  simp only [ite_self]

/-! ## The Jukes–Cantor model as the equal-rates case -/

/-- **JC69 is the equal-rates GTR model**: equal base frequencies `1/4` and equal
exchangeabilities `4 μ / 3` give the Jukes–Cantor rate matrix `jcRateMatrix μ`. -/
theorem gtrRate_jukesCantor (μ : ℝ) :
    gtrRate (fun _ : Fin 4 => 1 / 4) (Matrix.of fun _ _ => 4 * μ / 3) = jcRateMatrix μ := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [gtrRate, jcRateMatrix, jcRate]
    ring
  · simp [gtrRate, jcRateMatrix, jcRate, h]
    ring

/-- The equal-rates GTR transition function is the Jukes–Cantor transition probability
`jcProb μ t` (by `JukesCantor.jcProb_eq_exp`). -/
theorem ctmcTransition_gtrRate_jukesCantor (μ t : ℝ) (i j : Fin 4) :
    ctmcTransition (gtrRate (fun _ : Fin 4 => 1 / 4) (Matrix.of fun _ _ => 4 * μ / 3)) t i j =
      jcProb μ t i j := by
  unfold ctmcTransition
  rw [gtrRate_jukesCantor]
  exact (jcProb_eq_exp μ t i j).symm

/-- For `μ ≥ 0` the Jukes–Cantor matrix is a rate matrix. -/
theorem isRateMatrix_jcRateMatrix {μ : ℝ} (hμ : 0 ≤ μ) : IsRateMatrix (jcRateMatrix μ) :=
  ⟨fun _ _ h => jcRate_nonneg hμ h, sum_jcRate μ⟩

/-- K80 with `κ = 1` is JC69 with substitution rate `μ = 3/4`. -/
theorem k80Rate_one : k80Rate 1 = jcRateMatrix (3 / 4) := by
  rw [← gtrRate_jukesCantor, k80Rate, hkyRate_one, f81Rate]
  norm_num

end MathlibExt.Biology.Phylogenetics.SubstitutionModels
