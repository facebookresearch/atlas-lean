/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The isothermal theorem: Moran fixation on isothermal graphs equals the well-mixed value

Lieberman, Hauert and Nowak (2005) place `N` individuals on the vertices of a graph with a
stochastic matrix `W` (rows sum to one). At each step an individual `i` is chosen to reproduce
with probability proportional to its fitness (`r` for a mutant, `1` for a resident), and its
offspring replaces the occupant of vertex `j` with probability `w_ij`. The temperature of vertex
`j` is `T_j = ∑_i w_ij`; the graph is isothermal when all temperatures are equal, which for a
stochastic `W` means that `W` is doubly stochastic (`T_j = 1`). The isothermal theorem says that
on an isothermal graph the fixation probability of a single mutant placed at a uniformly random
vertex is the Moran value `ρ₁ = (1 - 1/r) / (1 - 1/r^N)`.

Only the "if" direction is recorded. Keller and Uğurlu re-prove it by a martingale argument and
note that the original projection to a birth–death chain is incomplete; the "only if" direction
and the circulation criterion for general weights are not verified by any source read for this
module and are not stated. Strong connectivity of the weighted graph is assumed, as in the
model: without it (for example `W = 1`) no mutant ever spreads. Fixation probabilities are
characterized by the absorption equations of the chain on mutant sets.

The well-mixed Moran fixation probability is proved in
`Domains.Biology.PopulationGenetics.Moran` (`moranFixation`); `WantedExt` may not import
`Domains`, so the value `ρ₁` is restated here.

Sources: E. Lieberman, C. Hauert and M. A. Nowak, "Evolutionary dynamics on graphs", Nature 433
(2005) 312–316, p. 313 and eq. (1); F. Keller and B. Uğurlu, arXiv:2403.12598; Y. Kaveh,
N. L. Komarova and M. Kohandel, R. Soc. Open Sci. (2015), arXiv:1411.4556.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Field.Basic

@[expose] public section

namespace WantedExt.Biology.Ecology.IsothermalTheoremWanted

open Finset

variable {N : ℕ}

/-- Fitness of vertex `i` when the mutants occupy `S`: `r` for a mutant, `1` for a resident. -/
def fitness (r : ℝ) (S : Finset (Fin N)) (i : Fin N) : ℝ :=
  if i ∈ S then r else 1

/-- Total fitness `∑_i f_i` of the population when the mutants occupy `S`. -/
def totalFitness (r : ℝ) (S : Finset (Fin N)) : ℝ :=
  ∑ i, fitness r S i

/-- The mutant set after the individual at `i` places its offspring on vertex `j`. -/
def replace (S : Finset (Fin N)) (i j : Fin N) : Finset (Fin N) :=
  if i ∈ S then insert j S else S.erase j

/-- `φ` solves the **absorption equations** of the Moran process on the graph `W` with mutant
fitness `r`: `φ ∅ = 0`, `φ univ = 1`, and for every other mutant set `S`,
`φ(S) = ∑_{i,j} (f_i / ∑_k f_k) w_ij φ(S after i replaces j)`. -/
def IsFixationFunction (r : ℝ) (W : Matrix (Fin N) (Fin N) ℝ)
    (φ : Finset (Fin N) → ℝ) : Prop :=
  φ ∅ = 0 ∧ φ univ = 1 ∧ ∀ S : Finset (Fin N), S ≠ ∅ → S ≠ univ →
    φ S = ∑ i, ∑ j, fitness r S i / totalFitness r S * W i j * φ (replace S i j)

/-- The **Moran fixation probability** `ρ₁ = (1 - 1/r) / (1 - 1/r^N)` of a single mutant of
fitness `r` in a well-mixed population of size `N`. -/
noncomputable def moranFixation (r : ℝ) (N : ℕ) : ℝ :=
  (1 - r⁻¹) / (1 - r⁻¹ ^ N)

/-- **Isothermal theorem, "if" direction** (Lieberman, Hauert and Nowak 2005). Let `r > 0`,
`r ≠ 1`, and let `W` be a real `N × N` matrix with nonnegative entries, every row sum `1`
(stochastic) and every column sum `1` (all temperatures `T_j = 1`: doubly stochastic), that is
irreducible (for all `i, j` some power `W^k` has `(W^k)_{ij} > 0`). Then for every `φ` solving
the absorption equations of the Moran process on `W` with fitness `r`, the fixation probability
of a single mutant at a uniformly random vertex, `(∑_v φ {v}) / N`, equals
`(1 - 1/r) / (1 - 1/r^N)`.

Sources: Lieberman, Hauert and Nowak (2005), p. 313; Keller and Uğurlu, arXiv:2403.12598. -/
public theorem_wanted average_fixation_eq_moranFixation (r : ℝ) (hr : 0 < r) (hr1 : r ≠ 1)
    (W : Matrix (Fin N) (Fin N) ℝ) (hW : ∀ i j, 0 ≤ W i j) (hrow : ∀ i, ∑ j, W i j = 1)
    (hcol : ∀ j, ∑ i, W i j = 1) (hirr : ∀ i j, ∃ k : ℕ, 0 < (W ^ k) i j)
    (φ : Finset (Fin N) → ℝ) (hφ : IsFixationFunction r W φ) :
    (∑ v, φ {v}) / N = moranFixation r N

end WantedExt.Biology.Ecology.IsothermalTheoremWanted
