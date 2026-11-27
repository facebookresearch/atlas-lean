/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# At most `2n - 1` steady states in the `n`-site futile cycle

The `n`-site sequential distributive phosphorylation–dephosphorylation cycle (`n ≥ 1`) has the
`3n + 3` species `S_0, …, S_n`, `ES_0, …, ES_{n-1}`, `FS_1, …, FS_n`, `E` and `F`, and the `6n`
reactions, for `j = 0, …, n - 1`,
`S_j + E → ES_j` (`kon_j`), `ES_j → S_j + E` (`koff_j`), `ES_j → S_{j+1} + E` (`kcat_j`),
`S_{j+1} + F → FS_{j+1}` (`lon_j`), `FS_{j+1} → S_{j+1} + F` (`loff_j`),
`FS_{j+1} → S_j + F` (`lcat_j`),
with full mass-action kinetics and all `6n` rate constants positive. Writing `s_i`, `c_j`,
`d_{j+1}`, `e`, `f` for the concentrations, the conserved totals are
`E_tot = e + ∑_j c_j`, `F_tot = f + ∑_j d_{j+1}` and `S_tot = ∑_i s_i + ∑_j c_j + ∑_j d_{j+1}`.

**Theorem 3** (Wang–Sontag 2008). For every choice of positive rate constants `κ` and positive
totals `C = (E_tot, F_tot, S_tot)`, the system has at most `2n - 1` positive steady states: the
set of states with every concentration positive, the mass-action field zero, and the totals
equal to `C` has at most `2n - 1` points.

The bound counts distinct states (`Set.encard`), so it also asserts finiteness. The journal
version is followed; its arXiv preprint has index typos in the reaction list. The concentration
of `FS_{j+1}` is stored at index `j`.

Sources: L. Wang, E. D. Sontag, "On the number of steady states in a multiple futile cycle",
J. Math. Biol. 57 (2008) 29–52, Section 3, Eqs. (1)–(2), and Section 4.2, Theorem 3
(arXiv:0704.0036).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Set.Card

@[expose] public section

namespace WantedExt.Biology.Biophysics.FutileCycleSteadyStatesWanted

/-- A state of the `n`-site futile cycle: substrate forms `s i = [S_i]` (`i ≤ n`), complexes
`c j = [ES_j]` and `d j = [FS_{j+1}]` (`j < n`), and free enzymes `e = [E]`, `f = [F]`. -/
structure State (n : ℕ) where
  /-- The substrate forms `S_0, …, S_n`. -/
  s : Fin (n + 1) → ℝ
  /-- The kinase–substrate complexes `ES_0, …, ES_{n-1}`. -/
  c : Fin n → ℝ
  /-- The phosphatase–substrate complexes `FS_1, …, FS_n` (index `j` holds `FS_{j+1}`). -/
  d : Fin n → ℝ
  /-- The free kinase `E`. -/
  e : ℝ
  /-- The free phosphatase `F`. -/
  f : ℝ

/-- The `6n` rate constants, indexed by `j < n`: `kon_j`, `koff_j` and `kcat_j` for
`S_j + E → ES_j`, `ES_j → S_j + E` and `ES_j → S_{j+1} + E`, and `lon_j`, `loff_j` and `lcat_j`
for `S_{j+1} + F → FS_{j+1}`, `FS_{j+1} → S_{j+1} + F` and `FS_{j+1} → S_j + F`. -/
structure Rates (n : ℕ) where
  /-- Binding `S_j + E → ES_j`. -/
  kon : Fin n → ℝ
  /-- Unbinding `ES_j → S_j + E`. -/
  koff : Fin n → ℝ
  /-- Catalysis `ES_j → S_{j+1} + E`. -/
  kcat : Fin n → ℝ
  /-- Binding `S_{j+1} + F → FS_{j+1}`. -/
  lon : Fin n → ℝ
  /-- Unbinding `FS_{j+1} → S_{j+1} + F`. -/
  loff : Fin n → ℝ
  /-- Catalysis `FS_{j+1} → S_j + F`. -/
  lcat : Fin n → ℝ

namespace State

variable {n : ℕ} (κ : Rates n) (x : State n)

/-- The mass-action rate of change of `S_i`: reactions `j = i` consume or return `S_i` through
`E` (`- kon_i s_i e + koff_i c_i`) and produce it from `FS_{i+1}` (`+ lcat_i d_i`); reactions
`j = i - 1` produce it from `ES_{i-1}` (`+ kcat_{i-1} c_{i-1}`) and consume or return it through
`F` (`- lon_{i-1} s_i f + loff_{i-1} d_{i-1}`). -/
noncomputable def ds (i : Fin (n + 1)) : ℝ :=
  (∑ j : Fin n, if j.castSucc = i then
      -(κ.kon j * x.s i * x.e) + κ.koff j * x.c j + κ.lcat j * x.d j else 0) +
    ∑ j : Fin n, if j.succ = i then
      κ.kcat j * x.c j - κ.lon j * x.s i * x.f + κ.loff j * x.d j else 0

/-- The mass-action rate of change of `ES_j`: `kon_j s_j e - (koff_j + kcat_j) c_j`. -/
noncomputable def dc (j : Fin n) : ℝ :=
  κ.kon j * x.s j.castSucc * x.e - (κ.koff j + κ.kcat j) * x.c j

/-- The mass-action rate of change of `FS_{j+1}`: `lon_j s_{j+1} f - (loff_j + lcat_j) d_j`, where
`d_j = [FS_{j+1}]`. -/
noncomputable def dd (j : Fin n) : ℝ :=
  κ.lon j * x.s j.succ * x.f - (κ.loff j + κ.lcat j) * x.d j

/-- The mass-action rate of change of `E`: `∑_j (-kon_j s_j e + (koff_j + kcat_j) c_j)`. -/
noncomputable def de : ℝ :=
  ∑ j, (-(κ.kon j * x.s j.castSucc * x.e) + (κ.koff j + κ.kcat j) * x.c j)

/-- The mass-action rate of change of `F`: `∑_j (-lon_j s_{j+1} f + (loff_j + lcat_j) d_j)`, where
`d_j = [FS_{j+1}]`. -/
noncomputable def df : ℝ :=
  ∑ j, (-(κ.lon j * x.s j.succ * x.f) + (κ.loff j + κ.lcat j) * x.d j)

/-- All concentrations are positive. -/
def IsPositive : Prop :=
  (∀ i, 0 < x.s i) ∧ (∀ j, 0 < x.c j) ∧ (∀ j, 0 < x.d j) ∧ 0 < x.e ∧ 0 < x.f

/-- The mass-action vector field vanishes. -/
def IsSteady : Prop :=
  (∀ i, x.ds κ i = 0) ∧ (∀ j, x.dc κ j = 0) ∧ (∀ j, x.dd κ j = 0) ∧ x.de κ = 0 ∧ x.df κ = 0

/-- The conserved totals equal `(Etot, Ftot, Stot)`: `e + ∑_j c_j = Etot`, `f + ∑_j d_j = Ftot` and
`∑_i s_i + ∑_j c_j + ∑_j d_j = Stot`, where `d_j = [FS_{j+1}]`. -/
def HasTotals (Etot Ftot Stot : ℝ) : Prop :=
  x.e + ∑ j, x.c j = Etot ∧ x.f + ∑ j, x.d j = Ftot ∧
    ∑ i, x.s i + ∑ j, x.c j + ∑ j, x.d j = Stot

end State

/-- The positive steady states with totals `(Etot, Ftot, Stot)`. -/
def positiveSteadyStates {n : ℕ} (κ : Rates n) (Etot Ftot Stot : ℝ) : Set (State n) :=
  {x | x.IsPositive ∧ x.IsSteady κ ∧ x.HasTotals Etot Ftot Stot}

/-- **At most `2n - 1` positive steady states** (Wang–Sontag 2008, Theorem 3). For every `n ≥ 1`,
every choice of the `6n` rate constants with all of them positive, and all positive totals
`Etot`, `Ftot`, `Stot`, the set of states of the `n`-site futile cycle whose concentrations are
all positive, at which the mass-action vector field vanishes, and whose conserved totals are
`(Etot, Ftot, Stot)` has at most `2n - 1` elements (in particular it is finite).

Source: L. Wang, E. D. Sontag, J. Math. Biol. 57 (2008) 29–52, Theorem 3. -/
theorem_wanted encard_positiveSteadyStates_le {n : ℕ} (hn : 1 ≤ n) (κ : Rates n)
    (hkon : ∀ j, 0 < κ.kon j) (hkoff : ∀ j, 0 < κ.koff j) (hkcat : ∀ j, 0 < κ.kcat j)
    (hlon : ∀ j, 0 < κ.lon j) (hloff : ∀ j, 0 < κ.loff j) (hlcat : ∀ j, 0 < κ.lcat j)
    {Etot Ftot Stot : ℝ} (hE : 0 < Etot) (hF : 0 < Ftot) (hS : 0 < Stot) :
    (positiveSteadyStates κ Etot Ftot Stot).encard ≤ (2 * n - 1 : ℕ)

end WantedExt.Biology.Biophysics.FutileCycleSteadyStatesWanted
