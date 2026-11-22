/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Logic.Relation

namespace MetaMathlibExt

@[expose] public section

/-- Theorem 3 (Geroldinger; Elledge–Hurlbert), as quoted by Bushaw and
Hurlbert: in a finite abelian group `Γ`, every sequence of `|Γ|` elements is
*good*, i.e. it contains a zero-sum subsequence with cross number
`∑ 1 / |gᵢ|` at most one, where `|gᵢ|` is the order of `gᵢ`. The sequence is
indexed by `Fin |Γ|`, a subsequence is a nonempty index set (the empty
subsequence would make the claim vacuous), and the cross number is computed
in `ℚ`.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small
Cross Numbers in Abelian Groups*, INTEGERS 24 (2024), Article A93, Theorem 3
(`integers-2024-A93-thm-3`). -/
public theorem_wanted exists_zero_sum_cross_number_le_one {Γ : Type*} [AddCommGroup Γ]
    [Fintype Γ] (g : Fin (Fintype.card Γ) → Γ) :
    ∃ s : Finset (Fin (Fintype.card Γ)), s.Nonempty ∧ ∑ i ∈ s, g i = 0 ∧
      ∑ i ∈ s, (1 : ℚ) / addOrderOf (g i) ≤ 1

/-- Theorem 2 (Lemke–Kleitman; Chung), as quoted by Bushaw and Hurlbert: for
every positive integer `n`, every sequence of `n` elements of `ℤ/nℤ` contains a
nonempty zero-sum subsequence with cross number `∑ 1 / |gᵢ|` at most one.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small
Cross Numbers in Abelian Groups*, INTEGERS 24 (2024), Article A93, Theorem 2
(`integers-2024-A93-thm-2`). -/
public theorem_wanted ZMod.exists_zero_sum_cross_number_le_one {n : ℕ} (hn : 0 < n)
    (g : Fin n → ZMod n) :
    ∃ s : Finset (Fin n), s.Nonempty ∧ ∑ i ∈ s, g i = 0 ∧
      ∑ i ∈ s, (1 : ℚ) / addOrderOf (g i) ≤ 1

/-- A finite sequence `g` in a finite additive group is *good* if it has a nonempty zero-sum
subsequence (index set) with cross number `∑ 1 / |gᵢ|` at most one, computed in `ℚ`.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Section 1 (definition of good sequences). -/
def IsGoodSequence {Γ : Type*} [AddCommGroup Γ] [Finite Γ] {t : ℕ} (g : Fin t → Γ) : Prop :=
  ∃ s : Finset (Fin t), s.Nonempty ∧ ∑ i ∈ s, g i = 0 ∧
    ∑ i ∈ s, (1 : ℚ) / addOrderOf (g i) ≤ 1

/-- The probability that a uniformly random length-`t` sequence in `Γ` is good, namely
`#{good g : Fin t → Γ} / |Γ|^t` (the probability space `S(Γ, t)` of the source), for a finite
group `Γ` as in the source.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Section 1.1 (the event `E_Γ(t)`). -/
noncomputable def goodSequenceProb (Γ : Type*) [AddCommGroup Γ] [Finite Γ] (t : ℕ) : ℝ :=
  ({g : Fin t → Γ | IsGoodSequence g}.ncard : ℝ) / (Nat.card Γ : ℝ) ^ t

/-- The empty sequence is not good, so `goodSequenceProb Γ 0 = 0`.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, characteristic lemma of the Section 1.1
definition. -/
theorem goodSequenceProb_zero (Γ : Type*) [AddCommGroup Γ] [Finite Γ] :
    goodSequenceProb Γ 0 = 0 := by
  have h : {g : Fin 0 → Γ | IsGoodSequence g} = ∅ := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨s, ⟨i, -⟩, -⟩
    exact i.elim0
  simp [goodSequenceProb, h]

/-- `P_{1/2}(Γ)`, the least `t` for which a uniformly random length-`t` sequence in `Γ` is good
with probability at least `1/2`.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Section 1.1 (definition of `P_{1/2}(Γ)`). -/
noncomputable def halfGoodThreshold (Γ : Type*) [AddCommGroup Γ] [Finite Γ] : ℕ :=
  sInf {t : ℕ | (1 : ℝ) / 2 ≤ goodSequenceProb Γ t}

/-- For a finite group of order at most two, `P_{1/2}(Γ) = 1`: the sequence `(0)` is good.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, characteristic lemma of the Section 1.1
definition of `P_{1/2}(Γ)`. -/
theorem halfGoodThreshold_eq_one_of_card_le_two (Γ : Type*) [AddCommGroup Γ] [Finite Γ]
    (h : Nat.card Γ ≤ 2) : halfGoodThreshold Γ = 1 := by
  have h0 : (0 : ℕ) ∉ {t : ℕ | (1 : ℝ) / 2 ≤ goodSequenceProb Γ t} := by
    simp only [Set.mem_ofPred_eq, goodSequenceProb_zero]
    norm_num
  have h1 : (1 : ℕ) ∈ {t : ℕ | (1 : ℝ) / 2 ≤ goodSequenceProb Γ t} := by
    have hgood : (fun _ => (0 : Γ)) ∈ {g : Fin 1 → Γ | IsGoodSequence g} :=
      ⟨Finset.univ, Finset.univ_nonempty, by simp, by simp⟩
    have hpos : 0 < {g : Fin 1 → Γ | IsGoodSequence g}.ncard :=
      (Set.ncard_pos (Set.toFinite _)).2 ⟨_, hgood⟩
    have hcard : 0 < Nat.card Γ := Nat.card_pos
    have hpos' : (1 : ℝ) ≤ ({g : Fin 1 → Γ | IsGoodSequence g}.ncard : ℝ) := by
      exact_mod_cast hpos
    have hcard' : (0 : ℝ) < (Nat.card Γ : ℝ) := by exact_mod_cast hcard
    have h2 : (Nat.card Γ : ℝ) ≤ 2 := by exact_mod_cast h
    show (1 : ℝ) / 2 ≤ goodSequenceProb Γ 1
    rw [goodSequenceProb, pow_one, le_div_iff₀ hcard']
    linarith
  refine le_antisymm (Nat.sInf_le h1) (Nat.one_le_iff_ne_zero.2 fun hz => ?_)
  rcases Nat.sInf_eq_zero.1 hz with h | h
  · exact h0 h
  · rw [h] at h1
    exact h1

/-- `t` is a threshold function for the event probabilities `P k s` (probability of the event in
the `k`-th space with `s` random elements): `t` is eventually positive (the source's thresholds
are positive functions; little-o ignores sign, so without this `-t` would be a threshold
whenever `t` is), `P k (f k) → 1` whenever `t ∈ o(f)`, and `P k (f k) → 0` whenever `f ∈ o(t)`.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Section 1.1 (definition of a threshold and of
`τ(G)`). -/
def IsThresholdFunction (P : ℕ → ℕ → ℝ) (t : ℕ → ℝ) : Prop :=
  (∀ᶠ k in Filter.atTop, 0 < t k) ∧ ∀ f : ℕ → ℕ,
    (t =o[Filter.atTop] (fun k => (f k : ℝ)) →
        Filter.Tendsto (fun k => P k (f k)) Filter.atTop (nhds 1)) ∧
      ((fun k => (f k : ℝ)) =o[Filter.atTop] t →
        Filter.Tendsto (fun k => P k (f k)) Filter.atTop (nhds 0))

/-- Threshold functions are only determined up to positive constant factors.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, characteristic lemma of the Section 1.1
definition of a threshold. -/
theorem IsThresholdFunction.const_mul {P : ℕ → ℕ → ℝ} {t : ℕ → ℝ}
    (h : IsThresholdFunction P t) {c : ℝ} (hc : 0 < c) :
    IsThresholdFunction P (fun k => c * t k) :=
  ⟨h.1.mono fun _ hk => mul_pos hc hk, fun f =>
    ⟨fun hf => (h.2 f).1 ((Asymptotics.isLittleO_const_mul_left_iff hc.ne').1 hf),
      fun hf => (h.2 f).2 ((Asymptotics.isLittleO_const_mul_right_iff hc.ne').1 hf)⟩⟩

/-- One Lagarias–Saks pebbling step on `G` with edge costs `w`: along an edge `uv` with
`0 < w(uv) ≤ C u`, remove `w(uv)` pebbles from `u` and add one pebble to `v`. Costs live on
unordered pairs (`Sym2 V`), so each edge has one cost in both directions; the source's costs
are positive, and the step requires it, so a zero cost never creates a pebble for free.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Section 2.2 (pebbling step). -/
def PebblingStep {V : Type*} [DecidableEq V] (G : SimpleGraph V) (w : Sym2 V → ℕ)
    (C C' : V → ℕ) : Prop :=
  ∃ u v, G.Adj u v ∧ 0 < w s(u, v) ∧ w s(u, v) ≤ C u ∧
    C' = Function.update (Function.update C u (C u - w s(u, v))) v (C v + 1)

/-- A configuration `C` is *solvable* if for every target `r` some sequence of pebbling steps
puts a pebble on `r`.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Sections 2.2 and 3.1 (`r`-solvability, for
every target). -/
def PebblingSolvable {V : Type*} [DecidableEq V] (G : SimpleGraph V) (w : Sym2 V → ℕ)
    (C : V → ℕ) : Prop :=
  ∀ r : V, ∃ C', Relation.ReflTransGen (PebblingStep G w) C C' ∧ 1 ≤ C' r

/-- A configuration with a pebble on every vertex is solvable.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, characteristic lemma of the Section 2.2
definition. -/
theorem pebblingSolvable_of_forall_pos {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (w : Sym2 V → ℕ) {C : V → ℕ} (hC : ∀ r, 1 ≤ C r) : PebblingSolvable G w C :=
  fun r => ⟨C, Relation.ReflTransGen.refl, hC r⟩

/-- The probability that a configuration of `t` pebbles, uniform among all `C(n + t - 1, t)`
size-`t` configurations on the `n` vertices, is solvable (the space `D_{G,t}` of the source).

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Section 3.1 (configuration model). -/
noncomputable def solvableConfigurationProb {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℕ) (t : ℕ) : ℝ :=
  ({C : V → ℕ | ∑ v, C v = t ∧ PebblingSolvable G w C}.ncard : ℝ) /
    ({C : V → ℕ | ∑ v, C v = t}.ncard : ℝ)

/-- The solvability probability is at most one.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, characteristic lemma of the Section 3.1
definition. -/
theorem solvableConfigurationProb_le_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℕ) (t : ℕ) : solvableConfigurationProb G w t ≤ 1 := by
  have hfin : {C : V → ℕ | ∑ v, C v = t}.Finite := by
    refine (Set.Finite.pi (t := fun _ : V => Set.Iic t) fun _ => Set.finite_Iic t).subset ?_
    intro C hC v _
    rw [Set.mem_ofPred_eq] at hC
    rw [Set.mem_Iic, ← hC]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
  have hle := Set.ncard_le_ncard (fun C (hC : C ∈ {C : V → ℕ | ∑ v, C v = t ∧
    PebblingSolvable G w C}) => (show C ∈ {C : V → ℕ | ∑ v, C v = t} from hC.1)) hfin
  exact div_le_one_of_le₀ (by exact_mod_cast hle) (Nat.cast_nonneg _)

/-- The `d`-dimensional grid `□_{i<d} P_k`: vertices `Fin d → Fin k`, adjacent when they differ
in exactly one coordinate, by one. For `k = 2` this is the `d`-cube `Q_d`.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Section 2.1 (grids and cubes). -/
def gridGraph (d k : ℕ) : SimpleGraph (Fin d → Fin k) where
  Adj x y := ∃ i, (∀ j, j ≠ i → x j = y j) ∧ ((x i : ℕ) + 1 = y i ∨ (y i : ℕ) + 1 = x i)
  symm := ⟨fun _ _ ⟨i, h1, h2⟩ => ⟨i, fun j hj => (h1 j hj).symm, h2.symm⟩⟩
  loopless := ⟨fun _ ⟨_, _, h2⟩ => by omega⟩

/-- Edge costs on the grid with cost `w i` in coordinate `i`: on the pair `{x, y}`, the sum of
`w i` over the coordinates where `x` and `y` differ (exactly one for an edge).

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Section 3.2 (cost `wᵢ` in coordinate `i`). -/
def gridCost {d k : ℕ} (w : Fin d → ℕ) : Sym2 (Fin d → Fin k) → ℕ :=
  Sym2.lift ⟨fun x y => ∑ i, if x i = y i then 0 else w i, fun x y =>
    Finset.sum_congr rfl fun i _ => by simp only [eq_comm]⟩

/-- On a pair differing only in coordinate `i`, the grid cost is `w i`.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, characteristic lemma of the Section 3.2
grid costs. -/
theorem gridCost_eq_of_eq_off {d k : ℕ} (w : Fin d → ℕ) {x y : Fin d → Fin k} {i : Fin d}
    (hj : ∀ j, j ≠ i → x j = y j) (hi : x i ≠ y i) : gridCost w s(x, y) = w i := by
  show (∑ j, if x j = y j then 0 else w j) = w i
  rw [Finset.sum_eq_single i (fun j _ hji => by simp [hj j hji]) (by simp)]
  simp [hi]

/-- Threshold version of Geroldinger's theorem: for primes `p₁, …, p_d` (not necessarily
distinct) and `Γ_k = ∏ᵢ ℤ/pᵢᵏℤ`,
`P_{1/2}(Γ_k) ≤ k^d exp[((d+1)! ∏ᵢ lg pᵢ / 2 · lg k)^{1/(d+1)} - (d/(d+1)) lg lg k + O(1)]`,
with `lg = log₂`; the `O(1)` is a constant `C` and the bound holds for all large `k`.

Upper bound only, as in the journal record (the source's final comments say the bound need not
be an equality). `d = 0` is admitted (trivial group).

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Theorem 4 (`integers-2024-A93-thm-4`). -/
public theorem_wanted halfGoodThreshold_pi_zmod_prime_pow_le (d : ℕ) (p : Fin d → ℕ)
    [∀ i, Fact (p i).Prime] :
    ∃ C : ℝ, ∀ᶠ k : ℕ in Filter.atTop,
      (halfGoodThreshold ((i : Fin d) → ZMod (p i ^ k)) : ℝ) ≤
        (k : ℝ) ^ d * Real.exp ((((d + 1).factorial : ℝ) * (∏ i, Real.logb 2 (p i)) / 2 *
            Real.logb 2 k) ^ ((1 : ℝ) / (d + 1)) -
          (d : ℝ) / (d + 1) * Real.logb 2 (Real.logb 2 k) + C)

/-- Bushaw–Kettle threshold for grids: for fixed `d ≥ 1` and costs `wᵢ ≥ 2`, every pebbling
threshold function `t` of the grids `P_k^d = □_{i<d} P_k` with cost `wᵢ` in coordinate `i`
satisfies `t(k) = n exp[((d+1)! ∏ᵢ lg wᵢ / 2 · lg k)^{1/(d+1)} - (d/(d+1)) lg lg k + O(1)]`
with `n = k^d`, written as a two-sided bound with one constant `C` for all large `k`.

`wᵢ ≥ 2` is added: with cost `1` every nonempty configuration is solvable, so the thresholds
are bounded while the right side tends to infinity. `d ≥ 1` likewise (at `d = 0` the grid is a
single vertex).

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Theorem 9 (quoting Bushaw and Kettle,
`integers-2024-A93-thm-9`). -/
public theorem_wanted gridGraph_pebbling_threshold_eq (d : ℕ) (hd : 1 ≤ d) (w : Fin d → ℕ)
    (hw : ∀ i, 2 ≤ w i) (t : ℕ → ℝ)
    (ht : IsThresholdFunction
      (fun k s => solvableConfigurationProb (gridGraph d k) (gridCost w) s) t) :
    ∃ C : ℝ, ∀ᶠ k : ℕ in Filter.atTop,
      (k : ℝ) ^ d * Real.exp ((((d + 1).factorial : ℝ) * (∏ i, Real.logb 2 (w i)) / 2 *
            Real.logb 2 k) ^ ((1 : ℝ) / (d + 1)) -
          (d : ℝ) / (d + 1) * Real.logb 2 (Real.logb 2 k) - C) ≤ t k ∧
        t k ≤ (k : ℝ) ^ d * Real.exp ((((d + 1).factorial : ℝ) * (∏ i, Real.logb 2 (w i)) / 2 *
            Real.logb 2 k) ^ ((1 : ℝ) / (d + 1)) -
          (d : ℝ) / (d + 1) * Real.logb 2 (Real.logb 2 k) + C)

/-- Pebbling threshold of the cubes (Czygrinow–Wagner, Alon): with `n = 2^d` and cost `2`, every
pebbling threshold function `t` of the sequence of `d`-cubes satisfies, for every `ε > 0`,
`t ∈ Ω(n^{1-ε}) ∩ O(n / (lg lg n)^{1-ε})`.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Theorem 10 (`integers-2024-A93-thm-10`). -/
public theorem_wanted cube_pebbling_threshold_bounds (ε : ℝ) (hε : 0 < ε) (t : ℕ → ℝ)
    (ht : IsThresholdFunction
      (fun d s => solvableConfigurationProb (gridGraph d 2) (gridCost fun _ => 2) s) t) :
    (fun d : ℕ => ((2 : ℝ) ^ d) ^ (1 - ε)) =O[Filter.atTop] t ∧
      t =O[Filter.atTop]
        fun d : ℕ => (2 : ℝ) ^ d / Real.logb 2 (Real.logb 2 ((2 : ℝ) ^ d)) ^ (1 - ε)

/-- Zero sums with small cross number in `ℤ₂ᵈ`: with `n = 2^d`, every threshold function `t` for
the event that a uniformly random sequence in `ℤ₂ᵈ` is good satisfies, for every `ε > 0`,
`t ∈ O(n / (lg lg n)^{1-ε})`.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Theorem 11 (`integers-2024-A93-thm-11`). -/
public theorem_wanted zmod_two_pi_good_threshold_isBigO (ε : ℝ) (hε : 0 < ε) (t : ℕ → ℝ)
    (ht : IsThresholdFunction (fun d s => goodSequenceProb (Fin d → ZMod 2) s) t) :
    t =O[Filter.atTop]
      fun d : ℕ => (2 : ℝ) ^ d / Real.logb 2 (Real.logb 2 ((2 : ℝ) ^ d)) ^ (1 - ε)

/-- Zero sums with small cross number in `ℤ/35ᵏℤ`: every threshold function `t` for the event
that a uniformly random sequence in `ℤ/35ᵏℤ` is good satisfies
`t(k) ≤ n exp[(3 lg 5 lg 7 lg k)^{1/3} - (2/3) lg lg k + O(1)]`, with `lg = log₂`.

`n = k^2`, the prefactor `k^d` of Theorem 4 at `d = 2` (`ℤ/35ᵏℤ ≅ ℤ/5ᵏℤ × ℤ/7ᵏℤ`; the source
calls the corollary a concrete example of Theorem 4, and Theorem 9 sets `n = k^d`). The `O(1)` is
a constant `C` depending on `t`, the bound holding for all large `k` (thresholds are only
determined up to constant factors, so no single `C` serves every threshold).

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Corollary 2 (`integers-2024-A93-cor-2`). -/
public theorem_wanted zmod_thirtyFive_pow_good_threshold_le (t : ℕ → ℝ)
    (ht : IsThresholdFunction (fun k s => goodSequenceProb (ZMod (35 ^ k)) s) t) :
    ∃ C : ℝ, ∀ᶠ k : ℕ in Filter.atTop,
      t k ≤ (k : ℝ) ^ 2 * Real.exp ((3 * Real.logb 2 5 * Real.logb 2 7 * Real.logb 2 k) ^
          ((1 : ℝ) / 3) - 2 / 3 * Real.logb 2 (Real.logb 2 k) + C)

end

end MetaMathlibExt
