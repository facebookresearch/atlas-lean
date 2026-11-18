/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.NoRegretDynamics
public import MathlibExt.GameTheory.PotentialGame
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

/-! # Correlated equilibria and conditional regrets

We use the cost form of finite strategic games of `NoRegretDynamics` and `PotentialGame`
(players `ι`, finite strategy sets `S i`, costs `cost i s`, minimised); Hart and Mas-Colell
write payoffs `uⁱ = -cost i`. A probability distribution `ψ` on profiles (`IsDistribution`) is
an `ε`-*correlated equilibrium* (Aumann 1974) when, for every player `i` and every pair of
strategies `j, k` of `i`,
`∑_{s : sᵢ = j} ψ(s) (cost i s − cost i (k, s₋ᵢ)) ≤ ε`:
a player told by a referee to play `j` cannot gain more than `ε` (in total over the event
`{sᵢ = j}`) by playing `k` instead (Hart and Mas-Colell 2000, §2, Definition).

## Main results

* `IsCorrelatedEq.isCoarseCorrelatedEq`: correlated equilibria are coarse correlated
  equilibria (the Hannan set of Hart 2005, §10.1).
* `isCorrelatedEq_dirac`, `isCorrelatedEq_productDist`: pure Nash equilibria (as point
  masses) and mixed Nash equilibria (as product distributions) are correlated equilibria;
  `isCorrelatedEq_productDist_iff`: conversely, product correlated equilibria are Nash.
* `convex_setOf_isCorrelatedEq`, `isCompact_setOf_isCorrelatedEq`: the set of correlated
  `ε`-equilibria is convex and compact (a polytope: it is cut out of the simplex by finitely
  many linear inequalities).
* `condRegret_div_eq`: conditional regrets are linear functionals of the empirical
  distribution of play (Hart and Mas-Colell 2000, Proof of the Proposition in §3).
* `isCorrelatedEq_empirical_iff`: the empirical distribution of `T ≥ 1` rounds is a
  correlated `ε`-equilibrium iff all conditional regrets are at most `T ε` (the finite-horizon
  form of that Proposition).
* `sum_mul_sub_eq_zero_of_isRegretInvariant`: the algebraic core of Theorem A of Hart and
  Mas-Colell 2000: for a regret-invariant mixed action the Blackwell condition (3.3) holds
  with equality.
* `chickenCE_isCorrelatedEq`, `chickenCE_not_product`: Aumann's correlated equilibrium of
  Chicken (Hart 2005, Figure 3), which is not a product distribution.

## References

* S. Hart and A. Mas-Colell, "A simple adaptive procedure leading to correlated equilibrium",
  Econometrica 68(5) (2000), 1127–1150: §2 (Definition, (2.1b), (2.3)), §3 ((3.1), (3.3),
  Theorem A, Proposition).
* S. Hart, "Adaptive heuristics", Econometrica 73(5) (2005), 1401–1430: §6 (equation (6),
  Figure 3), §10.1, §10.2 (equation (12)).
* R. J. Aumann, "Subjectivity and correlation in randomized strategies", J. Math. Econom. 1
  (1974), 67–96.
-/

namespace MathlibExt.GameTheory.CorrelatedEquilibrium

open Finset
open MathlibExt.GameTheory.NoRegretDynamics (IsDistribution IsCoarseCorrelatedEq empirical
  sum_empirical_mul isDistribution_empirical)
open MathlibExt.GameTheory.PotentialGame (IsPureNash)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]
  [∀ i, DecidableEq (S i)]

/-- The gain of player `i` at profile `s` from playing `k` whenever told to play `j`: the cost
saving `cost i s − cost i (k, s₋ᵢ)` if `sᵢ = j`, and `0` otherwise. In payoff form this is
the bracket of Hart and Mas-Colell 2000, §2, Definition, and of (2.1a–b). -/
def switchGain (cost : ι → (∀ i, S i) → ℝ) (i : ι) (j k : S i) (s : ∀ i, S i) : ℝ :=
  if s i = j then cost i s - cost i (Function.update s i k) else 0

/-- **Correlated equilibrium** (Aumann 1974; Hart and Mas-Colell 2000, §2, Definition, in cost
form). A distribution `ψ` on profiles is a correlated `ε`-equilibrium when for every player `i`
and strategies `j, k` of `i`, `∑_{s : sᵢ = j} ψ(s) (cost i s − cost i (k, s₋ᵢ)) ≤ ε`; the case
`ε = 0` is a correlated equilibrium. -/
def IsCorrelatedEq (cost : ι → (∀ i, S i) → ℝ) (ψ : (∀ i, S i) → ℝ) (ε : ℝ) : Prop :=
  IsDistribution ψ ∧ ∀ i (j k : S i), ∑ s, ψ s * switchGain cost i j k s ≤ ε

omit [Fintype ι] in
/-- The correlated-equilibrium sum restricted to the event `{sᵢ = j}`, as in the Definition of
Hart and Mas-Colell 2000, §2. -/
theorem sum_mul_switchGain [Fintype ι] (cost : ι → (∀ i, S i) → ℝ) (ψ : (∀ i, S i) → ℝ) (i : ι)
    (j k : S i) :
    ∑ s, ψ s * switchGain cost i j k s =
      ∑ s ∈ univ.filter (fun s => s i = j),
        ψ s * (cost i s - cost i (Function.update s i k)) := by
  rw [sum_filter]
  refine sum_congr rfl fun s _ => ?_
  unfold switchGain
  split_ifs <;> simp

/-- **Correlated equilibria are coarse correlated equilibria.** Summing the correlated
equilibrium inequalities over the recommended strategy `j` gives the coarse (Hannan)
inequality for the fixed deviation `k`, with error `|Sᵢ| ε`. With `ε = δ = 0`: every
correlated equilibrium lies in the Hannan set (Hart 2005, §10.1). -/
theorem IsCorrelatedEq.isCoarseCorrelatedEq {cost : ι → (∀ i, S i) → ℝ}
    {ψ : (∀ i, S i) → ℝ} {ε δ : ℝ} (h : IsCorrelatedEq cost ψ ε)
    (hδ : ∀ i, (Fintype.card (S i) : ℝ) * ε ≤ δ) : IsCoarseCorrelatedEq cost ψ δ := by
  refine ⟨h.1, fun i k => ?_⟩
  have hsplit : ∑ s, ψ s * (cost i s - cost i (Function.update s i k)) =
      ∑ j : S i, ∑ s, ψ s * switchGain cost i j k s := by
    rw [sum_comm]
    refine sum_congr rfl fun s _ => ?_
    rw [← mul_sum]
    congr 1
    simp [switchGain]
  have hle : ∑ j : S i, ∑ s, ψ s * switchGain cost i j k s ≤ Fintype.card (S i) * ε := by
    calc ∑ j : S i, ∑ s, ψ s * switchGain cost i j k s ≤ ∑ _j : S i, ε :=
          sum_le_sum fun j _ => h.2 i j k
      _ = _ := by simp
  have := hδ i
  have hsub : ∑ s, ψ s * (cost i s - cost i (Function.update s i k)) =
      ∑ s, ψ s * cost i s - ∑ s, ψ s * cost i (Function.update s i k) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun s _ => by ring
  linarith

/-- **A pure Nash equilibrium is a correlated equilibrium.** The point mass at a pure Nash
equilibrium `s₀` (`PotentialGame.IsPureNash`) is a correlated equilibrium (Hart and
Mas-Colell 2000, §2: Nash equilibria are the product correlated equilibria). -/
theorem isCorrelatedEq_dirac {cost : ι → (∀ i, S i) → ℝ} {s₀ : ∀ i, S i}
    (h : IsPureNash cost s₀) :
    IsCorrelatedEq cost (fun s => if s = s₀ then 1 else 0) 0 := by
  refine ⟨⟨fun s => by dsimp only; split_ifs <;> norm_num, by simp⟩, fun i j k => ?_⟩
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]
  unfold switchGain
  split_ifs
  · linarith [h i k]
  · rfl

omit [∀ i, DecidableEq (S i)] in
/-- The set of correlated `ε`-equilibria is convex: it is an intersection of half-spaces
(the distribution constraints and the correlated equilibrium inequalities are linear in
`ψ`). -/
theorem convex_setOf_isCorrelatedEq [∀ i, DecidableEq (S i)] (cost : ι → (∀ i, S i) → ℝ)
    (ε : ℝ) : Convex ℝ {ψ : (∀ i, S i) → ℝ | IsCorrelatedEq cost ψ ε} := by
  intro ψ hψ φ hφ a b ha hb hab
  refine ⟨⟨fun s => ?_, ?_⟩, fun i j k => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hψ.1.1 s, hφ.1.1 s]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum,
      hψ.1.2, hφ.1.2]
    linarith
  · have h1 := hψ.2 i j k
    have h2 := hφ.2 i j k
    have : ∑ s, (a • ψ + b • φ) s * switchGain cost i j k s =
        a * ∑ s, ψ s * switchGain cost i j k s + b * ∑ s, φ s * switchGain cost i j k s := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun s _ => by ring
    rw [this]
    calc _ ≤ a * ε + b * ε :=
          add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
      _ = ε := by rw [← add_mul, hab, one_mul]

/-- The set of correlated `ε`-equilibria is closed. -/
theorem isClosed_setOf_isCorrelatedEq (cost : ι → (∀ i, S i) → ℝ) (ε : ℝ) :
    IsClosed {ψ : (∀ i, S i) → ℝ | IsCorrelatedEq cost ψ ε} := by
  have hc : ∀ g : (∀ i, S i) → ℝ, Continuous fun ψ : (∀ i, S i) → ℝ => ∑ s, ψ s * g s :=
    fun g => continuous_finsetSum _ fun s _ => (continuous_apply s).mul continuous_const
  have h1 : IsClosed {ψ : (∀ i, S i) → ℝ | ∀ s, 0 ≤ ψ s} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)
  have h2 : IsClosed {ψ : (∀ i, S i) → ℝ | ∑ s, ψ s = 1} := by
    have := isClosed_eq (hc fun _ => 1) (continuous_const (y := (1 : ℝ)))
    simpa using this
  have h3 : IsClosed {ψ : (∀ i, S i) → ℝ |
      ∀ i (j k : S i), ∑ s, ψ s * switchGain cost i j k s ≤ ε} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun k =>
      isClosed_le (hc _) continuous_const
  have : {ψ : (∀ i, S i) → ℝ | IsCorrelatedEq cost ψ ε} =
      ({ψ | ∀ s, 0 ≤ ψ s} ∩ {ψ | ∑ s, ψ s = 1}) ∩
        {ψ | ∀ i (j k : S i), ∑ s, ψ s * switchGain cost i j k s ≤ ε} := by
    ext ψ; simp [IsCorrelatedEq, IsDistribution, and_assoc]
  rw [this]
  exact (h1.inter h2).inter h3

/-- **The set of correlated `ε`-equilibria is compact** (Hart and Mas-Colell 2000, §2: "the set
of correlated equilibria is nonempty, closed and convex"; p. 1129 calls it a convex polytope).
It is a closed subset of the compact simplex of distributions on profiles. -/
theorem isCompact_setOf_isCorrelatedEq (cost : ι → (∀ i, S i) → ℝ) (ε : ℝ) :
    IsCompact {ψ : (∀ i, S i) → ℝ | IsCorrelatedEq cost ψ ε} := by
  refine (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset
    (isClosed_setOf_isCorrelatedEq cost ε) fun ψ hψ s _ => ⟨hψ.1.1 s, ?_⟩
  calc ψ s = ∑ t ∈ {s}, ψ t := by simp
    _ ≤ ∑ t, ψ t := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun t _ _ => hψ.1.1 t
    _ = 1 := hψ.1.2

/-- The **conditional regret** of player `i` for `j → k` after the rounds `play`: the total
cost saved had `i` played `k` in every round in which it played `j`,
`∑_{t : sᵢ(t) = j} (cost i (s(t)) − cost i (k, s₋ᵢ(t)))`. Divided by `T` this is
`D_T(j, k)` of Hart and Mas-Colell 2000, (2.1b), in cost form. -/
def condRegret (cost : ι → (∀ i, S i) → ℝ) {T : ℕ} (play : Fin T → ∀ i, S i) (i : ι)
    (j k : S i) : ℝ :=
  ∑ t, switchGain cost i j k (play t)

/-- **Conditional regrets are linear in the empirical distribution** (Hart and Mas-Colell 2000,
§3, Proof of the Proposition): `D_T(j, k) = ∑_{s : sᵢ = j} z_T(s) (cost i s − cost i (k, s₋ᵢ))`,
where `z_T` is the empirical distribution of play (2.3). -/
theorem condRegret_div_eq (cost : ι → (∀ i, S i) → ℝ) {T : ℕ} [NeZero T]
    (play : Fin T → ∀ i, S i) (i : ι) (j k : S i) :
    condRegret cost play i j k / T = ∑ s, empirical play s * switchGain cost i j k s := by
  rw [sum_empirical_mul]
  rfl

/-- **No conditional regret characterises correlated equilibria** (finite-horizon form of the
Proposition of Hart and Mas-Colell 2000, §3): after `T ≥ 1` rounds, the empirical distribution
of play is a correlated `ε`-equilibrium if and only if every conditional regret is at most
`T ε`. -/
theorem isCorrelatedEq_empirical_iff {cost : ι → (∀ i, S i) → ℝ} {T : ℕ} [NeZero T]
    (play : Fin T → ∀ i, S i) (ε : ℝ) :
    IsCorrelatedEq cost (empirical play) ε ↔
      ∀ i (j k : S i), condRegret cost play i j k ≤ T * ε := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast NeZero.pos T
  refine ⟨fun h i j k => ?_, fun h => ⟨isDistribution_empirical play, fun i j k => ?_⟩⟩
  · have := h.2 i j k
    rw [← condRegret_div_eq, div_le_iff₀ hT'] at this
    linarith
  · rw [← condRegret_div_eq, div_le_iff₀ hT']
    linarith [h i j k]

/-- `q` is **regret-invariant** for the matrix `λ` of (nonnegative) regrets `λ j k` of one
player: for every strategy `j`, the regret flowing into `j` equals the regret flowing out of `j`,
`∑ₖ q(k) λ(k, j) = q(j) ∑ₖ λ(j, k)` (Hart and Mas-Colell 2000, (3.1); Hart 2005, (12)). -/
def IsRegretInvariant {A : Type*} [Fintype A] (lam : A → A → ℝ) (q : A → ℝ) : Prop :=
  ∀ j, ∑ k, q k * lam k j = q j * ∑ k, lam j k

/-- **Blackwell's condition for regret-invariant play** (the algebraic core of the proof of
Theorem A in Hart and Mas-Colell 2000, §3). If the mixed action `q` is regret-invariant for `λ`,
then for every payoff vector `g` (in the paper `g = uⁱ(·, s⁻ⁱ)` for an arbitrary opponents'
profile) the left side of (3.3) vanishes: `∑_{j,k} λ(j, k) q(j) (g(k) − g(j)) = 0`. Hence the
nonpositive orthant of regret vectors is approachable with these strategies. -/
theorem sum_mul_sub_eq_zero_of_isRegretInvariant {A : Type*} [Fintype A] {lam : A → A → ℝ}
    {q : A → ℝ} (h : IsRegretInvariant lam q) (g : A → ℝ) :
    ∑ j, ∑ k, lam j k * q j * (g k - g j) = 0 := by
  have h1 : ∑ j, ∑ k, lam j k * q j * g k = ∑ k, g k * (q k * ∑ j, lam k j) := by
    rw [sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [← h k, mul_sum]
    exact sum_congr rfl fun j _ => by ring
  have h2 : ∑ j, ∑ k, lam j k * q j * g j = ∑ j, g j * (q j * ∑ k, lam j k) := by
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum, mul_sum]
    exact sum_congr rfl fun k _ => by ring
  simp only [mul_sub, sum_sub_distrib, h1, h2, sub_self]

/-! ### Nash equilibria are correlated equilibria -/

/-- The **product distribution** `s ↦ ∏ᵢ σᵢ(sᵢ)` of independent mixed strategies `σᵢ`. -/
def productDist (σ : ∀ i, S i → ℝ) (s : ∀ i, S i) : ℝ :=
  ∏ i, σ i (s i)

/-- The weight `∏_{l ≠ i} σₗ(sₗ)` of the opponents' part `s₋ᵢ` of a profile. -/
def othersWeight (σ : ∀ i, S i → ℝ) (i : ι) (s : ∀ i, S i) : ℝ :=
  ∏ l ∈ univ.erase i, σ l (s l)

/-- The expected cost `∑_{s₋ᵢ} (∏_{l ≠ i} σₗ(sₗ)) cost i (a, s₋ᵢ)` of the pure strategy `a`
of player `i` against the mixed strategies `σₗ` of the others. -/
def pureCost (cost : ι → (∀ i, S i) → ℝ) (σ : ∀ i, S i → ℝ) (i : ι) (a : S i) : ℝ :=
  ∑ s, (if s i = a then othersWeight σ i s * cost i s else 0)

omit [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
/-- The product weight splits as `σᵢ(sᵢ) · ∏_{l ≠ i} σₗ(sₗ)`. -/
theorem productDist_eq_mul (σ : ∀ i, S i → ℝ) (i : ι) (s : ∀ i, S i) :
    productDist σ s = σ i (s i) * othersWeight σ i s :=
  (mul_prod_erase univ (fun l => σ l (s l)) (mem_univ i)).symm

omit [Fintype ι] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
/-- The opponents' weight does not depend on player `i`'s own coordinate. -/
theorem othersWeight_update [Fintype ι] (σ : ∀ i, S i → ℝ) (i : ι) (s : ∀ i, S i) (a : S i) :
    othersWeight σ i (Function.update s i a) = othersWeight σ i s :=
  prod_congr rfl fun l hl => by rw [Function.update_of_ne (ne_of_mem_erase hl)]

/-- Moving the event `{sᵢ = j}` to `{sᵢ = k}` by changing player `i`'s coordinate. -/
theorem sum_ite_update (i : ι) (j k : S i) (f : (∀ i, S i) → ℝ) :
    ∑ s, (if s i = j then f (Function.update s i k) else 0) =
      ∑ s, (if s i = k then f s else 0) := by
  rw [← sum_filter, ← sum_filter]
  refine sum_nbij' (fun s => Function.update s i k) (fun s => Function.update s i j)
    (fun s _ => by simp) (fun s _ => by simp) (fun s hs => ?_) (fun s hs => ?_)
    (fun s _ => rfl)
  · have hs : s i = j := (mem_filter.1 hs).2
    rw [Function.update_idem, ← hs, Function.update_eq_self]
  · have hs : s i = k := (mem_filter.1 hs).2
    rw [Function.update_idem, ← hs, Function.update_eq_self]

omit [∀ i, DecidableEq (S i)] in
/-- The product distribution of mixed strategies is a distribution. -/
theorem isDistribution_productDist {σ : ∀ i, S i → ℝ} (hσ0 : ∀ i a, 0 ≤ σ i a)
    (hσ1 : ∀ i, ∑ a, σ i a = 1) : IsDistribution (productDist σ) := by
  refine ⟨fun s => prod_nonneg fun i _ => hσ0 i (s i), ?_⟩
  have := prod_univ_sum (fun i => (univ : Finset (S i))) σ
  simp only [hσ1, prod_const_one, Fintype.piFinset_univ] at this
  exact this.symm

/-- In the product distribution, player `i`'s expected cost is the `σᵢ`-average of the costs of
its pure strategies. -/
theorem sum_productDist_mul (cost : ι → (∀ i, S i) → ℝ) (σ : ∀ i, S i → ℝ) (i : ι) :
    ∑ s, productDist σ s * cost i s = ∑ a, σ i a * pureCost cost σ i a := by
  simp only [pureCost, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  rw [productDist_eq_mul σ i s]
  simp only [mul_ite, mul_zero, sum_ite_eq, mem_univ, ite_true]
  ring

/-- The correlated-equilibrium sum of a product distribution:
`∑_{s : sᵢ = j} ψ(s) (cost i s − cost i (k, s₋ᵢ)) = σᵢ(j) (c(j) − c(k))`, with `c` the pure
expected costs against the others' mixed strategies. -/
theorem sum_productDist_mul_switchGain (cost : ι → (∀ i, S i) → ℝ) (σ : ∀ i, S i → ℝ) (i : ι)
    (j k : S i) :
    ∑ s, productDist σ s * switchGain cost i j k s =
      σ i j * (pureCost cost σ i j - pureCost cost σ i k) := by
  have h1 : ∑ s, productDist σ s * switchGain cost i j k s =
      σ i j * (∑ s, (if s i = j then othersWeight σ i s * cost i s else 0) -
        ∑ s, (if s i = j then (othersWeight σ i (Function.update s i k) *
          cost i (Function.update s i k)) else 0)) := by
    rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun s _ => ?_
    rw [productDist_eq_mul σ i s, othersWeight_update]
    unfold switchGain
    split_ifs with h
    · rw [h]; ring
    · simp
  rw [h1, sum_ite_update i j k (fun s => othersWeight σ i s * cost i s)]
  rfl

/-- **Nash equilibria are correlated equilibria** (Hart and Mas-Colell 2000, §2: "every Nash
equilibrium is a correlated equilibrium"; Hart 2005, §6). If independent mixed strategies `σᵢ`
form a Nash equilibrium, in the sense that no player lowers its expected cost by switching to a
pure strategy, their product distribution is a correlated equilibrium. -/
theorem isCorrelatedEq_productDist {cost : ι → (∀ i, S i) → ℝ} {σ : ∀ i, S i → ℝ}
    (hσ0 : ∀ i a, 0 ≤ σ i a) (hσ1 : ∀ i, ∑ a, σ i a = 1)
    (hnash : ∀ i a, ∑ s, productDist σ s * cost i s ≤ pureCost cost σ i a) :
    IsCorrelatedEq cost (productDist σ) 0 := by
  refine ⟨isDistribution_productDist hσ0 hσ1, fun i j k => ?_⟩
  rw [sum_productDist_mul_switchGain]
  set E := ∑ s, productDist σ s * cost i s
  have hE : E = ∑ a, σ i a * pureCost cost σ i a := sum_productDist_mul cost σ i
  -- every pure strategy in the support of `σᵢ` has expected cost exactly `E`
  have hzero : ∑ a, σ i a * (pureCost cost σ i a - E) = 0 := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hσ1, one_mul, ← hE, sub_self]
  have hj : σ i j * (pureCost cost σ i j - E) = 0 :=
    (sum_eq_zero_iff_of_nonneg fun a _ =>
      mul_nonneg (hσ0 i a) (sub_nonneg.2 (hnash i a))).1 hzero j (mem_univ j)
  have hk := hnash i k
  nlinarith [hσ0 i j]

/-- **The product correlated equilibria are the Nash equilibria** (Hart and Mas-Colell 2000, §2:
"Nash equilibria correspond to the special case where ψ is a product measure"). For mixed
strategies `σᵢ`, the product distribution is a correlated equilibrium if and only if no player
can lower its expected cost by switching to a pure strategy. -/
theorem isCorrelatedEq_productDist_iff {cost : ι → (∀ i, S i) → ℝ} {σ : ∀ i, S i → ℝ}
    (hσ0 : ∀ i a, 0 ≤ σ i a) (hσ1 : ∀ i, ∑ a, σ i a = 1) :
    IsCorrelatedEq cost (productDist σ) 0 ↔
      ∀ i a, ∑ s, productDist σ s * cost i s ≤ pureCost cost σ i a := by
  refine ⟨fun h i k => ?_, isCorrelatedEq_productDist hσ0 hσ1⟩
  have hj : ∀ j, σ i j * (pureCost cost σ i j - pureCost cost σ i k) ≤ 0 := fun j => by
    have := h.2 i j k
    rwa [sum_productDist_mul_switchGain] at this
  have hsum : ∑ j, σ i j * (pureCost cost σ i j - pureCost cost σ i k) ≤ 0 :=
    sum_nonpos fun j _ => hj j
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, hσ1, one_mul] at hsum
  rw [sum_productDist_mul]
  linarith

/-! ### Chicken -/

/-- The game of **Chicken** in cost form (Hart 2005, Figure 3): strategy `0` is *leave* and `1`
is *stay*; the payoffs are `(5, 5)` for (leave, leave), `(3, 6)` for (leave, stay), `(6, 3)` for
(stay, leave) and `(0, 0)` for (stay, stay), and costs are their negatives. -/
def chickenCost (i : Fin 2) (s : Fin 2 → Fin 2) : ℝ :=
  -(![![5, 3], ![6, 0]] (s i) (s (1 - i)))

/-- The correlated distribution of Chicken putting probability `1/3` on each profile except
(stay, stay) (Hart 2005, Figure 3). -/
noncomputable def chickenCE (s : Fin 2 → Fin 2) : ℝ :=
  if s 0 = 1 ∧ s 1 = 1 then 0 else 1 / 3

private theorem sum_fin_two_pi (f : (Fin 2 → Fin 2) → ℝ) :
    ∑ s, f s = f ![0, 0] + f ![0, 1] + f ![1, 0] + f ![1, 1] := by
  rw [← (piFinTwoEquiv fun _ => Fin 2).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, piFinTwoEquiv_symm_apply]
  rw [← add_assoc]
  rfl

/-- **Aumann's correlated equilibrium of Chicken** (Hart 2005, §6, Figure 3): the uniform
distribution on (leave, leave), (leave, stay) and (stay, leave) is a correlated equilibrium. -/
theorem chickenCE_isCorrelatedEq : IsCorrelatedEq chickenCost chickenCE 0 := by
  refine ⟨⟨fun s => by unfold chickenCE; split_ifs <;> norm_num, ?_⟩, fun i j k => ?_⟩
  · rw [sum_fin_two_pi]; simp [chickenCE]; norm_num
  · rw [sum_fin_two_pi]
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp [chickenCE, switchGain, chickenCost, Function.update] <;> norm_num

/-- The correlated equilibrium of Chicken is not the product of its marginals: (stay, stay) has
probability `0`, while each player stays with probability `1/3`. So it is not a mixed Nash
equilibrium (Hart 2005, §6). -/
theorem chickenCE_not_product :
    chickenCE ![1, 1] ≠ (chickenCE ![1, 0] + chickenCE ![1, 1]) *
      (chickenCE ![0, 1] + chickenCE ![1, 1]) := by
  simp [chickenCE]

end MathlibExt.GameTheory.CorrelatedEquilibrium
