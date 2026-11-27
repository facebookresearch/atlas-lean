/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Data.Nat.Pairing
import Mathlib.Topology.MetricSpace.PiNat

/-!
# Mazur and Orlicz's Scottish Book Problem 26

`foBoundedUniformNeighborhood_continuous_refuted` answers Mazur and Orlicz's Problem 26 in the
negative: their claim, about continuous linear functionals
(`ScottishBookProblem26ContinuousClaim`), is false. `foBoundedUniformNeighborhood_refuted`
follows for the formally stronger variant about all linear functionals
(`ScottishBookProblem26Claim`).

A closed subspace of a countable product of Banach spaces provides a sequence of continuous linear
functionals converging uniformly to zero on bounded sets but on no neighborhood of zero.
Partition the entries of a bounded sequence into infinite blocks indexed by `k`. In addition
to the supremum norm, control the entries in each block with the weight `n + 1` at index `n`.
The functionals evaluate entry `n` and divide by `k + 1` for the block containing it.
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook26Wanted

/-- **Spaces of type (F) in Scottish Book Problem 26.** A real vector space $E$ with a topology
is of type (F) if there is a metric $d$ on $E$ that induces its topology, is translation
invariant, $d(x + z, y + z) = d(x, y)$ for all $x, y, z \in E$, and is complete, and if
addition $E \times E \to E$ and scalar multiplication $\mathbb{R} \times E \to E$ are
continuous. -/
def IsTypeF (E : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] : Prop :=
  ∃ d : E → E → ℝ, (∀ x y, 0 ≤ d x y) ∧ (∀ x y, d x y = 0 ↔ x = y) ∧
    (∀ x y, d x y = d y x) ∧ (∀ x y z, d x z ≤ d x y + d y z) ∧
    (∀ x y z, d (x + z) (y + z) = d x y) ∧
    (∀ U : Set E, IsOpen U ↔ ∀ x ∈ U, ∃ ε > 0, ∀ y, d y x < ε → y ∈ U) ∧
    (∀ x : ℕ → E, (∀ ε > 0, ∃ N, ∀ m n, m ≥ N → n ≥ N → d (x m) (x n) < ε) →
      ∃ y, ∀ ε > 0, ∃ N, ∀ n, n ≥ N → d (x n) y < ε) ∧
    Continuous (fun p : E × E => p.1 + p.2) ∧ Continuous fun p : ℝ × E => p.1 • p.2

/-- **Bounded sets in Scottish Book Problem 26.** Let $E$ be a real vector space with a topology.
A set $R \subseteq E$ is bounded if for every sequence $(x_n)_{n \ge 0}$ of points of $R$ and
every real sequence $(t_n)_{n \ge 0}$ with $t_n \to 0$, we have $t_n x_n \to 0$ in $E$.

This sequential definition is the one printed in the problem statement. -/
def IsBoundedSet (E : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (R : Set E) : Prop :=
  ∀ (x : ℕ → E) (t : ℕ → ℝ), (∀ n, x n ∈ R) →
    Filter.Tendsto t Filter.atTop (nhds 0) →
    Filter.Tendsto (fun n => t n • x n) Filter.atTop (nhds 0)

/-- **Spaces of type $\{F_o\}$.** A real vector space $E$ with a topology is of type $\{F_o\}$ if
it is of type (F) and, for every sequence $(x_n)_{n \ge 0}$ in $E$ with $x_n \to 0$ and every
real sequence $(t_n)_{n \ge 0}$ with $\sum_n |t_n| < \infty$, the series $\sum_n t_n x_n$
converges in $E$. -/
def IsTypeFo (E : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] : Prop :=
  IsTypeF E ∧ ∀ (x : ℕ → E) (t : ℕ → ℝ),
    Filter.Tendsto x Filter.atTop (nhds 0) → Summable (fun n => |t n|) →
    ∃ y, Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, t n • x n)
      Filter.atTop (nhds y)

/-- **Scottish Book Problem 26 for all linear functionals.** The claim that for every real vector
space $E$ with a topology that is of type $\{F_o\}$ and every sequence $(F_n)_{n \ge 0}$ of
linear functionals $E \to \mathbb{R}$, if $F_n \to 0$ uniformly on every bounded set
$R \subseteq E$, then there is an open set $U \subseteq E$ containing $0$ on which
$F_n \to 0$ uniformly.

Here $F_n \to 0$ uniformly on a set $S$ means that for every $\varepsilon > 0$ there is $N$
with $|F_n(x)| < \varepsilon$ for all $n \ge N$ and all $x \in S$. The $F_n$ are only assumed
linear, not continuous, so this claim is formally stronger than Mazur and Orlicz's claim
(`ScottishBookProblem26ContinuousClaim`), whose functionals are continuous. -/
def ScottishBookProblem26Claim : Prop :=
  ∀ (E : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E],
    IsTypeFo E →
    ∀ (F : ℕ → E →ₗ[ℝ] ℝ),
      (∀ R : Set E, IsBoundedSet E R →
        ∀ ε > 0, ∃ N, ∀ n, n ≥ N → ∀ x ∈ R, |F n x| < ε) →
      ∃ U : Set E, IsOpen U ∧ (0 : E) ∈ U ∧
        ∀ ε > 0, ∃ N, ∀ n, n ≥ N → ∀ x ∈ U, |F n x| < ε

/-- **Scottish Book Problem 26 (Mazur and Orlicz's claim).** The claim that for every real vector
space $E$ with a topology that is of type $\{F_o\}$ and every sequence $(F_n)_{n \ge 0}$ of
continuous linear functionals $E \to \mathbb{R}$, if $F_n \to 0$ uniformly on every bounded set
$R \subseteq E$, then there is an open set $U \subseteq E$ containing $0$ on which
$F_n \to 0$ uniformly.

Here $F_n \to 0$ uniformly on a set $S$ means that for every $\varepsilon > 0$ there is $N$
with $|F_n(x)| < \varepsilon$ for all $n \ge N$ and all $x \in S$. The source's linear
functionals are read as continuous; dropping continuity gives the formally stronger claim
`ScottishBookProblem26Claim`.

Source: S. Mazur and W. Orlicz, Problem 26 of the Scottish Book (prize: one small beer);
S. M. Ulam, *The Scottish Book*, Los Alamos report LA-6832 (1977), Problem 26, p. 8. -/
def ScottishBookProblem26ContinuousClaim : Prop :=
  ∀ (E : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E],
    IsTypeFo E →
    ∀ (F : ℕ → E →L[ℝ] ℝ),
      (∀ R : Set E, IsBoundedSet E R →
        ∀ ε > 0, ∃ N, ∀ n, n ≥ N → ∀ x ∈ R, |F n x| < ε) →
      ∃ U : Set E, IsOpen U ∧ (0 : E) ∈ U ∧
        ∀ ε > 0, ∃ N, ∀ n, n ≥ N → ∀ x ∈ U, |F n x| < ε

noncomputable section

open Filter Topology

private abbrev Row := lp (fun _ : ℕ => ℝ) ⊤

private def block (n : ℕ) : ℕ := n.unpair.1

/-- Row zero stores the original sequence. Row `block n + 1` controls its `n`th entry
with the stronger weight `n + 1`. -/
private def space : Submodule ℝ (ℕ → Row) where
  carrier := {x | ∀ n, x (block n + 1) n = (n + 1 : ℝ) * x 0 n}
  zero_mem' := by simp
  add_mem' {x y} hx hy n := by
    change x _ n + y _ n = _ * (x 0 n + y 0 n)
    rw [hx n, hy n, mul_add]
  smul_mem' c x hx n := by
    change c * x _ n = _ * (c * x 0 n)
    rw [hx n, mul_left_comm]

private theorem space_closed : IsClosed (space : Set (ℕ → Row)) := by
  change IsClosed {x : ℕ → Row | ∀ n, x (block n + 1) n = (n + 1 : ℝ) * x 0 n}
  rw [Set.ofPred_forall]
  have h (i n : ℕ) : Continuous (fun x : ℕ → Row => x i n) :=
    (lp.evalCLM ℝ _ ⊤ n).continuous.comp (continuous_apply i)
  exact isClosed_iInter fun n => isClosed_eq (h _ _) (continuous_const.mul (h _ _))

private def proj (i : ℕ) : space →L[ℝ] Row :=
  (ContinuousLinearMap.proj i).comp space.subtypeL

open scoped PiCountable in
private theorem space_typeF : IsTypeF space := by
  let : MetricSpace (ℕ → Row) := PiCountable.metricSpace
  let : CompleteSpace space := space_closed.isComplete.completeSpace_coe
  refine ⟨dist, fun _ _ => dist_nonneg, fun _ _ => dist_eq_zero, dist_comm, dist_triangle,
    ?_, ?_, ?_, continuous_add, continuous_smul⟩
  · intro x y z
    change dist (x.val + z.val) (y.val + z.val) = dist x.val y.val
    simp only [PiCountable.dist_eq_tsum, Pi.add_apply, dist_add_right]
  · intro U
    simpa only [Set.subset_def, Metric.mem_ball] using (Metric.isOpen_iff (s := U))
  · intro x hx
    have hc : CauchySeq x := Metric.cauchySeq_iff.mpr fun ε hε => by
      obtain ⟨N, hN⟩ := hx ε hε
      exact ⟨N, fun m hm n hn => hN m n hm hn⟩
    obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hc
    exact ⟨y, Metric.tendsto_atTop.mp hy⟩

private theorem space_typeFo : IsTypeFo space := by
  refine ⟨space_typeF, ?_⟩
  intro x t hx ht
  have hs : Summable (fun n => t n • (x n).val) := by
    apply Pi.summable.mpr
    intro i
    apply Summable.of_norm_bounded_eventually_nat ht
    have hi := ((proj i).continuous.tendsto 0).comp hx
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hi 1 zero_lt_one
    filter_upwards [eventually_ge_atTop N] with n hn
    have h : ‖(x n).val i‖ < 1 := by simpa [proj, dist_zero_right] using hN n hn
    change ‖t n • (x n).val i‖ ≤ |t n|
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) h.le
  obtain ⟨y, hy⟩ := hs
  have hlim := hy.tendsto_sum_nat
  have hmem : ∀ N, (∑ n ∈ Finset.range N, t n • (x n).val) ∈ space :=
    fun N => space.sum_mem fun n _ => space.smul_mem _ (x n).property
  refine ⟨⟨y, space_closed.mem_of_tendsto hlim (.of_forall hmem)⟩, tendsto_subtype_rng.mpr ?_⟩
  simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower] using hlim

private theorem row_bounds {R : Set space} (hR : IsBoundedSet space R) (i : ℕ) :
    ∃ C : ℝ, ∀ x ∈ R, ‖x.val i‖ ≤ C := by
  have hb : Bornology.IsVonNBounded ℝ R := by
    apply Bornology.isVonNBounded_of_smul_tendsto_zero
      (l := atTop) (ε := fun n : ℕ => 1 / (n + 1 : ℝ)) (.of_forall fun _ => by positivity)
    exact fun x hx => hR x _ hx tendsto_one_div_add_atTop_nhds_zero_nat
  exact (NormedSpace.image_isVonNBounded_iff ℝ).mp (hb.image (proj i))

private def functional (n : ℕ) : space →L[ℝ] ℝ :=
  (block n + 1 : ℝ)⁻¹ • (lp.evalCLM ℝ _ ⊤ n).comp (proj 0)

private theorem abs_functional (n : ℕ) (x : space) :
    |functional n x| = |x.val 0 n| / (block n + 1 : ℝ) := by
  change |(block n + 1 : ℝ)⁻¹ * x.val 0 n| = _
  rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < block n + 1), div_eq_inv_mul]

private theorem uniform_on_bounded (R : Set space) (hR : IsBoundedSet space R) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x ∈ R, |functional n x| < ε := by
  intro ε hε
  choose C hC using row_bounds hR
  obtain ⟨K, hK⟩ := exists_nat_gt (C 0 / ε)
  let B := ∑ i ∈ Finset.range K, |C (i + 1)|
  obtain ⟨N, hN⟩ := exists_nat_gt (B / ε)
  refine ⟨N, fun n hn x hx => ?_⟩
  have heval (i : ℕ) : |x.val i n| ≤ C i :=
    (lp.norm_apply_le_norm ENNReal.top_ne_zero (x.val i) n).trans (hC i x hx)
  rw [abs_functional]
  by_cases hk : K ≤ block n
  · -- The global bound suffices on the high blocks.
    apply (div_lt_iff₀' (by positivity)).mpr
    exact (heval 0).trans_lt (((div_lt_iff₀ hε).mp hK).trans_le
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ_of_le hk) hε.le))
  · -- On the finitely many low blocks, use the stronger weight in the corresponding row.
    have hB : C (block n + 1) ≤ B :=
      (le_abs_self _).trans (Finset.single_le_sum (fun i _ => abs_nonneg (C (i + 1)))
        (Finset.mem_range.mpr (lt_of_not_ge hk)))
    have hweight : (n + 1 : ℝ) * |x.val 0 n| ≤ B := by
      have h := (heval (block n + 1)).trans hB
      rwa [x.property n, abs_mul, abs_of_pos (by positivity : 0 < (n + 1 : ℝ))] at h
    have hlt : B < (n + 1 : ℝ) * ε :=
      ((div_lt_iff₀ hε).mp hN).trans_le
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ_of_le hn) hε.le)
    have hden : (1 : ℝ) ≤ block n + 1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
    exact (div_le_self (abs_nonneg _) hden).trans_lt
      (lt_of_mul_lt_mul_left (hweight.trans_lt hlt) (by positivity))

/-- A spike at entry `n` is supported on the two rows that control this entry. -/
private def spike (n : ℕ) (a : ℝ) : space :=
  ⟨fun i => if i = 0 then lp.single ⊤ n a
    else if i = block n + 1 then lp.single ⊤ n ((n + 1 : ℝ) * a) else 0, by
    intro j
    dsimp only
    by_cases h : j = n
    · subst j
      simp
    · by_cases hb : block j = block n <;> simp [hb, h, Pi.single_eq_of_ne]⟩

private theorem spikes_tendsto (m : ℕ → ℕ) :
    Tendsto (fun k => spike (Nat.pair k (m k)) (1 / (k + 1 : ℝ))) atTop (𝓝 0) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro i
  cases i with
  | zero =>
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa (disch := positivity) [spike, lp.norm_single ENNReal.zero_lt_top, Real.norm_eq_abs,
      abs_of_pos] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  | succ i =>
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop i] with k hk
    simp [spike, block, hk.ne]

/--
**Mazur and Orlicz's Problem 26 has a negative answer.** The claim of Scottish Book Problem 26
is false: there are a real vector space $E$ with a topology, of type $\{F_o\}$, and a sequence
$(F_n)_{n \ge 0}$ of continuous linear functionals $E \to \mathbb{R}$ that converges to $0$
uniformly on every bounded subset of $E$ but does not converge to $0$ uniformly on any open set
containing $0$.

Source: S. Mazur and W. Orlicz, Problem 26 of the Scottish Book (prize: one small beer);
S. M. Ulam, *The Scottish Book*, Los Alamos report LA-6832 (1977), Problem 26, p. 8, which
records the answer "Ad 26. The answer is negative." (M. Eidelheit, June 4, 1938).
-/
theorem foBoundedUniformNeighborhood_continuous_refuted :
    ¬ ScottishBookProblem26ContinuousClaim := by
  intro claim
  obtain ⟨U, hU, h0, hu⟩ := claim space space_typeFo functional uniform_on_bounded
  let a (k : ℕ) : ℝ := 1 / (k + 1 : ℝ)
  have ha (k : ℕ) : 0 < a k := by
    dsimp [a]
    positivity
  -- Choose a spike beyond the cutoff for each block. Eventually these spikes lie in U.
  choose N hN using fun k => hu (a k / (k + 1 : ℝ)) (div_pos (ha k) (by positivity))
  obtain ⟨k, hk⟩ := ((spikes_tendsto N).eventually_mem (hU.mem_nhds h0)).exists
  have h := hN k (Nat.pair k (N k)) (Nat.right_le_pair ..) _ hk
  rw [abs_functional] at h
  simp (disch := positivity) [spike, block, a, abs_of_pos] at h

/--
**Problem 26 for all linear functionals has a negative answer.** The variant of Scottish Book
Problem 26 for all linear functionals (`ScottishBookProblem26Claim`), formally stronger than
Mazur and Orlicz's claim because its functionals need not be continuous, is false: there are a
real vector space $E$ with a topology, of type $\{F_o\}$, and a sequence $(F_n)_{n \ge 0}$ of
linear functionals $E \to \mathbb{R}$ that converges to $0$ uniformly on every bounded subset of
$E$ but does not converge to $0$ uniformly on any open set containing $0$. This is weaker than,
and follows from, the negative answer to Mazur and Orlicz's problem
(`foBoundedUniformNeighborhood_continuous_refuted`).

Source: S. Mazur and
W. Orlicz, Problem 26 of the Scottish Book (prize: one small beer); S. M. Ulam,
*The Scottish Book*, Los Alamos report LA-6832 (1977), Problem 26, p. 8, which records the
answer "Ad 26. The answer is negative." (M. Eidelheit, June 4, 1938).
-/
theorem foBoundedUniformNeighborhood_refuted : ¬ ScottishBookProblem26Claim :=
  -- Continuous linear maps are linear maps, so the claim for all linear maps covers them.
  fun claim => foBoundedUniformNeighborhood_continuous_refuted fun E _ _ _ hE F hF =>
    claim E hE (fun n => (F n).toLinearMap) hF

end
end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook26Wanted
