/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.ComplexBalanced
public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.RateMatrix
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Convex.DoublyStochasticMatrix
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Logic.Relation
public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Semigroup
import MathlibExt.Analysis.Convex.LinearProgrammingDuality
import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Stationary
import MathlibExt.LinearAlgebra.Matrix.Sinkhorn
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Core theorems of systems biology

Six classical results relating network structure to dynamics.

**Stochastic mass action.** For a reaction network (`ReactionNetwork` from
`MathlibExt.Biology.Dynamics.ComplexBalanced`) the stochastic mass-action chain on molecule
counts `x : S → ℕ` fires reaction `r` at rate `λ_r(x) = k_r ∏_s x_s (x_s - 1) ⋯ (x_s - src_s + 1)`
(`propensity`), moving to `x - src r + prod r` (`fire`). If the deterministic system is complex
balanced at `c`, the product-form Poisson weights `π(x) = ∏_s c_s^{x_s} e^{-c_s} / x_s!`
(`poissonWeight`) satisfy global balance, and on every finite set of states closed under the
reactions in both directions they give a stationary law of the restricted chain.

**Metabolic control analysis.** For rates `v_i(e, s) = e_i f_i(s)` and a steady state
`s = σ(e)` of `N v = 0`, the scaled flux control coefficients `C^{J_j}_{e_i}`, concentration
control coefficients `C^{s_m}_{e_i}` and elasticities `ε^{v_i}_{s_m}` obey the summation and
connectivity theorems. A regular steady state exists by the implicit function theorem.

**Flux balance analysis.** FBA is the linear program `max cᵀv` subject to `S v = b`,
`l ≤ v ≤ u`. Its optimum is attained, LP duality holds, the optimal value is concave in `b`,
and the metabolite prices of the optimal dual solutions are exactly its supergradients
(shadow prices).

**Matrix balancing.** A symmetric matrix with positive entries has a unique positive vector
`d` with `diag(d) A diag(d)` doubly stochastic. This balanced matrix is the target of the
iterative correction (ICE) of Hi-C contact maps under the equal-visibility assumption; the
convergence of the iteration itself is not covered.

**Boolean networks.** If the interaction graph of `f : {0,1}ⁿ → {0,1}ⁿ` is acyclic, `f` has a
unique fixed point, reached from every state after `n` synchronous updates.

**Markov chain tree theorem.** The weights `w(r)` of the spanning in-trees rooted at each
state are a left null vector of any matrix with zero row sums; for an irreducible rate matrix
they are positive and every invariant vector is a multiple of them.

## Main results

* `poissonWeight_mul_sum_propensity`: global balance of the Poisson weights at every state
  (all real `k`, `c`); `poissonWeight_vecMul_classGenerator`, `isRateMatrix_classGenerator`,
  `classStationaryLaw_spec`: the normalized weights are a stationary distribution on a finite
  class (Anderson, Craciun & Kurtz 2010, Thm 4.1–4.2, finite case).
* `sum_concControl`, `sum_fluxControl`, `sum_fluxControl_mul_elasticity`: the summation and
  flux connectivity theorems; `exists_isRegularSteadyState`: the steady state continues
  differentiably when the Jacobian is invertible.
* `exists_fbaValue_eq`, `dotProduct_le_fbaDualValue`, `exists_fbaDualValue_eq`,
  `fbaValue_concave`, `exists_optimal_dual_iff_supergradient`.
* `sinkhorn_scaling_unique`, `existsUnique_symmetric_balancing`; `hasTotalSupport_of_balancing`
  (a balanced nonnegative matrix has total support).
* `robert_fixed_point`.
* `treeWeight_vecMul_eq_zero`, `treeWeight_pos`, `eq_smul_treeWeight_of_vecMul_eq_zero`.

## Not covered

Infinite closed classes of the stochastic chain (where normalizability must be shown), the
existence of a complex-balanced `c` (the deficiency-zero theorem, recorded as wanted in
`WantedExt/Biology/Dynamics/DeficiencyZeroWanted.lean`), networks with conservation laws in
metabolic control analysis (singular Jacobian, link matrices), piecewise linearity and
differentiability of the FBA value and the existence of a balancing for nonnegative matrices
with total support (recorded in `WantedExt/Biology/Dynamics/SystemsBiologyWanted.lean`), and
Thomas' rules for Boolean networks with cycles.

## References

* D. F. Anderson, G. Craciun and T. G. Kurtz, "Product-form stationary distributions for
  deficiency zero chemical reaction networks", Bull. Math. Biol. 72 (2010) 1947–1970.
* H. Kacser and J. A. Burns, "The control of flux", Symp. Soc. Exp. Biol. 27 (1973) 65–104.
* R. Heinrich and T. A. Rapoport, "A linear steady-state treatment of enzymatic chains",
  Eur. J. Biochem. 42 (1974) 89–95.
* J. D. Orth, I. Thiele and B. Ø. Palsson, "What is flux balance analysis?", Nat.
  Biotechnol. 28 (2010) 245–248.
* R. Sinkhorn, "A relationship between arbitrary positive matrices and doubly stochastic
  matrices", Ann. Math. Statist. 35 (1964) 876–879.
* R. Sinkhorn and P. Knopp, "Concerning nonnegative matrices and doubly stochastic matrices",
  Pacific J. Math. 21 (1967) 343–348.
* J. Csima and B. N. Datta, "The DAD theorem for symmetric non-negative matrices", J.
  Combin. Theory Ser. A 12 (1972) 147–152.
* M. Imakaev et al., "Iterative correction of Hi-C data reveals hallmarks of chromosome
  organization", Nat. Methods 9 (2012) 999–1003.
* F. Robert, "Iterations sur des ensembles finis et automates cellulaires contractants",
  Linear Algebra Appl. 29 (1980) 393–412.
* E. L. King and C. Altman, "A schematic method of deriving the rate laws for enzyme-catalyzed
  reactions", J. Phys. Chem. 60 (1956) 1375–1378.
* T. L. Hill, "Studies in irreversible thermodynamics IV", J. Theor. Biol. 10 (1966) 442–459.
* V. Anantharam and P. Tsoucas, "A proof of the Markov chain tree theorem", Statist. Probab.
  Lett. 8 (1989) 189–192.
-/

@[expose] public section

open Finset Matrix

namespace MathlibExt.Biology.Dynamics.SystemsBiology

/-! ### Stochastic mass-action kinetics -/

section StochasticMassAction

open MathlibExt.Biology.Dynamics.ComplexBalanced

variable {S ρ : Type*} [Fintype S] [Fintype ρ] (N : ReactionNetwork S ρ)

/-- The stochastic mass-action propensity of reaction `r` in state `x` (molecule counts):
`k r * ∏_s x_s (x_s - 1) ⋯ (x_s - src_s + 1)`, the falling factorial
`Nat.descFactorial x_s src_s` (it vanishes when `x_s < src_s`). Anderson, Craciun & Kurtz
(2010), §2. -/
noncomputable def propensity (k : ρ → ℝ) (r : ρ) (x : S → ℕ) : ℝ :=
  k r * ∏ s, ((x s).descFactorial (N.src r s) : ℝ)

/-- The state reached from `x` by one firing of reaction `r`, `x - src r + prod r`
(meaningful when `src r ≤ x`, the only case in which the propensity is nonzero). -/
def fire (r : ρ) (x : S → ℕ) : S → ℕ := fun s => x s - N.src r s + N.prod r s

/-- The state from which one firing of reaction `r` leads to `x`, `x - prod r + src r`
(meaningful when `prod r ≤ x`). -/
def unfire (r : ρ) (x : S → ℕ) : S → ℕ := fun s => x s - N.prod r s + N.src r s

/-- The product-form Poisson weight `∏_s c_s ^ x_s e^{-c_s} / Nat.factorial x_s` of a
state `x`. -/
noncomputable def poissonWeight (c : S → ℝ) (x : S → ℕ) : ℝ :=
  ∏ s, c s ^ x s * Real.exp (-c s) / ((x s).factorial : ℝ)

/-- The generator of the stochastic mass-action chain restricted to a finite set `Ω` of
states: `Q x y = ∑_r λ_r(x) ([fire r x = y] - [x = y])`. It is a rate matrix when `Ω` is
closed under firing (`isRateMatrix_classGenerator`). -/
noncomputable def classGenerator (k : ρ → ℝ) (Ω : Finset (S → ℕ)) : Matrix Ω Ω ℝ :=
  fun x y => ∑ r, propensity N k r x *
    ((if fire N r x = (y : S → ℕ) then 1 else 0) - if x = y then 1 else 0)

/-- The remaining Poisson factor `∏_s c_s^{x_s - z_s} / Nat.factorial (x_s - z_s)`, zero
unless `z ≤ x`. -/
private noncomputable def residual (c : S → ℝ) (x z : S → ℕ) : ℝ :=
  if z ≤ x then ∏ s, c s ^ (x s - z s) / ((x s - z s).factorial : ℝ) else 0

omit [Fintype ρ] in
/-- The propensity vanishes unless the source complex fits into the state. -/
private theorem propensity_eq_zero {k : ρ → ℝ} {r : ρ} {x : S → ℕ} (h : ¬ N.src r ≤ x) :
    propensity N k r x = 0 := by
  obtain ⟨s, hs⟩ : ∃ s, x s < N.src r s := by
    by_contra h'
    push Not at h'
    exact h h'
  simp only [propensity]
  rw [Finset.prod_eq_zero (Finset.mem_univ s) (by simp [Nat.descFactorial_eq_zero_iff_lt.2 hs]),
    mul_zero]

omit [Fintype ρ] in
/-- The outflow term: `π(x) λ_r(x) = e^{-Σ c} · rate_r(c) · residual c x (src r)`. -/
private theorem poissonWeight_mul_propensity (k : ρ → ℝ) (c : S → ℝ) (r : ρ) (x : S → ℕ) :
    poissonWeight c x * propensity N k r x =
      (∏ s, Real.exp (-c s)) * N.rate k c r * residual c x (N.src r) := by
  by_cases h : N.src r ≤ x
  · simp only [residual, h, ↓reduceIte, ReactionNetwork.rate, poissonWeight, propensity]
    rw [mul_left_comm, ← Finset.prod_mul_distrib]
    have : ∀ s, c s ^ x s * Real.exp (-c s) / ((x s).factorial : ℝ) *
        ((x s).descFactorial (N.src r s) : ℝ) = Real.exp (-c s) * c s ^ N.src r s *
          (c s ^ (x s - N.src r s) / ((x s - N.src r s).factorial : ℝ)) := by
      intro s
      have hs := h s
      have hf : ((x s - N.src r s).factorial : ℝ) * ((x s).descFactorial (N.src r s) : ℝ) =
          ((x s).factorial : ℝ) := by exact_mod_cast Nat.factorial_mul_descFactorial hs
      have hpow : c s ^ x s = c s ^ N.src r s * c s ^ (x s - N.src r s) := by
        rw [← pow_add, Nat.add_sub_cancel' hs]
      have h1 : ((x s - N.src r s).factorial : ℝ) ≠ 0 := by positivity
      have h2 : ((x s).factorial : ℝ) ≠ 0 := by positivity
      have h3 : ((x s).descFactorial (N.src r s) : ℝ) ≠ 0 := by
        exact_mod_cast fun h0 => absurd (Nat.descFactorial_eq_zero_iff_lt.1 h0) (not_lt.2 hs)
      rw [hpow, ← hf]
      field_simp
    simp only [this, Finset.prod_mul_distrib]
    ring
  · rw [propensity_eq_zero N h, mul_zero]
    simp [residual, h]

omit [Fintype S] [Fintype ρ] in
/-- The state `unfire r x` contains the source complex of `r`. -/
private theorem src_le_unfire {r : ρ} {x : S → ℕ} : N.src r ≤ unfire N r x :=
  fun s => by simp [unfire]

omit [Fintype ρ] in
/-- The residual factor of the inflow term. -/
private theorem residual_unfire (c : S → ℝ) {r : ρ} {x : S → ℕ} (h : N.prod r ≤ x) :
    residual c (unfire N r x) (N.src r) = residual c x (N.prod r) := by
  simp only [residual, src_le_unfire N, h, ↓reduceIte]
  refine Finset.prod_congr rfl fun s _ => ?_
  have : unfire N r x s - N.src r s = x s - N.prod r s := by simp [unfire]
  rw [this]

/-- **Global balance of the product-form Poisson weights** (Anderson, Craciun & Kurtz 2010,
Thm 4.1): if `c` is complex balanced for the deterministic mass-action system with rate
constants `k`, then at every state `x` the total outflow `π(x) ∑_r λ_r(x)` equals the total
inflow `∑_{r : prod r ≤ x} π(x - prod r + src r) λ_r(x - prod r + src r)` for
`π = poissonWeight c`. This is an algebraic identity valid for all real `k` and `c`. -/
theorem poissonWeight_mul_sum_propensity {k : ρ → ℝ} {c : S → ℝ}
    (hcb : N.IsComplexBalanced k c) (x : S → ℕ) :
    poissonWeight c x * ∑ r, propensity N k r x =
      ∑ r ∈ univ.filter (fun r => N.prod r ≤ x),
        poissonWeight c (unfire N r x) * propensity N k r (unfire N r x) := by
  rw [Finset.mul_sum, Finset.sum_filter]
  have hin : ∀ r, (if N.prod r ≤ x then
      poissonWeight c (unfire N r x) * propensity N k r (unfire N r x) else 0) =
      (∏ s, Real.exp (-c s)) * (N.rate k c r * residual c x (N.prod r)) := by
    intro r
    split_ifs with h
    · rw [poissonWeight_mul_propensity, residual_unfire N c h, mul_assoc]
    · simp [residual, h]
  rw [Finset.sum_congr rfl fun r _ => hin r]
  simp only [poissonWeight_mul_propensity, mul_assoc, ← Finset.mul_sum]
  rw [N.sum_rate_mul_prod_eq hcb (residual c x)]

/-- The restricted generator is a rate matrix when the rate constants are nonnegative and
`Ω` is closed under the reactions. -/
theorem isRateMatrix_classGenerator {k : ρ → ℝ} (hk : ∀ r, 0 ≤ k r) {Ω : Finset (S → ℕ)}
    (hfwd : ∀ x ∈ Ω, ∀ r, N.src r ≤ x → fire N r x ∈ Ω) :
    ProbabilityTheory.IsRateMatrix (classGenerator N k Ω) := by
  have hlam : ∀ r x, 0 ≤ propensity N k r x := fun r x =>
    mul_nonneg (hk r) (Finset.prod_nonneg fun s _ => Nat.cast_nonneg _)
  refine ⟨fun x y hxy => ?_, fun x => ?_⟩
  · simp only [classGenerator, hxy, ↓reduceIte, sub_zero]
    exact Finset.sum_nonneg fun r _ => mul_nonneg (hlam r x) (by split_ifs <;> norm_num)
  · simp only [classGenerator]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    by_cases h : N.src r ≤ x
    · have hmem := hfwd x x.2 r h
      have h1 : ∑ y : Ω, (if fire N r x = (y : S → ℕ) then (1 : ℝ) else 0) = 1 := by
        rw [Finset.sum_coe_sort Ω (fun y => if fire N r x = y then (1 : ℝ) else 0),
          Finset.sum_ite_eq]
        simp [hmem]
      rw [h1, Finset.sum_ite_eq]
      simp
    · rw [propensity_eq_zero N h, zero_mul]

/-- **Anderson–Craciun–Kurtz on a finite class** (Anderson, Craciun & Kurtz 2010,
Thm 4.1–4.2): if `c` is complex balanced and every state of `Ω` from which a reaction leads
into `Ω` lies in `Ω` (`hbwd`), the Poisson weights restricted to `Ω` are invariant for the
restricted generator: `π Q = 0`, for all real `k` and `c`. For a closed communicating class of
a weakly reversible network with positive rate constants `hbwd` holds (the reverse reaction
path leads back); that implication is not formalized here. -/
theorem poissonWeight_vecMul_classGenerator {k : ρ → ℝ} {c : S → ℝ}
    (hcb : N.IsComplexBalanced k c) {Ω : Finset (S → ℕ)}
    (hbwd : ∀ x ∈ Ω, ∀ r, N.prod r ≤ x → unfire N r x ∈ Ω) :
    (fun x : Ω => poissonWeight c x) ᵥ* classGenerator N k Ω = 0 := by
  funext y
  simp only [Matrix.vecMul, dotProduct, classGenerator, Finset.mul_sum, Pi.zero_apply]
  rw [Finset.sum_comm]
  simp only [mul_sub, Finset.sum_sub_distrib]
  -- inflow through reaction `r`
  have hin : ∀ r, ∑ x : Ω, poissonWeight c x * (propensity N k r x *
      (if fire N r x = (y : S → ℕ) then 1 else 0)) =
      if N.prod r ≤ y then poissonWeight c (unfire N r y) * propensity N k r (unfire N r y)
      else 0 := by
    intro r
    have hpt : ∀ x : Ω, poissonWeight c x * (propensity N k r x *
        (if fire N r x = (y : S → ℕ) then 1 else 0)) =
        if (x : S → ℕ) = unfire N r y ∧ N.prod r ≤ y then
          poissonWeight c (unfire N r y) * propensity N k r (unfire N r y) else 0 := by
      intro x
      by_cases hs : N.src r ≤ x
      · have hiff : fire N r x = (y : S → ℕ) ↔ (x : S → ℕ) = unfire N r y ∧ N.prod r ≤ y := by
          constructor
          · intro hf
            refine ⟨funext fun s => ?_, fun s => ?_⟩
            · have h1 := congrFun hf s
              have h2 : N.src r s ≤ (x : S → ℕ) s := hs s
              simp only [unfire, fire] at h1 ⊢
              omega
            · have h1 := congrFun hf s
              simp only [fire] at h1
              change N.prod r s ≤ (y : S → ℕ) s
              omega
          · rintro ⟨hx, hp⟩
            funext s
            have h1 := congrFun hx s
            have h2 : N.prod r s ≤ (y : S → ℕ) s := hp s
            simp only [unfire, fire] at h1 ⊢
            omega
        by_cases hc : (x : S → ℕ) = unfire N r y ∧ N.prod r ≤ y
        · have hf := hiff.2 hc
          rw [hc.1] at hf
          simp only [hc, hf, ↓reduceIte, mul_one, and_self]
        · have hnf : ¬ fire N r x = (y : S → ℕ) := fun h => hc (hiff.1 h)
          simp only [hnf, hc, ↓reduceIte, mul_zero]
      · rw [propensity_eq_zero N hs, zero_mul, mul_zero]
        split_ifs with hc
        · exact absurd (hc.1 ▸ src_le_unfire N) hs
        · rfl
    rw [Finset.sum_congr rfl fun x _ => hpt x]
    rw [Finset.sum_coe_sort Ω (fun x => if x = unfire N r y ∧ N.prod r ≤ y then
      poissonWeight c (unfire N r y) * propensity N k r (unfire N r y) else 0)]
    split_ifs with hp
    · simp only [hp, and_true]
      rw [Finset.sum_ite_eq' Ω (unfire N r y)]
      simp [hbwd y y.2 r hp]
    · simp [hp]
  have hout : ∀ r, ∑ x : Ω, poissonWeight c x * (propensity N k r x *
      (if x = y then 1 else 0)) = poissonWeight c y * propensity N k r y := by
    intro r
    rw [Finset.sum_eq_single y (fun b _ hb => by simp [hb]) (by simp)]
    simp
  simp only [hin, hout]
  rw [← Finset.sum_filter, ← poissonWeight_mul_sum_propensity N hcb, Finset.mul_sum, sub_self]

/-- The Poisson weights normalized on a finite set `Ω` of states. -/
noncomputable def classStationaryLaw (c : S → ℝ) (Ω : Finset (S → ℕ)) : Ω → ℝ :=
  fun x => poissonWeight c x / ∑ y ∈ Ω, poissonWeight c y

/-- **Stationary law of the stochastic mass-action chain on a finite class** (Anderson,
Craciun & Kurtz 2010, Thm 4.1–4.2). Let the rate constants be nonnegative, `c > 0` complex
balanced, and `Ω` a nonempty finite set of states closed under the reactions in both
directions. Then the restricted generator is a rate matrix, and the normalized product-form
Poisson law `π(x) ∝ ∏_s c_s^{x_s} e^{-c_s} / Nat.factorial x_s` on `Ω` is a positive
probability vector invariant under the transition semigroup: `π P(t) = π` for every `t`. -/
theorem classStationaryLaw_spec {k : ρ → ℝ} (hk : ∀ r, 0 ≤ k r) {c : S → ℝ}
    (hc : ∀ s, 0 < c s) (hcb : N.IsComplexBalanced k c) {Ω : Finset (S → ℕ)}
    (hΩ : Ω.Nonempty) (hfwd : ∀ x ∈ Ω, ∀ r, N.src r ≤ x → fire N r x ∈ Ω)
    (hbwd : ∀ x ∈ Ω, ∀ r, N.prod r ≤ x → unfire N r x ∈ Ω) :
    ProbabilityTheory.IsRateMatrix (classGenerator N k Ω) ∧
      (∀ x, 0 < classStationaryLaw c Ω x) ∧ ∑ x, classStationaryLaw c Ω x = 1 ∧
      ∀ t, classStationaryLaw c Ω ᵥ* ProbabilityTheory.ctmcTransition (classGenerator N k Ω) t =
        classStationaryLaw c Ω := by
  have hw : ∀ x, 0 < poissonWeight c x := fun x =>
    Finset.prod_pos fun s _ => div_pos (mul_pos (pow_pos (hc s) _) (Real.exp_pos _))
      (by positivity)
  have hZ : 0 < ∑ y ∈ Ω, poissonWeight c y := Finset.sum_pos (fun y _ => hw y) hΩ
  refine ⟨isRateMatrix_classGenerator N hk hfwd, fun x => div_pos (hw x) hZ, ?_, ?_⟩
  · simp only [classStationaryLaw, ← Finset.sum_div]
    rw [Finset.sum_coe_sort Ω (fun y => poissonWeight c y), div_self hZ.ne']
  · refine (ProbabilityTheory.vecMul_eq_zero_iff_forall_vecMul_ctmcTransition _ _).1 ?_
    have h0 := poissonWeight_vecMul_classGenerator N hcb hbwd
    funext y
    have := congrFun h0 y
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, classStationaryLaw] at this ⊢
    simp only [div_mul_eq_mul_div, ← Finset.sum_div, this, zero_div]

end StochasticMassAction

/-! ### Metabolic control analysis -/

section MetabolicControl

open Filter Topology

variable {M R : Type*} [Fintype R] [DecidableEq R]

/-- Reaction rates `v_i(e, s) = e_i f_i(s)` proportional to enzyme levels `e`. -/
def flux (f : R → (M → ℝ) → ℝ) (e : R → ℝ) (s : M → ℝ) : R → ℝ := fun i => e i * f i s

/-- The steady-state fluxes `J(e) = v(e, σ(e))` along a steady-state map `σ`. -/
def steadyFlux (f : R → (M → ℝ) → ℝ) (σ : (R → ℝ) → M → ℝ) (e : R → ℝ) : R → ℝ :=
  flux f e (σ e)

/-- The flux control coefficient `C^{J_j}_{e_i} = (e_i / J_j) ∂J_j/∂e_i`. It is meaningful
when `J_j ≠ 0` and the steady-state flux is differentiable at `e`; otherwise Lean's `x / 0 = 0`
and `fderiv` of a non-differentiable map, `0`, give junk values. -/
noncomputable def fluxControl (f : R → (M → ℝ) → ℝ) (σ : (R → ℝ) → M → ℝ) (e : R → ℝ)
    (j i : R) : ℝ :=
  e i / steadyFlux f σ e j * fderiv ℝ (fun e' => steadyFlux f σ e' j) e (Pi.single i 1)

/-- The concentration control coefficient `C^{s_m}_{e_i} = (e_i / s_m) ∂s_m/∂e_i`, meaningful
for a positive concentration `s_m` and a steady state differentiable at `e`. -/
noncomputable def concControl (σ : (R → ℝ) → M → ℝ) (e : R → ℝ) (m : M) (i : R) : ℝ :=
  e i / σ e m * fderiv ℝ (fun e' => σ e' m) e (Pi.single i 1)

/-- The elasticity `ε^{v_i}_{s_m} = (s_m / v_i) ∂v_i/∂s_m`, meaningful for a nonzero rate
`v_i` and a rate law differentiable at `s`. -/
noncomputable def elasticity [DecidableEq M] (f : R → (M → ℝ) → ℝ) (e : R → ℝ) (s : M → ℝ)
    (i : R) (m : M) : ℝ :=
  s m / flux f e s i * fderiv ℝ (fun s' => flux f e s' i) s (Pi.single m 1)

/-- A regular steady state at enzyme levels `e₀`: `σ` is differentiable at `e₀`, the rate
laws are differentiable at `σ e₀`, `N v(e, σ e) = 0` for `e` near `e₀`, and the Jacobian
`δ ↦ N ∂_s v(e₀, σ e₀) δ` is injective (it is square, so this is its invertibility). -/
structure IsRegularSteadyState (N : Matrix M R ℝ) (f : R → (M → ℝ) → ℝ)
    (σ : (R → ℝ) → M → ℝ) (e₀ : R → ℝ) : Prop where
  /-- The steady state depends differentiably on the enzyme levels. -/
  differentiableAt_steady : DifferentiableAt ℝ σ e₀
  /-- The rate laws are differentiable at the steady state. -/
  differentiableAt_rate : ∀ i, DifferentiableAt ℝ (f i) (σ e₀)
  /-- `σ e` is a steady state for `e` near `e₀`. -/
  steady : ∀ᶠ e in 𝓝 e₀, N *ᵥ flux f e (σ e) = 0
  /-- The Jacobian of the steady-state equation in the concentrations is injective. -/
  regular : Function.Injective fun δ : M → ℝ =>
    N *ᵥ fun i => e₀ i * fderiv ℝ (f i) (σ e₀) δ

omit [DecidableEq R] in
/-- **Regular steady states exist by the implicit function theorem.** If `s₀` is a steady state
at enzyme levels `e₀`, the rate laws are continuously differentiable at `s₀`, and the Jacobian
`δ ↦ N (e₀ ⊙ f'(s₀) δ)` is injective, then the steady state continues to a map `σ` with
`σ e₀ = s₀` satisfying `IsRegularSteadyState`. -/
theorem exists_isRegularSteadyState [Fintype M] {N : Matrix M R ℝ} {f : R → (M → ℝ) → ℝ}
    {e₀ : R → ℝ} {s₀ : M → ℝ} (hf : ∀ i, ContDiffAt ℝ 1 (f i) s₀)
    (hss : N *ᵥ flux f e₀ s₀ = 0)
    (hreg : Function.Injective fun δ : M → ℝ => N *ᵥ fun i => e₀ i * fderiv ℝ (f i) s₀ δ) :
    ∃ σ : (R → ℝ) → M → ℝ, σ e₀ = s₀ ∧ IsRegularSteadyState N f σ e₀ := by
  set F : (R → ℝ) × (M → ℝ) → M → ℝ := fun p => N *ᵥ flux f p.1 p.2 with hFdef
  have hFc : ContDiffAt ℝ 1 F (e₀, s₀) := by
    refine contDiffAt_pi.2 fun k => ?_
    simp only [hFdef, Matrix.mulVec, dotProduct, flux]
    refine ContDiffAt.sum fun i _ => contDiffAt_const.mul ?_
    exact ContDiffAt.mul
      (ContDiffAt.comp (e₀, s₀) (contDiffAt_apply (𝕜 := ℝ) (F' := fun _ : R => ℝ) i e₀)
        contDiffAt_fst)
      (ContDiffAt.comp (e₀, s₀) (hf i) contDiffAt_snd)
  have hF := hFc.hasStrictFDerivAt one_ne_zero
  set F' := fderiv ℝ F (e₀, s₀)
  -- the partial derivative in the concentrations
  set A : (M → ℝ) →ₗ[ℝ] (M → ℝ) :=
    { toFun := fun δ => N *ᵥ fun i => e₀ i * fderiv ℝ (f i) s₀ δ
      map_add' := fun x y => by
        rw [← Matrix.mulVec_add]; congr 1; funext i; simp [mul_add]
      map_smul' := fun c x => by
        rw [RingHom.id_apply, ← Matrix.mulVec_smul]; congr 1; funext i
        simp [smul_eq_mul]; ring } with hA
  have hpart : ∀ δ, (F' ∘L ContinuousLinearMap.inr ℝ (R → ℝ) (M → ℝ)) δ = A δ := by
    have h1 : HasFDerivAt (fun s => F (e₀, s)) (F' ∘L ContinuousLinearMap.inr ℝ _ _) s₀ :=
      hF.hasFDerivAt.comp s₀ (hasFDerivAt_prodMk_right e₀ s₀)
    have h2 : HasFDerivAt (fun s => F (e₀, s)) (LinearMap.toContinuousLinearMap A) s₀ := by
      refine hasFDerivAt_pi''  fun k => ?_
      have : HasFDerivAt (fun s => ∑ i, N k i * (e₀ i * f i s))
          (∑ i, N k i • e₀ i • fderiv ℝ (f i) s₀) s₀ :=
        HasFDerivAt.fun_sum fun i _ =>
          (((hf i).differentiableAt one_ne_zero).hasFDerivAt.const_mul (e₀ i)).const_mul _
      have hfun : (fun s => F (e₀, s) k) = fun s => ∑ i, N k i * (e₀ i * f i s) := by
        funext s
        simp [hFdef, Matrix.mulVec, dotProduct, flux]
      have hder : (ContinuousLinearMap.proj k).comp (LinearMap.toContinuousLinearMap A) =
          ∑ i, N k i • e₀ i • fderiv ℝ (f i) s₀ := by
        ext δ
        simp [hA, Matrix.mulVec, dotProduct]
      rw [hfun, hder]
      exact this
    intro δ
    rw [h1.unique h2]
    rfl
  have hAinj : Function.Injective A := hreg
  have hinv : (F' ∘L ContinuousLinearMap.inr ℝ (R → ℝ) (M → ℝ)).IsInvertible := by
    have hbij : Function.Bijective A :=
      ⟨hAinj, LinearMap.injective_iff_surjective.1 hAinj⟩
    refine ⟨(LinearEquiv.ofBijective A hbij).toContinuousLinearEquiv, ?_⟩
    ext δ
    simp [hpart]
  set σ := hF.implicitFunctionOfProdDomain hinv
  have hσ0 : σ e₀ = s₀ :=
    ((hF.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv).self_of_nhds).1 rfl
  refine ⟨σ, hσ0, ⟨(hF.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).differentiableAt,
    fun i => hσ0 ▸ (hf i).differentiableAt one_ne_zero, ?_, hσ0 ▸ hreg⟩⟩
  filter_upwards [hF.eventually_apply_implicitFunctionOfProdDomain hinv] with e he
  exact he.trans hss

/-- A continuous linear map on `R → ℝ` is determined by its values on the basis vectors. -/
private theorem sum_smul_apply_single {F : Type*} [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] (D : (R → ℝ) →L[ℝ] F) (e : R → ℝ) :
    ∑ i, e i • D (Pi.single i 1) = D e := by
  conv_rhs => rw [← Finset.univ_sum_single e]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : Pi.single i (e i) = e i • (Pi.single i 1 : R → ℝ) := by
    ext j; by_cases h : j = i <;> simp [h]
  rw [this, map_smul]

omit [Fintype R] [DecidableEq R] in
/-- The derivative of the steady-state flux `e ↦ e_i f_i(σ e)`. -/
private theorem hasFDerivAt_steadyFlux [Finite R] [Finite M] {f : R → (M → ℝ) → ℝ}
    {σ : (R → ℝ) → M → ℝ}
    {e₀ : R → ℝ} (hσ : DifferentiableAt ℝ σ e₀) (hf : ∀ i, DifferentiableAt ℝ (f i) (σ e₀))
    (i : R) :
    HasFDerivAt (fun e => steadyFlux f σ e i)
      (e₀ i • (fderiv ℝ (f i) (σ e₀)).comp (fderiv ℝ σ e₀) +
        f i (σ e₀) • ContinuousLinearMap.proj i) e₀ := by
  have := Fintype.ofFinite R
  have := Fintype.ofFinite M
  have hc : HasFDerivAt (fun e => f i (σ e)) ((fderiv ℝ (f i) (σ e₀)).comp (fderiv ℝ σ e₀))
      e₀ := (hf i).hasFDerivAt.comp e₀ hσ.hasFDerivAt
  exact (hasFDerivAt_apply i e₀).mul hc

omit [DecidableEq R] in
/-- Differentiating the steady-state equation: for every direction `δ`,
`N (e₀ ⊙ f'(σ'δ)) + N (f(s₀) ⊙ δ) = 0`. -/
private theorem steady_deriv [Finite M] {N : Matrix M R ℝ} {f : R → (M → ℝ) → ℝ}
    {σ : (R → ℝ) → M → ℝ} {e₀ : R → ℝ} (h : IsRegularSteadyState N f σ e₀) (δ : R → ℝ) :
    (N *ᵥ fun i => e₀ i * fderiv ℝ (f i) (σ e₀) (fderiv ℝ σ e₀ δ)) =
      -(N *ᵥ fun i => f i (σ e₀) * δ i) := by
  have := Fintype.ofFinite M
  funext k
  have hd : HasFDerivAt (fun e => ∑ i, N k i * steadyFlux f σ e i)
      (∑ i, N k i • (e₀ i • (fderiv ℝ (f i) (σ e₀)).comp (fderiv ℝ σ e₀) +
        f i (σ e₀) • ContinuousLinearMap.proj i)) e₀ :=
    HasFDerivAt.fun_sum fun i _ =>
      (hasFDerivAt_steadyFlux h.differentiableAt_steady h.differentiableAt_rate i).const_mul _
  have hev : (fun e => ∑ i, N k i * steadyFlux f σ e i) =ᶠ[𝓝 e₀] fun _ => (0 : ℝ) := by
    refine h.steady.mono fun e he => ?_
    have := congrFun he k
    simpa [Matrix.mulVec, dotProduct, steadyFlux] using this
  have h0 : HasFDerivAt (fun e => ∑ i, N k i * steadyFlux f σ e i) (0 : (R → ℝ) →L[ℝ] ℝ) e₀ :=
    (hasFDerivAt_const (0 : ℝ) e₀).congr_of_eventuallyEq hev
  have := congrArg (fun L => L δ) (hd.unique h0)
  simp only [_root_.sum_apply, _root_.smul_apply,
    _root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, _root_.zero_apply] at this
  simp only [Matrix.mulVec, dotProduct, Pi.neg_apply, ← Finset.sum_neg_distrib]
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

omit [DecidableEq R] in
/-- At a regular steady state the steady state does not move when all enzyme levels are
scaled together: `σ'(e₀) e₀ = 0`. -/
private theorem fderiv_steady_self [Finite M] {N : Matrix M R ℝ} {f : R → (M → ℝ) → ℝ}
    {σ : (R → ℝ) → M → ℝ} {e₀ : R → ℝ} (h : IsRegularSteadyState N f σ e₀) :
    fderiv ℝ σ e₀ e₀ = 0 := by
  apply h.regular
  have h1 := steady_deriv h e₀
  have h2 : (N *ᵥ fun i => f i (σ e₀) * e₀ i) = 0 := by
    have := h.steady.self_of_nhds
    have hfl : flux f e₀ (σ e₀) = fun i => f i (σ e₀) * e₀ i := funext fun i => mul_comm _ _
    rwa [hfl] at this
  simp only at h1 ⊢
  rw [h1, h2, neg_zero]
  simp only [map_zero, mul_zero]
  exact (Matrix.mulVec_zero N).symm

omit [DecidableEq R] in
/-- A regular steady state forces finitely many metabolites: the injective Jacobian factors
through the finite-dimensional space `R → ℝ`. -/
private theorem finite_metabolites {N : Matrix M R ℝ} {f : R → (M → ℝ) → ℝ}
    {σ : (R → ℝ) → M → ℝ} {e₀ : R → ℝ} (h : IsRegularSteadyState N f σ e₀) : Finite M := by
  classical
  let L : (M → ℝ) →ₗ[ℝ] (R → ℝ) :=
    LinearMap.pi fun i => e₀ i • (fderiv ℝ (f i) (σ e₀)).toLinearMap
  have hL : Function.Injective L := by
    intro x y hxy
    apply h.regular
    exact congrArg (fun v => N *ᵥ v) hxy
  have : FiniteDimensional ℝ (M → ℝ) := FiniteDimensional.of_injective L hL
  exact (Pi.linearIndependent_single_one M ℝ).finite

/-- **Concentration summation theorem** (Heinrich & Rapoport 1974): for a positive
steady-state concentration `s_m`, `∑_i C^{s_m}_{e_i} = 0`. The positivity hypothesis is the
domain on which the scaled concentration control coefficients have their biological meaning. -/
theorem sum_concControl {N : Matrix M R ℝ} {f : R → (M → ℝ) → ℝ} {σ : (R → ℝ) → M → ℝ}
    {e₀ : R → ℝ} (h : IsRegularSteadyState N f σ e₀) (m : M) (_hm : 0 < σ e₀ m) :
    ∑ i, concControl σ e₀ m i = 0 := by
  have := finite_metabolites h
  have := Fintype.ofFinite M
  have hd : HasFDerivAt (fun e => σ e m)
      ((ContinuousLinearMap.proj m).comp (fderiv ℝ σ e₀)) e₀ := by
    have := (hasFDerivAt_apply m (σ e₀)).comp e₀ h.differentiableAt_steady.hasFDerivAt
    exact this
  have hsum := congrFun (sum_smul_apply_single (fderiv ℝ σ e₀) e₀) m
  rw [fderiv_steady_self h] at hsum
  simp only [concControl, hd.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, div_mul_eq_mul_div, ← Finset.sum_div]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hsum
  rw [hsum, zero_div]

/-- **Flux summation theorem** (Kacser & Burns 1973; Heinrich & Rapoport 1974): for a
nonzero steady-state flux `J_j`, `∑_i C^{J_j}_{e_i} = 1`. -/
theorem sum_fluxControl {N : Matrix M R ℝ} {f : R → (M → ℝ) → ℝ} {σ : (R → ℝ) → M → ℝ}
    {e₀ : R → ℝ} (h : IsRegularSteadyState N f σ e₀) {j : R}
    (hj : steadyFlux f σ e₀ j ≠ 0) :
    ∑ i, fluxControl f σ e₀ j i = 1 := by
  have := finite_metabolites h
  have := Fintype.ofFinite M
  have hd := hasFDerivAt_steadyFlux h.differentiableAt_steady h.differentiableAt_rate j
  have hsum := sum_smul_apply_single (e₀ j • (fderiv ℝ (f j) (σ e₀)).comp (fderiv ℝ σ e₀) +
    f j (σ e₀) • ContinuousLinearMap.proj j) e₀
  simp only [fluxControl, hd.fderiv, div_mul_eq_mul_div, ← Finset.sum_div]
  simp only [smul_eq_mul] at hsum
  rw [hsum, div_eq_one_iff_eq hj]
  simp only [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, fderiv_steady_self h,
    map_zero, smul_eq_mul, mul_zero, zero_add, steadyFlux, flux]
  ring

/-- **Flux connectivity theorem** (Kacser & Burns 1973): when all steady-state fluxes are
nonzero, `∑_i C^{J_j}_{e_i} ε^{v_i}_{s_m} = 0` for every flux `J_j` and metabolite `s_m`. -/
theorem sum_fluxControl_mul_elasticity [DecidableEq M] {N : Matrix M R ℝ}
    {f : R → (M → ℝ) → ℝ} {σ : (R → ℝ) → M → ℝ} {e₀ : R → ℝ}
    (h : IsRegularSteadyState N f σ e₀)
    (hJ : ∀ i, steadyFlux f σ e₀ i ≠ 0) (j : R) (m : M) :
    ∑ i, fluxControl f σ e₀ j i * elasticity f e₀ (σ e₀) i m = 0 := by
  have := finite_metabolites h
  have := Fintype.ofFinite M
  set L := fun i => fderiv ℝ (f i) (σ e₀) with hL
  have hd := hasFDerivAt_steadyFlux h.differentiableAt_steady h.differentiableAt_rate j
  have hel : ∀ i, fderiv ℝ (fun s' => flux f e₀ s' i) (σ e₀) = e₀ i • L i := fun i =>
    ((h.differentiableAt_rate i).hasFDerivAt.const_mul (e₀ i)).fderiv
  set w : R → ℝ := fun i => e₀ i * (e₀ i * L i (Pi.single m 1)) / steadyFlux f σ e₀ i
    with hw
  have hfw : (fun i => f i (σ e₀) * w i) = fun i => e₀ i * L i (Pi.single m 1) := by
    funext i
    have hi := hJ i
    simp only [hw, steadyFlux, flux] at hi ⊢
    have hf0 : f i (σ e₀) ≠ 0 := right_ne_zero_of_mul hi
    field_simp
  have hDw : fderiv ℝ σ e₀ w = -Pi.single m 1 := by
    apply h.regular
    have h1 := steady_deriv h w
    simp only at h1 ⊢
    rw [h1, hfw]
    simp only [map_neg, mul_neg]
    rw [← Matrix.mulVec_neg]
    rfl
  set Ψ : (R → ℝ) →L[ℝ] ℝ := e₀ j • (fderiv ℝ (f j) (σ e₀)).comp (fderiv ℝ σ e₀) +
    f j (σ e₀) • ContinuousLinearMap.proj j with hΨdef
  have hsum := sum_smul_apply_single Ψ w
  have hΨ : Ψ w = 0 := by
    have hj := congrFun hfw j
    simp only [hΨdef, _root_.add_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, hDw, map_neg] at hj ⊢
    rw [hj]
    ring
  rw [hΨ] at hsum
  have : ∀ i, fluxControl f σ e₀ j i * elasticity f e₀ (σ e₀) i m =
      σ e₀ m / steadyFlux f σ e₀ j * (w i • Ψ (Pi.single i 1)) := by
    intro i
    simp only [fluxControl, elasticity, hd.fderiv, hel, _root_.smul_apply, smul_eq_mul, hw]
    simp only [steadyFlux]
    ring
  rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.mul_sum, hsum, mul_zero]

end MetabolicControl

/-! ### Flux balance analysis -/

section FluxBalance

variable {m n : ℕ}

/-- The feasible fluxes of flux balance analysis: `S v = b`, `l ≤ v ≤ u`. -/
def fbaFeasible (S : Matrix (Fin m) (Fin n) ℝ) (l u : Fin n → ℝ) (b : Fin m → ℝ) :
    Set (Fin n → ℝ) :=
  {v | S *ᵥ v = b ∧ l ≤ v ∧ v ≤ u}

/-- The optimal value `max {c ⬝ᵥ v | S v = b, l ≤ v ≤ u}` of flux balance analysis
(the supremum; it is `0` by convention when the problem is infeasible). -/
noncomputable def fbaValue (S : Matrix (Fin m) (Fin n) ℝ) (l u c : Fin n → ℝ)
    (b : Fin m → ℝ) : ℝ :=
  sSup ((fun v => c ⬝ᵥ v) '' fbaFeasible S l u b)

/-- Dual feasibility for flux balance analysis: `y` prices the metabolites, `α, β ≥ 0` the
upper and lower flux bounds, and `Sᵀ y + α - β = c`. -/
def fbaDualFeasible (S : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (y : Fin m → ℝ)
    (α β : Fin n → ℝ) : Prop :=
  0 ≤ α ∧ 0 ≤ β ∧ Sᵀ *ᵥ y + α - β = c

/-- The dual objective `b ⬝ᵥ y + u ⬝ᵥ α - l ⬝ᵥ β`. -/
def fbaDualValue (l u : Fin n → ℝ) (b : Fin m → ℝ) (y : Fin m → ℝ) (α β : Fin n → ℝ) : ℝ :=
  b ⬝ᵥ y + u ⬝ᵥ α - l ⬝ᵥ β

/-- The feasible set is closed and contained in the box `[l, u]`, hence compact. -/
private theorem isCompact_fbaFeasible (S : Matrix (Fin m) (Fin n) ℝ) (l u : Fin n → ℝ)
    (b : Fin m → ℝ) : IsCompact (fbaFeasible S l u b) := by
  have hcl : IsClosed (fbaFeasible S l u b) := by
    refine IsClosed.inter (isClosed_eq ?_ continuous_const)
      (IsClosed.inter (isClosed_le continuous_const continuous_id)
        (isClosed_le continuous_id continuous_const))
    exact Continuous.matrix_mulVec continuous_const continuous_id
  exact (isCompact_Icc (a := l) (b := u)).of_isClosed_subset hcl fun v hv => ⟨hv.2.1, hv.2.2⟩

/-- The objective is bounded above on the feasible set. -/
private theorem bddAbove_fba (S : Matrix (Fin m) (Fin n) ℝ) (l u c : Fin n → ℝ)
    (b : Fin m → ℝ) : BddAbove ((fun v => c ⬝ᵥ v) '' fbaFeasible S l u b) :=
  (isCompact_fbaFeasible S l u b).bddAbove_image
    (continuous_const.dotProduct continuous_id).continuousOn

/-- Every feasible objective value is at most the optimal value. -/
private theorem le_fbaValue {S : Matrix (Fin m) (Fin n) ℝ} {l u c : Fin n → ℝ}
    {b : Fin m → ℝ} {v : Fin n → ℝ} (hv : v ∈ fbaFeasible S l u b) :
    c ⬝ᵥ v ≤ fbaValue S l u c b :=
  le_csSup (bddAbove_fba S l u c b) ⟨v, hv, rfl⟩

/-- A feasible flux balance problem attains its optimum. -/
theorem exists_fbaValue_eq {S : Matrix (Fin m) (Fin n) ℝ} {l u c : Fin n → ℝ}
    {b : Fin m → ℝ} (hb : (fbaFeasible S l u b).Nonempty) :
    ∃ v ∈ fbaFeasible S l u b, fbaValue S l u c b = c ⬝ᵥ v ∧
      ∀ w ∈ fbaFeasible S l u b, c ⬝ᵥ w ≤ c ⬝ᵥ v := by
  obtain ⟨v, hv, hmax⟩ := (isCompact_fbaFeasible S l u b).exists_isMaxOn hb
    (continuous_const.dotProduct continuous_id).continuousOn
  refine ⟨v, hv, ?_, fun w hw => hmax hw⟩
  refine le_antisymm (csSup_le (hb.image _) ?_) (le_fbaValue hv)
  rintro _ ⟨w, hw, rfl⟩
  exact hmax hw

/-- Weak duality for flux balance analysis. -/
theorem dotProduct_le_fbaDualValue {S : Matrix (Fin m) (Fin n) ℝ} {l u c : Fin n → ℝ}
    {b : Fin m → ℝ} {v : Fin n → ℝ} (hv : v ∈ fbaFeasible S l u b) {y : Fin m → ℝ}
    {α β : Fin n → ℝ} (hd : fbaDualFeasible S c y α β) :
    c ⬝ᵥ v ≤ fbaDualValue l u b y α β := by
  obtain ⟨hSv, hlv, hvu⟩ := hv
  obtain ⟨hα, hβ, hc⟩ := hd
  have hαv : α ⬝ᵥ v ≤ α ⬝ᵥ u :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hvu i) (hα i)
  have hβv : β ⬝ᵥ l ≤ β ⬝ᵥ v :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hlv i) (hβ i)
  have hyv : (Sᵀ *ᵥ y) ⬝ᵥ v = b ⬝ᵥ y := by
    rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec, hSv, dotProduct_comm]
  rw [← hc, sub_dotProduct, add_dotProduct, hyv]
  simp only [fbaDualValue, dotProduct_comm u, dotProduct_comm l, dotProduct_comm α v,
    dotProduct_comm β v] at *
  linarith

/-- The constraint matrix `[S; -S; I]` of the shifted problem. -/
private noncomputable def stackMatrix (S : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin (m + m + n)) (Fin n) ℝ :=
  Matrix.of fun k j => Fin.append (Fin.append (fun i => S i j) (fun i => -S i j))
    (fun i => (1 : Matrix (Fin n) (Fin n) ℝ) i j) k

/-- The right-hand side `[b - S l; -(b - S l); u - l]` of the shifted problem. -/
private noncomputable def stackRhs (S : Matrix (Fin m) (Fin n) ℝ) (l u : Fin n → ℝ)
    (b : Fin m → ℝ) : Fin (m + m + n) → ℝ :=
  Fin.append (Fin.append (b - S *ᵥ l) (-(b - S *ᵥ l))) (u - l)

/-- The first block of `[S; -S; I] x`. -/
private theorem stack_mulVec_left (S : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) (i : Fin m) :
    (stackMatrix S *ᵥ x) (Fin.castAdd n (Fin.castAdd m i)) = (S *ᵥ x) i := by
  simp only [stackMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply, Fin.append_left]

/-- The second block of `[S; -S; I] x`. -/
private theorem stack_mulVec_mid (S : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) (i : Fin m) :
    (stackMatrix S *ᵥ x) (Fin.castAdd n (Fin.natAdd m i)) = -(S *ᵥ x) i := by
  simp only [stackMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply, Fin.append_left,
    Fin.append_right, neg_mul, Finset.sum_neg_distrib]

/-- The third block of `[S; -S; I] x`. -/
private theorem stack_mulVec_right (S : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) (j : Fin n) :
    (stackMatrix S *ᵥ x) (Fin.natAdd (m + m) j) = x j := by
  simp only [stackMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply, Fin.append_right,
    Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]

/-- The transpose of the stacked matrix applied to a stacked multiplier. -/
private theorem stack_transpose_mulVec (S : Matrix (Fin m) (Fin n) ℝ)
    (y : Fin (m + m + n) → ℝ) :
    (stackMatrix S)ᵀ *ᵥ y = Sᵀ *ᵥ (fun i => y (Fin.castAdd n (Fin.castAdd m i)) -
      y (Fin.castAdd n (Fin.natAdd m i))) + fun j => y (Fin.natAdd (m + m) j) := by
  funext j
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fin.sum_univ_add,
    stackMatrix, Matrix.of_apply, Fin.append_left, Fin.append_right, Pi.add_apply,
    Matrix.one_apply, mul_sub, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, neg_mul, Finset.sum_neg_distrib]
  ring

/-- The stacked right-hand side paired with a stacked multiplier. -/
private theorem stackRhs_dot (S : Matrix (Fin m) (Fin n) ℝ) (l u : Fin n → ℝ) (b : Fin m → ℝ)
    (y : Fin (m + m + n) → ℝ) :
    stackRhs S l u b ⬝ᵥ y = (b - S *ᵥ l) ⬝ᵥ (fun i => y (Fin.castAdd n (Fin.castAdd m i)) -
      y (Fin.castAdd n (Fin.natAdd m i))) + (u - l) ⬝ᵥ fun j => y (Fin.natAdd (m + m) j) := by
  simp only [dotProduct, stackRhs, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    mul_sub, Finset.sum_sub_distrib, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  ring

/-- Strong duality for flux balance analysis: a feasible problem has a dual feasible point
whose value is the optimal value. -/
theorem exists_fbaDualValue_eq {S : Matrix (Fin m) (Fin n) ℝ} {l u c : Fin n → ℝ}
    {b : Fin m → ℝ} (hb : (fbaFeasible S l u b).Nonempty) :
    ∃ y α β, fbaDualFeasible S c y α β ∧ fbaDualValue l u b y α β = fbaValue S l u c b := by
  obtain ⟨v₀, hSv₀, hlv₀, hv₀u⟩ := hb
  have hfeas : ∃ x : Fin n → ℝ, (∀ i, 0 ≤ x i) ∧
      ∀ j, ((stackMatrix S).mulVec x) j ≤ stackRhs S l u b j := by
    refine ⟨v₀ - l, fun i => sub_nonneg.2 (hlv₀ i), fun k => ?_⟩
    have hS : S *ᵥ (v₀ - l) = b - S *ᵥ l := by rw [Matrix.mulVec_sub, hSv₀]
    refine Fin.addCases (fun k₁ => Fin.addCases (fun i => ?_) (fun i => ?_) k₁)
      (fun i => ?_) k
    · rw [stack_mulVec_right]
      simp only [stackRhs, Fin.append_right, Pi.sub_apply]
      linarith [hv₀u i]
    · rw [stack_mulVec_left, hS]; simp only [stackRhs, Fin.append_left, le_refl]
    · rw [stack_mulVec_mid, hS]
      simp only [stackRhs, Fin.append_left, Fin.append_right, Pi.neg_apply, le_refl]
  have hbdd : ∃ M : ℝ, ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) →
      (∀ j, ((stackMatrix S).mulVec x) j ≤ stackRhs S l u b j) → c ⬝ᵥ x ≤ M := by
    refine ⟨∑ i, |c i| * |u i - l i|, fun x hx hAx => Finset.sum_le_sum fun i _ => ?_⟩
    have hxi : x i ≤ u i - l i := by
      have := hAx (Fin.natAdd (m + m) i)
      rwa [stack_mulVec_right, stackRhs, Fin.append_right] at this
    calc c i * x i ≤ |c i| * x i := mul_le_mul_of_nonneg_right (le_abs_self _) (hx i)
      _ ≤ |c i| * |u i - l i| :=
          mul_le_mul_of_nonneg_left (hxi.trans (le_abs_self _)) (abs_nonneg _)
  obtain ⟨x, y, hx, hAx, hy, hcy, hval⟩ :=
    MathlibExt.Analysis.Convex.LPDuality.strong_linear_programming_duality _ _ c hfeas hbdd
  set yS : Fin m → ℝ := fun i => y (Fin.castAdd n (Fin.castAdd m i)) -
    y (Fin.castAdd n (Fin.natAdd m i)) with hyS
  set α : Fin n → ℝ := fun j => y (Fin.natAdd (m + m) j) with hα
  have hT := stack_transpose_mulVec S y
  rw [← hyS, ← hα] at hT
  -- the primal optimum `v = x + l`
  have hSx : S *ᵥ x = b - S *ᵥ l := by
    funext i
    have h1 := hAx (Fin.castAdd n (Fin.castAdd m i))
    have h2 := hAx (Fin.castAdd n (Fin.natAdd m i))
    rw [stack_mulVec_left, stackRhs, Fin.append_left, Fin.append_left] at h1
    rw [stack_mulVec_mid, stackRhs, Fin.append_left, Fin.append_right, Pi.neg_apply] at h2
    linarith
  have hv : x + l ∈ fbaFeasible S l u b := by
    refine ⟨by rw [Matrix.mulVec_add, hSx, sub_add_cancel], fun i => ?_, fun i => ?_⟩
    · simp only [Pi.add_apply]; linarith [hx i]
    · have := hAx (Fin.natAdd (m + m) i)
      rw [stack_mulVec_right, stackRhs, Fin.append_right, Pi.sub_apply] at this
      simp only [Pi.add_apply]; linarith
  refine ⟨yS, α, Sᵀ *ᵥ yS + α - c, ⟨fun j => hy _, fun j => ?_, by abel⟩, ?_⟩
  · have := hcy j
    rw [hT, Pi.add_apply] at this
    simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply]
    linarith
  · have hD : fbaDualValue l u b yS α (Sᵀ *ᵥ yS + α - c) = c ⬝ᵥ (x + l) := by
      have hl : l ⬝ᵥ (Sᵀ *ᵥ yS) = (S *ᵥ l) ⬝ᵥ yS := by
        rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
      rw [dotProduct_add, hval, stackRhs_dot, ← hyS, ← hα]
      simp only [fbaDualValue, dotProduct_sub, dotProduct_add, sub_dotProduct, hl,
        dotProduct_comm l c]
      ring
    rw [hD]
    obtain ⟨w, hw, hVw, hmax⟩ := exists_fbaValue_eq (c := c) ⟨x + l, hv⟩
    refine le_antisymm (le_trans (hmax _ hv) hVw.ge) ?_
    rw [hVw, ← hD]
    refine dotProduct_le_fbaDualValue hw ⟨fun j => hy _, fun j => ?_, by abel⟩
    have := hcy j
    rw [hT, Pi.add_apply] at this
    simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply]
    linarith

/-- The optimal value is concave in the right-hand side `b` on the set of feasible `b`. -/
theorem fbaValue_concave {S : Matrix (Fin m) (Fin n) ℝ} {l u c : Fin n → ℝ}
    {b₁ b₂ : Fin m → ℝ} (h₁ : (fbaFeasible S l u b₁).Nonempty)
    (h₂ : (fbaFeasible S l u b₂).Nonempty) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    t * fbaValue S l u c b₁ + (1 - t) * fbaValue S l u c b₂ ≤
      fbaValue S l u c (t • b₁ + (1 - t) • b₂) := by
  obtain ⟨v₁, hv₁, hV₁, -⟩ := exists_fbaValue_eq (c := c) h₁
  obtain ⟨v₂, hv₂, hV₂, -⟩ := exists_fbaValue_eq (c := c) h₂
  have ht₁' : 0 ≤ 1 - t := by linarith
  have hw : t • v₁ + (1 - t) • v₂ ∈ fbaFeasible S l u (t • b₁ + (1 - t) • b₂) := by
    refine ⟨by rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hv₁.1, hv₂.1],
      fun i => ?_, fun i => ?_⟩
    · have := hv₁.2.1 i; have := hv₂.2.1 i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
    · have := hv₁.2.2 i; have := hv₂.2.2 i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
  have := le_fbaValue (c := c) hw
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at this
  rw [hV₁, hV₂]
  exact this

/-- **Shadow prices** (Orth, Thiele & Palsson 2010): at a feasible `b`, the metabolite prices
`y` of the optimal dual solutions are exactly the supergradients of the optimal value:
`fbaValue b' ≤ fbaValue b + y ⬝ᵥ (b' - b)` for every feasible `b'`. -/
theorem exists_optimal_dual_iff_supergradient {S : Matrix (Fin m) (Fin n) ℝ}
    {l u c : Fin n → ℝ} {b : Fin m → ℝ} (hb : (fbaFeasible S l u b).Nonempty) (y : Fin m → ℝ) :
    (∃ α β, fbaDualFeasible S c y α β ∧ ∀ y' α' β', fbaDualFeasible S c y' α' β' →
        fbaDualValue l u b y α β ≤ fbaDualValue l u b y' α' β') ↔
      ∀ b', (fbaFeasible S l u b').Nonempty →
        fbaValue S l u c b' ≤ fbaValue S l u c b + y ⬝ᵥ (b' - b) := by
  obtain ⟨v, hv, hV, -⟩ := exists_fbaValue_eq (c := c) hb
  have hshift : ∀ b' (y : Fin m → ℝ) α β, fbaDualValue l u b' y α β =
      fbaDualValue l u b y α β + y ⬝ᵥ (b' - b) := by
    intro b' y α β
    simp only [fbaDualValue, dotProduct_sub, dotProduct_comm y b, dotProduct_comm y b']
    ring
  constructor
  · rintro ⟨α, β, hd, hopt⟩ b' hb'
    obtain ⟨y₀, α₀, β₀, hd₀, hV₀⟩ := exists_fbaDualValue_eq (c := c) hb
    have heq : fbaDualValue l u b y α β = fbaValue S l u c b :=
      le_antisymm (hV₀ ▸ hopt y₀ α₀ β₀ hd₀) (hV ▸ dotProduct_le_fbaDualValue hv hd)
    obtain ⟨v', hv', hV', -⟩ := exists_fbaValue_eq (c := c) hb'
    rw [hV', ← heq, ← hshift]
    exact dotProduct_le_fbaDualValue hv' hd
  · intro hsup
    set g : Fin n → ℝ := c - Sᵀ *ᵥ y with hg
    refine ⟨fun i => max (g i) 0, fun i => max (-g i) 0, ⟨fun i => le_max_right _ _,
      fun i => le_max_right _ _, ?_⟩, fun y' α' β' hd' => ?_⟩
    · funext i
      change (Sᵀ *ᵥ y) i + max (g i) 0 - max (-g i) 0 = c i
      rw [add_sub_assoc, max_zero_sub_eq_self, hg, Pi.sub_apply]
      ring
    refine le_trans ?_ (hV ▸ dotProduct_le_fbaDualValue hv hd')
    have hlu : l ≤ u := fun i => (hv.2.1 i).trans (hv.2.2 i)
    set w : Fin n → ℝ := fun i => if 0 ≤ g i then u i else l i with hw
    have hwf : w ∈ fbaFeasible S l u (S *ᵥ w) := by
      refine ⟨rfl, fun i => ?_, fun i => ?_⟩ <;> simp only [hw] <;> split_ifs
      exacts [hlu i, le_rfl, le_rfl, hlu i]
    have h1 := le_fbaValue (c := c) hwf
    have h2 := hsup _ ⟨w, hwf⟩
    have hgw : g ⬝ᵥ w = u ⬝ᵥ (fun i => max (g i) 0) - l ⬝ᵥ (fun i => max (-g i) 0) := by
      simp only [dotProduct, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hw]
      split_ifs with h
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    have hcw : c ⬝ᵥ w = g ⬝ᵥ w + y ⬝ᵥ (S *ᵥ w) := by
      rw [hg, sub_dotProduct, dotProduct_comm (Sᵀ *ᵥ y), Matrix.dotProduct_transpose_mulVec]
      ring
    simp only [fbaDualValue, dotProduct_sub] at h2 ⊢
    rw [hcw, hgw] at h1
    rw [dotProduct_comm b y]
    linarith

end FluxBalance

/-! ### Symmetric matrix balancing -/

section MatrixBalancing

/-- Membership in the doubly stochastic matrices, for a matrix given as a function. -/
private theorem ds_iff {n : ℕ} (f : Fin n → Fin n → ℝ) :
    f ∈ doublyStochastic ℝ (Fin n) ↔
      (∀ i j, 0 ≤ f i j) ∧ (∀ i, ∑ j, f i j = 1) ∧ ∀ j, ∑ i, f i j = 1 :=
  mem_doublyStochastic_iff_sum

/-- Core of the uniqueness of matrix scaling. -/
private theorem scaling_const {n : ℕ} (hn : 0 < n) {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : ∀ i j, 0 < B i j) (hrow : ∀ i, ∑ j, B i j = 1) (hcol : ∀ j, ∑ i, B i j = 1)
    {x y : Fin n → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ j, 0 < y j)
    (hxr : ∀ i, x i * ∑ j, B i j * y j = 1) (hyc : ∀ j, y j * ∑ i, B i j * x i = 1) :
    ∃ M : ℝ, 0 < M ∧ (∀ i, x i = M⁻¹) ∧ ∀ j, y j = M := by
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image univ y ⟨⟨0, hn⟩, mem_univ _⟩
  set M := y k
  have hM : 0 < M := hy k
  -- every `x i ≥ M⁻¹`
  have hxge : ∀ i, M⁻¹ ≤ x i := by
    intro i
    have h1 : ∑ j, B i j * y j ≤ M := by
      calc ∑ j, B i j * y j ≤ ∑ j, B i j * M :=
            sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hk j (mem_univ _)) (hB i j).le
        _ = M := by rw [← sum_mul, hrow i, one_mul]
    rw [inv_le_iff_one_le_mul₀ hM, ← hxr i]
    exact mul_le_mul_of_nonneg_left h1 (hx i).le
  have hxeq : ∀ i, x i = M⁻¹ := by
    have hsum : ∑ i, B i k * (x i - M⁻¹) = 0 := by
      have h := hyc k
      simp only [mul_sub, sum_sub_distrib, ← sum_mul, hcol k, one_mul]
      field_simp
      linarith
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      mul_nonneg (hB i k).le (sub_nonneg.2 (hxge i))).1 hsum i (mem_univ _)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (hB i k).ne'
    · linarith
  refine ⟨M, hM, hxeq, fun j => ?_⟩
  have h0 := hxr ⟨0, hn⟩
  rw [hxeq] at h0
  have hs : ∑ j, B ⟨0, hn⟩ j * (M - y j) = 0 := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hrow, one_mul]
    field_simp at h0
    linarith
  have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
    mul_nonneg (hB ⟨0, hn⟩ j).le (sub_nonneg.2 (hk j (mem_univ _)))).1 hs j (mem_univ _)
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h (hB _ j).ne'
  · linarith

/-- **Uniqueness of Sinkhorn scaling**: two diagonal scalings of a positive matrix to doubly
stochastic form differ by a positive scalar. -/
theorem sinkhorn_scaling_unique {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, 0 < A i j) {r c r' c' : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (hr' : ∀ i, 0 < r' i) (hc' : ∀ j, 0 < c' j)
    (h : (fun i j => r i * A i j * c j) ∈ doublyStochastic ℝ (Fin n))
    (h' : (fun i j => r' i * A i j * c' j) ∈ doublyStochastic ℝ (Fin n)) :
    ∃ t : ℝ, 0 < t ∧ r' = t • r ∧ c' = t⁻¹ • c := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, one_pos, funext fun i => i.elim0, funext fun i => i.elim0⟩
  rw [ds_iff] at h h'
  obtain ⟨M, hM, hx, hy⟩ := scaling_const hn (B := Matrix.of fun i j => r i * A i j * c j)
    (fun i j => mul_pos (mul_pos (hr i) (hA i j)) (hc j)) h.2.1 h.2.2
    (x := fun i => r' i / r i) (y := fun j => c' j / c j)
    (fun i => div_pos (hr' i) (hr i)) (fun j => div_pos (hc' j) (hc j))
    (fun i => by
      rw [← h'.2.1 i, mul_sum]
      refine sum_congr rfl fun j _ => ?_
      simp only [Matrix.of_apply]
      field_simp [(hr i).ne', (hc j).ne'])
    (fun j => by
      rw [← h'.2.2 j, mul_sum]
      refine sum_congr rfl fun i _ => ?_
      simp only [Matrix.of_apply]
      field_simp [(hr i).ne', (hc j).ne'])
  refine ⟨M⁻¹, inv_pos.2 hM, funext fun i => ?_, funext fun j => ?_⟩
  · have := hx i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_eq_iff (hr i).ne'] at this
    rw [this]
  · have := hy j
    simp only [Pi.smul_apply, smul_eq_mul, inv_inv]
    rw [div_eq_iff (hc j).ne'] at this
    rw [this]

/-- **Symmetric matrix balancing** (Sinkhorn 1964; the "equal visibility" normalization of
Imakaev et al. 2012): a symmetric matrix with positive entries has a unique positive vector
`d` with `diag(d) A diag(d)` doubly stochastic. -/
theorem existsUnique_symmetric_balancing {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : A.IsSymm) (hA : ∀ i j, 0 < A i j) :
    ∃! d : Fin n → ℝ, (∀ i, 0 < d i) ∧
      (fun i j => d i * A i j * d j) ∈ doublyStochastic ℝ (Fin n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨fun i => i.elim0, ⟨fun i => i.elim0, ?_⟩, fun d _ => funext fun i => i.elim0⟩
    rw [ds_iff]
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  have hAij : ∀ i j, A i j = A j i := fun i j => by
    simpa using congrFun (congrFun hsymm.symm i) j
  obtain ⟨r, c, hr, hc, hds⟩ :=
    MathlibExt.LinearAlgebra.Matrix.SinkhornWanted.sinkhorn_scaling hn A hA
  -- the transposed scaling `(c, r)` is also doubly stochastic
  have hds' : (fun i j => c i * A i j * r j) ∈ doublyStochastic ℝ (Fin n) := by
    rw [ds_iff] at hds ⊢
    refine ⟨fun i j => mul_nonneg (mul_nonneg (hc i).le (hA i j).le) (hr j).le,
      fun i => ?_, fun j => ?_⟩
    · rw [← hds.2.2 i]; exact sum_congr rfl fun j _ => by rw [hAij]; ring
    · rw [← hds.2.1 j]; exact sum_congr rfl fun i _ => by rw [hAij]; ring
  obtain ⟨t, ht, hcr, -⟩ := sinkhorn_scaling_unique hA hr hc hc hr hds hds'
  refine ⟨Real.sqrt t • r, ⟨fun i => mul_pos (Real.sqrt_pos.2 ht) (hr i), ?_⟩, ?_⟩
  · have hfun : (fun i j => (Real.sqrt t • r) i * A i j * (Real.sqrt t • r) j) =
        fun i j => r i * A i j * c j := by
      funext i j
      have hcj : c j = t * r j := by simpa using congrFun hcr j
      simp only [Pi.smul_apply, smul_eq_mul, hcj]
      have := Real.mul_self_sqrt ht.le
      linear_combination (r i * A i j * r j) * this
    rw [hfun]
    exact hds
  · rintro d ⟨hd, hdds⟩
    obtain ⟨s, hs, hdr, hdc⟩ := sinkhorn_scaling_unique hA hr hc hd hd hds hdds
    -- `d = s r` and `d = s⁻¹ c = s⁻¹ t r`, so `s ^ 2 = t`
    have hst : s * s = t := by
      have h1 := congrFun hdr ⟨0, hn⟩
      have h2 := congrFun hdc ⟨0, hn⟩
      have hcj : c ⟨0, hn⟩ = t * r ⟨0, hn⟩ := by simpa using congrFun hcr ⟨0, hn⟩
      simp only [Pi.smul_apply, smul_eq_mul] at h1 h2
      rw [h1, hcj] at h2
      have hr0 := (hr ⟨0, hn⟩).ne'
      field_simp at h2
      nlinarith [h2]
    have : s = Real.sqrt t := by
      rw [← hst, Real.sqrt_mul_self hs.le]
    rw [hdr, this]

/-- A square matrix has **total support** if it is nonzero and every positive entry lies on a
positive diagonal: for `A i j > 0` there is a permutation `σ` with `σ i = j` and
`A k (σ k) > 0` for all `k` (Sinkhorn & Knopp 1967; Csima & Datta 1972). -/
def HasTotalSupport {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A ≠ 0 ∧ ∀ i j, 0 < A i j → ∃ σ : Equiv.Perm (Fin n), σ i = j ∧ ∀ k, 0 < A k (σ k)

/-- Entries of a weighted sum of permutation matrices. -/
private theorem perm_sum_apply {n : ℕ} (w : Equiv.Perm (Fin n) → ℝ) (i j : Fin n) :
    (∑ σ, w σ • σ.permMatrix ℝ) i j = ∑ σ, if σ i = j then w σ else 0 := by
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

/-- **Necessity of total support** (Sinkhorn & Knopp 1967; Csima & Datta 1972): if a positive
diagonal scaling `diag(d) A diag(d)` is doubly stochastic, then `A` has total support. The proof
uses Birkhoff's theorem. The converse for symmetric nonnegative `A` is recorded as wanted. -/
theorem hasTotalSupport_of_balancing {n : ℕ} (hn : 0 < n) {A : Matrix (Fin n) (Fin n) ℝ}
    {d : Fin n → ℝ} (hd : ∀ i, 0 < d i)
    (h : (fun i j => d i * A i j * d j) ∈ doublyStochastic ℝ (Fin n)) : HasTotalSupport A := by
  obtain ⟨w, hw0, -, hw⟩ := exists_eq_sum_perm_of_mem_doublyStochastic h
  have hB : ∀ i j, d i * A i j * d j = ∑ σ, if σ i = j then w σ else 0 := fun i j => by
    rw [← perm_sum_apply, hw]
  have hpos : ∀ i j, 0 < A i j ↔ 0 < d i * A i j * d j := fun i j => by
    constructor
    · intro h; exact mul_pos (mul_pos (hd i) h) (hd j)
    · intro h
      by_contra hle
      push Not at hle
      have := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (hd i).le hle)
        (hd j).le
      linarith
  refine ⟨fun hA0 => ?_, fun i j hij => ?_⟩
  · have hrow := (mem_doublyStochastic_iff_sum.1 h).2.1 ⟨0, hn⟩
    simp [hA0] at hrow
  · have hsum := (hpos i j).1 hij
    rw [hB] at hsum
    obtain ⟨σ, hσ⟩ : ∃ σ, 0 < if σ i = j then w σ else 0 := by
      by_contra hne
      push Not at hne
      exact (Finset.sum_nonpos fun σ _ => hne σ).not_gt hsum
    have hσi : σ i = j := by
      by_contra hne
      simp [hne] at hσ
    simp only [hσi, ↓reduceIte] at hσ
    refine ⟨σ, hσi, fun k => (hpos k (σ k)).2 ?_⟩
    rw [hB]
    calc (0 : ℝ) < w σ := hσ
      _ = if σ k = σ k then w σ else 0 := by simp
      _ ≤ ∑ τ, if τ k = σ k then w τ else 0 :=
        Finset.single_le_sum (f := fun τ => if τ k = σ k then w τ else 0)
          (fun τ _ => by split_ifs <;> simp [hw0 τ]) (mem_univ σ)

end MatrixBalancing

/-! ### Boolean networks -/

section BooleanNetwork

variable {n : ℕ}

/-- In the interaction graph of `f : {0,1}ⁿ → {0,1}ⁿ` there is an edge `j → i` when the
`i`-th coordinate of `f` depends on the `j`-th variable. -/
def Influences (f : (Fin n → Bool) → Fin n → Bool) (j i : Fin n) : Prop :=
  ∃ x, f (Function.update x j (!x j)) i ≠ f x i

/-- The interaction graph of `f` has no directed cycle (loops included). -/
def IsAcyclic (f : (Fin n → Bool) → Fin n → Bool) : Prop :=
  ∀ i, ¬ Relation.TransGen (Influences f) i i

/-- Changing only coordinates that do not influence `i` does not change `f · i`. -/
private theorem apply_eq_of_eqOn_influences {f : (Fin n → Bool) → Fin n → Bool} {i : Fin n} :
    ∀ (D : Finset (Fin n)) (u v : Fin n → Bool), (∀ j, u j ≠ v j → j ∈ D) →
      (∀ j ∈ D, ¬ Influences f j i) → f u i = f v i := by
  classical
  intro D
  induction D using Finset.induction_on with
  | empty =>
    intro u v huv _
    have : u = v := funext fun j => by by_contra h; simpa using huv j h
    rw [this]
  | @insert a D ha ih =>
    intro u v huv hD
    have hna : ¬ Influences f a i := hD a (Finset.mem_insert_self a D)
    set u' := Function.update u a (v a) with hu'
    have h1 : f u' i = f u i := by
      by_cases h : u a = v a
      · rw [hu', ← h, Function.update_eq_self]
      · have hv : v a = !u a := by cases hu : u a <;> cases hv : v a <;> simp_all
        rw [hu', hv]
        by_contra hne
        exact hna ⟨u, hne⟩
    rw [← h1]
    refine ih u' v (fun j hj => ?_) (fun j hj => hD j (Finset.mem_insert_of_mem hj))
    by_cases hja : j = a
    · subst hja; simp [hu'] at hj
    · have hj' : u j ≠ v j := by simpa [hu', Function.update_of_ne hja] using hj
      rcases Finset.mem_insert.1 (huv j hj') with h | h
      · exact absurd h hja
      · exact h

private theorem apply_eq_of_forall_influences {f : (Fin n → Bool) → Fin n → Bool} {i : Fin n}
    {u v : Fin n → Bool} (h : ∀ j, Influences f j i → u j = v j) : f u i = f v i := by
  classical
  refine apply_eq_of_eqOn_influences (Finset.univ.filter fun j => u j ≠ v j) u v
    (fun j hj => by simpa using hj) (fun j hj hinf => ?_)
  exact (Finset.mem_filter.1 hj).2 (h j hinf)

/-- Coordinate `i` is constant after `k` synchronous steps. -/
private def Settled (f : (Fin n → Bool) → Fin n → Bool) (k : ℕ) (i : Fin n) : Prop :=
  ∀ x y, f^[k] x i = f^[k] y i

private theorem settled_succ {f : (Fin n → Bool) → Fin n → Bool} {k : ℕ} {i : Fin n}
    (h : Settled f k i) : Settled f (k + 1) i := fun x y => by
  simp only [Function.iterate_succ_apply]
  exact h (f x) (f y)

private theorem settled_succ_of_influences {f : (Fin n → Bool) → Fin n → Bool} {k : ℕ}
    {i : Fin n} (h : ∀ j, Influences f j i → Settled f k j) : Settled f (k + 1) i :=
  fun x y => by
    simp only [Function.iterate_succ_apply']
    exact apply_eq_of_forall_influences fun j hj => h j hj x y

open scoped Classical in
private theorem card_lt_card_settled {f : (Fin n → Bool) → Fin n → Bool} (hf : IsAcyclic f)
    {k : ℕ} (hk : ∃ i, ¬ Settled f k i) :
    (Finset.univ.filter (Settled f k)).card <
      (Finset.univ.filter (Settled f (k + 1))).card := by
  classical
  have hwf : WellFounded (Influences f) := by
    have : IsTrans (Fin n) (Relation.TransGen (Influences f)) := ⟨fun _ _ _ => .trans⟩
    have : Std.Irrefl (Relation.TransGen (Influences f)) := ⟨hf⟩
    exact Subrelation.wf (fun h => Relation.TransGen.single h)
      (Finite.wellFounded_of_trans_of_irrefl _)
  obtain ⟨i, hi, hmin⟩ := hwf.has_min {i | ¬ Settled f k i} hk
  have hi1 : Settled f (k + 1) i := settled_succ_of_influences fun j hj => by
    by_contra hjs
    exact hmin j hjs hj
  apply Finset.card_lt_card
  refine (Finset.ssubset_iff_of_subset (fun j hj => ?_)).2
    ⟨i, by simpa using hi1, by simpa using hi⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact settled_succ hj

open scoped Classical in
private theorem settled_n {f : (Fin n → Bool) → Fin n → Bool} (hf : IsAcyclic f) (i : Fin n) :
    Settled f n i := by
  have key : ∀ k, min k n ≤ (Finset.univ.filter (Settled f k)).card := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      by_cases hk : ∃ i, ¬ Settled f k i
      · have := card_lt_card_settled hf hk
        omega
      · push Not at hk
        have : (Finset.univ.filter (Settled f (k + 1))) = Finset.univ :=
          Finset.filter_true_of_mem fun j _ => settled_succ (hk j)
        rw [this, Finset.card_univ, Fintype.card_fin]
        omega
  have h := key n
  rw [min_self] at h
  have huniv : Finset.univ.filter (Settled f n) = Finset.univ :=
    Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) (by simpa using h))
  have : i ∈ Finset.univ.filter (Settled f n) := by rw [huniv]; exact Finset.mem_univ i
  exact (Finset.mem_filter.1 this).2

/-- **Robert's theorem** (Robert 1980): if the interaction graph of `f : {0,1}ⁿ → {0,1}ⁿ`
is acyclic, `f` has a unique fixed point `p`, and every synchronous trajectory reaches it
within `n` steps. -/
theorem robert_fixed_point {f : (Fin n → Bool) → Fin n → Bool} (hf : IsAcyclic f) :
    ∃ p, f p = p ∧ (∀ q, f q = q → q = p) ∧ ∀ x, f^[n] x = p := by
  set p := f^[n] (fun _ => false) with hp
  have hall : ∀ x, f^[n] x = p := fun x => funext fun i => settled_n hf i x _
  refine ⟨p, ?_, fun q hq => ?_, hall⟩
  · rw [hp, ← Function.iterate_succ_apply' f n, Function.iterate_succ_apply]
    exact hall _
  · rw [← hall q, Function.iterate_fixed hq]


end BooleanNetwork

/-! ### The Markov chain tree theorem -/

section TreeTheorem

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `t : ι → ι` is a spanning in-tree rooted at `r` (each `i ≠ r` points to its parent
`t i`): `t r = r` and iterating `t` from any state reaches `r`. -/
def IsInTree (r : ι) (t : ι → ι) : Prop :=
  t r = r ∧ ∀ i, ∃ k, t^[k] i = r

/-- The total weight `∑_t ∏_{i ≠ r} Q i (t i)` of the spanning in-trees rooted at `r`. -/
noncomputable def treeWeight (Q : Matrix ι ι ℝ) (r : ι) : ℝ := by
  classical
  exact ∑ t ∈ univ.filter (IsInTree r), ∏ i ∈ univ.erase r, Q i (t i)

/-- A rate matrix is irreducible if every state reaches every other state through positive
jump rates. -/
def IsIrreducible (Q : Matrix ι ι ℝ) : Prop :=
  ∀ i j, Relation.ReflTransGen (fun a b => a ≠ b ∧ 0 < Q a b) i j

/-- `i` is reached from every state by iterating `g`. -/
private def Rooted (g : ι → ι) (i : ι) : Prop := ∀ a, ∃ n, g^[n] a = i

omit [Fintype ι] in
/-- Before `g` first hits `i`, iterating `update g i i` agrees with iterating `g`. -/
private theorem iterate_update_eq_of_lt (g : ι → ι) (i a : ι) :
    ∀ n, (∀ m < n, g^[m] a ≠ i) → (Function.update g i i)^[n] a = g^[n] a := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih fun m hm => h m (Nat.lt_succ_of_lt hm), Function.update_of_ne (h n (Nat.lt_succ_self n))]

omit [Fintype ι] in
/-- Before `update g i i` first hits `i`, its iterates agree with those of `g`. -/
private theorem iterate_update_eq_of_lt' (g : ι → ι) (i a : ι) :
    ∀ n, (∀ m < n, (Function.update g i i)^[m] a ≠ i) →
      (Function.update g i i)^[n] a = g^[n] a := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    have hn := ih fun m hm => h m (Nat.lt_succ_of_lt hm)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hn,
      Function.update_of_ne (hn ▸ h n (Nat.lt_succ_self n))]

omit [Fintype ι] in
/-- `i` is reached from everywhere under `g` iff `update g i i` is an in-tree rooted at `i`. -/
private theorem rooted_iff_isInTree (g : ι → ι) (i : ι) :
    Rooted g i ↔ IsInTree i (Function.update g i i) := by
  classical
  constructor
  · intro h
    refine ⟨Function.update_self _ _ _, fun a => ?_⟩
    have hex := h a
    refine ⟨Nat.find hex, ?_⟩
    rw [iterate_update_eq_of_lt g i a _ fun m hm => Nat.find_min hex hm]
    exact Nat.find_spec hex
  · rintro ⟨-, h⟩ a
    have hex := h a
    refine ⟨Nat.find hex, ?_⟩
    rw [← iterate_update_eq_of_lt' g i a _ fun m hm => Nat.find_min hex hm]
    exact Nat.find_spec hex

omit [Fintype ι] [DecidableEq ι] in
/-- A rooted point whose image is `j` makes `j` rooted and not fixed. -/
private theorem rooted_succ {g : ι → ι} {i j : ι} (hi : Rooted g i) (hgi : g i = j)
    (hij : i ≠ j) : g j ≠ j ∧ Rooted g j := by
  refine ⟨fun hj => ?_, fun a => ?_⟩
  · obtain ⟨n, hn⟩ := hi j
    rw [Function.iterate_fixed hj] at hn
    exact hij hn.symm
  · obtain ⟨n, hn⟩ := hi a
    exact ⟨n + 1, by rw [Function.iterate_succ_apply', hn, hgi]⟩

omit [Fintype ι] [DecidableEq ι] in
/-- Conversely the predecessor of a rooted non-fixed `j` on its cycle is rooted. -/
private theorem exists_pred {g : ι → ι} {j : ι} (hj : g j ≠ j) (hr : Rooted g j) :
    ∃ i, i ≠ j ∧ g i = j ∧ Rooted g i := by
  classical
  have hex : ∃ n, g^[n + 1] j = j := by
    obtain ⟨n, hn⟩ := hr (g j)
    exact ⟨n, by rwa [Function.iterate_succ_apply]⟩
  set p := Nat.find hex with hp
  have hspec : g^[p + 1] j = j := Nat.find_spec hex
  refine ⟨g^[p] j, fun h => ?_, by rwa [← Function.iterate_succ_apply' g p j], fun a => ?_⟩
  · rcases Nat.eq_zero_or_pos p with h0 | hpos
    · rw [h0] at h hspec; exact hj (by simpa using hspec)
    · have := Nat.find_min hex (show p - 1 < p by omega)
      apply this
      rw [Nat.sub_add_cancel hpos, h]
  · obtain ⟨n, hn⟩ := hr a
    exact ⟨p + n, by rw [Function.iterate_add_apply, hn]⟩

omit [Fintype ι] [DecidableEq ι] in
/-- At most one rooted point is mapped to `j`. -/
private theorem pred_unique {g : ι → ι} {j i₁ i₂ : ι} (h₁ : Rooted g i₁) (h₂ : Rooted g i₂)
    (hg₁ : g i₁ = j) (hg₂ : g i₂ = j) : i₁ = i₂ := by
  classical
  have e₁ := h₁ j
  have e₂ := h₂ j
  set n₁ := Nat.find e₁
  set n₂ := Nat.find e₂
  have s₁ : g^[n₁] j = i₁ := Nat.find_spec e₁
  have s₂ : g^[n₂] j = i₂ := Nat.find_spec e₂
  -- if `n₁ < n₂`, the orbit of `j` returns to `j` at `n₁ + 1 ≤ n₂`
  have key : ∀ {a b : ι} {na nb : ℕ}, g^[na] j = a → g a = j → na < nb →
      (∀ m < nb, g^[m] j ≠ b) → g^[nb] j = b → False := by
    intro a b na nb ha hga hlt hmin hb
    have hret : g^[na + 1] j = j := by rw [Function.iterate_succ_apply', ha, hga]
    have : g^[nb - (na + 1)] j = b := by
      rw [← hb, show nb = (nb - (na + 1)) + (na + 1) by omega, Function.iterate_add_apply,
        hret, Nat.add_sub_cancel]
    exact hmin _ (by omega) this
  rcases lt_trichotomy n₁ n₂ with h | h | h
  · exact (key s₁ hg₁ h (fun m hm => Nat.find_min e₂ hm) s₂).elim
  · rw [← s₁, ← s₂, h]
  · exact (key s₂ hg₂ h (fun m hm => Nat.find_min e₁ hm) s₁).elim

/-- Adding the edge `i → v` to the weight of a tree rooted at `i`. -/
private theorem prod_erase_mul_update (Q : Matrix ι ι ℝ) (t : ι → ι) (i v : ι) :
    (∏ a ∈ univ.erase i, Q a (t a)) * Q i v = ∏ a, Q a (Function.update t i v a) := by
  rw [← Finset.prod_erase_mul _ _ (mem_univ i), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun a ha => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase ha)]

open scoped Classical in
/-- Re-indexing in-trees rooted at `i` with the extra edge `i → v` by maps `g`. -/
private theorem sum_isInTree_update (F : (ι → ι) → ℝ) (i v : ι) :
    ∑ t ∈ univ.filter (IsInTree i), F (Function.update t i v) =
      ∑ g ∈ univ.filter (fun g : ι → ι => g i = v ∧ Rooted g i), F g := by
  refine Finset.sum_nbij' (fun t => Function.update t i v) (fun g => Function.update g i i)
    ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro t ht
    have ht' := (Finset.mem_filter.1 ht).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Function.update_self _ _ _, (rooted_iff_isInTree _ _).2 ?_⟩
    rwa [Function.update_idem, Function.update_eq_self_iff.2 ht'.1.symm]
  · intro g hg
    have hg' := (Finset.mem_filter.1 hg).2
    simpa using (rooted_iff_isInTree g i).1 hg'.2
  · intro t ht
    have ht' := (Finset.mem_filter.1 ht).2
    simp only [Function.update_idem]
    exact Function.update_eq_self_iff.2 ht'.1.symm
  · intro g hg
    have hg' := (Finset.mem_filter.1 hg).2
    simp only [Function.update_idem]
    exact Function.update_eq_self_iff.2 hg'.1.symm

open scoped Classical in
/-- Exactly one rooted predecessor of `j` exists iff `j` is rooted and not fixed. -/
private theorem sum_erase_indicator (g : ι → ι) (j : ι) (c : ℝ) :
    ∑ i ∈ univ.erase j, (if g i = j ∧ Rooted g i then c else 0) =
      if g j ≠ j ∧ Rooted g j then c else 0 := by
  by_cases hc : g j ≠ j ∧ Rooted g j
  · obtain ⟨i₀, hi₀j, hgi₀, hri₀⟩ := exists_pred hc.1 hc.2
    simp only [hc, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
    have : (univ.erase j).filter (fun i => g i = j ∧ Rooted g i) = {i₀} := by
      refine Finset.eq_singleton_iff_unique_mem.2 ⟨by simp [hi₀j, hgi₀, hri₀], ?_⟩
      intro i hi
      have hi' := (Finset.mem_filter.1 hi).2
      exact pred_unique hi'.2 hri₀ hi'.1 hgi₀
    rw [this, Finset.card_singleton, one_smul]
  · rw [show (if g j ≠ j ∧ Rooted g j then c else 0) = 0 from by simp [hc]]
    refine Finset.sum_eq_zero fun i hi => ?_
    have : ¬ (g i = j ∧ Rooted g i) := fun ⟨hgi, hri⟩ =>
      hc (rooted_succ hri hgi (Finset.ne_of_mem_erase hi))
    simp [this]

/-- **Markov chain tree theorem** (King & Altman 1956; Hill 1966): the in-tree weights are
invariant for every matrix with zero row sums, `w Q = 0`. The proof matches both sides with the
maps `g : ι → ι` whose functional graph has its cycle through `j` (Anantharam & Tsoucas 1989). -/
theorem treeWeight_vecMul_eq_zero {Q : Matrix ι ι ℝ} (hQ : ∀ i, ∑ j, Q i j = 0) :
    treeWeight Q ᵥ* Q = 0 := by
  classical
  funext j
  set P : (ι → ι) → ℝ := fun g => ∏ a, Q a (g a) with hP
  set G := ∑ g ∈ univ.filter (fun g : ι → ι => g j ≠ j ∧ Rooted g j), P g with hG
  -- the diagonal entry
  have hdiag : Q j j = -∑ k ∈ univ.erase j, Q j k := by
    have := hQ j
    rw [← Finset.add_sum_erase _ _ (mem_univ j)] at this
    linarith
  have htw : ∀ i, treeWeight Q i = ∑ t ∈ univ.filter (IsInTree i),
      ∏ a ∈ univ.erase i, Q a (t a) := by
    intro i
    simp only [treeWeight]
  -- off-diagonal inflow
  have hin : ∑ i ∈ univ.erase j, treeWeight Q i * Q i j = G := by
    have h1 : ∀ i, treeWeight Q i * Q i j =
        ∑ g ∈ univ.filter (fun g : ι → ι => g i = j ∧ Rooted g i), P g := by
      intro i
      rw [htw, Finset.sum_mul]
      simp only [prod_erase_mul_update]
      exact sum_isInTree_update P i j
    simp only [h1, Finset.sum_filter]
    rw [Finset.sum_comm, hG, Finset.sum_filter]
    exact Finset.sum_congr rfl fun g _ => sum_erase_indicator g j (P g)
  -- outflow
  have hout' : treeWeight Q j * ∑ k ∈ univ.erase j, Q j k = G := by
    rw [htw, Finset.sum_mul]
    simp only [Finset.mul_sum, prod_erase_mul_update]
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun k _ => sum_isInTree_update P j k).trans ?_
    rw [hG, ← Finset.sum_fiberwise_of_maps_to (s := univ.filter
      (fun g : ι → ι => g j ≠ j ∧ Rooted g j)) (t := univ.erase j) (g := fun g => g j)
      (fun g hg => by simpa using (Finset.mem_filter.1 hg).2.1)]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.filter_filter]
    refine Finset.sum_congr (Finset.filter_congr fun g _ => ?_) fun _ _ => rfl
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1 ▸ Finset.ne_of_mem_erase hk, h2⟩, h1⟩
    · rintro ⟨⟨-, h2⟩, h1⟩; exact ⟨h1, h2⟩
  have hout : treeWeight Q j * Q j j = -G := by rw [hdiag, mul_neg, hout']
  simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
  rw [← Finset.add_sum_erase _ _ (mem_univ j), hin, hout, neg_add_cancel]

/-- `i` reaches `r` in at most `n` positive-rate jumps. -/
private def ReachWithin (Q : Matrix ι ι ℝ) (r : ι) : ℕ → ι → Prop
  | 0, i => i = r
  | n + 1, i => i = r ∨ ∃ b, (i ≠ b ∧ 0 < Q i b) ∧ ReachWithin Q r n b

omit [Fintype ι] [DecidableEq ι] in
/-- Reachability gives a finite number of steps. -/
private theorem exists_reachWithin {Q : Matrix ι ι ℝ} {r i : ι}
    (h : Relation.ReflTransGen (fun a b => a ≠ b ∧ 0 < Q a b) i r) :
    ∃ n, ReachWithin Q r n i := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, rfl⟩
  | head hab _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, Or.inr ⟨_, hab, hn⟩⟩

omit [Fintype ι] [DecidableEq ι] in
/-- A spanning in-tree never maps a non-root state to itself. -/
private theorem isInTree_ne {r : ι} {t : ι → ι} (ht : IsInTree r t) {i : ι} (hi : i ≠ r) :
    t i ≠ i := by
  intro hti
  obtain ⟨k, hk⟩ := ht.2 i
  rw [Function.iterate_fixed hti] at hk
  exact hi hk

/-- For an irreducible rate matrix every in-tree weight is positive. -/
theorem treeWeight_pos {Q : Matrix ι ι ℝ} (hQ : ProbabilityTheory.IsRateMatrix Q)
    (hirr : IsIrreducible Q) (r : ι) : 0 < treeWeight Q r := by
  classical
  have hex : ∀ i, ∃ n, ReachWithin Q r n i := fun i => exists_reachWithin (hirr i r)
  let d : ι → ℕ := fun i => Nat.find (hex i)
  have hstep : ∀ i, i ≠ r → ∃ b, (i ≠ b ∧ 0 < Q i b) ∧ d b < d i := by
    intro i hi
    have hspec := Nat.find_spec (hex i)
    rcases hdi : Nat.find (hex i) with _ | n
    · rw [hdi] at hspec; exact absurd hspec hi
    · rw [hdi] at hspec
      rcases hspec with h | ⟨b, hb, hbn⟩
      · exact absurd h hi
      · exact ⟨b, hb, lt_of_le_of_lt (Nat.find_min' (hex b) hbn) (by simp [d, hdi])⟩
  let t₀ : ι → ι := fun i => if hi : i = r then r else Classical.choose (hstep i hi)
  have ht₀ : ∀ i, i ≠ r → (i ≠ t₀ i ∧ 0 < Q i (t₀ i)) ∧ d (t₀ i) < d i := by
    intro i hi
    simp only [t₀, hi, ↓reduceDIte]
    exact Classical.choose_spec (hstep i hi)
  have htree : IsInTree r t₀ := by
    refine ⟨by simp [t₀], fun i => ?_⟩
    induction hd : d i using Nat.strong_induction_on generalizing i with
    | _ n ih =>
      by_cases hi : i = r
      · exact ⟨0, hi⟩
      · obtain ⟨k, hk⟩ := ih _ (hd ▸ (ht₀ i hi).2) (t₀ i) rfl
        exact ⟨k + 1, by rwa [Function.iterate_succ_apply]⟩
  have hnonneg : ∀ t ∈ univ.filter (IsInTree r), 0 ≤ ∏ a ∈ univ.erase r, Q a (t a) := by
    intro t ht
    refine Finset.prod_nonneg fun a ha => hQ.nonneg_of_ne ?_
    exact (isInTree_ne (Finset.mem_filter.1 ht).2 (Finset.ne_of_mem_erase ha)).symm
  simp only [treeWeight]
  refine Finset.sum_pos' (fun t ht => ?_) ⟨t₀, by simp [htree], ?_⟩
  · convert hnonneg t (by simpa using ht)
  · exact Finset.prod_pos fun a ha => (ht₀ a (Finset.ne_of_mem_erase ha)).1.2

omit [DecidableEq ι] in
/-- For a nonnegative invariant vector of a rate matrix, the zero set is closed under
positive-rate predecessors. -/
private theorem eq_zero_of_pred {Q : Matrix ι ι ℝ} (hQ : ProbabilityTheory.IsRateMatrix Q)
    {μ : ι → ℝ} (hμ : 0 ≤ μ) (hμQ : μ ᵥ* Q = 0) {a b : ι} (hab : a ≠ b ∧ 0 < Q a b)
    (hb : μ b = 0) : μ a = 0 := by
  classical
  have h := congrFun hμQ b
  simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at h
  rw [← Finset.add_sum_erase _ _ (mem_univ b), hb, zero_mul, zero_add] at h
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg fun k hk =>
    mul_nonneg (hμ k) (hQ.nonneg_of_ne (Finset.ne_of_mem_erase hk))).1 h a
    (Finset.mem_erase.2 ⟨hab.1, mem_univ a⟩)
  rcases mul_eq_zero.1 hterms with h0 | h0
  · exact h0
  · exact absurd h0 hab.2.ne'

/-- For an irreducible rate matrix every invariant vector is a multiple of the in-tree weights:
the stationary law is proportional, at each state, to the weight of the spanning in-trees
rooted there. -/
theorem eq_smul_treeWeight_of_vecMul_eq_zero {Q : Matrix ι ι ℝ}
    (hQ : ProbabilityTheory.IsRateMatrix Q) (hirr : IsIrreducible Q) {π : ι → ℝ}
    (hπ : π ᵥ* Q = 0) : ∃ a : ℝ, π = a • treeWeight Q := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨0, funext fun i => (IsEmpty.false i).elim⟩
  have hw := treeWeight_pos hQ hirr
  obtain ⟨i₀, -, hmin⟩ := Finset.exists_min_image univ (fun i => π i / treeWeight Q i)
    univ_nonempty
  set a := π i₀ / treeWeight Q i₀
  set μ : ι → ℝ := π - a • treeWeight Q with hμdef
  have hμ : 0 ≤ μ := fun i => by
    have := hmin i (mem_univ i)
    rw [div_le_div_iff₀ (hw i₀) (hw i)] at this
    simp only [hμdef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, a]
    rw [div_mul_eq_mul_div, sub_nonneg, div_le_iff₀ (hw i₀)]
    linarith
  have hμ0 : μ i₀ = 0 := by
    simp only [hμdef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, a]
    field_simp [(hw i₀).ne']
    ring
  have hμQ : μ ᵥ* Q = 0 := by
    rw [hμdef, Matrix.sub_vecMul, Matrix.smul_vecMul, hπ,
      treeWeight_vecMul_eq_zero hQ.sum_row, smul_zero, sub_zero]
  refine ⟨a, funext fun i => ?_⟩
  have : μ i = 0 := by
    induction hirr i i₀ using Relation.ReflTransGen.head_induction_on with
    | refl => exact hμ0
    | head hab _ ih => exact eq_zero_of_pred hQ hμ hμQ hab ih
  have h := this
  simp only [hμdef, Pi.sub_apply, sub_eq_zero] at h
  exact h


end TreeTheorem

end MathlibExt.Biology.Dynamics.SystemsBiology
