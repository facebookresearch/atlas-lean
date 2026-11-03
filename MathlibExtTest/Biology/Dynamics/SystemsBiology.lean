/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.SystemsBiology
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Tests for the systems-biology core: the stochastic dimerization `2A ⇌ B` on the closed
class `{(2, 0), (0, 1)}` (product-form stationary law `(2/3, 1/3)`), a two-reaction pathway
satisfying the metabolic-control hypotheses, a small flux balance problem with its optimum and
the infeasible junk value, symmetric balancing of the all-ones matrix, Boolean networks with
and without cycles, and spanning in-trees. -/

open Finset Matrix

namespace MathlibExtTest.Biology.Dynamics.SystemsBiology

open MathlibExt.Biology.Dynamics.SystemsBiology MathlibExt.Biology.Dynamics.ComplexBalanced
  ReactionNetwork

/-! ### Stochastic mass action -/

/-- The dimerization `2A ⇌ B` (`0 = A`, `1 = B`): reaction `0` is `2A → B`, reaction `1` is
`B → 2A`. -/
def dimer : ReactionNetwork (Fin 2) (Fin 2) where
  src := ![![2, 0], ![0, 1]]
  prod := ![![0, 1], ![2, 0]]

/-- Rate constants `k₀ = 1`, `k₁ = 4`. -/
noncomputable def kDimer : Fin 2 → ℝ := ![1, 4]

/-- The complex-balanced concentrations `c = (2, 1)`. -/
noncomputable def cDimer : Fin 2 → ℝ := ![2, 1]

theorem rate_dimer (r : Fin 2) : dimer.rate kDimer cDimer r = 4 := by
  fin_cases r <;> norm_num [rate, dimer, kDimer, cDimer, Fin.prod_univ_two]

theorem isComplexBalanced_dimer : dimer.IsComplexBalanced kDimer cDimer := by
  intro z
  simp only [Finset.sum_filter, Fin.sum_univ_two, rate_dimer]
  simp only [dimer, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact add_comm _ _

/-- The closed class `{(2, 0), (0, 1)}` of the conservation law `x_A + 2 x_B = 2`. -/
def classTwo : Finset (Fin 2 → ℕ) := {![2, 0], ![0, 1]}

theorem classTwo_fwd : ∀ x ∈ classTwo, ∀ r, dimer.src r ≤ x → fire dimer r x ∈ classTwo := by
  decide

theorem classTwo_bwd : ∀ x ∈ classTwo, ∀ r, dimer.prod r ≤ x → unfire dimer r x ∈ classTwo := by
  decide

/-- **Non-vacuity witness** for the finite-class theorem: every hypothesis holds for the
dimerization on `{(2, 0), (0, 1)}`. -/
theorem classStationaryLaw_dimer :
    ProbabilityTheory.IsRateMatrix (classGenerator dimer kDimer classTwo) ∧
      (∀ x, 0 < classStationaryLaw cDimer classTwo x) ∧
      ∑ x, classStationaryLaw cDimer classTwo x = 1 ∧
      ∀ t, classStationaryLaw cDimer classTwo ᵥ*
          ProbabilityTheory.ctmcTransition (classGenerator dimer kDimer classTwo) t =
        classStationaryLaw cDimer classTwo :=
  classStationaryLaw_spec dimer (by intro r; fin_cases r <;> norm_num [kDimer])
    (by intro s; fin_cases s <;> norm_num [cDimer]) isComplexBalanced_dimer
    ⟨![2, 0], by decide⟩ classTwo_fwd classTwo_bwd

/-- The Poisson weights on the class are in ratio `2 : 1` (`2²/2! : 1¹/1!`), so the stationary
law is `(2/3, 1/3)`: two molecules of `A` are twice as likely as one of `B`. -/
theorem poissonWeight_dimer :
    poissonWeight cDimer ![2, 0] = 2 * poissonWeight cDimer ![0, 1] := by
  simp [poissonWeight, cDimer, Fin.prod_univ_two]
  ring

/-- Global balance at `(2, 0)`: outflow `2 · π(2,0) = 4 · π(0,1)` (propensities `2` and `4`). -/
example : propensity dimer kDimer 0 ![2, 0] = 2 ∧ propensity dimer kDimer 1 ![0, 1] = 4 := by
  constructor <;> simp [propensity, dimer, kDimer, Fin.prod_univ_two, Nat.descFactorial]

/-- Boundary case: a reaction whose source does not fit has propensity `0`
(`B → 2A` in state `(2, 0)`). -/
example : propensity dimer kDimer 1 ![2, 0] = 0 := by
  simp [propensity, dimer, Fin.prod_univ_two]

/-! ### Metabolic control analysis -/

/-- A linear pathway with one metabolite `s`: an input reaction `v₀ = e₀` (rate law `1`)
and an output reaction `v₁ = e₁ s`. -/
noncomputable def fPath : Fin 2 → (Fin 1 → ℝ) → ℝ := ![fun _ => 1, fun s => s 0]

/-- Stoichiometry: `ṡ = v₀ - v₁`. -/
def nPath : Matrix (Fin 1) (Fin 2) ℝ := !![1, -1]

/-- The steady state `s = e₀ / e₁`. -/
noncomputable def σPath (e : Fin 2 → ℝ) : Fin 1 → ℝ := fun _ => e 0 / e 1

theorem fderiv_fPath_one (s : Fin 1 → ℝ) :
    fderiv ℝ (fPath 1) s = ContinuousLinearMap.proj 0 :=
  (hasFDerivAt_apply (0 : Fin 1) s).fderiv

theorem fderiv_fPath_zero (s : Fin 1 → ℝ) : fderiv ℝ (fPath 0) s = 0 := by
  simp [fPath]

/-- **Non-vacuity witness** for metabolic control analysis: the pathway at unit enzyme
levels is a regular steady state. -/
theorem isRegularSteadyState_path : IsRegularSteadyState nPath fPath σPath (fun _ => 1) where
  differentiableAt_steady := by
    refine differentiableAt_pi.2 fun i => ?_
    have he : (fun e : Fin 2 → ℝ => σPath e i) = fun e => e 0 * (e 1)⁻¹ := by
      funext e; simp [σPath, div_eq_mul_inv]
    simp only [he]
    exact DifferentiableAt.mul (hasFDerivAt_apply (0 : Fin 2) _).differentiableAt
      (DifferentiableAt.inv (hasFDerivAt_apply (1 : Fin 2) _).differentiableAt (by simp))
  differentiableAt_rate i := by
    fin_cases i
    · simp [fPath]
    · exact (hasFDerivAt_apply (0 : Fin 1) _).differentiableAt
  steady := by
    filter_upwards [(continuous_apply (1 : Fin 2)).continuousAt.eventually_ne
      (by simp : (fun _ : Fin 2 => (1 : ℝ)) 1 ≠ 0)] with e he
    funext k
    fin_cases k
    simp [nPath, flux, fPath, σPath, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    ring
  regular δ δ' h := by
    have := congrFun h 0
    simp [nPath, Matrix.mulVec, dotProduct, Fin.sum_univ_two, fderiv_fPath_zero,
      fderiv_fPath_one] at this
    funext i
    fin_cases i
    simpa using this

/-- **Zero-concentration boundary witness:** the same pathway is a regular steady state at
enzyme levels `(0, 1)`, where its steady-state concentration is zero. -/
theorem isRegularSteadyState_path_zero : IsRegularSteadyState nPath fPath σPath ![0, 1] where
  differentiableAt_steady := by
    refine differentiableAt_pi.2 fun i => ?_
    have he : (fun e : Fin 2 → ℝ => σPath e i) = fun e => e 0 * (e 1)⁻¹ := by
      funext e; simp [σPath, div_eq_mul_inv]
    simp only [he]
    exact DifferentiableAt.mul (hasFDerivAt_apply (0 : Fin 2) _).differentiableAt
      (DifferentiableAt.inv (hasFDerivAt_apply (1 : Fin 2) _).differentiableAt (by simp))
  differentiableAt_rate i := by
    fin_cases i
    · simp [fPath]
    · exact (hasFDerivAt_apply (0 : Fin 1) _).differentiableAt
  steady := by
    filter_upwards [(continuous_apply (1 : Fin 2)).continuousAt.eventually_ne
      (by simp : (![0, 1] : Fin 2 → ℝ) 1 ≠ 0)] with e he
    funext k
    fin_cases k
    simp [nPath, flux, fPath, σPath, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    ring
  regular δ δ' h := by
    have := congrFun h 0
    simp [nPath, Matrix.mulVec, dotProduct, Fin.sum_univ_two, fderiv_fPath_zero,
      fderiv_fPath_one] at this
    funext i
    fin_cases i
    simpa using this

/-- At the zero-concentration regular state, Lean's totalized division makes every raw
`concControl` value, and hence their sum, zero. This is algebraic behavior outside the
biological coefficient domain. -/
example : σPath ![0, 1] 0 = 0 ∧
    (∀ i, concControl σPath ![0, 1] 0 i = 0) ∧
    ∑ i, concControl σPath ![0, 1] 0 i = 0 := by
  constructor
  · simp [σPath]
  constructor
  · intro i
    simp [concControl, σPath]
  · simp [concControl, σPath]

/-- The flux control coefficients of the output flux sum to `1`. -/
example : ∑ i, fluxControl fPath σPath (fun _ => 1) 1 i = 1 :=
  sum_fluxControl isRegularSteadyState_path (by simp [steadyFlux, flux, fPath, σPath])

/-- At the positive concentration `1`, the concentration control coefficients sum to `0`. -/
example : ∑ i, concControl σPath (fun _ => 1) 0 i = 0 :=
  sum_concControl isRegularSteadyState_path 0 (by simp [σPath])

/-- A generic client of the source-labelled theorem must supply the positive-concentration
domain premise. -/
example {M R : Type*} [Fintype R] [DecidableEq R]
    {N : Matrix M R ℝ} {f : R → (M → ℝ) → ℝ} {σ : (R → ℝ) → M → ℝ} {e₀ : R → ℝ}
    (h : IsRegularSteadyState N f σ e₀) (m : M) (hm : 0 < σ e₀ m) :
    ∑ i, concControl σ e₀ m i = 0 :=
  sum_concControl h m hm

/-- The connectivity theorem for the pathway. -/
example : ∑ i, fluxControl fPath σPath (fun _ => 1) 0 i *
    elasticity fPath (fun _ => 1) (σPath fun _ => 1) i 0 = 0 :=
  sum_fluxControl_mul_elasticity isRegularSteadyState_path
    (by intro i; fin_cases i <;> simp [steadyFlux, flux, fPath, σPath]) 0 0

/-! ### Flux balance analysis -/

/-- One metabolite, two reactions: `v₀` produces it, `v₁` consumes it. -/
def sFba : Matrix (Fin 1) (Fin 2) ℝ := !![1, -1]

theorem fbaFeasible_sFba : ![1, 1] ∈ fbaFeasible sFba 0 ![1, 2] 0 := by
  refine ⟨?_, fun i => ?_, fun i => ?_⟩
  · funext i; fin_cases i; simp [sFba, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · fin_cases i <;> simp
  · fin_cases i <;> simp

/-- Maximizing `v₁` subject to `v₀ = v₁`, `0 ≤ v₀ ≤ 1`, `0 ≤ v₁ ≤ 2` gives `1`. -/
theorem fbaValue_sFba : fbaValue sFba 0 ![1, 2] ![0, 1] 0 = 1 := by
  obtain ⟨v, hv, hV, hmax⟩ := exists_fbaValue_eq (c := ![0, 1]) ⟨_, fbaFeasible_sFba⟩
  rw [hV]
  have h1 := hmax _ fbaFeasible_sFba
  have hv0 : v 0 = v 1 := by
    have := congrFun hv.1 0
    simp [sFba, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
    linarith
  have hle : v 0 ≤ 1 := by simpa using hv.2.2 0
  simp [dotProduct, Fin.sum_univ_two] at h1 ⊢
  linarith

/-- Junk value: an infeasible problem (`v₀ = v₁ + 5` with `v₀ ≤ 1`, `v₁ ≥ 0`) has
`fbaValue = sSup ∅ = 0`; the theorems assume feasibility. -/
example : fbaValue sFba 0 ![1, 2] ![0, 1] ![5] = 0 := by
  have : fbaFeasible sFba 0 ![1, 2] ![5] = ∅ := by
    ext v
    simp only [fbaFeasible, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hS, hl, hu⟩
    have h := congrFun hS 0
    simp [sFba, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h
    have h0 : v 0 ≤ 1 := by simpa using hu 0
    have h1 : 0 ≤ v 1 := by simpa using hl 1
    linarith
  simp [fbaValue, this]

/-! ### Symmetric matrix balancing -/

/-- The all-ones `2 × 2` matrix is balanced by `d = (1/√2, 1/√2)`, and by nothing else. -/
example : ∃! d : Fin 2 → ℝ, (∀ i, 0 < d i) ∧
    (fun i j => d i * (Matrix.of fun _ _ => (1 : ℝ)) i j * d j) ∈
      doublyStochastic ℝ (Fin 2) :=
  existsUnique_symmetric_balancing (by ext i j; simp) (by intro i j; simp)

/-- The all-ones matrix has total support (it admits a balancing). -/
example : HasTotalSupport (Matrix.of fun _ _ : Fin 2 => (1 : ℝ)) := by
  obtain ⟨d, ⟨hd, hds⟩, -⟩ := existsUnique_symmetric_balancing (n := 2)
    (A := Matrix.of fun _ _ => (1 : ℝ)) (by ext i j; simp) (by intro i j; simp)
  exact hasTotalSupport_of_balancing (by norm_num) hd hds

/-- The triangular matrix `!![1, 1; 0, 1]` lacks total support: the positive entry `(0, 1)`
lies on no positive diagonal. Hence no positive diagonal scaling makes it doubly stochastic. -/
example : ¬ ∃ d : Fin 2 → ℝ, (∀ i, 0 < d i) ∧
    (fun i j => d i * (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j * d j) ∈
      doublyStochastic ℝ (Fin 2) := by
  rintro ⟨d, hd, hds⟩
  obtain ⟨-, hts⟩ := hasTotalSupport_of_balancing (by norm_num) hd hds
  obtain ⟨σ, hσ, hpos⟩ := hts 0 1 (by simp)
  have h1 : σ 1 = 0 := by
    have hinj := σ.injective.ne (show (0 : Fin 2) ≠ 1 by decide)
    rw [hσ] at hinj
    revert hinj
    generalize σ 1 = a
    fin_cases a <;> simp
  have := hpos 1
  rw [h1] at this
  simp at this

/-! ### Boolean networks -/

/-- `x₀ ↦ true`, `x₁ ↦ x₀`: the interaction graph is the single edge `0 → 1`. -/
def chain : (Fin 2 → Bool) → Fin 2 → Bool := fun x => ![true, x 0]

theorem influences_chain {j i : Fin 2} (h : Influences chain j i) : j = 0 ∧ i = 1 := by
  obtain ⟨x, hx⟩ := h
  fin_cases i <;> fin_cases j <;> simp_all [chain, Function.update]

/-- **Non-vacuity witness** for Robert's theorem: the chain network is acyclic. -/
theorem isAcyclic_chain : IsAcyclic chain := by
  intro i h
  obtain ⟨b, hb, hbi⟩ := Relation.TransGen.tail'_iff.1 h
  obtain ⟨rfl, rfl⟩ := influences_chain hbi
  rcases Relation.ReflTransGen.cases_tail hb with h1 | ⟨c, -, hc⟩
  · simp at h1
  · simpa using (influences_chain hc).2

/-- The chain reaches its unique fixed point `(true, true)` in two steps. -/
example : ∃ p, chain p = p ∧ (∀ q, chain q = q → q = p) ∧ ∀ x, chain^[2] x = p :=
  robert_fixed_point isAcyclic_chain

/-- With the cycle `0 ⇄ 1` (swap), there are two fixed points: acyclicity cannot be dropped. -/
example : (fun x : Fin 2 → Bool => ![x 1, x 0]) ![true, true] = ![true, true] ∧
    (fun x : Fin 2 → Bool => ![x 1, x 0]) ![false, false] = ![false, false] := by
  constructor <;> decide

/-- A negative self-loop (`x₀ ↦ ¬x₀`) has no fixed point at all. -/
example : ∀ x : Fin 1 → Bool, (fun y : Fin 1 → Bool => ![!y 0]) x ≠ x := by
  decide

/-! ### Spanning in-trees -/

/-- The two-state chain with rates `0 → 1` at `1` and `1 → 0` at `2`. -/
def qTwo : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 1; 2, -2]

theorem isRateMatrix_qTwo : ProbabilityTheory.IsRateMatrix qTwo := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [qTwo]
  · fin_cases i <;> simp [qTwo, Fin.sum_univ_two]

/-- **Non-vacuity witness** for the irreducibility hypothesis. -/
theorem isIrreducible_qTwo : IsIrreducible qTwo := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact .refl
  · exact .single ⟨by decide, by simp [qTwo]⟩
  · exact .single ⟨by decide, by simp [qTwo]⟩
  · exact .refl

/-- Both in-tree weights of the two-state chain are positive, and every invariant vector is a
multiple of them. -/
example : (∀ r, 0 < treeWeight qTwo r) ∧
    ∀ π : Fin 2 → ℝ, π ᵥ* qTwo = 0 → ∃ a : ℝ, π = a • treeWeight qTwo :=
  ⟨treeWeight_pos isRateMatrix_qTwo isIrreducible_qTwo,
    fun _ hπ => eq_smul_treeWeight_of_vecMul_eq_zero isRateMatrix_qTwo isIrreducible_qTwo hπ⟩

/-- The star map sending every state to the root is a spanning in-tree. -/
example (r : Fin 3) : IsInTree r (fun _ => r) :=
  ⟨rfl, fun _ => ⟨1, rfl⟩⟩

#print axioms classStationaryLaw_spec
#print axioms robert_fixed_point
#print axioms sum_fluxControl_mul_elasticity
#print axioms existsUnique_symmetric_balancing
#print axioms exists_optimal_dual_iff_supergradient
#print axioms eq_smul_treeWeight_of_vecMul_eq_zero
#print axioms exists_isRegularSteadyState

end MathlibExtTest.Biology.Dynamics.SystemsBiology
