/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.MichaelisMenten.Trajectories
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import MathlibExt.Analysis.ODE.MaximalSolution
import MathlibExt.Analysis.ODE.InvariantRegions
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Order.IntermediateValue

/-!
# Reversible Michaelis–Menten kinetics

The enzyme mechanism with a reversible product step, `E + S ⇌ C ⇌ E + P`, with rate constants
`k₁` (binding), `k₋₁` (unbinding of `S`), `k₂` (catalysis) and `k₋₂` (rebinding of `P`;
`kb`, `kb₂` in Lean), has the mass-action equations (`IsSolution`)

  `s' = -k₁ e s + k₋₁ c`,
  `c' = k₁ e s - (k₋₁ + k₂) c + k₋₂ e p`,  `e' = -c'`,
  `p' = k₂ c - k₋₂ e p`.

For `k₋₂ = 0` this is the irreversible system `MichaelisMenten.IsSolution`
(`isSolution_zero_iff`).

## Main results

* `IsSolution.enzyme_conservation`, `IsSolution.substrate_conservation`: `e + c` and
  `s + c + p` are constant along solutions.
* `exists_isSolution_nonneg`: **global existence**. For nonnegative rate constants and every
  nonnegative initial state there is a solution on `[0, ∞)` that stays in the nonnegative orthant
  and keeps both totals.
* `IsSolution.eq_of_initial`: forward uniqueness; `IsSolution.nonneg`: every solution with
  nonnegative data stays nonnegative.
* `revField_eq_zero_iff`: the equilibria are exactly the states in **detailed balance**,
  `k₁ e s = k₋₁ c` and `k₂ c = k₋₂ e p`; `isSolution_const_iff` and
  `IsSolution.eq_of_equilibrium`: a solution started at an equilibrium stays there.
* `haldane_of_revField_eq_zero`, `haldane_div`: the **Haldane relation**: at an equilibrium with
  `e ≠ 0`, `k₁ k₂ s = k₋₁ k₋₂ p`, so `p / s = K_eq = k₁ k₂ / (k₋₁ k₋₂)`.
* `existsUnique_equilibrium`: for positive rate constants and positive totals `E_T`, `S_T`,
  the compatibility class `{e + c = E_T, s + c + p = S_T}` contains exactly one nonnegative
  equilibrium; `pos_of_equilibrium` shows it is positive.

## Not covered

Convergence of every solution to the equilibrium of its class (global asymptotic stability, e.g.
via the pseudo-Helmholtz Lyapunov function of `MathlibExt.Biology.Dynamics.ComplexBalanced`
and a LaSalle argument) is **not** proved here; neither file provides it.

## Source receipt (API-00 reuse gate)

Reused, not redefined: `substrateRate`, `complexRate`, `MichaelisMenten.IsSolution` from
`MathlibExt.Biology.Dynamics.MichaelisMenten`; `mmField` from
`MathlibExt.Biology.Dynamics.MichaelisMenten.Trajectories` (bridge `revField_zero`); the
maximal-solution exit theorem
`MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_maximal_solution_exit_compact`; the
orthant-invariance theorem `MetaMathlibExt.orthant_invariant_of_boundary_nonneg`; Mathlib's
`ODE_solution_unique_of_mem_Icc_right` and `intermediate_value_Icc`. The global-existence proof
follows `MichaelisMenten.exists_isSolution_nonneg` (whose helpers are private there). No
reversible Michaelis–Menten statement existed in MathlibExt, WantedExt, CSLibExt or PhyslibExt
before this file. The general Horn–Jackson uniqueness
(`MathlibExt.Biology.Dynamics.ComplexBalanced.existsUnique_equilibrium_of_isComplexBalanced`)
would need this network encoded as a `Fin 4` reaction network plus an identification of its
stoichiometric subspace with the two conservation laws; the two-line monotonicity argument used
here is shorter, and covers nonnegative (not only positive) equilibria.

Mathematical source: Keener–Sneyd, *Mathematical Physiology I*, §1.4 (enzyme kinetics: the
mass-action system of the Michaelis–Menten mechanism and its conservation laws); Cornish-Bowden,
*Fundamentals of Enzyme Kinetics*, ch. 2 (the reversible Michaelis–Menten mechanism and the
Haldane relationship `K_eq = k₁ k₂ / (k₋₁ k₋₂)`); Segel–Slemrod §2 for the well-posedness
argument.

## References

* J. Keener and J. Sneyd, *Mathematical Physiology I: Cellular Physiology*, 2nd ed., Springer
  (2009), §1.4.
* A. Cornish-Bowden, *Fundamentals of Enzyme Kinetics*, 4th ed., Wiley-Blackwell (2012), §2.7.
* J. B. S. Haldane, *Enzymes*, Longmans, Green and Co. (1930).
* L. A. Segel and M. Slemrod, *The quasi-steady-state assumption: a case study in
  perturbation*, SIAM Rev. 31 (1989) 446–477, §2.
-/

@[expose] public section

open Set Filter Metric Real
open scoped Topology

namespace MathlibExt.Biology.Dynamics.ReversibleMichaelisMenten

open MathlibExt.Biology.Dynamics.MichaelisMenten (substrateRate complexRate mmField)

variable {k₁ kb k₂ kb₂ : ℝ} {s c e p : ℝ → ℝ}

/-! ### The system -/

/-- The mass-action rate of the complex with a reversible product step,
`c' = k₁ e s - (kb + k₂) c + kb₂ e p`. -/
def revComplexRate (k₁ kb k₂ kb₂ s c e p : ℝ) : ℝ :=
  complexRate k₁ kb k₂ s c e + kb₂ * e * p

/-- The mass-action rate of the product with a reversible product step,
`p' = k₂ c - kb₂ e p`. -/
def revProductRate (k₂ kb₂ c e p : ℝ) : ℝ :=
  k₂ * c - kb₂ * e * p

/-- A solution of the reversible Michaelis–Menten system on `[0, ∞)`:
`s' = -k₁ e s + kb c`, `c' = k₁ e s - (kb + k₂) c + kb₂ e p`, `e' = -c'`,
`p' = k₂ c - kb₂ e p`. -/
structure IsSolution (k₁ kb k₂ kb₂ : ℝ) (s c e p : ℝ → ℝ) : Prop where
  hasDerivAt_substrate : ∀ t, 0 ≤ t → HasDerivAt s (substrateRate k₁ kb (s t) (c t) (e t)) t
  hasDerivAt_complex : ∀ t, 0 ≤ t →
    HasDerivAt c (revComplexRate k₁ kb k₂ kb₂ (s t) (c t) (e t) (p t)) t
  hasDerivAt_enzyme : ∀ t, 0 ≤ t →
    HasDerivAt e (-revComplexRate k₁ kb k₂ kb₂ (s t) (c t) (e t) (p t)) t
  hasDerivAt_product : ∀ t, 0 ≤ t → HasDerivAt p (revProductRate k₂ kb₂ (c t) (e t) (p t)) t

/-- With `kb₂ = 0` the reversible system is the irreversible Michaelis–Menten system. -/
theorem isSolution_zero_iff :
    IsSolution k₁ kb k₂ 0 s c e p ↔ MichaelisMenten.IsSolution k₁ kb k₂ s c e p := by
  constructor
  · intro h
    refine ⟨h.hasDerivAt_substrate, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
    · simpa [revComplexRate] using h.hasDerivAt_complex t ht
    · simpa [revComplexRate] using h.hasDerivAt_enzyme t ht
    · simpa [revProductRate] using h.hasDerivAt_product t ht
  · intro h
    refine ⟨h.hasDerivAt_substrate, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
    · simpa [revComplexRate] using h.hasDerivAt_complex t ht
    · simpa [revComplexRate] using h.hasDerivAt_enzyme t ht
    · simpa [revProductRate] using h.hasDerivAt_product t ht

/-! ### Conservation laws -/

/-- A function with zero derivative on `[0, ∞)` is constant there. -/
private lemma eq_of_hasDerivAt_zero {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ t → HasDerivAt f 0 t) {t : ℝ}
    (ht : 0 ≤ t) : f t = f 0 :=
  constant_of_has_deriv_right_zero (fun x hx => (hf x hx.1).continuousAt.continuousWithinAt)
    (fun x hx => (hf x hx.1).hasDerivWithinAt) t ⟨ht, le_rfl⟩

/-- **Enzyme conservation**: `e(t) + c(t) = e(0) + c(0)`. -/
theorem IsSolution.enzyme_conservation (h : IsSolution k₁ kb k₂ kb₂ s c e p) {t : ℝ}
    (ht : 0 ≤ t) : e t + c t = e 0 + c 0 := by
  refine eq_of_hasDerivAt_zero (f := fun t => e t + c t) (fun x hx => ?_) ht
  simpa using (h.hasDerivAt_enzyme x hx).fun_add (h.hasDerivAt_complex x hx)

/-- **Mass conservation**: `s(t) + c(t) + p(t) = s(0) + c(0) + p(0)`. -/
theorem IsSolution.substrate_conservation (h : IsSolution k₁ kb k₂ kb₂ s c e p) {t : ℝ}
    (ht : 0 ≤ t) : s t + c t + p t = s 0 + c 0 + p 0 := by
  refine eq_of_hasDerivAt_zero (f := fun t => s t + c t + p t) (fun x hx => ?_) ht
  convert ((h.hasDerivAt_substrate x hx).fun_add (h.hasDerivAt_complex x hx)).fun_add
    (h.hasDerivAt_product x hx) using 1
  simp only [substrateRate, revComplexRate, complexRate, revProductRate]; ring

/-! ### The vector field -/

/-- The reversible Michaelis–Menten field on `Fin 4 → ℝ`, with coordinates `x 0 = s`,
`x 1 = c`, `x 2 = e`, `x 3 = p`. -/
def revField (k₁ kb k₂ kb₂ : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![substrateRate k₁ kb (x 0) (x 1) (x 2), revComplexRate k₁ kb k₂ kb₂ (x 0) (x 1) (x 2) (x 3),
    -revComplexRate k₁ kb k₂ kb₂ (x 0) (x 1) (x 2) (x 3), revProductRate k₂ kb₂ (x 1) (x 2) (x 3)]

/-- The curve in `Fin 4 → ℝ` obtained by packing `s`, `c`, `e`, `p`. -/
def revCurve (s c e p : ℝ → ℝ) (t : ℝ) : Fin 4 → ℝ :=
  ![s t, c t, e t, p t]

/-- With `kb₂ = 0` the field is the irreversible field `mmField`. -/
theorem revField_zero : revField k₁ kb k₂ 0 = mmField k₁ kb k₂ := by
  ext x i
  fin_cases i <;> simp [revField, mmField, revComplexRate, revProductRate]

/-- `IsSolution` is the statement that the packed curve has derivative `revField` at every
`t ≥ 0`. -/
theorem isSolution_iff_hasDerivAt_revCurve :
    IsSolution k₁ kb k₂ kb₂ s c e p ↔
      ∀ t, 0 ≤ t →
        HasDerivAt (revCurve s c e p) (revField k₁ kb k₂ kb₂ (revCurve s c e p t)) t := by
  constructor
  · intro h t ht
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i
    · simpa [revCurve, revField] using h.hasDerivAt_substrate t ht
    · simpa [revCurve, revField] using h.hasDerivAt_complex t ht
    · simpa [revCurve, revField] using h.hasDerivAt_enzyme t ht
    · simpa [revCurve, revField] using h.hasDerivAt_product t ht
  · intro h
    refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
    · simpa [revCurve, revField] using hasDerivAt_pi.1 (h t ht) 0
    · simpa [revCurve, revField] using hasDerivAt_pi.1 (h t ht) 1
    · simpa [revCurve, revField] using hasDerivAt_pi.1 (h t ht) 2
    · simpa [revCurve, revField] using hasDerivAt_pi.1 (h t ht) 3

/-- The field is smooth: its components are polynomials. -/
theorem revField_contDiff {n : WithTop ℕ∞} : ContDiff ℝ n (revField k₁ kb k₂ kb₂) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;>
    simp only [revField, substrateRate, revComplexRate, complexRate, revProductRate, Fin.isValue,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Matrix.cons_val_zero,
      Matrix.cons_val_one] <;>
    fun_prop

/-- On a zero coordinate of a nonnegative state, the field points into the orthant. -/
private theorem revField_boundary_nonneg (hk₁ : 0 ≤ k₁) (hkb : 0 ≤ kb) (hk₂ : 0 ≤ k₂)
    (hkb₂ : 0 ≤ kb₂) (y : Fin 4 → ℝ) (hy : ∀ i, 0 ≤ y i) (i : Fin 4) (hi : y i = 0) :
    0 ≤ revField k₁ kb k₂ kb₂ y i := by
  fin_cases i
  · change y 0 = 0 at hi
    simpa [revField, substrateRate, hi] using mul_nonneg hkb (hy 1)
  · change y 1 = 0 at hi
    simpa [revField, revComplexRate, complexRate, hi] using
      add_nonneg (mul_nonneg (mul_nonneg hk₁ (hy 2)) (hy 0))
        (mul_nonneg (mul_nonneg hkb₂ (hy 2)) (hy 3))
  · change y 2 = 0 at hi
    simpa [revField, revComplexRate, complexRate, hi] using
      mul_nonneg (add_nonneg hkb hk₂) (hy 1)
  · change y 3 = 0 at hi
    simpa [revField, revProductRate, hi] using mul_nonneg hk₂ (hy 1)

private theorem rev_nonneg {α : ℝ → Fin 4 → ℝ} {T : ℝ}
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt α (revField k₁ kb k₂ kb₂ (α t)) t)
    (hk₁ : 0 ≤ k₁) (hkb : 0 ≤ kb) (hk₂ : 0 ≤ k₂) (hkb₂ : 0 ≤ kb₂)
    (h0 : ∀ i, 0 ≤ α 0 i) {t : ℝ} (ht : t ∈ Icc 0 T) : ∀ i, 0 ≤ α t i :=
  MetaMathlibExt.orthant_invariant_of_boundary_nonneg revField_contDiff.locallyLipschitz
    (revField_boundary_nonneg hk₁ hkb hk₂ hkb₂) (convex_Icc 0 T) hd
    ⟨le_rfl, ht.1.trans ht.2⟩ h0 t ht ht.1

private theorem revField_lip (q : ℝ × (Fin 4 → ℝ)) :
    ∃ C : NNReal, ∃ u ∈ 𝓝 q, ∀ t : ℝ, ∀ x y : Fin 4 → ℝ,
      (t, x) ∈ u ∩ univ → (t, y) ∈ u ∩ univ →
        dist (revField k₁ kb k₂ kb₂ x) (revField k₁ kb k₂ kb₂ y) ≤ C * dist x y := by
  obtain ⟨C, u, hu, hC⟩ :=
    (revField_contDiff (k₁ := k₁) (kb := kb) (k₂ := k₂) (kb₂ := kb₂)).locallyLipschitz q.2
  refine ⟨C, univ ×ˢ u, prod_mem_nhds univ_mem hu, ?_⟩
  rintro t x y ⟨⟨-, hx⟩, -⟩ ⟨⟨-, hy⟩, -⟩
  exact hC.dist_le_mul x hx y hy

/-- On `[0, T]`, curves following the field keep total enzyme and total substrate. -/
private theorem rev_conservation {α : ℝ → Fin 4 → ℝ} {T : ℝ}
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt α (revField k₁ kb k₂ kb₂ (α t)) t)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    α t 2 + α t 1 = α 0 2 + α 0 1 ∧
      α t 0 + α t 1 + α t 3 = α 0 0 + α 0 1 + α 0 3 := by
  have hm (u : ℝ) (hu : u ∈ Icc 0 T) (i : Fin 4) := hasDerivAt_pi.1 (hd u hu) i
  have hE : ∀ u ∈ Icc 0 T, HasDerivAt (fun u => α u 2 + α u 1) 0 u := fun u hu => by
    convert (hm u hu 2).add (hm u hu 1) using 1
    simp [revField]
  have hS : ∀ u ∈ Icc 0 T, HasDerivAt (fun u => α u 0 + α u 1 + α u 3) 0 u := fun u hu => by
    convert ((hm u hu 0).add (hm u hu 1)).add (hm u hu 3) using 1
    simp [revField, substrateRate, revComplexRate, complexRate, revProductRate]
    ring
  exact ⟨constant_of_has_deriv_right_zero (fun u hu => (hE u hu).continuousAt.continuousWithinAt)
      (fun u hu => (hE u (Ico_subset_Icc_self hu)).hasDerivWithinAt) t ht,
    constant_of_has_deriv_right_zero (fun u hu => (hS u hu).continuousAt.continuousWithinAt)
      (fun u hu => (hS u (Ico_subset_Icc_self hu)).hasDerivWithinAt) t ht⟩

/-! ### Global existence -/

/-- **Global nonnegative trajectories of the reversible Michaelis–Menten system.** For
nonnegative rate constants and every nonnegative initial state `(s₀, c₀, e₀, p₀)`, the system
has a solution with these initial values on `[0, ∞)` such that for all `t ≥ 0` all four
coordinates are nonnegative, the total enzyme `e + c = e₀ + c₀` and the total substrate
`s + c + p = s₀ + c₀ + p₀` are conserved. -/
theorem exists_isSolution_nonneg (hk₁ : 0 ≤ k₁) (hkb : 0 ≤ kb) (hk₂ : 0 ≤ k₂) (hkb₂ : 0 ≤ kb₂)
    {s₀ c₀ e₀ p₀ : ℝ} (hs₀ : 0 ≤ s₀) (hc₀ : 0 ≤ c₀) (he₀ : 0 ≤ e₀) (hp₀ : 0 ≤ p₀) :
    ∃ s c e p : ℝ → ℝ, IsSolution k₁ kb k₂ kb₂ s c e p ∧
      s 0 = s₀ ∧ c 0 = c₀ ∧ e 0 = e₀ ∧ p 0 = p₀ ∧
      (∀ t, 0 ≤ t → 0 ≤ s t ∧ 0 ≤ c t ∧ 0 ≤ e t ∧ 0 ≤ p t) ∧
      (∀ t, 0 ≤ t → e t + c t = e₀ + c₀) ∧
      (∀ t, 0 ≤ t → s t + c t + p t = s₀ + c₀ + p₀) := by
  obtain ⟨J, α, hα0, hJo, h0J, hJc, hαd, hexit⟩ :=
    MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_maximal_solution_exit_compact univ
      (fun q : ℝ × (Fin 4 → ℝ) => revField k₁ kb k₂ kb₂ q.2) 0 ![s₀, c₀, e₀, p₀] isOpen_univ
      trivial ((revField_contDiff (n := 1)).continuous.comp continuous_snd).continuousOn
      fun q _ => revField_lip q
  have hd : ∀ T ∈ J, ∀ t ∈ Icc 0 T, HasDerivAt α (revField k₁ kb k₂ kb₂ (α t)) t :=
    fun T hT t ht => (hαd t (hJc 0 h0J T hT ht)).2
  have hinit : α 0 0 = s₀ ∧ α 0 1 = c₀ ∧ α 0 2 = e₀ ∧ α 0 3 = p₀ := by simp [hα0]
  have h0 : ∀ i, 0 ≤ α 0 i := fun i => by
    fin_cases i <;> simp [hα0, hs₀, hc₀, he₀, hp₀]
  have hfw : ∀ T ∈ J, 0 ≤ T → ∀ i, 0 ≤ α T i := fun T hT hT0 =>
    rev_nonneg (hd T hT) hk₁ hkb hk₂ hkb₂ h0 ⟨hT0, le_rfl⟩
  have hcons : ∀ T ∈ J, 0 ≤ T →
      α T 2 + α T 1 = e₀ + c₀ ∧ α T 0 + α T 1 + α T 3 = s₀ + c₀ + p₀ := fun T hT hT0 => by
    have := rev_conservation (hd T hT) ⟨hT0, le_rfl⟩
    rwa [hinit.1, hinit.2.1, hinit.2.2.1, hinit.2.2.2] at this
  have hglobal : Ici 0 ⊆ J := by
    intro T hT0
    by_contra hTJ
    obtain ⟨⟨c, hcJ, hc⟩, -⟩ := hexit
      (Icc 0 T ×ˢ Icc (0 : Fin 4 → ℝ) (fun _ => (e₀ + c₀) + (s₀ + c₀ + p₀)))
      (isCompact_Icc.prod isCompact_Icc) (subset_univ _)
    have htJ : max c 0 ∈ J := by rcases max_choice c 0 with h | h <;> rw [h] <;> assumption
    set t := max c 0
    have ht0 : 0 ≤ t := le_max_right _ _
    have htT : t ≤ T := by
      by_contra h
      exact hTJ (hJc 0 h0J t htJ ⟨hT0, (not_le.1 h).le⟩)
    have hnn := hfw t htJ ht0
    obtain ⟨hE, hS⟩ := hcons t htJ ht0
    refine hc t htJ (le_max_left _ _) ⟨⟨ht0, htT⟩, fun i => by simpa using hnn i, fun i => ?_⟩
    have := hnn 0; have := hnn 1; have := hnn 2; have := hnn 3
    fin_cases i <;> simp <;> linarith
  have hJt : ∀ t, 0 ≤ t → t ∈ J := fun t ht => hglobal ht
  have hm : ∀ t, 0 ≤ t → ∀ i, HasDerivAt (α · i) (revField k₁ kb k₂ kb₂ (α t) i) t :=
    fun t ht i => hasDerivAt_pi.1 (hαd t (hJt t ht)).2 i
  have hsol : IsSolution k₁ kb k₂ kb₂ (α · 0) (α · 1) (α · 2) (α · 3) :=
    ⟨fun t ht => hm t ht 0, fun t ht => hm t ht 1, fun t ht => hm t ht 2, fun t ht => hm t ht 3⟩
  refine ⟨(α · 0), (α · 1), (α · 2), (α · 3), hsol, hinit.1, hinit.2.1, hinit.2.2.1,
    hinit.2.2.2, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · have hnn := hfw t (hJt t ht) ht
    exact ⟨hnn 0, hnn 1, hnn 2, hnn 3⟩
  · rw [hsol.enzyme_conservation ht, hinit.2.2.1, hinit.2.1]
  · rw [hsol.substrate_conservation ht, hinit.1, hinit.2.1, hinit.2.2.2]

/-! ### Forward uniqueness and invariance for every solution -/

/-- **Forward uniqueness.** Two solutions of the reversible system (any real rate constants)
with the same initial values agree at every time `t ≥ 0`. -/
theorem IsSolution.eq_of_initial {s' c' e' p' : ℝ → ℝ} (h : IsSolution k₁ kb k₂ kb₂ s c e p)
    (h' : IsSolution k₁ kb k₂ kb₂ s' c' e' p') (hs : s 0 = s' 0) (hc : c 0 = c' 0)
    (he : e 0 = e' 0) (hp : p 0 = p' 0) {t : ℝ} (ht : 0 ≤ t) :
    s t = s' t ∧ c t = c' t ∧ e t = e' t ∧ p t = p' t := by
  have hd := isSolution_iff_hasDerivAt_revCurve.1 h
  have hd' := isSolution_iff_hasDerivAt_revCurve.1 h'
  have hcont : ContinuousOn (revCurve s c e p) (Icc 0 t) :=
    fun x hx => (hd x hx.1).continuousAt.continuousWithinAt
  have hcont' : ContinuousOn (revCurve s' c' e' p') (Icc 0 t) :=
    fun x hx => (hd' x hx.1).continuousAt.continuousWithinAt
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont'
  obtain ⟨K, hK⟩ := ((revField_contDiff (k₁ := k₁) (kb := kb) (k₂ := k₂) (kb₂ := kb₂)
    (n := 1)).contDiffOn (s := closedBall 0 (max C₁ C₂))).exists_lipschitzOnWith one_ne_zero
    (convex_closedBall _ _) (isCompact_closedBall _ _)
  have heq := ODE_solution_unique_of_mem_Icc_right (v := fun _ => revField k₁ kb k₂ kb₂)
    (s := fun _ => closedBall 0 (max C₁ C₂))
    (fun _ _ => hK) hcont (fun x hx => (hd x hx.1).hasDerivWithinAt)
    (fun x hx => mem_closedBall_zero_iff.2
      ((hC₁ x (Ico_subset_Icc_self hx)).trans (le_max_left _ _)))
    hcont' (fun x hx => (hd' x hx.1).hasDerivWithinAt)
    (fun x hx => mem_closedBall_zero_iff.2
      ((hC₂ x (Ico_subset_Icc_self hx)).trans (le_max_right _ _)))
    (by simp [revCurve, hs, hc, he, hp]) ⟨ht, le_rfl⟩
  exact ⟨congrFun heq 0, congrFun heq 1, congrFun heq 2, congrFun heq 3⟩

/-- **Invariance of the nonnegative orthant.** Along every solution with nonnegative rate
constants and nonnegative initial data, all four coordinates stay nonnegative for `t ≥ 0`. -/
theorem IsSolution.nonneg (h : IsSolution k₁ kb k₂ kb₂ s c e p) (hk₁ : 0 ≤ k₁) (hkb : 0 ≤ kb)
    (hk₂ : 0 ≤ k₂) (hkb₂ : 0 ≤ kb₂) (hs : 0 ≤ s 0) (hc : 0 ≤ c 0) (he : 0 ≤ e 0)
    (hp : 0 ≤ p 0) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ s t ∧ 0 ≤ c t ∧ 0 ≤ e t ∧ 0 ≤ p t := by
  obtain ⟨s', c', e', p', h', hs', hc', he', hp', hnn, -, -⟩ :=
    exists_isSolution_nonneg hk₁ hkb hk₂ hkb₂ hs hc he hp
  obtain ⟨h1, h2, h3, h4⟩ := h.eq_of_initial h' hs'.symm hc'.symm he'.symm hp'.symm ht
  rw [h1, h2, h3, h4]
  exact hnn t ht

/-! ### Equilibria: detailed balance and the Haldane relation -/

/-- **Equilibria are detailed balanced.** The field vanishes at `x = (s, c, e, p)` iff both
reversible steps are balanced: `k₁ e s = kb c` and `k₂ c = kb₂ e p` (any real rate constants). -/
theorem revField_eq_zero_iff {x : Fin 4 → ℝ} :
    revField k₁ kb k₂ kb₂ x = 0 ↔ k₁ * x 2 * x 0 = kb * x 1 ∧ k₂ * x 1 = kb₂ * x 2 * x 3 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h3 := congrFun h 3
    simp [revField, substrateRate, revProductRate] at h0 h3
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    ext i
    fin_cases i <;> simp [revField, substrateRate, revComplexRate, complexRate,
      revProductRate] <;> linarith

/-- A constant curve solves the system iff its value is a zero of the field. -/
theorem isSolution_const_iff {x : Fin 4 → ℝ} :
    IsSolution k₁ kb k₂ kb₂ (fun _ => x 0) (fun _ => x 1) (fun _ => x 2) (fun _ => x 3) ↔
      revField k₁ kb k₂ kb₂ x = 0 := by
  rw [isSolution_iff_hasDerivAt_revCurve]
  have hx : ∀ t, revCurve (fun _ => x 0) (fun _ => x 1) (fun _ => x 2) (fun _ => x 3) t = x :=
    fun t => by ext i; fin_cases i <;> rfl
  have hc : revCurve (fun _ => x 0) (fun _ => x 1) (fun _ => x 2) (fun _ => x 3) =
      fun _ => x := funext hx
  simp only [hx, hc]
  constructor
  · intro h
    exact ((h 0 le_rfl).unique (hasDerivAt_const 0 x)).trans rfl
  · intro h t _
    rw [h]
    exact hasDerivAt_const t x

/-- A solution started at an equilibrium stays there for `t ≥ 0`. -/
theorem IsSolution.eq_of_equilibrium (h : IsSolution k₁ kb k₂ kb₂ s c e p)
    (h0 : revField k₁ kb k₂ kb₂ ![s 0, c 0, e 0, p 0] = 0) {t : ℝ} (ht : 0 ≤ t) :
    s t = s 0 ∧ c t = c 0 ∧ e t = e 0 ∧ p t = p 0 :=
  h.eq_of_initial (isSolution_const_iff.2 h0) rfl rfl rfl rfl ht

/-- **Haldane relation.** At an equilibrium with free enzyme `e ≠ 0`,
`k₁ k₂ s = kb kb₂ p` (any real rate constants). -/
theorem haldane_of_revField_eq_zero {x : Fin 4 → ℝ} (h : revField k₁ kb k₂ kb₂ x = 0)
    (he : x 2 ≠ 0) : k₁ * k₂ * x 0 = kb * kb₂ * x 3 := by
  obtain ⟨h1, h2⟩ := revField_eq_zero_iff.1 h
  have : x 2 * (k₁ * k₂ * x 0) = x 2 * (kb * kb₂ * x 3) := by
    linear_combination k₂ * h1 + kb * h2
  exact mul_left_cancel₀ he this

/-- **Haldane relation, equilibrium-constant form.** At an equilibrium with `e ≠ 0`, `s ≠ 0`
and `kb, kb₂ ≠ 0`, the product-to-substrate ratio is `K_eq = k₁ k₂ / (kb kb₂)`. -/
theorem haldane_div {x : Fin 4 → ℝ} (h : revField k₁ kb k₂ kb₂ x = 0) (he : x 2 ≠ 0)
    (hs : x 0 ≠ 0) (hkb : kb ≠ 0) (hkb₂ : kb₂ ≠ 0) : x 3 / x 0 = k₁ * k₂ / (kb * kb₂) := by
  have := haldane_of_revField_eq_zero h he
  rw [div_eq_div_iff hs (mul_ne_zero hkb hkb₂)]
  linarith

/-! ### One equilibrium per compatibility class -/

/-- The total substrate `s + c + p` at the equilibrium with free substrate `σ` and total enzyme
`eT`: `σ + k₁ eT σ/(kb + k₁ σ) + K_eq σ`. -/
private noncomputable def classMass (k₁ kb k₂ kb₂ eT σ : ℝ) : ℝ :=
  σ + k₁ * eT * σ / (kb + k₁ * σ) + k₁ * k₂ / (kb * kb₂) * σ

private theorem classMass_strictMonoOn (hk₁ : 0 < k₁) (hkb : 0 < kb) (hk₂ : 0 < k₂)
    (hkb₂ : 0 < kb₂) {eT : ℝ} (heT : 0 < eT) :
    StrictMonoOn (classMass k₁ kb k₂ kb₂ eT) (Ici 0) := by
  intro a ha b hb hab
  simp only [mem_Ici] at ha hb
  have hK : 0 ≤ k₁ * k₂ / (kb * kb₂) := by positivity
  have hmid : k₁ * eT * a / (kb + k₁ * a) ≤ k₁ * eT * b / (kb + k₁ * b) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (mul_pos hk₁ heT) hkb, mul_nonneg (mul_nonneg hk₁.le heT.le) hkb.le]
  unfold classMass
  nlinarith [mul_le_mul_of_nonneg_left hab.le hK]

private theorem continuousOn_classMass (hk₁ : 0 < k₁) (hkb : 0 < kb) (eT : ℝ) :
    ContinuousOn (classMass k₁ kb k₂ kb₂ eT) (Ici 0) := by
  unfold classMass
  refine ContinuousOn.add (ContinuousOn.add continuousOn_id ?_) (by fun_prop)
  exact ContinuousOn.div (by fun_prop) (by fun_prop) fun σ hσ => by
    simp only [mem_Ici] at hσ; positivity

/-- At an equilibrium in the class `e + c = eT`, the complex is `k₁ eT s / (kb + k₁ s)`. -/
private theorem complex_eq_of_equilibrium (hk₁ : 0 < k₁) (hkb : 0 < kb) {x : Fin 4 → ℝ} {eT : ℝ}
    (hx0 : 0 ≤ x 0) (h : k₁ * x 2 * x 0 = kb * x 1) (hE : x 2 + x 1 = eT) :
    x 1 = k₁ * eT * x 0 / (kb + k₁ * x 0) := by
  rw [eq_div_iff (by positivity)]
  have : x 2 = eT - x 1 := by linarith
  rw [this] at h
  linarith

/-- **Nonnegative equilibria with positive totals are positive.** For positive rate constants,
every nonnegative equilibrium in a class with `E_T > 0`, `S_T > 0` has all four coordinates
positive. -/
theorem pos_of_equilibrium (hk₁ : 0 < k₁) (hkb : 0 < kb) (hk₂ : 0 < k₂) (hkb₂ : 0 < kb₂)
    {eT sT : ℝ} (heT : 0 < eT) (hsT : 0 < sT) {x : Fin 4 → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hE : x 2 + x 1 = eT) (hS : x 0 + x 1 + x 3 = sT) (h : revField k₁ kb k₂ kb₂ x = 0) :
    ∀ i, 0 < x i := by
  obtain ⟨h1, h2⟩ := revField_eq_zero_iff.1 h
  have he : 0 < x 2 := by
    rcases (hx 2).lt_or_eq with h2' | h2'
    · exact h2'
    · rw [← h2'] at h1 hE
      have : x 1 = 0 := by
        have := mul_eq_zero.1 (show kb * x 1 = 0 by linarith)
        exact this.resolve_left hkb.ne'
      linarith
  have hs : 0 < x 0 := by
    rcases (hx 0).lt_or_eq with h0' | h0'
    · exact h0'
    · rw [← h0'] at h1 hS
      have hc : x 1 = 0 :=
        (mul_eq_zero.1 (show kb * x 1 = 0 by linarith)).resolve_left hkb.ne'
      rw [hc] at h2 hS
      have hp : x 3 = 0 :=
        (mul_eq_zero.1 (show kb₂ * x 2 * x 3 = 0 by linarith)).resolve_left
          (mul_pos hkb₂ he).ne'
      linarith
  have hc : 0 < x 1 := by
    have : 0 < kb * x 1 := by rw [← h1]; positivity
    exact pos_of_mul_pos_right this hkb.le
  have hp : 0 < x 3 := by
    have : 0 < kb₂ * x 2 * x 3 := by rw [← h2]; positivity
    exact pos_of_mul_pos_right this (mul_pos hkb₂ he).le
  intro i
  fin_cases i
  exacts [hs, hc, he, hp]

/-- At a nonnegative equilibrium in the class `(eT, sT)` with positive data, the total substrate
is `classMass` of the free substrate. -/
private theorem classMass_eq (hk₁ : 0 < k₁) (hkb : 0 < kb) (hk₂ : 0 < k₂) (hkb₂ : 0 < kb₂)
    {eT sT : ℝ} (heT : 0 < eT) (hsT : 0 < sT) {x : Fin 4 → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hE : x 2 + x 1 = eT) (hS : x 0 + x 1 + x 3 = sT) (h : revField k₁ kb k₂ kb₂ x = 0) :
    classMass k₁ kb k₂ kb₂ eT (x 0) = sT := by
  have hpos := pos_of_equilibrium hk₁ hkb hk₂ hkb₂ heT hsT hx hE hS h
  obtain ⟨h1, -⟩ := revField_eq_zero_iff.1 h
  have hc := complex_eq_of_equilibrium hk₁ hkb (hx 0) h1 hE
  have hH := haldane_of_revField_eq_zero h (hpos 2).ne'
  have hp : x 3 = k₁ * k₂ / (kb * kb₂) * x 0 := by
    field_simp
    linarith
  unfold classMass
  rw [← hc, ← hp]
  linarith

/-- **Existence and uniqueness of the equilibrium in each compatibility class.** For positive
rate constants and positive totals `E_T`, `S_T`, exactly one nonnegative state
`x = (s, c, e, p)` has `e + c = E_T`, `s + c + p = S_T` and is an equilibrium; by
`pos_of_equilibrium` it is positive, and by `haldane_div` it has `p / s = k₁ k₂ / (kb kb₂)`. -/
theorem existsUnique_equilibrium (hk₁ : 0 < k₁) (hkb : 0 < kb) (hk₂ : 0 < k₂) (hkb₂ : 0 < kb₂)
    {eT sT : ℝ} (heT : 0 < eT) (hsT : 0 < sT) :
    ∃! x : Fin 4 → ℝ, (∀ i, 0 ≤ x i) ∧ x 2 + x 1 = eT ∧ x 0 + x 1 + x 3 = sT ∧
      revField k₁ kb k₂ kb₂ x = 0 := by
  set K := k₁ * k₂ / (kb * kb₂) with hKdef
  have hK : 0 < K := by positivity
  -- existence of the free substrate level by the intermediate value theorem
  have hcont : ContinuousOn (classMass k₁ kb k₂ kb₂ eT) (Icc 0 sT) :=
    (continuousOn_classMass hk₁ hkb eT).mono Icc_subset_Ici_self
  have hlo : classMass k₁ kb k₂ kb₂ eT 0 = 0 := by simp [classMass]
  have hhi : sT ≤ classMass k₁ kb k₂ kb₂ eT sT := by
    unfold classMass
    have : 0 ≤ k₁ * eT * sT / (kb + k₁ * sT) := by positivity
    have : 0 ≤ K * sT := by positivity
    linarith
  obtain ⟨σ, hσ, hσeq⟩ := intermediate_value_Icc hsT.le hcont ⟨by rw [hlo]; exact hsT.le, hhi⟩
  have hσ0 : 0 < σ := by
    rcases hσ.1.lt_or_eq with h | h
    · exact h
    · rw [← h, hlo] at hσeq; linarith
  have hden : 0 < kb + k₁ * σ := by positivity
  set cσ := k₁ * eT * σ / (kb + k₁ * σ) with hcσ
  have hcσ0 : 0 ≤ cσ := by positivity
  have heσ : eT - cσ = eT * kb / (kb + k₁ * σ) := by
    rw [hcσ]; field_simp; ring
  have heσ0 : 0 ≤ eT - cσ := by rw [heσ]; positivity
  refine ⟨![σ, cσ, eT - cσ, K * σ], ⟨fun i => ?_, ?_, ?_, ?_⟩, ?_⟩
  · fin_cases i
    · exact hσ0.le
    · exact hcσ0
    · exact heσ0
    · exact (mul_pos hK hσ0).le
  · simp
  · simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
    unfold classMass at hσeq
    linarith
  · refine revField_eq_zero_iff.2 ⟨?_, ?_⟩
    · simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
      rw [heσ, hcσ]; field_simp
    · simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
      rw [heσ, hcσ, hKdef]; field_simp
  -- uniqueness: the free substrate is pinned by strict monotonicity of `classMass`
  · rintro y ⟨hy, hyE, hyS, hy0⟩
    have hmy := classMass_eq hk₁ hkb hk₂ hkb₂ heT hsT hy hyE hyS hy0
    have hs : y 0 = σ := (classMass_strictMonoOn hk₁ hkb hk₂ hkb₂ heT).injOn
      (show y 0 ∈ Ici 0 from hy 0) (show σ ∈ Ici 0 from hσ.1) (hmy.trans hσeq.symm)
    have hc : y 1 = cσ := by
      rw [complex_eq_of_equilibrium hk₁ hkb (hy 0) (revField_eq_zero_iff.1 hy0).1 hyE, hs]
    ext i
    fin_cases i
    · simpa using hs
    · simpa using hc
    · change y 2 = eT - cσ
      linarith
    · change y 3 = K * σ
      unfold classMass at hσeq
      rw [hs, hc] at hyS
      linarith

end MathlibExt.Biology.Dynamics.ReversibleMichaelisMenten
