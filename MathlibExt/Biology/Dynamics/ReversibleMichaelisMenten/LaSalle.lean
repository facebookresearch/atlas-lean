/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ODE.LaSalle
public import MathlibExt.Biology.Dynamics.ReversibleMichaelisMenten
public import MathlibExt.Biology.Dynamics.ComplexBalanced
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Convergence of reversible Michaelis–Menten kinetics

Every solution of the reversible Michaelis–Menten system `E + S ⇌ C ⇌ E + P`
(`MathlibExt.Biology.Dynamics.ReversibleMichaelisMenten`) with nonnegative data and positive
totals converges to the unique (positive) equilibrium of its compatibility class. The proof
applies LaSalle's invariance principle for ODEs (`MathlibExt.Analysis.ODE.LaSalle`) with the
pseudo-Helmholtz function of `MathlibExt.Biology.Dynamics.ComplexBalanced` as the Lyapunov
function.

## Main results

* `mmNetwork`, `massActionField_mmNetwork`, `isComplexBalanced_mmNetwork`: the mechanism as a
  mass-action network whose equilibria are complex balanced;
* the Lyapunov function is the **pseudo-Helmholtz function**
  `G = ReactionNetwork.pseudoHelmholtz x*`; `helmholtzRate_mmNetwork_nonpos` is `V' ≤ 0` (the
  Horn–Jackson inequality `ReactionNetwork.helmholtzRate_nonpos` for `mmNetwork`), and
  `IsSolution.antitoneOn_pseudoHelmholtz` is monotonicity along solutions;
* `IsSolution.pos`: solutions with nonnegative data and positive totals are strictly positive
  for `t > 0`;
* `IsSolution.tendsto_equilibrium`: **every solution with nonnegative data and positive totals
  converges to the unique (positive) equilibrium of its compatibility class.**

## Scope

* The proof uses `lasalle_of_antitoneOn`, not `lasalle_of_hasFDerivAt`: `G` involves `log`, so it
  is not differentiable on the boundary of the orthant, which meets the compatibility class.
  Instead `IsSolution.pos` shows that a solution in the class along which `G` is constant is
  positive at `t = 2`, where `G' = 0` makes it an equilibrium.
* Global convergence for general complex-balanced mass-action systems (the global attractor
  conjecture) is not proved; the boundary argument here is specific to this four-species system.

## References

* F. Horn and R. Jackson, *General mass action kinetics*, Arch. Rational Mech. Anal. 47 (1972)
  81–116.
* A. Cornish-Bowden, *Fundamentals of Enzyme Kinetics*, 4th ed., Wiley-Blackwell (2012), ch. 2.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology NNReal

namespace MathlibExt.Biology.Dynamics.ReversibleMichaelisMenten

open MathlibExt.Analysis.ODE MathlibExt.Biology.Dynamics.ComplexBalanced
open MathlibExt.Biology.Dynamics.ComplexBalanced.ReactionNetwork (pseudoHelmholtz)
open MathlibExt.Biology.Dynamics.MichaelisMenten (substrateRate complexRate mmCurve)

variable {k₁ kb k₂ kb₂ : ℝ} {s c e p : ℝ → ℝ}

/-- The reversible Michaelis–Menten mechanism `E + S ⇌ C ⇌ E + P` as a mass-action reaction
network on the species `s, c, e, p` (indices `0, 1, 2, 3`, as in `revField`). Reactions:
`0 : E + S → C`, `1 : C → E + S`, `2 : C → E + P`, `3 : E + P → C`. -/
def mmNetwork : ReactionNetwork (Fin 4) (Fin 4) where
  src := ![![1, 0, 1, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 1]]
  prod := ![![0, 1, 0, 0], ![1, 0, 1, 0], ![0, 0, 1, 1], ![0, 1, 0, 0]]

/-- The rate constants of `mmNetwork`: `k₁` (binding), `kb` (unbinding of `S`), `k₂`
(catalysis), `kb₂` (rebinding of `P`). -/
def mmRates (k₁ kb k₂ kb₂ : ℝ) : Fin 4 → ℝ := ![k₁, kb, k₂, kb₂]

/-- The mass-action field of `mmNetwork` is the reversible Michaelis–Menten field. -/
theorem massActionField_mmNetwork :
    mmNetwork.massActionField (mmRates k₁ kb k₂ kb₂) = revField k₁ kb k₂ kb₂ := by
  ext x i
  fin_cases i <;>
    simp [ReactionNetwork.massActionField, mmNetwork, mmRates, Fin.sum_univ_four,
      Fin.prod_univ_four, revField, substrateRate, revComplexRate, complexRate,
      revProductRate] <;> ring

/-- **Equilibria are complex balanced.** Every zero of `revField` (a detailed-balanced state,
`revField_eq_zero_iff`) is a complex-balanced state of `mmNetwork`. -/
theorem isComplexBalanced_mmNetwork {x : Fin 4 → ℝ} (hx : revField k₁ kb k₂ kb₂ x = 0) :
    mmNetwork.IsComplexBalanced (mmRates k₁ kb k₂ kb₂) x := by
  obtain ⟨h1, h2⟩ := revField_eq_zero_iff.1 hx
  have hr : ∀ r, mmNetwork.rate (mmRates k₁ kb k₂ kb₂) x r =
      ![k₁ * x 0 * x 2, kb * x 1, k₂ * x 1, kb₂ * x 2 * x 3] r := by
    intro r
    fin_cases r <;> simp [ReactionNetwork.rate, mmNetwork, mmRates, Fin.prod_univ_four] <;> ring
  have e12 : mmNetwork.src 2 = mmNetwork.src 1 := rfl
  have p0 : mmNetwork.prod 0 = mmNetwork.src 1 := rfl
  have p1 : mmNetwork.prod 1 = mmNetwork.src 0 := rfl
  have p2 : mmNetwork.prod 2 = mmNetwork.src 3 := rfl
  have p3 : mmNetwork.prod 3 = mmNetwork.src 1 := rfl
  intro z
  rw [Finset.sum_filter, Finset.sum_filter]
  simp only [Fin.sum_univ_four, hr, e12, p0, p1, p2, p3]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  split_ifs <;> linarith

/-- The terms of the pseudo-Helmholtz gap: for `a > 0` and `y ≥ 0`,
`y (log y - log a - 1) + a ≥ 0`, with equality only at `y = a`. -/
private theorem helmholtz_gap_pos {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) (hne : y ≠ a) :
    0 < y * (Real.log y - Real.log a - 1) + a := by
  rcases hy.eq_or_lt with rfl | hy
  · simpa using ha
  have hne' : a / y ≠ 1 := fun h => hne ((div_eq_one_iff_eq hy.ne').1 h).symm
  have hlt := Real.log_lt_sub_one_of_pos (div_pos ha hy) hne'
  rw [Real.log_div ha.ne' hy.ne'] at hlt
  have := mul_lt_mul_of_pos_left hlt hy
  rw [mul_sub, mul_sub, mul_div_cancel₀ _ hy.ne'] at this
  nlinarith

private theorem helmholtz_gap_nonneg {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) :
    0 ≤ y * (Real.log y - Real.log a - 1) + a := by
  rcases eq_or_ne y a with rfl | hne
  · simp
  · exact (helmholtz_gap_pos ha hy hne).le

/-- **Gibbs inequality for the pseudo-Helmholtz function.** For a positive reference state
`cstar` and a nonnegative state `y`, `pseudoHelmholtz cstar y = pseudoHelmholtz cstar cstar`
only if `y = cstar`. -/
theorem eq_of_pseudoHelmholtz_eq {cstar y : Fin 4 → ℝ} (hcstar : ∀ i, 0 < cstar i)
    (hy : ∀ i, 0 ≤ y i) (h : pseudoHelmholtz cstar y = pseudoHelmholtz cstar cstar) :
    y = cstar := by
  by_contra hne
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  have hgap : pseudoHelmholtz cstar y - pseudoHelmholtz cstar cstar =
      ∑ j, (y j * (Real.log (y j) - Real.log (cstar j) - 1) + cstar j) := by
    unfold pseudoHelmholtz
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hpos : 0 < ∑ j, (y j * (Real.log (y j) - Real.log (cstar j) - 1) + cstar j) :=
    Finset.sum_pos' (fun j _ => helmholtz_gap_nonneg (hcstar j) (hy j))
      ⟨i, Finset.mem_univ _, helmholtz_gap_pos (hcstar i) (hy i) hi⟩
  rw [← hgap, h, sub_self] at hpos
  exact lt_irrefl _ hpos

/-- `x t e^{a t}` is nondecreasing when `x' ≥ -a x`, so positivity of `x` persists. -/
private theorem pos_of_pos_of_deriv_ge {x x' : ℝ → ℝ} {a : ℝ}
    (hd : ∀ t, 0 ≤ t → HasDerivAt x (x' t) t) (hb : ∀ t, 0 ≤ t → -a * x t ≤ x' t)
    {t₀ t : ℝ} (h₀ : 0 ≤ t₀) (ht : t₀ ≤ t) (hpos : 0 < x t₀) : 0 < x t := by
  have hmono : MonotoneOn (fun τ => x τ * Real.exp (a * τ)) (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun τ => (x' τ + a * x τ) * Real.exp (a * τ)) (convex_Ici 0) ?_ ?_ ?_
    · intro τ hτ
      exact ((hd τ hτ).continuousAt.mul (by fun_prop)).continuousWithinAt
    · intro τ hτ
      rw [interior_Ici] at hτ
      have he : HasDerivAt (fun τ => Real.exp (a * τ)) (Real.exp (a * τ) * a) τ := by
        simpa using ((hasDerivAt_id' τ).const_mul a).exp
      have : HasDerivAt (fun τ => x τ * Real.exp (a * τ))
          (x' τ * Real.exp (a * τ) + x τ * (Real.exp (a * τ) * a)) τ :=
        (hd τ (le_of_lt hτ)).mul he
      convert this.hasDerivWithinAt using 1
      ring
    · intro τ hτ
      rw [interior_Ici] at hτ
      exact mul_nonneg (by linarith [hb τ (le_of_lt hτ)]) (Real.exp_pos _).le
  have h1 : 0 < x t₀ * Real.exp (a * t₀) := mul_pos hpos (Real.exp_pos _)
  have h2 := hmono (mem_Ici.2 h₀) (mem_Ici.2 (h₀.trans ht)) ht
  exact (pos_iff_pos_of_mul_pos (h1.trans_le h2)).2 (Real.exp_pos _)

/-- A function constant on an open interval has derivative `0` inside it. -/
private theorem deriv_eq_zero_of_eqOn_Ioo {x : ℝ → ℝ} {d a b C τ : ℝ} (hx : HasDerivAt x d τ)
    (hz : ∀ u ∈ Ioo a b, x u = C) (hτ : τ ∈ Ioo a b) : d = 0 :=
  hx.unique ((hasDerivAt_const τ C).congr_of_eventuallyEq
    (Filter.eventually_of_mem (Ioo_mem_nhds hτ.1 hτ.2) hz))

/-- **Strict positivity.** For positive rate constants, nonnegative initial data and positive
totals `E_T = e₀ + c₀`, `S_T = s₀ + c₀ + p₀`, every solution has all four coordinates strictly
positive at every `t > 0`, even if some start at `0`. -/
theorem IsSolution.pos (h : IsSolution k₁ kb k₂ kb₂ s c e p) (hk₁ : 0 < k₁) (hkb : 0 < kb)
    (hk₂ : 0 < k₂) (hkb₂ : 0 < kb₂) (hs₀ : 0 ≤ s 0) (hc₀ : 0 ≤ c 0) (he₀ : 0 ≤ e 0)
    (hp₀ : 0 ≤ p 0) (hE : 0 < e 0 + c 0) (hS : 0 < s 0 + c 0 + p 0) {t : ℝ} (ht : 0 < t) :
    0 < s t ∧ 0 < c t ∧ 0 < e t ∧ 0 < p t := by
  have hnn := fun τ (hτ : 0 ≤ τ) => h.nonneg hk₁.le hkb.le hk₂.le hkb₂.le hs₀ hc₀ he₀ hp₀ hτ
  have hEc := fun τ (hτ : 0 ≤ τ) => h.enzyme_conservation hτ
  have hSc := fun τ (hτ : 0 ≤ τ) => h.substrate_conservation hτ
  -- positivity of each coordinate persists forward in time
  have hs_p : ∀ τ, 0 ≤ τ → τ ≤ t → 0 < s τ → 0 < s t := fun τ hτ hτt hpos =>
    pos_of_pos_of_deriv_ge (a := k₁ * (e 0 + c 0)) h.hasDerivAt_substrate (fun u hu => by
      obtain ⟨hsu, hcu, heu, hpu⟩ := hnn u hu
      rw [← hEc u hu]
      simp only [substrateRate]
      nlinarith [mul_nonneg (mul_nonneg hk₁.le hcu) hsu, mul_nonneg hkb.le hcu]) hτ hτt hpos
  have hc_p : ∀ τ, 0 ≤ τ → τ ≤ t → 0 < c τ → 0 < c t := fun τ hτ hτt hpos =>
    pos_of_pos_of_deriv_ge (a := kb + k₂) h.hasDerivAt_complex (fun u hu => by
      obtain ⟨hsu, hcu, heu, hpu⟩ := hnn u hu
      simp only [revComplexRate, complexRate]
      nlinarith [mul_nonneg (mul_nonneg hk₁.le heu) hsu, mul_nonneg (mul_nonneg hkb₂.le heu) hpu])
      hτ hτt hpos
  have he_p : ∀ τ, 0 ≤ τ → τ ≤ t → 0 < e τ → 0 < e t := fun τ hτ hτt hpos =>
    pos_of_pos_of_deriv_ge (a := (k₁ + kb₂) * (s 0 + c 0 + p 0)) h.hasDerivAt_enzyme
      (fun u hu => by
        obtain ⟨hsu, hcu, heu, hpu⟩ := hnn u hu
        rw [← hSc u hu]
        simp only [revComplexRate, complexRate]
        nlinarith [mul_nonneg (mul_nonneg hk₁.le heu) (add_nonneg hcu hpu),
          mul_nonneg (mul_nonneg hkb₂.le heu) (add_nonneg hsu hcu),
          mul_nonneg (add_nonneg hkb.le hk₂.le) hcu]) hτ hτt hpos
  have hp_p : ∀ τ, 0 ≤ τ → τ ≤ t → 0 < p τ → 0 < p t := fun τ hτ hτt hpos =>
    pos_of_pos_of_deriv_ge (a := kb₂ * (e 0 + c 0)) h.hasDerivAt_product (fun u hu => by
      obtain ⟨hsu, hcu, heu, hpu⟩ := hnn u hu
      rw [← hEc u hu]
      simp only [revProductRate]
      nlinarith [mul_nonneg hk₂.le hcu, mul_nonneg (mul_nonneg hkb₂.le hcu) hpu]) hτ hτt hpos
  -- a coordinate that vanishes at `t` vanishes on `[0, t]`
  have zero_on : ∀ x : ℝ → ℝ, (∀ τ, 0 ≤ τ → 0 ≤ x τ) →
      (∀ τ, 0 ≤ τ → τ ≤ t → 0 < x τ → 0 < x t) → ¬ 0 < x t → ∀ u ∈ Ioo 0 t, x u = 0 :=
    fun x hx hpers hxt u hu => le_antisymm (not_lt.1 fun hpos =>
      hxt (hpers u hu.1.le hu.2.le hpos)) (hx u hu.1.le)
  have hm : t / 2 ∈ Ioo 0 t := ⟨by linarith, by linarith⟩
  -- `c ≡ 0` on `(0, t)` is impossible
  have hc_ne : ¬ ∀ u ∈ Ioo 0 t, c u = 0 := by
    intro hc0
    have hd := deriv_eq_zero_of_eqOn_Ioo (h.hasDerivAt_complex _ hm.1.le) hc0 hm
    obtain ⟨hsu, -, heu, hpu⟩ := hnn _ hm.1.le
    have hEm := hEc _ hm.1.le
    have hSm := hSc _ hm.1.le
    rw [hc0 _ hm] at hEm hSm
    simp only [revComplexRate, complexRate, hc0 _ hm] at hd
    have he' : e (t / 2) = e 0 + c 0 := by linarith
    rw [he'] at hd
    have hA := mul_nonneg (mul_nonneg hk₁.le hE.le) hsu
    have hB := mul_nonneg (mul_nonneg hkb₂.le hE.le) hpu
    have h1 : k₁ * (e 0 + c 0) * s (t / 2) = 0 := by linarith
    have h2 : kb₂ * (e 0 + c 0) * p (t / 2) = 0 := by linarith
    have hs' := (mul_eq_zero.1 h1).resolve_left (mul_pos hk₁ hE).ne'
    have hp' := (mul_eq_zero.1 h2).resolve_left (mul_pos hkb₂ hE).ne'
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hst
    have hs0 := zero_on s (fun τ hτ => (hnn τ hτ).1) hs_p hst
    refine hc_ne fun u hu => ?_
    have hd := deriv_eq_zero_of_eqOn_Ioo (h.hasDerivAt_substrate u hu.1.le) hs0 hu
    simp only [substrateRate, hs0 u hu] at hd
    have : kb * c u = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hkb.ne'
  · by_contra hct
    exact hc_ne (zero_on c (fun τ hτ => (hnn τ hτ).2.1) hc_p hct)
  · by_contra het
    have he0 := zero_on e (fun τ hτ => (hnn τ hτ).2.2.1) he_p het
    have hd := deriv_eq_zero_of_eqOn_Ioo (h.hasDerivAt_enzyme _ hm.1.le) he0 hm
    have hEm := hEc _ hm.1.le
    simp only [revComplexRate, complexRate, he0 _ hm] at hd hEm
    nlinarith [add_pos hkb hk₂]
  · by_contra hpt
    have hp0 := zero_on p (fun τ hτ => (hnn τ hτ).2.2.2) hp_p hpt
    refine hc_ne fun u hu => ?_
    have hd := deriv_eq_zero_of_eqOn_Ioo (h.hasDerivAt_product u hu.1.le) hp0 hu
    simp only [revProductRate, hp0 u hu] at hd
    have : k₂ * c u = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hk₂.ne'

/-- **The orbital derivative of the pseudo-Helmholtz function.** Along any curve with
`φ' = revField (φ t)` at a time where `φ t > 0`, `G = pseudoHelmholtz cstar` has derivative
`mmNetwork.helmholtzRate (mmRates k₁ kb k₂ kb₂) cstar (φ t)`. -/
theorem hasDerivAt_pseudoHelmholtz_revField (cstar : Fin 4 → ℝ) {φ : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hφ : HasDerivAt φ (revField k₁ kb k₂ kb₂ (φ t)) t) (hpos : ∀ i, 0 < φ t i) :
    HasDerivAt (fun τ => pseudoHelmholtz cstar (φ τ))
      (mmNetwork.helmholtzRate (mmRates k₁ kb k₂ kb₂) cstar (φ t)) t :=
  mmNetwork.hasDerivAt_pseudoHelmholtz cstar (by rw [massActionField_mmNetwork]; exact hφ) hpos

/-- **`V' ≤ 0` for reversible Michaelis–Menten.** For positive rate constants and a positive
equilibrium `cstar` (a zero of `revField`), the orbital derivative of the pseudo-Helmholtz
function `G = pseudoHelmholtz cstar` is `≤ 0` at every positive state, and it vanishes exactly
at the equilibria. This is the Horn–Jackson inequality `ReactionNetwork.helmholtzRate_nonpos`
for `mmNetwork`, whose hypothesis (complex balance of `cstar`) is detailed balance,
`revField_eq_zero_iff`. -/
theorem helmholtzRate_mmNetwork_nonpos (hk₁ : 0 < k₁) (hkb : 0 < kb) (hk₂ : 0 < k₂)
    (hkb₂ : 0 < kb₂) {cstar x : Fin 4 → ℝ} (hcstar : ∀ i, 0 < cstar i)
    (hf : revField k₁ kb k₂ kb₂ cstar = 0) (hx : ∀ i, 0 < x i) :
    mmNetwork.helmholtzRate (mmRates k₁ kb k₂ kb₂) cstar x ≤ 0 ∧
      (mmNetwork.helmholtzRate (mmRates k₁ kb k₂ kb₂) cstar x = 0 ↔
        revField k₁ kb k₂ kb₂ x = 0) := by
  have hk : ∀ r, 0 < mmRates k₁ kb k₂ kb₂ r := fun r => by
    fin_cases r <;> simp [mmRates, hk₁, hkb, hk₂, hkb₂]
  refine ⟨mmNetwork.helmholtzRate_nonpos hk hcstar (isComplexBalanced_mmNetwork hf) hx, ?_⟩
  rw [mmNetwork.helmholtzRate_eq_zero_iff hk hcstar (isComplexBalanced_mmNetwork hf) hx,
    massActionField_mmNetwork]

/-- The pseudo-Helmholtz function is continuous on the whole space (with `0 log 0 = 0`). -/
theorem continuous_pseudoHelmholtz (cstar : Fin 4 → ℝ) : Continuous (pseudoHelmholtz cstar) := by
  unfold pseudoHelmholtz
  refine continuous_finsetSum _ fun i _ => ?_
  have : (fun y : Fin 4 → ℝ => y i * (Real.log (y i) - Real.log (cstar i) - 1)) =
      fun y => y i * Real.log (y i) - y i * (Real.log (cstar i) + 1) := by
    funext y; ring
  rw [this]
  exact (Real.continuous_mul_log.comp (continuous_apply i)).sub
    ((continuous_apply i).mul continuous_const)

/-- **The pseudo-Helmholtz function is a Lyapunov function for reversible Michaelis–Menten.**
For positive rate constants, a positive equilibrium `cstar`, nonnegative initial data and
positive totals, `t ↦ pseudoHelmholtz cstar (s t, c t, e t, p t)` is nonincreasing on
`[0, ∞)`, also for solutions that start on the boundary of the orthant. -/
theorem IsSolution.antitoneOn_pseudoHelmholtz (h : IsSolution k₁ kb k₂ kb₂ s c e p)
    (hk₁ : 0 < k₁) (hkb : 0 < kb) (hk₂ : 0 < k₂) (hkb₂ : 0 < kb₂) (hs₀ : 0 ≤ s 0)
    (hc₀ : 0 ≤ c 0) (he₀ : 0 ≤ e 0) (hp₀ : 0 ≤ p 0) (hE : 0 < e 0 + c 0)
    (hS : 0 < s 0 + c 0 + p 0) {cstar : Fin 4 → ℝ} (hcstar : ∀ i, 0 < cstar i)
    (hf : revField k₁ kb k₂ kb₂ cstar = 0) :
    AntitoneOn (fun t => pseudoHelmholtz cstar (mmCurve s c e p t)) (Ici 0) := by
  have hd := isSolution_iff_hasDerivAt_mmCurve.1 h
  have hpos : ∀ t, 0 < t → ∀ i, 0 < mmCurve s c e p t i := fun t ht i => by
    obtain ⟨h1, h2, h3, h4⟩ := h.pos hk₁ hkb hk₂ hkb₂ hs₀ hc₀ he₀ hp₀ hE hS ht
    fin_cases i <;> simpa [mmCurve]
  refine antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun t => mmNetwork.helmholtzRate (mmRates k₁ kb k₂ kb₂) cstar (mmCurve s c e p t))
    (convex_Ici 0) ((continuous_pseudoHelmholtz cstar).comp_continuousOn
      fun t ht => (hd t ht).continuousAt.continuousWithinAt) (fun t ht => ?_) (fun t ht => ?_)
  · rw [interior_Ici] at ht
    exact (hasDerivAt_pseudoHelmholtz_revField cstar (hd t (le_of_lt ht))
      (hpos t ht)).hasDerivWithinAt
  · rw [interior_Ici] at ht
    exact (helmholtzRate_mmNetwork_nonpos hk₁ hkb hk₂ hkb₂ hcstar hf (hpos t ht)).1

/-- **Global convergence for reversible Michaelis–Menten kinetics, via LaSalle.** For positive
rate constants, every solution with nonnegative initial data and positive totals
`E_T = e₀ + c₀`, `S_T = s₀ + c₀ + p₀` converges to the unique equilibrium `x*` of its
compatibility class (`existsUnique_equilibrium`), which is positive.

Proof: `lasalle_of_antitoneOn` on the compact, convex, forward-invariant class
`K = {x ≥ 0 | x₂ + x₁ = E_T, x₀ + x₁ + x₃ = S_T}` with the Lyapunov function
`G = pseudoHelmholtz x*` (`IsSolution.antitoneOn_pseudoHelmholtz`). A solution in `K` along
which `G` is constant is positive at `t = 2` (`IsSolution.pos`), so there its orbital derivative
vanishes, hence it sits at an equilibrium of the class, i.e. at `x*`; since `G` is constant, the
Gibbs inequality `eq_of_pseudoHelmholtz_eq` forces the starting point to be `x*` as well. So
the largest forward-invariant set on which `G` is constant is `{x*}`. -/
theorem IsSolution.tendsto_equilibrium (h : IsSolution k₁ kb k₂ kb₂ s c e p)
    (hk₁ : 0 < k₁) (hkb : 0 < kb) (hk₂ : 0 < k₂) (hkb₂ : 0 < kb₂) (hs₀ : 0 ≤ s 0)
    (hc₀ : 0 ≤ c 0) (he₀ : 0 ≤ e 0) (hp₀ : 0 ≤ p 0) (hE : 0 < e 0 + c 0)
    (hS : 0 < s 0 + c 0 + p 0) :
    ∃ xs : Fin 4 → ℝ, (∀ i, 0 < xs i) ∧ xs 2 + xs 1 = e 0 + c 0 ∧
      xs 0 + xs 1 + xs 3 = s 0 + c 0 + p 0 ∧ revField k₁ kb k₂ kb₂ xs = 0 ∧
      Tendsto (mmCurve s c e p) atTop (𝓝 xs) := by
  obtain ⟨xs, ⟨hxs0, hxsE, hxsS, hxsf⟩, huniq⟩ :=
    existsUnique_equilibrium hk₁ hkb hk₂ hkb₂ hE hS
  have hxs := pos_of_equilibrium hk₁ hkb hk₂ hkb₂ hE hS hxs0 hxsE hxsS hxsf
  have hanti := h.antitoneOn_pseudoHelmholtz hk₁ hkb hk₂ hkb₂ hs₀ hc₀ he₀ hp₀ hE hS hxs hxsf
  set ET := e 0 + c 0
  set ST := s 0 + c 0 + p 0
  set K : Set (Fin 4 → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ x 2 + x 1 = ET ∧ x 0 + x 1 + x 3 = ST}
    with hKdef
  -- the compatibility class is compact and convex
  have hKclosed : IsClosed K := by
    refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
    · have : {x : Fin 4 → ℝ | ∀ i, 0 ≤ x i} = Ici 0 := by ext x; simp [Pi.le_def]
      have hc0 : IsClosed {x : Fin 4 → ℝ | ∀ i, 0 ≤ x i} := by rw [this]; exact isClosed_Ici
      exact hc0
    · exact isClosed_eq (by fun_prop) continuous_const
    · exact isClosed_eq (by fun_prop) continuous_const
  have hKc : IsCompact K := by
    refine (isCompact_Icc (a := (0 : Fin 4 → ℝ)) (b := fun _ => ET + ST)).of_isClosed_subset
      hKclosed ?_
    rintro x ⟨hx, hxE, hxS⟩
    refine ⟨fun i => hx i, fun i => ?_⟩
    have := hx 0; have := hx 1; have := hx 2; have := hx 3
    fin_cases i <;> simp <;> linarith
  have hKconv : Convex ℝ K := by
    rintro x ⟨hx, hxE, hxS⟩ y ⟨hy, hyE, hyS⟩ a b ha hb hab
    refine ⟨fun i => ?_, ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination a * hxE + b * hyE + ET * hab
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination a * hxS + b * hyS + ST * hab
  -- the field is Lipschitz on the class
  have hcd : ContDiff ℝ 1 (revField k₁ kb k₂ kb₂) := revField_contDiff
  obtain ⟨C, hC⟩ :=
    hKc.exists_bound_of_continuousOn (hcd.continuous_fderiv one_ne_zero).continuousOn
  have hlip : LipschitzOnWith ⟨max C 0, le_max_right _ _⟩ (revField k₁ kb k₂ kb₂) K :=
    hKconv.lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ => hcd.differentiable one_ne_zero x)
      (fun x hx => NNReal.coe_le_coe.1 ((hC x hx).trans (le_max_left _ _)))
  -- the class is forward invariant
  have hinv : IsForwardInvariant (revField k₁ kb k₂ kb₂) K := by
    rintro x ⟨hx, hxE, hxS⟩
    obtain ⟨s', c', e', p', hsol, hs', hc', he', hp', hnn', hE', hS'⟩ :=
      exists_isSolution_nonneg hk₁.le hkb.le hk₂.le hkb₂.le (hx 0) (hx 1) (hx 2) (hx 3)
    refine ⟨mmCurve s' c' e' p',
      fun t ht => (isSolution_iff_hasDerivAt_mmCurve.1 hsol t ht).hasDerivWithinAt, ?_,
      fun t ht => ?_⟩
    · ext i; fin_cases i <;> simp [mmCurve, hs', hc', he', hp']
    · obtain ⟨h1, h2, h3, h4⟩ := hnn' t ht
      refine ⟨fun i => ?_, ?_, ?_⟩
      · fin_cases i <;> simpa [mmCurve]
      · simp only [mmCurve, Fin.isValue, Matrix.cons_val, Matrix.cons_val_one,
          Matrix.cons_val_zero]
        rw [hE' t ht, hxE]
      · simp only [mmCurve, Fin.isValue, Matrix.cons_val, Matrix.cons_val_one,
          Matrix.cons_val_zero]
        rw [hS' t ht, hxS]
  -- the given solution
  have hγ : IsIntegralCurveOn (mmCurve s c e p) (fun _ => revField k₁ kb k₂ kb₂) (Ici 0) :=
    fun t ht => (isSolution_iff_hasDerivAt_mmCurve.1 h t ht).hasDerivWithinAt
  have hγK : ∀ t, 0 ≤ t → mmCurve s c e p t ∈ K := fun t ht => by
    obtain ⟨h1, h2, h3, h4⟩ := h.nonneg hk₁.le hkb.le hk₂.le hkb₂.le hs₀ hc₀ he₀ hp₀ ht
    refine ⟨fun i => ?_, ?_, ?_⟩
    · fin_cases i <;> simpa [mmCurve]
    · simpa [mmCurve] using h.enzyme_conservation ht
    · simpa [mmCurve] using h.substrate_conservation ht
  -- a solution in the class along which `G` is constant starts at `xs`
  have hZ : ∀ x ∈ K, ∀ φ : ℝ → Fin 4 → ℝ,
      IsIntegralCurveOn φ (fun _ => revField k₁ kb k₂ kb₂) (Ici 0) → φ 0 = x →
      (∀ t, 0 ≤ t → φ t ∈ K) → (∀ t, 0 ≤ t → pseudoHelmholtz xs (φ t) = pseudoHelmholtz xs x) →
      x ∈ ({xs} : Set (Fin 4 → ℝ)) := by
    intro x hx φ hφ hφ0 hφK hconst
    have hφd : ∀ t, 0 < t → HasDerivAt φ (revField k₁ kb k₂ kb₂ (φ t)) t := fun t ht =>
      (hφ t ht.le).hasDerivAt (Ici_mem_nhds ht)
    have hψ : IsSolution k₁ kb k₂ kb₂ (fun t => φ (t + 1) 0) (fun t => φ (t + 1) 1)
        (fun t => φ (t + 1) 2) (fun t => φ (t + 1) 3) := by
      rw [isSolution_iff_hasDerivAt_mmCurve]
      have hc : mmCurve (fun t => φ (t + 1) 0) (fun t => φ (t + 1) 1) (fun t => φ (t + 1) 2)
          (fun t => φ (t + 1) 3) = fun t => φ (t + 1) := by
        funext t; ext i; fin_cases i <;> rfl
      rw [hc]
      intro t ht
      exact HasDerivAt.comp_add_const t 1 (hφd (t + 1) (by linarith))
    obtain ⟨h1K, h1E, h1S⟩ := hφK 1 zero_le_one
    have hpos2 := hψ.pos hk₁ hkb hk₂ hkb₂ (by simpa using h1K 0) (by simpa using h1K 1)
      (by simpa using h1K 2) (by simpa using h1K 3) (by simp only [zero_add]; linarith)
      (by simp only [zero_add]; linarith) one_pos
    norm_num at hpos2
    have hp2 : ∀ i, 0 < φ 2 i := fun i => by
      fin_cases i
      · exact hpos2.1
      · exact hpos2.2.1
      · exact hpos2.2.2.1
      · exact hpos2.2.2.2
    have hrate := deriv_eq_zero_of_eqOn_Ioo
      (hasDerivAt_pseudoHelmholtz_revField xs (hφd 2 two_pos) hp2) (a := 0) (b := 3)
      (fun u hu => hconst u hu.1.le) ⟨two_pos, by norm_num⟩
    have hf2 : revField k₁ kb k₂ kb₂ (φ 2) = 0 :=
      ((helmholtzRate_mmNetwork_nonpos hk₁ hkb hk₂ hkb₂ hxs hxsf hp2).2).1 hrate
    have heq : φ 2 = xs := huniq _ ⟨(hφK 2 two_pos.le).1, (hφK 2 two_pos.le).2.1,
      (hφK 2 two_pos.le).2.2, hf2⟩
    have hG : pseudoHelmholtz xs x = pseudoHelmholtz xs xs := by
      rw [← hconst 2 two_pos.le, heq]
    exact eq_of_pseudoHelmholtz_eq hxs hx.1 hG
  have res := lasalle_of_antitoneOn hKc hlip hinv hγ hγK
    (fun x _ => (continuous_pseudoHelmholtz xs).continuousAt) hanti hZ
  exact ⟨xs, hxs, hxsE, hxsS, hxsf, tendsto_nhds.2 fun U hU hx => res.2.2 U hU
    (largestForwardInvariantSubset_subset.trans (singleton_subset_iff.2 hx))⟩

end MathlibExt.Biology.Dynamics.ReversibleMichaelisMenten
