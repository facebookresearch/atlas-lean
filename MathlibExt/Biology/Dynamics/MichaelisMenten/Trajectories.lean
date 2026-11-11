/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.MichaelisMenten
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import MathlibExt.Analysis.ODE.MaximalSolution
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Global positive trajectories of the Michaelis–Menten system

For the mass-action system of the enzyme mechanism `E + S ⇌ C → E + P`
(`MathlibExt.Biology.Dynamics.MichaelisMenten.IsSolution`)

  `s' = -k₁ e s + k₋₁ c`,  `c' = k₁ e s - (k₋₁ + k₂) c`,  `e' = -c'`,  `p' = k₂ c`,

with nonnegative rate constants, this file proves that every nonnegative initial state has a
solution defined for all `t ≥ 0`, that the solution is unique forward in time, that it stays in
the nonnegative orthant (and in its interior for the coordinates that start positive), and that it
keeps the total enzyme `e + c` and the total substrate `s + c + p`.

## Main results

* `exists_isSolution_nonneg`: global existence, nonnegativity, conservation of `e + c` and
  `s + c + p`, and preservation of positivity of `s`, `c`, `e`, for nonnegative initial data.
* `IsSolution.eq_of_initial`: forward uniqueness.
* `IsSolution.nonneg`, `IsSolution.substrate_pos`, `IsSolution.complex_pos`,
  `IsSolution.enzyme_pos`: the same invariance for *every* solution.
* `IsSolution.complex_pos_of_pos`: with `s(0), e(0) > 0`, `k₁ > 0` and any `c(0) ≥ 0`, the
  complex is positive at every `t > 0`; this includes the unprepared start `c(0) = 0`, where
  `c(0)` differs from the quasi-steady-state value `qssComplex`.
* `isSolution_zeroSubstrate`, `IsSolution.eq_zeroSubstrate`: with no substrate and no complex
  nothing happens: `s ≡ c ≡ 0`, `e ≡ e(0)`, `p ≡ p(0)`.

## Proof of global existence

The polynomial field `mmField` is not used directly: nonnegativity of its solutions is circular
coordinate by coordinate (`s ≥ 0` needs `c ≥ 0`, which needs `s, e ≥ 0`). Instead we take the
maximal solution (`ode_maximal_solution_exit_compact`, with `U = univ`, `t₀ = 0`) of the field
obtained by replacing each *source* term by its positive part,

  `s' = -k₁ e s + k₋₁ c⁺`,  `c' = k₁ e⁺ s⁺ - (k₋₁ + k₂) c`,  `e' = -k₁ s e + (k₋₁ + k₂) c⁺`,
  `p' = k₂ c⁺`.

This field is locally Lipschitz (a `C¹` map composed with `x ↦ (x, x⁺)`), and every coordinate
has the linear form `u' = g(t) u + h(t)` with `h ≥ 0`, so an integrating factor gives `u ≥ 0`
(and `u > 0` if `u(0) > 0`) on every `[0, T]` in the interval of definition. On the nonnegative
orthant the clamped field equals `mmField`, so the two conservation laws hold there and keep the
solution in a compact box; the exit property then forces the interval to contain `[0, ∞)`.

## Source receipt (API-00 reuse gate)

Reused, not redefined: `IsSolution`, `substrateRate`, `complexRate`, `qssComplex`,
`IsSolution.enzyme_conservation`, `IsSolution.substrate_conservation` from
`MathlibExt.Biology.Dynamics.MichaelisMenten`; the maximal-solution exit theorem
`MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_maximal_solution_exit_compact` from
`MathlibExt.Analysis.ODE.MaximalSolution`; Mathlib's `ODE_solution_unique_of_mem_Icc_right` for
uniqueness. The global-existence argument follows the one for the SIR system in
`MathlibExt.Biology.Epidemiology.SIRExistence`. The mathematical statements (well-posedness,
invariance of the nonnegative orthant, the two conservation laws) are the standard ones of
Segel–Slemrod §2 and Murray §6.1 below; no Michaelis–Menten global-existence or positivity
statement existed in the repository before this file.

## References

* L. A. Segel and M. Slemrod, *The quasi-steady-state assumption: a case study in
  perturbation*, SIAM Rev. 31 (1989) 446–477, §2.
* J. D. Murray, *Mathematical Biology I: An Introduction*, 3rd ed., Springer (2002), §6.1.
* J. Keener and J. Sneyd, *Mathematical Physiology I: Cellular Physiology*, 2nd ed., Springer
  (2009), §1.4.
-/

@[expose] public section

open Set Filter Metric Real
open scoped Topology

namespace MathlibExt.Biology.Dynamics.MichaelisMenten

variable {k₁ kb k₂ : ℝ} {s c e p : ℝ → ℝ}

/-! ### The vector field -/

/-- The Michaelis–Menten mass-action field on `Fin 4 → ℝ`, with coordinates `x 0 = s`,
`x 1 = c`, `x 2 = e`, `x 3 = p`. -/
def mmField (k₁ kb k₂ : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![substrateRate k₁ kb (x 0) (x 1) (x 2), complexRate k₁ kb k₂ (x 0) (x 1) (x 2),
    -complexRate k₁ kb k₂ (x 0) (x 1) (x 2), k₂ * x 1]

/-- The curve in `Fin 4 → ℝ` obtained by packing `s`, `c`, `e`, `p`. -/
def mmCurve (s c e p : ℝ → ℝ) (t : ℝ) : Fin 4 → ℝ :=
  ![s t, c t, e t, p t]

/-- `IsSolution` is the statement that the packed curve has derivative `mmField` at every
`t ≥ 0`. -/
theorem isSolution_iff_hasDerivAt_mmCurve :
    IsSolution k₁ kb k₂ s c e p ↔
      ∀ t, 0 ≤ t → HasDerivAt (mmCurve s c e p) (mmField k₁ kb k₂ (mmCurve s c e p t)) t := by
  constructor
  · intro h t ht
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i
    · simpa [mmCurve, mmField] using h.hasDerivAt_substrate t ht
    · simpa [mmCurve, mmField] using h.hasDerivAt_complex t ht
    · simpa [mmCurve, mmField] using h.hasDerivAt_enzyme t ht
    · simpa [mmCurve, mmField] using h.hasDerivAt_product t ht
  · intro h
    refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
    · simpa [mmCurve, mmField] using hasDerivAt_pi.1 (h t ht) 0
    · simpa [mmCurve, mmField] using hasDerivAt_pi.1 (h t ht) 1
    · simpa [mmCurve, mmField] using hasDerivAt_pi.1 (h t ht) 2
    · simpa [mmCurve, mmField] using hasDerivAt_pi.1 (h t ht) 3

/-- The field is smooth: its components are polynomials. -/
theorem mmField_contDiff {n : WithTop ℕ∞} : ContDiff ℝ n (mmField k₁ kb k₂) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;>
    simp only [mmField, substrateRate, complexRate, Fin.isValue, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    fun_prop

/-! ### The clamped field -/

/-- Coordinatewise positive part. -/
private def posPart4 (x : Fin 4 → ℝ) : Fin 4 → ℝ := fun i => max (x i) 0

/-- The field with the state `q.1` in the loss terms and `q.2` in the source terms. -/
private def mmFieldAux (k₁ kb k₂ : ℝ) (q : (Fin 4 → ℝ) × (Fin 4 → ℝ)) : Fin 4 → ℝ :=
  ![substrateRate k₁ kb (q.1 0) (q.2 1) (q.1 2), complexRate k₁ kb k₂ (q.2 0) (q.1 1) (q.2 2),
    -complexRate k₁ kb k₂ (q.1 0) (q.2 1) (q.1 2), k₂ * q.2 1]

/-- The clamped field: source terms use positive parts. -/
private def clampedField (k₁ kb k₂ : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  mmFieldAux k₁ kb k₂ (x, posPart4 x)

private theorem clampedField_of_nonneg {x : Fin 4 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    clampedField k₁ kb k₂ x = mmField k₁ kb k₂ x := by
  have : posPart4 x = x := funext fun i => max_eq_left (hx i)
  rw [clampedField, this]
  rfl

private theorem lipschitzWith_posPart4 : LipschitzWith 1 posPart4 := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul]
  refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
  refine le_trans ?_ (dist_le_pi_dist x y i)
  rw [Real.dist_eq, Real.dist_eq]
  exact abs_max_sub_max_le_abs _ _ _

private theorem mmFieldAux_contDiff : ContDiff ℝ 1 (mmFieldAux k₁ kb k₂) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;>
    simp only [mmFieldAux, substrateRate, complexRate, Fin.isValue, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    fun_prop

private theorem locallyLipschitz_clampedField : LocallyLipschitz (clampedField k₁ kb k₂) :=
  (mmFieldAux_contDiff (k₁ := k₁) (kb := kb) (k₂ := k₂)).locallyLipschitz.comp
    (LocallyLipschitz.id.prodMk lipschitzWith_posPart4.locallyLipschitz)

private theorem clampedField_lip (p : ℝ × (Fin 4 → ℝ)) :
    ∃ C : NNReal, ∃ s ∈ 𝓝 p, ∀ t : ℝ, ∀ x y : Fin 4 → ℝ,
      (t, x) ∈ s ∩ univ → (t, y) ∈ s ∩ univ →
        dist ((fun q : ℝ × (Fin 4 → ℝ) => clampedField k₁ kb k₂ q.2) (t, x))
          ((fun q : ℝ × (Fin 4 → ℝ) => clampedField k₁ kb k₂ q.2) (t, y)) ≤ C * dist x y := by
  obtain ⟨C, u, hu, hC⟩ := locallyLipschitz_clampedField (k₁ := k₁) (kb := kb) (k₂ := k₂) p.2
  refine ⟨C, univ ×ˢ u, prod_mem_nhds univ_mem hu, ?_⟩
  rintro t x y ⟨⟨-, hx⟩, -⟩ ⟨⟨-, hy⟩, -⟩
  exact hC.dist_le_mul x hx y hy

/-! ### Integrating factors -/

/-- A continuous `g` on `[0, T]` has an antiderivative there vanishing at `0`. -/
private theorem exists_antideriv {g : ℝ → ℝ} {T : ℝ} (hg : ContinuousOn g (Icc 0 T)) :
    ∃ G : ℝ → ℝ, G 0 = 0 ∧ ∀ t ∈ Icc 0 T, HasDerivAt G (g t) t := by
  by_cases hT : 0 ≤ T
  · set g' : ℝ → ℝ := fun s => g (max 0 (min T s)) with hg'
    have hg'c : Continuous g' := hg.comp_continuous (by fun_prop)
      fun s => ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩
    refine ⟨fun t => ∫ s in (0 : ℝ)..t, g' s, intervalIntegral.integral_same, fun t ht => ?_⟩
    have := (hg'c.integral_hasStrictDerivAt 0 t).hasDerivAt
    simpa [hg', min_eq_right ht.2, max_eq_right ht.1] using this
  · exact ⟨0, rfl, fun t ht => absurd (ht.1.trans ht.2) hT⟩

/-- The integrated form `u e^{-G}` of a linear equation `u' = g u + h`. -/
private theorem hasDerivAt_mul_exp {u g h G : ℝ → ℝ} {t : ℝ} (hu : HasDerivAt u (g t * u t + h t) t)
    (hG : HasDerivAt G (g t) t) :
    HasDerivAt (fun s => u s * exp (-G s)) (h t * exp (-G t)) t := by
  have h := hu.mul hG.neg.exp
  simp only [Pi.neg_apply] at h
  convert h using 1
  ring

/-- **Integrating factor with a nonnegative source.** If `u' = g u + h` on `[0, T]` with `g`
continuous and `h ≥ 0`, then `u ≥ 0` (resp. `u > 0`) on `[0, T]` when `u(0) ≥ 0`
(resp. `u(0) > 0`). -/
private theorem nonneg_pos_of_hasDerivAt {u g h : ℝ → ℝ} {T : ℝ}
    (hg : ContinuousOn g (Icc 0 T)) (hh : ∀ t ∈ Icc 0 T, 0 ≤ h t)
    (hu : ∀ t ∈ Icc 0 T, HasDerivAt u (g t * u t + h t) t) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (0 ≤ u 0 → 0 ≤ u t) ∧ (0 < u 0 → 0 < u t) := by
  obtain ⟨G, hG0, hG⟩ := exists_antideriv hg
  have hF : ∀ s ∈ Icc 0 T, HasDerivAt (fun s => u s * exp (-G s)) (h s * exp (-G s)) s :=
    fun s hs => hasDerivAt_mul_exp (hu s hs) (hG s hs)
  have hmono : MonotoneOn (fun s => u s * exp (-G s)) (Icc 0 T) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T)
      (fun s hs => (hF s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hF s (interior_subset hs)).hasDerivWithinAt)
      fun s hs => mul_nonneg (hh s (interior_subset hs)) (exp_pos _).le
  have hle : u 0 ≤ u t * exp (-G t) := by
    have := hmono ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
    simpa [hG0] using this
  exact ⟨fun h0 => (mul_nonneg_iff_of_pos_right (exp_pos _)).1 (h0.trans hle),
    fun h0 => (mul_pos_iff_of_pos_right (exp_pos _)).1 (h0.trans_le hle)⟩

/-- **Integrating factor with a positive source.** If `u' = g u + h` on `[0, T]`, `T > 0`, with
`g` continuous, `h > 0` and `u(0) ≥ 0`, then `u(T) > 0`. -/
private theorem pos_of_hasDerivAt_of_source_pos {u g h : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hg : ContinuousOn g (Icc 0 T)) (hh : ∀ t ∈ Icc 0 T, 0 < h t)
    (hu : ∀ t ∈ Icc 0 T, HasDerivAt u (g t * u t + h t) t) (hu0 : 0 ≤ u 0) : 0 < u T := by
  obtain ⟨G, hG0, hG⟩ := exists_antideriv hg
  have hF : ∀ s ∈ Icc 0 T, HasDerivAt (fun s => u s * exp (-G s)) (h s * exp (-G s)) s :=
    fun s hs => hasDerivAt_mul_exp (hu s hs) (hG s hs)
  have hmono : StrictMonoOn (fun s => u s * exp (-G s)) (Icc 0 T) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 T)
      (fun s hs => (hF s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hF s (interior_subset hs)).hasDerivWithinAt)
      fun s hs => mul_pos (hh s (interior_subset hs)) (exp_pos _)
  have hlt : u 0 < u T * exp (-G T) := by
    have := hmono ⟨le_rfl, hT.le⟩ ⟨hT.le, le_rfl⟩ hT
    simpa [hG0] using this
  exact (mul_pos_iff_of_pos_right (exp_pos _)).1 (hu0.trans_lt hlt)

/-! ### Invariance for the clamped system on `[0, T]` -/

section Clamped

variable {α : ℝ → Fin 4 → ℝ} {T : ℝ}

private theorem clamped_coord
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt α (clampedField k₁ kb k₂ (α t)) t) (i : Fin 4) :
    ∀ t ∈ Icc 0 T, HasDerivAt (α · i) (clampedField k₁ kb k₂ (α t) i) t :=
  fun t ht => hasDerivAt_pi.1 (hd t ht) i

private theorem clamped_continuousOn
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt α (clampedField k₁ kb k₂ (α t)) t) (i : Fin 4) :
    ContinuousOn (α · i) (Icc 0 T) :=
  fun t ht => (clamped_coord hd i t ht).continuousAt.continuousWithinAt

/-- Along the clamped system, nonnegative initial data stay nonnegative on `[0, T]` and positive
initial `s`, `c`, `e` stay positive. -/
private theorem clamped_nonneg_pos
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt α (clampedField k₁ kb k₂ (α t)) t)
    (hk₁ : 0 ≤ k₁) (hkb : 0 ≤ kb) (hk₂ : 0 ≤ k₂)
    (h0 : ∀ i, 0 ≤ α 0 i) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∀ i, 0 ≤ α t i) ∧ (0 < α 0 0 → 0 < α t 0) ∧ (0 < α 0 1 → 0 < α t 1) ∧
      (0 < α 0 2 → 0 < α t 2) := by
  have hs := nonneg_pos_of_hasDerivAt (u := (α · 0)) (g := fun t => -k₁ * α t 2)
    (h := fun t => kb * max (α t 1) 0)
    (by have := clamped_continuousOn hd 2; fun_prop)
    (fun t _ => mul_nonneg hkb (le_max_right _ _))
    (fun t ht => by
      convert clamped_coord hd 0 t ht using 1
      simp [clampedField, mmFieldAux, posPart4, substrateRate]) ht
  have hc := nonneg_pos_of_hasDerivAt (u := (α · 1)) (g := fun _ => -(kb + k₂))
    (h := fun t => k₁ * max (α t 2) 0 * max (α t 0) 0) continuousOn_const
    (fun t _ => mul_nonneg (mul_nonneg hk₁ (le_max_right _ _)) (le_max_right _ _))
    (fun t ht => by
      convert clamped_coord hd 1 t ht using 1
      simp [clampedField, mmFieldAux, posPart4, complexRate]; ring) ht
  have he := nonneg_pos_of_hasDerivAt (u := (α · 2)) (g := fun t => -k₁ * α t 0)
    (h := fun t => (kb + k₂) * max (α t 1) 0)
    (by have := clamped_continuousOn hd 0; fun_prop)
    (fun t _ => mul_nonneg (add_nonneg hkb hk₂) (le_max_right _ _))
    (fun t ht => by
      convert clamped_coord hd 2 t ht using 1
      simp [clampedField, mmFieldAux, posPart4, complexRate]; ring) ht
  have hp := nonneg_pos_of_hasDerivAt (u := (α · 3)) (g := fun _ => 0)
    (h := fun t => k₂ * max (α t 1) 0) continuousOn_const
    (fun t _ => mul_nonneg hk₂ (le_max_right _ _))
    (fun t ht => by
      convert clamped_coord hd 3 t ht using 1
      simp [clampedField, mmFieldAux, posPart4]) ht
  refine ⟨fun i => ?_, hs.2, hc.2, he.2⟩
  fin_cases i
  · exact hs.1 (h0 0)
  · exact hc.1 (h0 1)
  · exact he.1 (h0 2)
  · exact hp.1 (h0 3)

/-- On `[0, T]`, nonnegative clamped solutions keep `e + c` and `s + c + p`. -/
private theorem clamped_conservation
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt α (clampedField k₁ kb k₂ (α t)) t)
    (hk₁ : 0 ≤ k₁) (hkb : 0 ≤ kb) (hk₂ : 0 ≤ k₂)
    (h0 : ∀ i, 0 ≤ α 0 i) {t : ℝ} (ht : t ∈ Icc 0 T) :
    α t 2 + α t 1 = α 0 2 + α 0 1 ∧ α t 0 + α t 1 + α t 3 = α 0 0 + α 0 1 + α 0 3 := by
  have hm : ∀ s ∈ Icc 0 T, ∀ i, HasDerivAt (α · i) (mmField k₁ kb k₂ (α s) i) s := fun s hs i => by
    rw [← clampedField_of_nonneg (clamped_nonneg_pos hd hk₁ hkb hk₂ h0 hs).1]
    exact clamped_coord hd i s hs
  have hE : ∀ s ∈ Icc 0 T, HasDerivAt (fun s => α s 2 + α s 1) 0 s := fun s hs => by
    convert (hm s hs 2).add (hm s hs 1) using 1
    simp [mmField]
  have hS : ∀ s ∈ Icc 0 T, HasDerivAt (fun s => α s 0 + α s 1 + α s 3) 0 s := fun s hs => by
    convert ((hm s hs 0).add (hm s hs 1)).add (hm s hs 3) using 1
    simp [mmField, substrateRate, complexRate]; ring
  exact ⟨constant_of_has_deriv_right_zero (fun s hs => (hE s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hE s (Ico_subset_Icc_self hs)).hasDerivWithinAt) t ht,
    constant_of_has_deriv_right_zero (fun s hs => (hS s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hS s (Ico_subset_Icc_self hs)).hasDerivWithinAt) t ht⟩

end Clamped

/-! ### Forward-global existence -/

/-- **Global positive Michaelis–Menten trajectories.** For nonnegative rate constants and every
nonnegative initial state `(s₀, c₀, e₀, p₀)`, the Michaelis–Menten system has a solution with
these initial values, with two-sided derivatives at every `t ≥ 0`, such that for all `t ≥ 0`:
all four coordinates are nonnegative and `p` does not fall below `p₀`; the total enzyme
`e + c = e₀ + c₀` and the total substrate `s + c + p = s₀ + c₀ + p₀` are conserved; and each of
`s`, `c`, `e` that starts positive stays positive.

The initial complex `c₀` is arbitrary in `[0, ∞)`; it need not be the quasi-steady-state value
`qssComplex k₁ kb k₂ (e₀ + c₀) s₀`. -/
theorem exists_isSolution_nonneg (hk₁ : 0 ≤ k₁) (hkb : 0 ≤ kb) (hk₂ : 0 ≤ k₂)
    {s₀ c₀ e₀ p₀ : ℝ} (hs₀ : 0 ≤ s₀) (hc₀ : 0 ≤ c₀) (he₀ : 0 ≤ e₀) (hp₀ : 0 ≤ p₀) :
    ∃ s c e p : ℝ → ℝ, IsSolution k₁ kb k₂ s c e p ∧
      s 0 = s₀ ∧ c 0 = c₀ ∧ e 0 = e₀ ∧ p 0 = p₀ ∧
      (∀ t, 0 ≤ t → 0 ≤ s t ∧ 0 ≤ c t ∧ 0 ≤ e t ∧ p₀ ≤ p t) ∧
      (∀ t, 0 ≤ t → e t + c t = e₀ + c₀) ∧
      (∀ t, 0 ≤ t → s t + c t + p t = s₀ + c₀ + p₀) ∧
      (∀ t, 0 ≤ t → (0 < s₀ → 0 < s t) ∧ (0 < c₀ → 0 < c t) ∧ (0 < e₀ → 0 < e t)) := by
  obtain ⟨J, α, hα0, hJo, h0J, hJc, hαd, hexit⟩ :=
    MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_maximal_solution_exit_compact univ
      (fun q : ℝ × (Fin 4 → ℝ) => clampedField k₁ kb k₂ q.2) 0 ![s₀, c₀, e₀, p₀] isOpen_univ
      trivial (locallyLipschitz_clampedField.continuous.comp continuous_snd).continuousOn
      fun p _ => clampedField_lip p
  have hd : ∀ T ∈ J, ∀ t ∈ Icc 0 T, HasDerivAt α (clampedField k₁ kb k₂ (α t)) t :=
    fun T hT t ht => (hαd t (hJc 0 h0J T hT ht)).2
  have hinit : α 0 0 = s₀ ∧ α 0 1 = c₀ ∧ α 0 2 = e₀ ∧ α 0 3 = p₀ := by simp [hα0]
  have h0 : ∀ i, 0 ≤ α 0 i := fun i => by
    fin_cases i <;> simp [hα0, hs₀, hc₀, he₀, hp₀]
  have hfw : ∀ T ∈ J, 0 ≤ T → (∀ i, 0 ≤ α T i) ∧ (0 < s₀ → 0 < α T 0) ∧
      (0 < c₀ → 0 < α T 1) ∧ (0 < e₀ → 0 < α T 2) := fun T hT hT0 => by
    have := clamped_nonneg_pos (hd T hT) hk₁ hkb hk₂ h0 ⟨hT0, le_rfl⟩
    rwa [hinit.1, hinit.2.1, hinit.2.2.1] at this
  have hcons : ∀ T ∈ J, 0 ≤ T →
      α T 2 + α T 1 = e₀ + c₀ ∧ α T 0 + α T 1 + α T 3 = s₀ + c₀ + p₀ := fun T hT hT0 => by
    have := clamped_conservation (hd T hT) hk₁ hkb hk₂ h0 ⟨hT0, le_rfl⟩
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
    obtain ⟨hnn, -⟩ := hfw t htJ ht0
    obtain ⟨hE, hS⟩ := hcons t htJ ht0
    refine hc t htJ (le_max_left _ _) ⟨⟨ht0, htT⟩, fun i => by simpa using hnn i, fun i => ?_⟩
    have := hnn 0; have := hnn 1; have := hnn 2; have := hnn 3
    fin_cases i <;> simp <;> linarith
  have hJt : ∀ t, 0 ≤ t → t ∈ J := fun t ht => hglobal ht
  have hm : ∀ t, 0 ≤ t → ∀ i, HasDerivAt (α · i) (mmField k₁ kb k₂ (α t) i) t := fun t ht i => by
    rw [← clampedField_of_nonneg (hfw t (hJt t ht) ht).1]
    exact hasDerivAt_pi.1 (hαd t (hJt t ht)).2 i
  have hsol : IsSolution k₁ kb k₂ (α · 0) (α · 1) (α · 2) (α · 3) :=
    ⟨fun t ht => hm t ht 0, fun t ht => hm t ht 1, fun t ht => hm t ht 2, fun t ht => hm t ht 3⟩
  refine ⟨(α · 0), (α · 1), (α · 2), (α · 3), hsol, hinit.1, hinit.2.1, hinit.2.2.1,
    hinit.2.2.2, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_,
    fun t ht => (hfw t (hJt t ht) ht).2⟩
  · obtain ⟨hnn, -⟩ := hfw t (hJt t ht) ht
    refine ⟨hnn 0, hnn 1, hnn 2, ?_⟩
    have hmono : MonotoneOn (α · 3) (Icc 0 t) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t)
        (fun x hx => (hsol.hasDerivAt_product x hx.1).continuousAt.continuousWithinAt)
        (fun x hx => (hsol.hasDerivAt_product x (interior_subset hx).1).hasDerivWithinAt)
        fun x hx => mul_nonneg hk₂
          ((hfw x (hJt x (interior_subset hx).1) (interior_subset hx).1).1 1)
    simpa [hinit.2.2.2] using hmono ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  · rw [hsol.enzyme_conservation ht, hinit.2.2.1, hinit.2.1]
  · rw [hsol.substrate_conservation ht, hinit.1, hinit.2.1, hinit.2.2.2]

/-! ### Forward uniqueness and invariance for every solution -/

/-- **Forward uniqueness.** Two solutions of the Michaelis–Menten system (any real rate
constants) with the same initial values agree at every time `t ≥ 0`.

Proof: on `[0, t]` both packed curves lie in a common closed ball, on which the polynomial field
is Lipschitz; apply Mathlib's `ODE_solution_unique_of_mem_Icc_right`. -/
theorem IsSolution.eq_of_initial {s' c' e' p' : ℝ → ℝ} (h : IsSolution k₁ kb k₂ s c e p)
    (h' : IsSolution k₁ kb k₂ s' c' e' p') (hs : s 0 = s' 0) (hc : c 0 = c' 0) (he : e 0 = e' 0)
    (hp : p 0 = p' 0) {t : ℝ} (ht : 0 ≤ t) :
    s t = s' t ∧ c t = c' t ∧ e t = e' t ∧ p t = p' t := by
  have hd := isSolution_iff_hasDerivAt_mmCurve.1 h
  have hd' := isSolution_iff_hasDerivAt_mmCurve.1 h'
  have hcont : ContinuousOn (mmCurve s c e p) (Icc 0 t) :=
    fun x hx => (hd x hx.1).continuousAt.continuousWithinAt
  have hcont' : ContinuousOn (mmCurve s' c' e' p') (Icc 0 t) :=
    fun x hx => (hd' x hx.1).continuousAt.continuousWithinAt
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont'
  obtain ⟨K, hK⟩ := ((mmField_contDiff (k₁ := k₁) (kb := kb) (k₂ := k₂) (n := 1)).contDiffOn
    (s := closedBall 0 (max C₁ C₂))).exists_lipschitzOnWith one_ne_zero
    (convex_closedBall _ _) (isCompact_closedBall _ _)
  have heq := ODE_solution_unique_of_mem_Icc_right (v := fun _ => mmField k₁ kb k₂)
    (s := fun _ => closedBall 0 (max C₁ C₂))
    (fun _ _ => hK) hcont (fun x hx => (hd x hx.1).hasDerivWithinAt)
    (fun x hx => mem_closedBall_zero_iff.2
      ((hC₁ x (Ico_subset_Icc_self hx)).trans (le_max_left _ _)))
    hcont' (fun x hx => (hd' x hx.1).hasDerivWithinAt)
    (fun x hx => mem_closedBall_zero_iff.2
      ((hC₂ x (Ico_subset_Icc_self hx)).trans (le_max_right _ _)))
    (by simp [mmCurve, hs, hc, he, hp]) ⟨ht, le_rfl⟩
  exact ⟨congrFun heq 0, congrFun heq 1, congrFun heq 2, congrFun heq 3⟩

/-- Every solution with nonnegative rate constants and initial data is the one constructed in
`exists_isSolution_nonneg`, so it inherits its invariance properties. -/
private theorem IsSolution.nonneg_pos (h : IsSolution k₁ kb k₂ s c e p) (hk₁ : 0 ≤ k₁)
    (hkb : 0 ≤ kb) (hk₂ : 0 ≤ k₂) (hs : 0 ≤ s 0) (hc : 0 ≤ c 0) (he : 0 ≤ e 0) (hp : 0 ≤ p 0)
    {t : ℝ} (ht : 0 ≤ t) :
    (0 ≤ s t ∧ 0 ≤ c t ∧ 0 ≤ e t ∧ p 0 ≤ p t) ∧
      ((0 < s 0 → 0 < s t) ∧ (0 < c 0 → 0 < c t) ∧ (0 < e 0 → 0 < e t)) := by
  obtain ⟨s', c', e', p', h', hs', hc', he', hp', hnn, -, -, hpos⟩ :=
    exists_isSolution_nonneg hk₁ hkb hk₂ hs hc he hp
  obtain ⟨h1, h2, h3, h4⟩ := h.eq_of_initial h' hs'.symm hc'.symm he'.symm hp'.symm ht
  rw [h1, h2, h3, h4]
  exact ⟨hnn t ht, hpos t ht⟩

/-- **Invariance of the nonnegative orthant.** Along every solution with nonnegative rate
constants and nonnegative initial data, all four coordinates stay nonnegative for `t ≥ 0`, and the
product does not decrease below its initial value. -/
theorem IsSolution.nonneg (h : IsSolution k₁ kb k₂ s c e p) (hk₁ : 0 ≤ k₁) (hkb : 0 ≤ kb)
    (hk₂ : 0 ≤ k₂) (hs : 0 ≤ s 0) (hc : 0 ≤ c 0) (he : 0 ≤ e 0) (hp : 0 ≤ p 0) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ s t ∧ 0 ≤ c t ∧ 0 ≤ e t ∧ p 0 ≤ p t :=
  (h.nonneg_pos hk₁ hkb hk₂ hs hc he hp ht).1

/-- Along every solution with nonnegative rate constants and initial data, a positive initial
substrate stays positive. -/
theorem IsSolution.substrate_pos (h : IsSolution k₁ kb k₂ s c e p) (hk₁ : 0 ≤ k₁) (hkb : 0 ≤ kb)
    (hk₂ : 0 ≤ k₂) (hs : 0 < s 0) (hc : 0 ≤ c 0) (he : 0 ≤ e 0) (hp : 0 ≤ p 0) {t : ℝ}
    (ht : 0 ≤ t) : 0 < s t :=
  (h.nonneg_pos hk₁ hkb hk₂ hs.le hc he hp ht).2.1 hs

/-- Along every solution with nonnegative rate constants and initial data, a positive initial
complex stays positive. -/
theorem IsSolution.complex_pos (h : IsSolution k₁ kb k₂ s c e p) (hk₁ : 0 ≤ k₁) (hkb : 0 ≤ kb)
    (hk₂ : 0 ≤ k₂) (hs : 0 ≤ s 0) (hc : 0 < c 0) (he : 0 ≤ e 0) (hp : 0 ≤ p 0) {t : ℝ}
    (ht : 0 ≤ t) : 0 < c t :=
  (h.nonneg_pos hk₁ hkb hk₂ hs hc.le he hp ht).2.2.1 hc

/-- Along every solution with nonnegative rate constants and initial data, a positive initial
free enzyme stays positive. -/
theorem IsSolution.enzyme_pos (h : IsSolution k₁ kb k₂ s c e p) (hk₁ : 0 ≤ k₁) (hkb : 0 ≤ kb)
    (hk₂ : 0 ≤ k₂) (hs : 0 ≤ s 0) (hc : 0 ≤ c 0) (he : 0 < e 0) (hp : 0 ≤ p 0) {t : ℝ}
    (ht : 0 ≤ t) : 0 < e t :=
  (h.nonneg_pos hk₁ hkb hk₂ hs hc he.le hp ht).2.2.2 he

/-- **Unprepared initial complex.** With `k₁ > 0` and positive initial substrate and free enzyme,
the complex is positive at every `t > 0`, whatever its initial value `c(0) ≥ 0`. This covers the
classical unprepared start `c(0) = 0`, where `c(0)` differs from the quasi-steady-state value
`qssComplex k₁ kb k₂ (e(0) + c(0)) s(0) > 0`. -/
theorem IsSolution.complex_pos_of_pos (h : IsSolution k₁ kb k₂ s c e p) (hk₁ : 0 < k₁)
    (hkb : 0 ≤ kb) (hk₂ : 0 ≤ k₂) (hs : 0 < s 0) (hc : 0 ≤ c 0) (he : 0 < e 0) (hp : 0 ≤ p 0)
    {t : ℝ} (ht : 0 < t) : 0 < c t :=
  pos_of_hasDerivAt_of_source_pos (u := c) (g := fun _ => -(kb + k₂))
    (h := fun x => k₁ * e x * s x) ht continuousOn_const
    (fun x hx => mul_pos (mul_pos hk₁ (h.enzyme_pos hk₁.le hkb hk₂ hs.le hc he hp hx.1))
      (h.substrate_pos hk₁.le hkb hk₂ hs hc he.le hp hx.1))
    (fun x hx => by
      convert h.hasDerivAt_complex x hx.1 using 1
      simp only [complexRate]
      ring) hc

/-! ### Zero substrate -/

/-- **Zero substrate.** With no substrate and no complex, the state is an equilibrium:
`s ≡ c ≡ 0`, `e ≡ e₀`, `p ≡ p₀` (any real rate constants). -/
theorem isSolution_zeroSubstrate (k₁ kb k₂ e₀ p₀ : ℝ) :
    IsSolution k₁ kb k₂ (fun _ => 0) (fun _ => 0) (fun _ => e₀) (fun _ => p₀) where
  hasDerivAt_substrate t _ := by simpa [substrateRate] using hasDerivAt_const t (0 : ℝ)
  hasDerivAt_complex t _ := by simpa [complexRate] using hasDerivAt_const t (0 : ℝ)
  hasDerivAt_enzyme t _ := by simpa [complexRate] using hasDerivAt_const t e₀
  hasDerivAt_product t _ := by simpa using hasDerivAt_const t p₀

/-- Every solution starting with no substrate and no complex is the zero-substrate
equilibrium for `t ≥ 0`. -/
theorem IsSolution.eq_zeroSubstrate (h : IsSolution k₁ kb k₂ s c e p) (hs : s 0 = 0)
    (hc : c 0 = 0) {t : ℝ} (ht : 0 ≤ t) : s t = 0 ∧ c t = 0 ∧ e t = e 0 ∧ p t = p 0 :=
  h.eq_of_initial (isSolution_zeroSubstrate k₁ kb k₂ (e 0) (p 0)) hs hc rfl rfl ht

end MathlibExt.Biology.Dynamics.MichaelisMenten
