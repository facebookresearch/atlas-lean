/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.ODE.DiscreteGronwall

/-!
# Explicit Runge–Kutta methods

An explicit Runge–Kutta method with `s` stages is given by a strictly lower-triangular
Butcher tableau `a` and weights `b`. The nodes are `c i = ∑ j, a i j`. Given a vector field
`f`, a time `t`, a state `y`, and a step `h`, the stages are

  `k i = f (t + c i * h) (y + h • ∑ j < i, a i j • k j)`

and one step is `rkStep = y + h • ∑ i, b i • k i`. The stages are built row by row
(`stageRow`), so no well-founded recursion is needed.

Main results:

* `stage_eq`: the defining equation of the stages.
* `rkStep_sub_inv_smul_tendsto`: **consistency**: if `∑ b i = 1` and `f` is continuous at
  `(t, y)`, then `h⁻¹ • (rkStep h - y) → f t y` as `h → 0` (through nonzero values).
* `eulerRK`, `midpointRK`, `heunRK`, `rk4`: the Euler, midpoint, Heun, and classical
  fourth-order tableaux, with `eulerRK_orderOne`, `midpointRK_orderTwo`, `heunRK_orderTwo`,
  and `rk4_orderFour`: **the classical RK4 tableau satisfies all eight order-four
  conditions** (Hairer, Nørsett, and Wanner, *Solving Ordinary Differential Equations I*,
  Section II.1).
* `euler_step`: the one-stage method is the explicit Euler step
  (`MathlibExt/Analysis/ODE/ExplicitEuler.lean` proves its first-order convergence).
* `rk4_stability`: on the linear test equation `y' = λ y`, one RK4 step multiplies by the
  stability polynomial `1 + z + z² / 2 + z³ / 6 + z⁴ / 24`, `z = λ h`.

## References

* E. Hairer, S. P. Nørsett, and G. Wanner, *Solving Ordinary Differential Equations I:
  Nonstiff Problems*, Springer, 1993, Chapter II.
* J. C. Butcher, *Numerical Methods for Ordinary Differential Equations*, Wiley, 2016.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Analysis.ODE.RungeKutta

open Filter Topology

/-- An explicit Runge–Kutta method with `s` stages: a strictly lower-triangular Butcher
tableau `a` and weights `b`. -/
structure ExplicitRK (s : ℕ) where
  /-- The Butcher tableau, strictly lower triangular. -/
  a : Fin s → Fin s → ℝ
  /-- The weights. -/
  b : Fin s → ℝ
  /-- Strict lower-triangularity: `a i j = 0` for `i ≤ j`. -/
  lower : ∀ i j : Fin s, i ≤ j → a i j = 0

/-- The nodes of a Runge–Kutta method: `c i = ∑ j, a i j`. -/
def ExplicitRK.c {s : ℕ} (rk : ExplicitRK s) (i : Fin s) : ℝ := ∑ j, rk.a i j

section Stages

variable {s : ℕ} (rk : ExplicitRK s) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f : ℝ → E → E) (t : ℝ) (y : E) (h : ℝ)

/-- The stages built row by row: `stageRow n` fills in the stages with index `< n`, leaving
the rest `0`. -/
def stageRow : ℕ → Fin s → E
  | 0 => fun _ => 0
  | n + 1 => fun i =>
      if i.val = n then
        f (t + rk.c i * h)
          (y + h • ∑ j : Fin s, if j.val < n then rk.a i j • stageRow n j else 0)
      else stageRow n i

/-- The `i`-th stage. -/
def stage (i : Fin s) : E := stageRow rk f t y h (i.val + 1) i

/-- A row agrees with the finished stages on all indices below its length. -/
theorem stageRow_eq_of_lt : ∀ (m : ℕ) (i : Fin s), i.val < m →
    stageRow rk f t y h m i = stage rk f t y h i
  | 0, i, hi => absurd hi (Nat.not_lt_zero _)
  | m + 1, i, hi => by
      by_cases hcase : i.val = m
      · unfold stage
        rw [hcase]
      · have hi' : i.val < m := by omega
        have : stageRow rk f t y h (m + 1) i = stageRow rk f t y h m i := by
          simp only [stageRow, hcase, ite_false]
        rw [this]
        exact stageRow_eq_of_lt m i hi'

/-- **The defining equation of the stages.** -/
theorem stage_eq (i : Fin s) :
    stage rk f t y h i =
      f (t + rk.c i * h)
        (y + h • ∑ j : Fin s, if j < i then rk.a i j • stage rk f t y h j else 0) := by
  have hsum : (∑ j : Fin s, if j.val < i.val then rk.a i j • stageRow rk f t y h i.val j
      else 0) =
      ∑ j : Fin s, if j < i then rk.a i j • stage rk f t y h j else 0 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j < i
    · have hj' : j.val < i.val := hj
      rw [ite_eq_left hj', ite_eq_left hj]
      congr 1
      exact stageRow_eq_of_lt rk f t y h i.val j hj
    · have hj' : ¬ j.val < i.val := hj
      rw [ite_eq_right hj', ite_eq_right hj]
  conv_lhs => rw [stage]
  rw [stageRow]
  simp only [ite_true]
  rw [hsum]

/-- One Runge–Kutta step: `y + h • ∑ i, b i • k i`. -/
def rkStep : E := y + h • ∑ i, rk.b i • stage rk f t y h i

end Stages

/-! ## Order conditions -/

section OrderConditions

variable {s : ℕ} (rk : ExplicitRK s)

/-- Order-one condition: the weights sum to `1`. -/
def OrderOne : Prop := ∑ i, rk.b i = 1

/-- Order-two conditions. -/
def OrderTwo : Prop := OrderOne rk ∧ ∑ i, rk.b i * rk.c i = 1 / 2

/-- Order-three conditions. -/
def OrderThree : Prop :=
  OrderTwo rk ∧ ∑ i, rk.b i * rk.c i ^ 2 = 1 / 3 ∧
    ∑ i, ∑ j, rk.b i * rk.a i j * rk.c j = 1 / 6

/-- Order-four conditions: the eight Butcher conditions. -/
def OrderFour : Prop :=
  OrderThree rk ∧ ∑ i, rk.b i * rk.c i ^ 3 = 1 / 4 ∧
    ∑ i, ∑ j, rk.b i * rk.c i * rk.a i j * rk.c j = 1 / 8 ∧
    ∑ i, ∑ j, rk.b i * rk.a i j * rk.c j ^ 2 = 1 / 12 ∧
    ∑ i, ∑ j, ∑ k, rk.b i * rk.a i j * rk.a j k * rk.c k = 1 / 24

end OrderConditions

/-! ## Classical tableaux -/

section Tableaux

/-- The Euler tableau: one stage, weight `1`. -/
def eulerRK : ExplicitRK 1 where
  a := !![0]
  b := ![1]
  lower := by
    intro i j _
    (fin_cases i; fin_cases j; rfl)

/-- The midpoint tableau: `a = [[0, 0], [1 / 2, 0]]`, `b = [0, 1]`. -/
noncomputable def midpointRK : ExplicitRK 2 where
  a := !![0, 0; 1 / 2, 0]
  b := ![0, 1]
  lower := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- Heun's tableau: `a = [[0, 0], [1, 0]]`, `b = [1 / 2, 1 / 2]`. -/
noncomputable def heunRK : ExplicitRK 2 where
  a := !![0, 0; 1, 0]
  b := ![1 / 2, 1 / 2]
  lower := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- The classical fourth-order Runge–Kutta tableau. -/
noncomputable def rk4 : ExplicitRK 4 where
  a := !![0, 0, 0, 0; 1 / 2, 0, 0, 0; 0, 1 / 2, 0, 0; 0, 0, 1, 0]
  b := ![1 / 6, 1 / 3, 1 / 3, 1 / 6]
  lower := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- Euler satisfies the order-one condition. -/
theorem eulerRK_orderOne : OrderOne eulerRK := by
  simp [OrderOne, eulerRK]

/-- The midpoint method satisfies the order-two conditions. -/
theorem midpointRK_orderTwo : OrderTwo midpointRK := by
  refine ⟨?_, ?_⟩ <;>
    simp [OrderOne, midpointRK, ExplicitRK.c, Fin.sum_univ_two]

/-- Heun's method satisfies the order-two conditions. -/
theorem heunRK_orderTwo : OrderTwo heunRK := by
  refine ⟨?_, ?_⟩
  · simp [OrderOne, heunRK, Fin.sum_univ_two]
    norm_num
  · simp [heunRK, ExplicitRK.c, Fin.sum_univ_two]

/-- **The classical RK4 tableau satisfies all eight order-four conditions.** -/
theorem rk4_orderFour : OrderFour rk4 := by
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    simp [OrderOne, rk4, ExplicitRK.c, Fin.sum_univ_four] <;>
    norm_num

end Tableaux

/-! ## Euler as a Runge–Kutta method -/

section EulerStep

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E → E) (t : ℝ) (y : E)
  (h : ℝ)

/-- The one-stage method is the explicit Euler step. -/
theorem euler_step : rkStep eulerRK f t y h = y + h • f t y := by
  simp [rkStep, stage, stageRow, eulerRK, ExplicitRK.c]

end EulerStep

/-! ## Consistency -/

section Consistency

variable {s : ℕ} (rk : ExplicitRK s) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f : ℝ → E → E) (t : ℝ) (y : E)

/-- Each stage tends to `f t y` as `h → 0` through nonzero values, by strong induction on
the stage index (earlier stages appear in later ones). -/
theorem stage_tendsto (hf : ContinuousAt (Function.uncurry f) (t, y)) :
    ∀ (n : ℕ) (i : Fin s), i.val < n →
      Tendsto (fun h => stage rk f t y h i) (𝓝[≠] 0) (𝓝 (f t y)) := by
  intro n
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
      intro i hi
      have harg : Tendsto (fun h : ℝ => (t + rk.c i * h,
          y + h • ∑ j : Fin s, if j < i then rk.a i j • stage rk f t y h j else 0))
          (𝓝[≠] 0) (𝓝 (t, y)) := by
        have hId : Tendsto (fun h : ℝ => h) (𝓝[≠] 0) (𝓝 0) :=
          tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
        have hSum : Tendsto
            (fun h : ℝ => ∑ j : Fin s, if j < i then rk.a i j • stage rk f t y h j else 0)
            (𝓝[≠] 0)
            (𝓝 (∑ j : Fin s, if j < i then rk.a i j • f t y else 0)) := by
          refine tendsto_finsetSum _ fun j _ => ?_
          by_cases hj : j < i
          · have heq : (fun h : ℝ => if j < i then rk.a i j • stage rk f t y h j else 0) =
                fun h => rk.a i j • stage rk f t y h j := by
              funext h
              rw [ite_eq_left hj]
            rw [heq, ite_eq_left hj]
            exact (ih j (by
              have : j.val < i.val := hj
              omega)).const_smul _
          · have heq : (fun h : ℝ => if j < i then rk.a i j • stage rk f t y h j else 0) =
                fun _ => (0 : E) := by
              funext h
              rw [ite_eq_right hj]
            rw [heq, ite_eq_right hj]
            exact tendsto_const_nhds
        have hScaled : Tendsto
            (fun h : ℝ => h • ∑ j : Fin s, if j < i then rk.a i j • stage rk f t y h j else 0)
            (𝓝[≠] 0) (𝓝 0) := by
          have := hId.smul hSum
          simpa using this
        have h1 : Tendsto (fun h : ℝ => t + rk.c i * h) (𝓝[≠] 0) (𝓝 t) := by
          have := (tendsto_const_nhds (x := t)).add
            ((tendsto_const_nhds (x := rk.c i)).mul hId)
          simpa using this
        have h2 : Tendsto (fun h : ℝ => y + h •
            ∑ j : Fin s, if j < i then rk.a i j • stage rk f t y h j else 0)
            (𝓝[≠] 0) (𝓝 y) := by
          have := (tendsto_const_nhds (x := y)).add hScaled
          simpa using this
        rw [nhds_prod_eq]
        exact h1.prodMk h2
      have heq : (fun h => stage rk f t y h i) =
          fun h => f (t + rk.c i * h)
            (y + h • ∑ j : Fin s, if j < i then rk.a i j • stage rk f t y h j else 0) := by
        funext h
        exact stage_eq rk f t y h i
      rw [heq]
      exact hf.tendsto.comp harg

/-- **Consistency**: if `∑ b i = 1` and `f` is continuous at `(t, y)`, then
`h⁻¹ • (rkStep h - y) → f t y` as `h → 0` through nonzero values. -/
theorem rkStep_sub_inv_smul_tendsto (hOrder : OrderOne rk)
    (hf : ContinuousAt (Function.uncurry f) (t, y)) :
    Tendsto (fun h => h⁻¹ • (rkStep rk f t y h - y)) (𝓝[≠] 0) (𝓝 (f t y)) := by
  have hSum : Tendsto (fun h => ∑ i, rk.b i • stage rk f t y h i) (𝓝[≠] 0)
      (𝓝 (∑ i, rk.b i • f t y)) :=
    tendsto_finsetSum _ fun i _ => (stage_tendsto rk f t y hf s i i.isLt).const_smul _
  have hLim : ∑ i, rk.b i • f t y = f t y := by
    rw [← Finset.sum_smul, hOrder, one_smul]
  rw [← hLim]
  have heq : (fun h => h⁻¹ • (rkStep rk f t y h - y)) =ᶠ[𝓝[≠] 0]
      fun h => ∑ i, rk.b i • stage rk f t y h i := by
    refine eventually_nhdsWithin_of_forall fun h hh => ?_
    change h⁻¹ • (rkStep rk f t y h - y) = ∑ i, rk.b i • stage rk f t y h i
    have hh0 : h ≠ 0 := by simpa using hh
    have hsub : rkStep rk f t y h - y =
        h • ∑ i, rk.b i • stage rk f t y h i := by
      simp [rkStep, add_sub_cancel_left]
    rw [hsub, smul_smul, inv_mul_cancel₀ hh0, one_smul]
  exact hSum.congr' heq.symm

end Consistency

/-! ## Linear stability of RK4 -/

section Stability

/-- On the linear test equation `y' = λ y`, one RK4 step multiplies by the stability
polynomial `1 + z + z² / 2 + z³ / 6 + z⁴ / 24`, `z = λ h`. -/
theorem rk4_stability (lam y h : ℝ) :
    rkStep rk4 (fun _ y => lam * y) 0 y h =
      y * (1 + lam * h + (lam * h) ^ 2 / 2 + (lam * h) ^ 3 / 6 + (lam * h) ^ 4 / 24) := by
  have e0 : stage rk4 (fun _ y => lam * y) 0 y h 0 = lam * y := by
    rw [stage_eq]
    simp
  have e1 : stage rk4 (fun _ y => lam * y) 0 y h 1 =
      lam * (y + h * (1 / 2 * (lam * y))) := by
    rw [stage_eq, Fin.sum_univ_four,
      ite_eq_left (show (0 : Fin 4) < 1 by decide),
      ite_eq_right (show ¬ (1 : Fin 4) < 1 by decide),
      ite_eq_right (show ¬ (2 : Fin 4) < 1 by decide),
      ite_eq_right (show ¬ (3 : Fin 4) < 1 by decide), e0,
      show rk4.a 1 0 = (1 / 2 : ℝ) from rfl]
    simp only [add_zero, smul_eq_mul]
  have e2 : stage rk4 (fun _ y => lam * y) 0 y h 2 =
      lam * (y + h * (1 / 2 * (lam * (y + h * (1 / 2 * (lam * y)))))) := by
    rw [stage_eq, Fin.sum_univ_four,
      ite_eq_left (show (0 : Fin 4) < 2 by decide),
      ite_eq_left (show (1 : Fin 4) < 2 by decide),
      ite_eq_right (show ¬ (2 : Fin 4) < 2 by decide),
      ite_eq_right (show ¬ (3 : Fin 4) < 2 by decide), e0, e1,
      show rk4.a 2 0 = (0 : ℝ) from rfl, show rk4.a 2 1 = (1 / 2 : ℝ) from rfl]
    simp only [zero_mul, zero_add, add_zero, smul_eq_mul]
  have e3 : stage rk4 (fun _ y => lam * y) 0 y h 3 =
      lam * (y + h * (lam * (y + h * (1 / 2 * (lam * (y + h * (1 / 2 * (lam * y)))))))) := by
    rw [stage_eq, Fin.sum_univ_four,
      ite_eq_left (show (0 : Fin 4) < 3 by decide),
      ite_eq_left (show (1 : Fin 4) < 3 by decide),
      ite_eq_left (show (2 : Fin 4) < 3 by decide),
      ite_eq_right (show ¬ (3 : Fin 4) < 3 by decide), e0, e1, e2,
      show rk4.a 3 0 = (0 : ℝ) from rfl, show rk4.a 3 1 = (0 : ℝ) from rfl,
      show rk4.a 3 2 = (1 : ℝ) from rfl]
    simp only [zero_mul, zero_add, add_zero, one_mul, smul_eq_mul]
  rw [rkStep]
  simp only [Fin.sum_univ_four, e0, e1, e2, e3, smul_eq_mul,
    show rk4.b 0 = (1 / 6 : ℝ) from rfl, show rk4.b 1 = (1 / 3 : ℝ) from rfl,
    show rk4.b 2 = (1 / 3 : ℝ) from rfl, show rk4.b 3 = (1 / 6 : ℝ) from rfl]
  ring

end Stability

end MathlibExt.Analysis.ODE.RungeKutta
