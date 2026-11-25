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

/-- **Explicit Runge–Kutta method.** An explicit Runge–Kutta method with $s$ stages consists of
a real $s \times s$ Butcher tableau $a = (a_{ij})$ that is strictly lower triangular, meaning
$a_{ij} = 0$ whenever $i \le j$, and real weights $b_1, \dots, b_s$. -/
structure ExplicitRK (s : ℕ) where
  /-- The Butcher tableau, strictly lower triangular. -/
  a : Fin s → Fin s → ℝ
  /-- The weights. -/
  b : Fin s → ℝ
  /-- Strict lower-triangularity: `a i j = 0` for `i ≤ j`. -/
  lower : ∀ i j : Fin s, i ≤ j → a i j = 0

/-- **Nodes of a Runge–Kutta method.** For an explicit Runge–Kutta method with $s$ stages and
Butcher tableau $a$, the node of stage $i$ is the row sum $c_i = \sum_j a_{ij}$, taken over all
$s$ stages $j$. -/
def ExplicitRK.c {s : ℕ} (rk : ExplicitRK s) (i : Fin s) : ℝ := ∑ j, rk.a i j

section Stages

variable {s : ℕ} (rk : ExplicitRK s) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f : ℝ → E → E) (t : ℝ) (y : E) (h : ℝ)

/-- **Stages computed row by row.** Let $E$ be a real normed space, fix an explicit Runge–Kutta
method with $s$ stages, strictly lower-triangular tableau $a$ and nodes $c_i = \sum_j a_{ij}$, a
vector field $f$ assigning a vector $f(t', x) \in E$ to each time $t' \in \mathbb{R}$ and state
$x \in E$, a time $t$, a state $y \in E$ and a step $h \in \mathbb{R}$. The rows $K^{(n)} \in E^s$,
indexed by $0 \le i < s$, are defined by recursion on $n$: $K^{(0)} = 0$, and $K^{(n+1)}_i$ equals
$f\bigl(t + c_i h,\ y + h \sum_{j < n} a_{ij} K^{(n)}_j\bigr)$ when $i = n$ and equals
$K^{(n)}_i$ when $i \ne n$. Only the entries of $K^{(n)}$ with index less than $n$ are filled in;
the others are $0$. -/
def stageRow : ℕ → Fin s → E
  | 0 => fun _ => 0
  | n + 1 => fun i =>
      if i.val = n then
        f (t + rk.c i * h)
          (y + h • ∑ j : Fin s, if j.val < n then rk.a i j • stageRow n j else 0)
      else stageRow n i

/-- **Runge–Kutta stages.** Let $E$ be a real normed space, fix an explicit Runge–Kutta method
with $s$ stages, strictly lower-triangular tableau $a$ and nodes $c_i = \sum_j a_{ij}$, a vector
field $f$ assigning a vector $f(t', x) \in E$ to each time $t' \in \mathbb{R}$ and state
$x \in E$, a time $t$, a state $y \in E$ and a step $h \in \mathbb{R}$. Let the rows
$K^{(n)} \in E^s$, indexed by $0 \le i < s$, be defined by $K^{(0)} = 0$, and $K^{(n+1)}_i$ equal
to $f\bigl(t + c_i h,\ y + h \sum_{j < n} a_{ij} K^{(n)}_j\bigr)$ when $i = n$ and to
$K^{(n)}_i$ when $i \ne n$. For $0 \le i < s$, the $i$-th stage $k_i \in E$ is the entry at
index $i$ of the row $K^{(i+1)}$. -/
def stage (i : Fin s) : E := stageRow rk f t y h (i.val + 1) i

/-- **Partial stage rows agree with the stages.** Let $E$ be a real normed vector space and
$f(t, y)$ a vector field $\mathbb{R} \times E \to E$, and fix an explicit Runge–Kutta method,
a time $t$, a state $y \in E$ and a step size $h \in \mathbb{R}$. Index the stages from $0$.
For every natural number $m$ and every stage index $i < m$, the $i$-th entry of the $m$-th
partial row for $f$, $t$, $y$ and $h$ (the row-by-row construction that fills in the stages
with index less than $m$ and sets the rest to $0$) equals the $i$-th stage $k_i$. -/
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

/-- **The defining equation of the stages.** Let $E$ be a real normed vector space and $f(t, y)$
a vector field $\mathbb{R} \times E \to E$. For an explicit Runge–Kutta method with tableau $a$
and nodes $c_i = \sum_j a_{ij}$, a time $t$, a state $y \in E$ and a step size $h$, the
stages $k_i$ satisfy
$k_i = f\bigl(t + c_i h, \; y + h \sum_{j < i} a_{ij} k_j\bigr)$ for every stage index $i$. -/
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

/-- **One Runge–Kutta step.** Let $E$ be a real normed vector space and $f(t, y)$ a vector
field $\mathbb{R} \times E \to E$. For an explicit Runge–Kutta method with weights $b$, a
time $t$, a state $y \in E$ and a step size $h \in \mathbb{R}$, one step of the method
is $y + h \sum_i b_i k_i$, where $k_i$ is the $i$-th stage of the method for $f$, $t$, $y$
and $h$, and the sum runs over the stages. -/
def rkStep : E := y + h • ∑ i, rk.b i • stage rk f t y h i

end Stages

/-! ## Order conditions -/

section OrderConditions

variable {s : ℕ} (rk : ExplicitRK s)

/-- **Order-one condition for Runge–Kutta methods.** An explicit Runge–Kutta method with
weights $b_i$ satisfies the order-one condition when $\sum_i b_i = 1$, the sum running
over all of its stages $i$. -/
def OrderOne : Prop := ∑ i, rk.b i = 1

/-- **Order-two conditions for Runge–Kutta methods.** An explicit Runge–Kutta method with
tableau $a$, weights $b$ and nodes $c_i = \sum_j a_{ij}$ satisfies the order-two
conditions when it satisfies the order-one condition $\sum_i b_i = 1$ and moreover
$\sum_i b_i c_i = \frac{1}{2}$, all sums running over the stages. -/
def OrderTwo : Prop := OrderOne rk ∧ ∑ i, rk.b i * rk.c i = 1 / 2

/-- **Order-three conditions for Runge–Kutta methods.** An explicit Runge–Kutta method with
tableau $a$, weights $b$ and nodes $c_i = \sum_j a_{ij}$ satisfies the order-three
conditions when it satisfies the order-two conditions $\sum_i b_i = 1$ and
$\sum_i b_i c_i = \frac{1}{2}$, and moreover $\sum_i b_i c_i^2 = \frac{1}{3}$ and
$\sum_{i, j} b_i a_{ij} c_j = \frac{1}{6}$, all sums running over the stages. -/
def OrderThree : Prop :=
  OrderTwo rk ∧ ∑ i, rk.b i * rk.c i ^ 2 = 1 / 3 ∧
    ∑ i, ∑ j, rk.b i * rk.a i j * rk.c j = 1 / 6

/-- **Order-four conditions.** An explicit Runge–Kutta method with Butcher tableau $a$, weights
$b$ and nodes $c$ satisfies the order-four conditions when it satisfies the order-three
conditions, namely $\sum_i b_i = 1$, $\sum_i b_i c_i = 1/2$, $\sum_i b_i c_i^2 = 1/3$ and
$\sum_{i,j} b_i a_{ij} c_j = 1/6$, together with $\sum_i b_i c_i^3 = 1/4$,
$\sum_{i,j} b_i c_i a_{ij} c_j = 1/8$, $\sum_{i,j} b_i a_{ij} c_j^2 = 1/12$ and
$\sum_{i,j,k} b_i a_{ij} a_{jk} c_k = 1/24$. These are the eight Butcher conditions. -/
def OrderFour : Prop :=
  OrderThree rk ∧ ∑ i, rk.b i * rk.c i ^ 3 = 1 / 4 ∧
    ∑ i, ∑ j, rk.b i * rk.c i * rk.a i j * rk.c j = 1 / 8 ∧
    ∑ i, ∑ j, rk.b i * rk.a i j * rk.c j ^ 2 = 1 / 12 ∧
    ∑ i, ∑ j, ∑ k, rk.b i * rk.a i j * rk.a j k * rk.c k = 1 / 24

end OrderConditions

/-! ## Classical tableaux -/

section Tableaux

/-- **Euler tableau.** The explicit Runge–Kutta method with one stage, Butcher tableau
$a = (0)$ and weight $b_1 = 1$. -/
def eulerRK : ExplicitRK 1 where
  a := !![0]
  b := ![1]
  lower := by
    intro i j _
    (fin_cases i; fin_cases j; rfl)

/-- **Midpoint tableau.** The explicit Runge–Kutta method with two stages, Butcher tableau
entries $a_{21} = 1/2$ and $a_{11} = a_{12} = a_{22} = 0$, and weights $b_1 = 0$, $b_2 = 1$. -/
noncomputable def midpointRK : ExplicitRK 2 where
  a := !![0, 0; 1 / 2, 0]
  b := ![0, 1]
  lower := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- **Heun's tableau.** The explicit Runge–Kutta method with two stages, Butcher tableau entries
$a_{21} = 1$ and $a_{11} = a_{12} = a_{22} = 0$, and weights $b_1 = b_2 = 1/2$. -/
noncomputable def heunRK : ExplicitRK 2 where
  a := !![0, 0; 1, 0]
  b := ![1 / 2, 1 / 2]
  lower := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- **The classical RK4 tableau.** The classical fourth-order Runge–Kutta method is the
explicit four-stage Runge–Kutta method whose tableau, with stages indexed $1, \dots, 4$, has
$a_{21} = \frac{1}{2}$, $a_{32} = \frac{1}{2}$, $a_{43} = 1$ and all other $a_{ij} = 0$,
and whose weights are $b = (\frac{1}{6}, \frac{1}{3}, \frac{1}{3}, \frac{1}{6})$. -/
noncomputable def rk4 : ExplicitRK 4 where
  a := !![0, 0, 0, 0; 1 / 2, 0, 0, 0; 0, 1 / 2, 0, 0; 0, 0, 1, 0]
  b := ![1 / 6, 1 / 3, 1 / 3, 1 / 6]
  lower := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- **The Euler tableau satisfies the order-one condition.** The weights of the Euler
tableau sum to $1$. -/
theorem eulerRK_orderOne : OrderOne eulerRK := by
  simp [OrderOne, eulerRK]

/-- **The midpoint tableau satisfies the order-two conditions.** For the midpoint tableau, with
weights $b_i$ and nodes $c_i$, we have $\sum_i b_i = 1$ and $\sum_i b_i c_i = 1/2$. -/
theorem midpointRK_orderTwo : OrderTwo midpointRK := by
  refine ⟨?_, ?_⟩ <;>
    simp [OrderOne, midpointRK, ExplicitRK.c, Fin.sum_univ_two]

/-- **Heun's tableau satisfies the order-two conditions.** For Heun's tableau, with weights
$b_i$ and nodes $c_i$, we have $\sum_i b_i = 1$ and $\sum_i b_i c_i = 1/2$. -/
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

/-- **The Euler tableau gives the explicit Euler step.** Let $E$ be a real normed space and let
$f$ assign to each time $t \in \mathbb{R}$ and state $y \in E$ a vector $f(t, y) \in E$. For all
$t, h \in \mathbb{R}$ and $y \in E$, one Runge–Kutta step of size $h$ from the state $y$ at time
$t$ with the Euler tableau equals $y + h f(t, y)$. -/
theorem euler_step : rkStep eulerRK f t y h = y + h • f t y := by
  simp [rkStep, stage, stageRow, eulerRK, ExplicitRK.c]

end EulerStep

/-! ## Consistency -/

section Consistency

variable {s : ℕ} (rk : ExplicitRK s) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f : ℝ → E → E) (t : ℝ) (y : E)

/-- **Runge–Kutta stages tend to the vector field as the step shrinks.** Let $E$ be a real normed
space, fix an explicit Runge–Kutta method with $s$ stages, a vector field $f$ assigning a vector
$f(t', x) \in E$ to each time $t' \in \mathbb{R}$ and state $x \in E$, a time $t$ and a state
$y \in E$, and suppose that $(t', x) \mapsto f(t', x)$ is continuous at $(t, y)$. For a step
$h \in \mathbb{R}$, let $k_i(h)$ be the $i$-th stage of the method with step $h$. Then for every
natural number $n$ and every stage index $i < n$, $k_i(h) \to f(t, y)$ as $h \to 0$ with
$h \ne 0$.

The proof is by strong induction on the stage index, since earlier stages appear in later ones. -/
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

/-- **Consistency of explicit Runge–Kutta methods.** Let $E$ be a real normed vector space,
let $f(t, y)$ be a vector field $\mathbb{R} \times E \to E$, let $t \in \mathbb{R}$ and
$y \in E$, and for an explicit Runge–Kutta method with weights $b$ let $y_1(h)$ be the
result of one step of size $h$ from the state $y$ at time $t$. If $\sum_i b_i = 1$ and $f$
is continuous at $(t, y)$ as a function of both variables, then
$h^{-1} (y_1(h) - y) \to f(t, y)$ as $h \to 0$ with $h \neq 0$. -/
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

/-- **Stability function of the classical RK4 method.** For all real numbers $\lambda$, $y$
and $h$, one step of size $h$ of the classical fourth-order Runge–Kutta method applied to
the scalar linear test equation $u' = \lambda u$ on $\mathbb{R}$, starting from the state
$y$ at time $0$, gives $y \, R(\lambda h)$, where
$R(z) = 1 + z + \frac{z^2}{2} + \frac{z^3}{6} + \frac{z^4}{24}$. -/
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
