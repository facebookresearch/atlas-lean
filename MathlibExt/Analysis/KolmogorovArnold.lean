/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Analysis/KolmogorovArnold.lean` (leanprover/lean-eval), at commit
38361be884302c7edce1908c4aef8296eb2cb27e, problem `kolmogorov_arnold_superposition`
(manifest `manifests/problems/kolmogorov_arnold_superposition.toml`, rev 1, submitter Kim Morrison,
status archived). The adapted portions are the statement of `kolmogorov_arnold` and the accompanying
documentation from `WantedExt/Analysis/KolmogorovArnoldWanted.lean`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison (problem submitter)
Licensed under the Apache License, Version 2.0 (the "License"). You may obtain a copy at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). ATLAS previously converted the eval problem
to a wanted declaration in the `MathlibExt.Analysis.KolmogorovArnoldWanted.Analysis` namespace.
The theorem now has a proof in MathlibExt with its name and statement preserved.
-/
module

public import MathlibExt.Analysis.ContinuousMap.KolmogorovSuperposition
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Kolmogorov–Arnold superposition theorem (non-universal existence form)

For every continuous `f` on the unit cube `[0, 1]ⁿ` (with `n ≥ 1`),
there exist continuous one-variable inner functions `φ_{k,l} : ℝ → ℝ`
and a single continuous outer function `g : ℝ → ℝ` such that

  `f(x₁, …, xₙ) = ∑_{k=0}^{2n} g(∑_{l=1}^{n} φ_{k,l}(x_l))`.

This is the Lorentz (1962) single-outer-function form. Both `g` and the
`φ_{k,l}` are allowed to depend on `f` — weaker than the universal-
inner-functions formulation, since here the inner functions may depend
on `f`. The two-variable function used to combine the layers is just
addition, resolving the continuous form of Hilbert's 13th problem.

The inner and outer functions are stated as globally continuous maps
`ℝ → ℝ`. This is a harmless strengthening of versions stated on
compact subsets: the inner functions are only evaluated on `[0, 1]`,
and the outer function is only evaluated on the compact set of inner
sums, so Tietze extension gives global continuous representatives.
-/

public section

namespace MathlibExt.Analysis.KolmogorovArnoldWanted.Analysis

open scoped BigOperators

/-- On finitely many disjoint translates of `[-B, B]`, one continuous function can reproduce
each of the given outer functions in its original coordinates. -/
private theorem exists_shifted_outer {m : ℕ} (h : Fin m → C(ℝ, ℝ)) (B : ℝ) (hB : 0 ≤ B) :
    ∃ (g : ℝ → ℝ) (a : Fin m → ℝ), Continuous g ∧
      ∀ k t, |t| ≤ B → g (t + a k) = h k t := by
  let a (k : Fin m) : ℝ := (2 * B + 2) * (k.val : ℝ)
  have gap {j k : Fin m} (hjk : j < k) : a j + (2 * B + 2) ≤ a k := by
    have hj : (j.val : ℝ) + 1 ≤ k.val := by exact_mod_cast Nat.succ_le_of_lt hjk
    calc
      a j + (2 * B + 2) = (2 * B + 2) * (j.val + 1 : ℝ) := by dsimp [a]; ring
      _ ≤ a k := mul_le_mul_of_nonneg_left hj (by linarith)
  let cutoff (t : ℝ) := min 1 (max 0 (B + 1 - |t|))
  refine ⟨fun x => ∑ j, cutoff (x - a j) * h j (x - a j), a, ?_, ?_⟩
  · dsimp [cutoff]
    fun_prop
  · intro k t ht
    dsimp only
    rw [Finset.sum_eq_single k]
    · have hone : 1 ≤ max 0 (B + 1 - |t|) := le_max_of_le_right (by linarith)
      simp [cutoff, min_eq_left hone]
    · intro j _ hj
      have hfar : B + 1 ≤ |t + a k - a j| := by
        rcases lt_or_gt_of_ne hj with hjk | hkj
        · exact le_trans (by linarith [(abs_le.mp ht).1, gap hjk]) (le_abs_self _)
        · exact le_trans (by linarith [(abs_le.mp ht).2, gap hkj]) (neg_le_abs _)
      simp [cutoff, max_eq_left (sub_nonpos.mpr hfar)]
    · simp

set_option linter.dupNamespace false in
/-- **Kolmogorov–Arnold superposition with a single outer function.** Let $n \ge 1$ and let
$f : \mathbb{R}^n \to \mathbb{R}$ be continuous on the unit cube $[0, 1]^n$. Then there exist a
continuous function $g : \mathbb{R} \to \mathbb{R}$ and continuous functions
$\varphi_{k,l} : \mathbb{R} \to \mathbb{R}$ for $0 \le k \le 2n$ and $0 \le l < n$ such that for
every $x = (x_0, \dots, x_{n-1}) \in [0, 1]^n$,

$$f(x) = \sum_{k=0}^{2n} g\left(\sum_{l=0}^{n-1} \varphi_{k,l}(x_l)\right).$$

Both $g$ and the $\varphi_{k,l}$ may depend on $f$, so this is weaker than the form in which the
inner functions are universal.

Source: A. N. Kolmogorov, *On the representation of continuous functions of several variables by
superposition of continuous functions of one variable and addition*, Doklady Akad. Nauk SSSR 114
(1957), 953-956. V. I. Arnold, *On functions of three variables*, Doklady Akad. Nauk SSSR 114
(1957), 679-681. G. G. Lorentz, *Metric entropy, widths, and superpositions of functions*, Amer.
Math. Monthly 69 (1962), 469-485 (single-outer-function refinement). Listed as §80 in O.
Knill, *Some Fundamental Theorems in Mathematics*
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via
leanprover/lean-eval@38361be, problem `kolmogorov_arnold_superposition`. -/
theorem kolmogorov_arnold (n : ℕ) (_hn : 1 ≤ n)
    (f : (Fin n → ℝ) → ℝ) (_hf : ContinuousOn f (Set.Icc 0 1)) :
    ∃ (g : ℝ → ℝ) (φ : Fin (2 * n + 1) → Fin n → ℝ → ℝ),
      Continuous g ∧ (∀ k l, Continuous (φ k l)) ∧
      ∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1,
        f x = ∑ k, g (∑ l, φ k l (x l)) := by
  let F : C(Fin n → Set.Icc (0 : ℝ) 1, ℝ) :=
    ⟨fun y => f (fun l => y l), _hf.comp_continuous (by fun_prop)
      (fun y => ⟨fun l => (y l).property.1, fun l => (y l).property.2⟩)⟩
  obtain rfl | hn := eq_or_lt_of_le _hn
  · -- The three outer summands can each supply one third of the value.
    let g (t : ℝ) := F (fun _ => Set.projIcc 0 1 zero_le_one t) / 3
    refine ⟨g, fun _ _ => id, ?_, fun _ _ => continuous_id, ?_⟩
    · dsimp [g]
      fun_prop
    · intro x hx
      have hx₀ : x 0 ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1 0, hx.2 0⟩
      have he : (fun _ : Fin 1 => x 0) = x := funext fun i => congrArg x (Subsingleton.elim 0 i)
      simp [g, F, Set.projIcc_of_mem _ hx₀, he]
      ring
  obtain ⟨ψ, hψ⟩ :=
    MathlibExt.Analysis.ContinuousMap.KolmogorovSuperpositionWanted.kolmogorov_superposition hn
  obtain ⟨h, hh⟩ := hψ F
  let B := ∑ k, ∑ l, ‖ψ k l‖
  have hB (k) (y : Fin n → Set.Icc (0 : ℝ) 1) : |∑ l, ψ k l (y l)| ≤ B := by
    calc
      _ ≤ ∑ l, |ψ k l (y l)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l, ‖ψ k l‖ := Finset.sum_le_sum fun l _ => (ψ k l).norm_coe_le_norm _
      _ ≤ B := Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun l _ => norm_nonneg (ψ j l))
        (Finset.mem_univ k)
  have hB₀ : 0 ≤ B := Finset.sum_nonneg fun k _ =>
    Finset.sum_nonneg fun l _ => norm_nonneg (ψ k l)
  obtain ⟨g, a, hg, ha⟩ := exists_shifted_outer h B hB₀
  -- Put the entire translation into the first coordinate of each inner sum.
  let first : Fin n := ⟨0, by omega⟩
  refine ⟨g, fun k l t => ψ k l (Set.projIcc 0 1 zero_le_one t) +
    (if l = first then a k else 0), hg, ?_, ?_⟩
  · intro k l
    fun_prop
  · intro x hx
    let y (l : Fin n) : Set.Icc (0 : ℝ) 1 := ⟨x l, hx.1 l, hx.2 l⟩
    change F y = _
    rw [hh y]
    apply Finset.sum_congr rfl
    intro k _
    have hproj (l) : Set.projIcc 0 1 zero_le_one (x l) = y l := Set.projIcc_of_mem _ (y l).2
    simp only [hproj, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact (ha k _ (hB k y)).symm

end MathlibExt.Analysis.KolmogorovArnoldWanted.Analysis
