/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Combinatorics/ShannonCapacityPentagon.lean` (leanprover/lean-eval),
problem `shannon_capacity_pentagon`, at commit 38361be884302c7edce1908c4aef8296eb2cb27e (manifest
`manifests/problems/shannon_capacity_pentagon.toml`, rev 1, submitter Kim Morrison,
status archived):
the definitions `strongPower` and `HasShannonCapacity` and the statement of
`shannon_capacity_pentagon`, with their docstrings from the former wanted module.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License"); you may not use these portions
except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). ATLAS placed the declarations in their
current namespace, inlined any LeanEval helper modules, and replaced the evaluation marker with
a Batteries `theorem_wanted`. ATLAS subsequently proved the theorem and moved the declarations
into this module with their statements unchanged.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import MathlibExt.Combinatorics.SimpleGraph.LovaszThetaPentagon

/-!
# Shannon capacity of the pentagon

The roots of the independence numbers of the strong powers of the pentagon converge to `√5`.
The upper bound uses Lovász theta. The lower bound repeats the two-coordinate code `(a, 2a)`
over the vertices modulo five.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ShannonCapacityPentagonWanted
namespace Combinatorics.ShannonCapacityPentagon

open Filter
open scoped Topology

set_option linter.dupNamespace false in
/-- **Strong power of a graph.** Let $G$ be a simple graph with vertex set $V$ and let $k$ be a
natural number. The $k$-th strong power $G^{\boxtimes k}$ is the simple graph whose vertices are
the words $x = (x_1, \dots, x_k) \in V^k$ of length $k$, in which two words $x$ and $y$ are
adjacent (confusable) when $x \neq y$ and for every $i$ either $x_i = y_i$ or $x_i$ and $y_i$ are
adjacent in $G$. -/
def strongPower {V : Type*} (G : SimpleGraph V) (k : ℕ) : SimpleGraph (Fin k → V) where
  Adj x y := x ≠ y ∧ ∀ i, x i = y i ∨ G.Adj (x i) (y i)
  symm.symm x y := by
    rintro ⟨hxy, hcoord⟩
    exact ⟨hxy.symm, fun i => (hcoord i).imp Eq.symm SimpleGraph.Adj.symm⟩
  loopless := ⟨fun x h => h.1 rfl⟩

set_option linter.dupNamespace false in
/-- **Shannon capacity of a graph.** Let $G$ be a simple graph on a finite vertex set and let
$\theta$ be a real number. For $k \ge 1$ let $G^{\boxtimes k}$ be the $k$-th strong power of $G$
and $\alpha(G^{\boxtimes k})$ its independence number. The graph $G$ has Shannon capacity $\theta$
when $\alpha(G^{\boxtimes k})^{1/k} \to \theta$ as $k \to \infty$. -/
noncomputable def HasShannonCapacity {V : Type*} [Fintype V] (G : SimpleGraph V) (θ : ℝ) :
    Prop :=
  Tendsto
    (fun k : ℕ =>
      Real.rpow
        ((strongPower G (k + 1)).indepNum : ℝ)
        ((k + 1 : ℝ)⁻¹))
    atTop (𝓝 θ)


/-- Confusability in both coordinates of the two-coordinate code determines the symbol. -/
private theorem eq_of_cycleGraph_five_code :
    ∀ a b : Fin 5, (a = b ∨ (SimpleGraph.cycleGraph 5).Adj a b) →
      (2 * a = 2 * b ∨ (SimpleGraph.cycleGraph 5).Adj (2 * a) (2 * b)) → a = b := by
  decide

/-- Each symbol occupies two coordinates. Any remaining coordinates can be filled with zeros. -/
private theorem five_pow_le_indepNum {m n : ℕ} (hmn : m + m ≤ n) :
    5 ^ m ≤ (strongPower (SimpleGraph.cycleGraph 5) n).indepNum := by
  have hn : m + (m + (n - (m + m))) = n := by omega
  let word (x : Fin m → Fin 5) (i : Fin n) : Fin 5 :=
    Fin.append x (Fin.append (fun j => 2 * x j) (fun _ => 0)) (Fin.cast hn.symm i)
  let left (i : Fin m) : Fin n := Fin.cast hn (Fin.castAdd _ i)
  let right (i : Fin m) : Fin n := Fin.cast hn (Fin.natAdd m (Fin.castAdd _ i))
  have word_left (x) (i) : word x (left i) = x i := by simp [word, left]
  have word_right (x) (i) : word x (right i) = 2 * x i := by simp [word, right]
  let encode : (Fin m → Fin 5) ↪ (Fin n → Fin 5) :=
    ⟨word, fun _ _ h => funext fun i => by simpa only [word_left] using congrFun h (left i)⟩
  let code := Finset.univ.map encode
  have hind : (strongPower (SimpleGraph.cycleGraph 5) n).IsIndepSet (↑code) := by
    intro u hu v hv huv hadj
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hu)
    obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hv)
    change (strongPower (SimpleGraph.cycleGraph 5) n).Adj (word x) (word y) at hadj
    apply huv
    change word x = word y
    apply congrArg word
    funext i
    exact eq_of_cycleGraph_five_code (x i) (y i)
      (by simpa only [word_left] using hadj.2 (left i))
      (by simpa only [word_right] using hadj.2 (right i))
  simpa [code] using hind.card_le_indepNum

open MathlibExt.Combinatorics.SimpleGraph.LovaszTheta in
private theorem indepNum_le_sqrt_five_pow (n : ℕ) :
    ((strongPower (SimpleGraph.cycleGraph 5) n).indepNum : ℝ) ≤ (Real.sqrt 5) ^ n := by
  refine (indepNum_le_lovaszTheta_pow _ ?_).trans
    (pow_le_pow_left₀ (lovaszTheta_nonneg _) lovaszTheta_cycleGraph_five_le _)
  intro x y hxy hna
  by_contra! h
  exact hna ⟨hxy, fun i => or_iff_not_imp_left.mpr (h i)⟩

set_option linter.dupNamespace false in
/-- **Lovász's theorem: the Shannon capacity of the pentagon.** The cycle graph $C_5$ on five
vertices has Shannon capacity $\sqrt{5}$: writing $\alpha(C_5^{\boxtimes k})$ for the independence
number of the $k$-th strong power of $C_5$, we have $\alpha(C_5^{\boxtimes k})^{1/k} \to \sqrt{5}$
as $k \to \infty$.

Source: Knill, *Some fundamental theorems in mathematics*, §238. Via leanprover/lean-eval@38361be,
problem `shannon_capacity_pentagon`. -/
public theorem shannon_capacity_pentagon :
    HasShannonCapacity (SimpleGraph.cycleGraph 5) (Real.sqrt 5) := by
  let s := Real.sqrt 5
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs₁ : 1 ≤ s := Real.le_sqrt_of_sq_le (by norm_num)
  have hs₂ : s ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hlim : Tendsto (fun k : ℕ => s ^ ((k : ℝ) / (k + 1))) atTop (𝓝 s) := by
    have ht := (Real.continuousAt_const_rpow (a := s) (b := 1)
      (zero_lt_one.trans_le hs₁).ne').tendsto.comp (tendsto_natCast_div_add_atTop (1 : ℝ))
    rw [Real.rpow_one] at ht
    exact ht
  unfold HasShannonCapacity
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds ?_ ?_
  · intro k
    let m := (k + 1) / 2
    have hmn : m + m ≤ k + 1 := by dsimp [m]; omega
    have hkm : k ≤ 2 * m := by dsimp [m]; omega
    have hlower : s ^ k ≤ ((strongPower (SimpleGraph.cycleGraph 5) (k + 1)).indepNum : ℝ) :=
      calc
        s ^ k ≤ s ^ (2 * m) := pow_le_pow_right₀ hs₁ hkm
        _ = (5 : ℝ) ^ m := by rw [pow_mul, hs₂]
        _ ≤ _ := by exact_mod_cast (five_pow_le_indepNum hmn)
    change s ^ ((k : ℝ) / (k + 1)) ≤
      ((strongPower (SimpleGraph.cycleGraph 5) (k + 1)).indepNum : ℝ) ^ (((k : ℝ) + 1)⁻¹)
    rw [div_eq_mul_inv, Real.rpow_natCast_mul hs]
    exact Real.rpow_le_rpow (pow_nonneg hs _) hlower (by positivity)
  · intro k
    change ((strongPower (SimpleGraph.cycleGraph 5) (k + 1)).indepNum : ℝ) ^
      (((k : ℝ) + 1)⁻¹) ≤ Real.sqrt 5
    have h := Real.rpow_le_rpow (Nat.cast_nonneg _) (indepNum_le_sqrt_five_pow (k + 1))
      (by positivity : 0 ≤ ((k + 1 : ℕ) : ℝ)⁻¹)
    rw [Real.pow_rpow_inv_natCast (Real.sqrt_nonneg _) (Nat.succ_ne_zero k)] at h
    simpa only [Nat.cast_add, Nat.cast_one] using h

end Combinatorics.ShannonCapacityPentagon

end MathlibExt.Combinatorics.ShannonCapacityPentagonWanted
