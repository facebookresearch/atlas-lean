/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Normal numbers

This file adapts the normal-number API from
[`FormalConjecturesForMathlib/NumberTheory/NormalNumber.lean`](https://github.com/google-deepmind/formal-conjectures/blob/62f56e8e4dab933a720f649721875c478b0ecf1c/FormalConjecturesForMathlib/NumberTheory/NormalNumber.lean)
at commit `62f56e8e4dab933a720f649721875c478b0ecf1c`.

The local adaptation places the declarations below `MetaMathlibExt`. The digit
formula is total for every natural `b`, but its interpretation as a positional
expansion, and therefore the normality predicates, is intended only for bases
`b ≥ 2`.
-/

@[expose] public section

open Real Filter

namespace MetaMathlibExt.NormalNumber

/-- **Base-$b$ digits of a real number.** For natural numbers $b$ and $n$ and a real number $x$, the
$n$-th digit of $x$ in base $b$, counting from $n = 0$ just after the radix point, is
$\lfloor b^{n+1} \{x\} \rfloor \bmod b$, where $\{x\} = x - \lfloor x \rfloor$ is the fractional
part of $x$.

For $b \ge 2$ these are the digits of the base-$b$ expansion of $\{x\}$ that does not end in an
infinite run of the digit $b - 1$. The formula is intended only for bases $b \ge 2$. -/
noncomputable def digitSeq (b : ℕ) (x : ℝ) (n : ℕ) : ℕ :=
  ⌊(b : ℝ) ^ (n + 1) * Int.fract x⌋₊ % b

/-- **Simply normal numbers.** For a natural number $b$ and a real number $x$, write $a_k$ for the
$k$-th base-$b$ digit of $x$ after the radix point, counting from $k = 0$. Then $x$ is simply
normal in base $b$ if for every natural number $d < b$ the proportion
$\#\{k < n : a_k = d\} / n$ tends to $1/b$ as $n \to \infty$.

This predicate is intended for bases $b \ge 2$. -/
noncomputable def IsSimplyNormalInBase (b : ℕ) (x : ℝ) : Prop :=
  ∀ d : ℕ, d < b →
    Tendsto
      (fun n : ℕ =>
        (((Finset.range n).filter (fun k => digitSeq b x k = d)).card : ℝ) / n)
      atTop
      (nhds (1 / (b : ℝ)))

/-- **Normal numbers.** For a natural number $b$ and a real number $x$, write $a_i$ for the $i$-th
base-$b$ digit of $x$ after the radix point, counting from $i = 0$. Then $x$ is normal in base $b$
if for every natural number $k$ and all natural numbers $w_0, \dots, w_{k-1} < b$ the proportion
$\#\{i < n : a_{i+j} = w_j \text{ for all } j < k\} / n$ tends to $1/b^k$ as $n \to \infty$.

This predicate is intended for bases $b \ge 2$. -/
noncomputable def IsNormalInBase (b : ℕ) (x : ℝ) : Prop :=
  ∀ (k : ℕ) (w : Fin k → ℕ), (∀ j, w j < b) →
    Tendsto
      (fun n : ℕ =>
        (((Finset.range n).filter
          (fun i => ∀ j : Fin k, digitSeq b x (i + j) = w j)).card : ℝ) / n)
      atTop
      (nhds (1 / (b : ℝ) ^ k))

/-- **Normal numbers are simply normal.** If a real number $x$ is normal in base $b$, then $x$ is
simply normal in base $b$. -/
theorem IsNormalInBase.isSimplyNormalInBase {b : ℕ} {x : ℝ} (h : IsNormalInBase b x) :
    IsSimplyNormalInBase b x := by
  intro d hd
  simpa [Fin.forall_fin_one] using h 1 (fun _ => d) (fun _ => hd)

/-- A real number is absolutely normal if it is normal in every base at least two. -/
noncomputable def IsAbsolutelyNormal (x : ℝ) : Prop :=
  ∀ b : ℕ, 2 ≤ b → IsNormalInBase b x

end MetaMathlibExt.NormalNumber
