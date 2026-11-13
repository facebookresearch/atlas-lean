/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fatou–Julia / Cantor dichotomy

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.ComplexAnalysis.FatouJulia` — fatou_julia_dichotomy (manifest `manifests/problems/fatou_julia_dichotomy.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.FatouJuliaWanted` namespace. Mathematical
statements are unchanged. Source: P. Fatou, *Sur les équations fonctionnelles*, Bull. Soc. Math. France 47 (1919), 161-271; 48 (1920), 33-94, 208-314. G. Julia, *Mémoire sur l'itération des fonctions rationnelles*, J. Math. Pures Appl. 1 (1918), 47-245. Modern statement: A. Douady and J. H. Hubbard, *Étude dynamique des polynômes complexes I, II*, Publ. Math. Orsay 84-02, 85-04. Listed as §62 (additional statement 1) in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.FatouJuliaWanted
namespace ComplexAnalysis
namespace FatouJuliaProblem

/-!
# Fatou–Julia / Cantor dichotomy

For the quadratic family `T_c(z) = z² + c`, the filled Julia set
`K_c = { z ∈ ℂ | T_c^n(z) stays bounded }` satisfies:

- `c ∈ M` (Mandelbrot set) implies `K_c` is connected;
- `c ∉ M` implies `K_c` is homeomorphic to the Cantor space `ℕ → Bool`.

For quadratic polynomials, the usual Julia set is `∂K_c`. The submitted
statement uses the filled Julia set `K_c`; this is equivalent for the
dichotomy here, since connectedness of `K_c` is equivalent to
connectedness of `∂K_c`, and in the escaping case `K_c = ∂K_c` is a
Cantor set.
-/

open Function

/-- **Quadratic map $T_c$.** For $c \in \mathbb{C}$, $T_c \colon \mathbb{C} \to \mathbb{C}$ is the
map $T_c(z) = z^2 + c$. -/
def Tc (c : ℂ) (z : ℂ) : ℂ := z ^ 2 + c

/-- **Mandelbrot set of the quadratic family.** Let $T_c(z) = z^2 + c$ for $c \in \mathbb{C}$
and let $T_c^n$ be its $n$-fold iterate. The Mandelbrot set $M$ is the set of $c \in \mathbb{C}$
for which the orbit of $0$ under $T_c$ is bounded: there is a real $R$ such that
$|T_c^n(0)| \le R$ for every $n \ge 0$. -/
def Mandelbrot : Set ℂ :=
  { c : ℂ | ∃ M : ℝ, ∀ n : ℕ, ‖(Tc c)^[n] 0‖ ≤ M }

/-- **Filled Julia set.** For $c \in \mathbb{C}$, let $T_c(z) = z^2 + c$ and let $T_c^n$ be its
$n$-fold iterate. The filled Julia set $K_c$ is the set of $z \in \mathbb{C}$ whose orbit under
$T_c$ is bounded: there is a real $M$ such that $|T_c^n(z)| \le M$ for every $n \ge 0$. -/
def FilledJulia (c : ℂ) : Set ℂ :=
  { z : ℂ | ∃ M : ℝ, ∀ n : ℕ, ‖(Tc c)^[n] z‖ ≤ M }

/- **Fatou–Julia dichotomy.** For the quadratic family, `c ∈ M` implies
the filled Julia set `K_c` is connected; `c ∉ M` implies `K_c` is
homeomorphic to the Cantor space `ℕ → Bool`. -/
/-- **Fatou–Julia dichotomy for quadratic polynomials.** For $c \in \mathbb{C}$, let $K_c$ be the
filled Julia set of $T_c(z) = z^2 + c$ and let $M$ be the Mandelbrot set. If $c \in M$, then $K_c$
is nonempty and connected. If $c \notin M$, then $K_c$ is homeomorphic to the Cantor space
$\{0, 1\}^{\mathbb{N}}$ of binary sequences with the product topology.

Source: P. Fatou, *Sur les équations fonctionnelles*, Bull. Soc. Math. France 47 (1919), 161-271; 48 (1920), 33-94, 208-314. G. Julia, *Mémoire sur l'itération des fonctions rationnelles*, J. Math. Pures Appl. 1 (1918), 47-245. Modern statement: A. Douady and J. H. Hubbard, *Étude dynamique des polynômes complexes I, II*, Publ. Math. Orsay 84-02, 85-04. Listed as §62 (additional statement 1) in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `fatou_julia_dichotomy`. -/
public theorem_wanted julia_cantor_dichotomy (c : ℂ) :
    (c ∈ Mandelbrot → IsConnected (FilledJulia c)) ∧
    (c ∉ Mandelbrot → Nonempty ((FilledJulia c) ≃ₜ (ℕ → Bool)))

end FatouJuliaProblem
end ComplexAnalysis

end MathlibExt.Analysis.FatouJuliaWanted
