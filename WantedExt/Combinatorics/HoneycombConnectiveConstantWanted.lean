/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Connective constant of the honeycomb lattice

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Combinatorics.HoneycombConnectiveConstant` — honeycomb_connective_constant (manifest `manifests/problems/honeycomb_connective_constant.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.HoneycombConnectiveConstantWanted` namespace. Mathematical
statements are unchanged. Source: H. Duminil-Copin and S. Smirnov, 'The connective constant of the honeycomb lattice equals sqrt(2 + sqrt 2)', Ann. of Math. 175 (2012), 1653-1665, https://doi.org/10.4007/annals.2012.175.3.14.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Combinatorics.HoneycombConnectiveConstantWanted
namespace Combinatorics.HoneycombConnectiveConstant

/-!
# The connective constant of the honeycomb lattice

Duminil-Copin and Smirnov proved Nienhuis's prediction that the connective
constant of the honeycomb (hexagonal) lattice is `sqrt (2 + sqrt 2)`.

The lattice is represented in bipartite integer coordinates. A vertex
`(x, y, false)` is adjacent to `(x, y, true)`, `(x - 1, y, true)`, and
`(x, y - 1, true)`; the reverse moves apply on the other side. Thus a
finite direction word determines a walk, and injectivity of its sequence
of visited vertices is exactly the self-avoiding condition.
-/

open Filter Topology

/-- **Vertices of the honeycomb lattice.** A vertex of the honeycomb lattice is a triple
$(x, y, s)$ with $x, y \in \mathbb{Z}$ and $s$ a boolean recording which of the two classes of
the bipartition the vertex belongs to. -/
structure HoneycombVertex where
  x : ℤ
  y : ℤ
  side : Bool
deriving DecidableEq

/-- **Steps in the honeycomb lattice.** For a vertex $v = (x, y, s)$ and a direction label
$d \in \{0, 1, 2\}$, the step from $v$ in direction $d$ is a vertex on the other side of the
bipartition. If $s$ is true, it is $(x, y, \mathrm{false})$, $(x + 1, y, \mathrm{false})$ or
$(x, y + 1, \mathrm{false})$ for $d = 0, 1, 2$ respectively. If $s$ is false, it is
$(x, y, \mathrm{true})$, $(x - 1, y, \mathrm{true})$ or $(x, y - 1, \mathrm{true})$ for
$d = 0, 1, 2$ respectively. -/
def step (v : HoneycombVertex) (direction : Fin 3) : HoneycombVertex :=
  if v.side then
    match direction.1 with
    | 0 => ⟨v.x, v.y, false⟩
    | 1 => ⟨v.x + 1, v.y, false⟩
    | _ => ⟨v.x, v.y + 1, false⟩
  else
    match direction.1 with
    | 0 => ⟨v.x, v.y, true⟩
    | 1 => ⟨v.x - 1, v.y, true⟩
    | _ => ⟨v.x, v.y - 1, true⟩

/-- **Steps are involutions.** For every vertex $v$ of the honeycomb lattice and every
direction label $d \in \{0, 1, 2\}$, taking the step in direction $d$ from $v$ and then the
step in direction $d$ again returns to $v$.

In particular, the coordinate model defines an undirected graph. -/
@[simp]
theorem step_step (v : HoneycombVertex) (direction : Fin 3) :
    step (step v direction) direction = v := by
  rcases v with ⟨x, y, side⟩
  fin_cases direction
  all_goals cases side
  all_goals simp [step]

/-- **Distinct labels give distinct neighbors.** For every vertex $v$ of the honeycomb
lattice, the steps from $v$ in the directions $0$, $1$ and $2$ are three distinct vertices. -/
theorem step_injective (v : HoneycombVertex) : Function.Injective (step v) := by
  intro direction₁ direction₂ h
  rcases v with ⟨x, y, side⟩
  cases side
  all_goals fin_cases direction₁
  all_goals fin_cases direction₂
  all_goals simp [step] at h ⊢
  all_goals omega

/-- **Origin of the honeycomb lattice.** The origin is the vertex $(0, 0, \mathrm{false})$.

The honeycomb lattice is vertex-transitive, so the choice of base vertex is arbitrary. -/
def origin : HoneycombVertex := ⟨0, 0, false⟩

/-- **Endpoint of a direction word.** For a finite word $d_1 d_2 \cdots d_k$ of direction labels
in $\{0, 1, 2\}$, its endpoint is the vertex reached from the origin by taking the step in
direction $d_1$, then the step in direction $d_2$, and so on through $d_k$. The endpoint of the
empty word is the origin. -/
def endpoint (directions : List (Fin 3)) : HoneycombVertex :=
  directions.foldl step origin

/-- **Vertices along a direction word.** For a word $(d_1, \ldots, d_n)$ of direction labels in
$\{0, 1, 2\}$ and an integer $0 \le i \le n$, the $i$-th vertex of the word is the endpoint of
its prefix $(d_1, \ldots, d_i)$, the vertex reached from the origin after the first $i$ steps. -/
def vertexAt {n : ℕ} (directions : Fin n → Fin 3) (i : Fin (n + 1)) :
    HoneycombVertex :=
  endpoint ((List.ofFn directions).take i.1)

/-- **Vertices visited by a direction word.** For a word $(d_1, \ldots, d_n)$ of direction
labels in $\{0, 1, 2\}$, the set of visited vertices is the finite set of its $i$-th vertices for
$0 \le i \le n$; it contains the origin (for $i = 0$) and the endpoint of the word. -/
def visitedVertices {n : ℕ} (directions : Fin n → Fin 3) : Finset HoneycombVertex :=
  Finset.univ.image (vertexAt directions)

/-- **Self-avoiding direction words.** A word $(d_1, \ldots, d_n)$ of direction labels in
$\{0, 1, 2\}$ is self-avoiding when its set of visited vertices has exactly $n + 1$ elements,
that is, when its $n + 1$ vertices, the $i$-th vertices for $0 \le i \le n$, are pairwise
distinct. -/
def IsSelfAvoiding {n : ℕ} (directions : Fin n → Fin 3) : Prop :=
  (visitedVertices directions).card = n + 1

instance {n : ℕ} (directions : Fin n → Fin 3) : Decidable (IsSelfAvoiding directions) := by
  unfold IsSelfAvoiding
  infer_instance

/-- **Number of self-avoiding walks on the honeycomb lattice.** For a natural number $n$, this
is the number of self-avoiding walks with $n$ steps on the honeycomb lattice starting at the
origin. -/
def walkCount (n : ℕ) : ℕ :=
  (Finset.univ.filter fun directions : Fin n → Fin 3 =>
    IsSelfAvoiding directions).card

/-- **Three-step self-avoiding walks on the honeycomb lattice.** There are exactly $12$
self-avoiding walks with $3$ steps on the honeycomb lattice starting at a fixed vertex. -/
theorem walkCount_three : walkCount 3 = 12 := by
  decide

/-- **Six-step self-avoiding walks on the honeycomb lattice.** There are exactly $90$
self-avoiding walks with $6$ steps on the honeycomb lattice starting at a fixed vertex.

Six is the first length at which a walk can close a hexagon. -/
theorem walkCount_six : walkCount 6 = 90 := by
  decide +kernel

/- **Duminil-Copin-Smirnov honeycomb connective-constant theorem.** The
exponential growth rate of the number of self-avoiding walks is
`sqrt (2 + sqrt 2)`. -/
/-- **The connective constant of the honeycomb lattice.** Let $c_n$ be the number of $n$-step
self-avoiding walks on the honeycomb lattice starting at the origin. Then
$c_n^{1/n} \to \sqrt{2 + \sqrt{2}}$ as $n \to \infty$.

Source: H. Duminil-Copin and S. Smirnov, 'The connective constant of the honeycomb lattice equals sqrt(2 + sqrt 2)', Ann. of Math. 175 (2012), 1653-1665, https://doi.org/10.4007/annals.2012.175.3.14. Via leanprover/lean-eval@38361be, problem `honeycomb_connective_constant`. -/
public theorem_wanted honeycomb_connective_constant :
    Tendsto
      (fun n ↦ (walkCount n : ℝ) ^ (1 / n : ℝ))
      atTop
      (nhds (Real.sqrt (2 + Real.sqrt 2)))

end Combinatorics.HoneycombConnectiveConstant

end MathlibExt.Combinatorics.HoneycombConnectiveConstantWanted
