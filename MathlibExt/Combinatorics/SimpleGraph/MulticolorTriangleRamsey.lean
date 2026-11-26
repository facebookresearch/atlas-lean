/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Definition adapted from OpenAI, Ten Advances in Mathematics and Theoretical
Computer Science, ComparatorChallenges/I_MulticolorTriangleRamsey.lean (Apache-2.0).
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling

@[expose] public section

set_option autoImplicit false

namespace SimpleGraph

/--
**Multicolor triangle Ramsey number.** For a natural number $k$, $R_k(3)$ is the
least natural number $N$ such that every edge coloring of the complete graph on
$N$ vertices with colors in $\{0,\ldots,k-1\}$ has a monochromatic triangle.
Unused colors are permitted. This is expressed as the infimum in $\mathbb N$
of the set of such $N$. For the empty palette ($k=0$) the value is $2$:
a labeling exists on the edgeless complete graphs on zero and one vertex,
but no labeling exists on the complete graph on two vertices. The universal
condition is therefore vacuous at order two.

Source: R. E. Greenwood and A. M. Gleason,
[*Combinatorial Relations and Chromatic Graphs*](https://doi.org/10.4153/CJM-1955-001-4),
Canadian Journal of Mathematics 7 (1955), 1–7, §1 and §2, Corollaries 1–3.
Taking each target clique size to be three specializes their threshold;
the bounds in §2 give finiteness for two or more colors.

Source: OpenAI, [*Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 9](https://cdn.openai.com/pdf/ten-proofs-oai.pdf),
[pinned definition](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/I_MulticolorTriangleRamsey.lean#L8-L16).
-/
noncomputable def multicolorTriangleRamseyNumber (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∀ C : TopEdgeLabeling (Fin n) (Fin k),
    ∃ color : Fin k, ¬ (C.labelGraph color).CliqueFree 3}

end SimpleGraph
