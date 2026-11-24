/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.PiecewiseSyndetic

/-!
# Piecewise syndetic sets in `ℕ^t`

Statements from Tom C. Brown, *Piecewise Syndetic Sets in `N^t` and `N^X`*,
INTEGERS 24 (2024), Article A2.

Points of `ℕ^t` are functions `Fin t → ℕ`. A subcube of size `m^t` is a lattice
cube `∏ i, [a i, a i + m)` with side `m`. A set `C` is `d`-dense in a cube `M` when
every subcube of `M` of size `d^t` meets `C` (Lemma 1 of the paper). A set `C` is
piecewise syndetic when, for some fixed `d`, `C + [0, d]^t` contains arbitrarily
large subcubes (Proof 1 of Theorem 2 of the paper).

Here `ℕ` contains `0`, while the paper works in positive integers; translating by
the all-ones vector identifies the two settings and preserves all notions above.

Proved in `MathlibExt.Combinatorics.PiecewiseSyndetic`, which this module imports:
the definitions above, Lemma 1 (`exists_subcube_isDenseInCubes_colorClass`) and
Lemma 2 (`exists_cube_bound_isDenseInCubes`).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Piecewise syndeticity is partition regular.** Let $A \subseteq \mathbb{N}^t$ be piecewise
syndetic and let $A_1, \dots, A_r \subseteq \mathbb{N}^t$ with $A = A_1 \cup \dots \cup A_r$. Then
some $A_i$ is piecewise syndetic.

Source: Tom C. Brown, *Piecewise Syndetic Sets in `N^t` and `N^X`*, INTEGERS 24
(2024), Article A2, Theorem 1 (`integers-2024-A2-thm-1`). -/
public theorem_wanted IsPiecewiseSyndetic.exists_of_eq_iUnion {t r : ℕ}
    {A : Set (Fin t → ℕ)} (hA : IsPiecewiseSyndetic A) (B : Fin r → Set (Fin t → ℕ))
    (hAB : A = ⋃ i, B i) : ∃ i, IsPiecewiseSyndetic (B i)

/-- **Monochromatic sets that are large relative to their gap size.** Let $r, t \in \mathbb{N}$ with
$t \ge 1$, and let $f : \mathbb{N} \to \mathbb{N}$ be nondecreasing. There is $B \in \mathbb{N}$
such that for every coloring of $\mathbb{N}^t$ with $r$ colors there is a finite monochromatic set
$S \subseteq [1, B]^t$ with $|S| > f(\operatorname{gs}(S))$, where $\operatorname{gs}(S)$ is the gap
size of $S$ and $[1, B]^t$ is the set of points $x$ with $1 \le x_i \le B$ for every coordinate $i$.

The paper's "(a smallest)" is omitted: it follows from existence. Only the restriction of the
coloring to $[1, B]^t$ matters. The hypothesis $t \ge 1$ is the paper's; for $t = 0$ and $r \ge 1$
the statement fails when $f(1) \ge 1$, since the only point gives $|S| = 1 = \operatorname{gs}(S)$.
The paper's hypothesis $r \ge 1$ is dropped: for $r = 0$ there is no coloring and the statement
holds vacuously.

Source: Tom C. Brown, *Piecewise Syndetic Sets in `N^t` and `N^X`*, INTEGERS 24
(2024), Article A2, Theorem 2 (`integers-2024-A2-thm-2`). -/
public theorem_wanted exists_cube_bound_monochromatic_card_gt_gapSize (r t : ℕ) (ht : 1 ≤ t)
    (f : ℕ → ℕ) (hf : Monotone f) :
    ∃ B : ℕ, ∀ c : (Fin t → ℕ) → Fin r, ∃ j : Fin r, ∃ S : Finset (Fin t → ℕ),
      (S : Set (Fin t → ℕ)) ⊆ latticeCube (fun _ => 1) B ∧ (∀ x ∈ S, c x = j) ∧
        f (cubeGapSize (S : Set (Fin t → ℕ))) < S.card

end

end MetaMathlibExt
