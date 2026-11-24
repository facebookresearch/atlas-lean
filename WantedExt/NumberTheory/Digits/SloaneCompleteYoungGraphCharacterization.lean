/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.GCD.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Complete Young graphs.** For natural numbers $g$, $k$ and $m$, the Young graph $Y(g, k)$ of
the $k$-reverse multiples in base $g$ is complete on $m$ nodes: the nodes other than its
distinguished starting node form the complete directed graph on $m$ nodes, so $Y(g, k)$ has
$m + 1$ nodes in all; the node $[0, 0]$ is one of these $m$ nodes, and the starting node has an
edge to every node except $[0, 0]$.

Source: L. H. Kendrick, "Young Graphs: 1089 et al.", Journal of
Integer Sequences 18 (2015), stable source URL
`https://cs.uwaterloo.ca/journals/JIS/VOL18/Kendrick/ken1.tex`
(frozen source SHA-256
`28568ffc708329fe2de23639f32fd9f7a24a772a043deb40f9098c0f82e465c2`,
stable source ID `jis_grounded_3014355e4f55ef0bb856bf6f`).
Definition at lines 458-460 (quotation span SHA-256
`bac9fd74d3d31197005bee521a9d8070be41ed00fac48e0db94c1523bfea2625`):
in the source's `K_m` convention, the nodes other than the distinguished
starting node form the complete directed graph on `m` nodes, so the Young
graph has `m + 1` total nodes including that distinguished start; `[0, 0]`
is one of the `m` non-start nodes, and the starting node connects to every
node except `[0, 0]`. -/
public def_wanted IsCompleteYoungGraph (g k m : Nat) : Prop

/-- **Characterization of complete Young graphs.** Let $g$, $k$ and $m$ be natural numbers with
$2 \le k < g$ and $m \ge 2$. Then the Young graph $Y(g, k)$ is complete on $m$ nodes if and only
if

$$\left\lfloor \frac{\gcd(g - k,\, k^2 - 1)}{k + 1} \right\rfloor = m - 1.$$

Source: Corollary at lines 574-576
(quotation span SHA-256
`a7c50f9bea3cb4b958aecdbee7b56879d930178eae594729d8e54e36b7767395`)
of L. H. Kendrick, "Young Graphs: 1089 et al.", Journal of Integer
Sequences 18 (2015), stable source URL
`https://cs.uwaterloo.ca/journals/JIS/VOL18/Kendrick/ken1.tex`
(frozen source SHA-256
`28568ffc708329fe2de23639f32fd9f7a24a772a043deb40f9098c0f82e465c2`,
stable source ID `jis_grounded_3014355e4f55ef0bb856bf6f`).
In the source's `K_m`
convention, the nodes other than the distinguished starting node form the
complete directed graph on `m` nodes, so the Young graph has `m + 1` total
nodes including that distinguished start; `[0, 0]` is one of the `m`
non-start nodes. Natural-number division represents the source floor
because all quantities are nonnegative and the denominator is positive.
The hypothesis is `2 ≤ m`, not `1 ≤ m`. The corollary rests on Theorem
`thm:completegraph`, whose proof starts "Since $s_1$ exists", so it needs
`m - 1 ≥ 1`. For `m = 1` the class `K_1` contains no Young graph: every Young
graph is connected and contains `[0, 0]`, so the starting node has an edge to
some node other than `[0, 0]` (proof of Theorem `thm:0iso`), while a graph in
`K_1` has none. With `1 ≤ m`, `(g, k) = (10, 9)` and `m = 1` give
`gcd(1, 80) / 10 = 0 = m - 1`, but `Y(10, 9)` is the 1089 graph, not in `K_1`. -/
public theorem_wanted sloane_complete_young_graph_characterization
    (g k m : Nat) (hk : 2 ≤ k) (hkg : k < g) (hm : 2 ≤ m) :
    ❰IsCompleteYoungGraph❱ g k m ↔
      Nat.gcd (g - k) (k ^ 2 - 1) / (k + 1) = m - 1

end

end MetaMathlibExt
