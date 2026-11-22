/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Convergence of the independence ratio of random regular graphs (Abért, Question 18)

M. Abért, Some questions, Question 18 (Bollobás): let `G_n` be a random `d`-regular graph on `n`
points. Is there a limit of the independence ratio of `G_n`? It is known that for every `n` it is
very concentrated, so maybe the value it is concentrated around changes with `n`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Combinatorics.RandomRegularIndependenceRatioAMR11Problem0018Wanted

/-!
Source: M. Abért, Some questions (2010), Question 18 (B. Bollobás),
https://www.renyi.hu/~abert/questions.pdf. UnsolvedMath record UM-01200018 (`AMR-011-0018`), dataset
ulamai/UnsolvedMath v1.8.0.

The random `d`-regular graph on `n` vertices is uniform over the `d`-regular simple graphs on `Fin
n` (Bayati–Gamarnik–Tetali's `G(N, r)`); the independence ratio is `α(G)/n` with `α =
SimpleGraph.indepNum`; 'a limit' is convergence in probability to a constant, as in the record and
the resolving paper (`w.h.p.`). The deviation probability is `0` for the `n` with no `d`-regular
graph (`n d` odd or `n ≤ d`), so the limit is effectively taken over the `n` where the model exists,
as in the paper. `d ≥ 1`: Abért's question fixes no range of `d`, and Bayati–Gamarnik–Tetali's
Theorem 3 covers every `r ∈ ℤ₊`.
-/

open Filter Topology

open scoped Classical in
/-- The `d`-regular simple graphs on the vertex set `Fin n`: the support of the uniformly random
`d`-regular graph on `n` vertices (empty when `n d` is odd or `n ≤ d`). -/
noncomputable def regularGraphs (n d : ℕ) : Finset (SimpleGraph (Fin n)) :=
  Finset.univ.filter fun G => G.IsRegularOfDegree d

open scoped Classical in
/-- The probability that the independence ratio `α(G) / n` of the uniformly random `d`-regular
graph `G` on `n` vertices differs from `c` by more than `ε` (`0` when there is no such graph). -/
noncomputable def ratioDeviationProb (n d : ℕ) (c ε : ℝ) : ℝ :=
  ((regularGraphs n d).filter fun G => ε < |(G.indepNum : ℝ) / n - c|).card /
    (regularGraphs n d).card

/-- Bollobás's question (Abért, Question 18): for each `d ≥ 1`, the independence ratio of the
uniformly random `d`-regular graph on `n` vertices converges in probability to a constant as
`n → ∞`. -/
def independenceRatioConverges : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ c : ℝ, ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n : ℕ => ratioDeviationProb n d c ε) atTop (𝓝 0)

/--
Resolved true: Bayati, Gamarnik and Tetali proved that for each `d ≥ 1` the normalized size of a
largest independent set of the uniformly random `d`-regular graph converges in probability (w.h.p.)
to a constant. Source: M. Abért, Some questions (2010), Question 18 (B. Bollobás),
https://www.renyi.hu/~abert/questions.pdf; resolution: M. Bayati, D. Gamarnik and P. Tetali,
Combinatorial approach to the interpolation method and scaling limits in sparse random graphs, Ann.
Probab. 41 (2013), no. 3, 1803-1826, DOI 10.1214/12-AOP816, arXiv:0912.2444, Theorem 3: for every r
and every model of §2 (independent sets included, H(G) = size of a largest independent set) there is
H(r) with lim N^{-1} H(G(N, r)) = H(r) w.h.p. (N along Nr even); §1: G(N, r) is chosen uniformly
from the r-regular graphs on N nodes and the result resolves the question whether |I_N|/N converges
in probability; §2: results proved w.h.p. for the configuration model carry over to simple regular
graphs, https://arxiv.org/abs/0912.2444.
-/
public theorem_wanted independenceRatioConverges_holds : independenceRatioConverges

end MathlibExt.Combinatorics.RandomRegularIndependenceRatioAMR11Problem0018Wanted
