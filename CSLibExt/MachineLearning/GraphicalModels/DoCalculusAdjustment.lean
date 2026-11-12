/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.CausalAdjustment

/-!
# The back-door and front-door formulas as do-calculus derivations

This file is documentation: it records how the two adjustment formulas proved in
`CSLibExt/MachineLearning/GraphicalModels/CausalAdjustment.lean` are obtained by Pearl's
do-calculus, and it adds no declarations. The do-calculus itself is not formalized in Atlas;
the adjustment theorems are proved directly from the truncated factorization and the global
Markov property.

## Notation

`G` is the graph of a causal Bayesian network (`BayesNet`), `G_{\bar X}` the graph with the arrows
into `X` removed, `G_{\underline X}` the graph with the arrows out of `X` removed, and
`(A ⫫ B | C)_H` d-separation in the graph `H` (`BayesNet.DSeparated`). The three rules (Pearl
1995; Pearl 2009, Theorem 3.4.1), for disjoint node sets `X, Y, Z, W`:

* Rule 1 (insert or delete an observation): `P(y | do(x), z, w) = P(y | do(x), w)` if
  `(Y ⫫ Z | X, W)` holds in `G_{\bar X}`.
* Rule 2 (exchange an action and an observation): `P(y | do(x), do(z), w) = P(y | do(x), z, w)` if
  `(Y ⫫ Z | X, W)` holds in `G_{\bar X \underline Z}`.
* Rule 3 (insert or delete an action): `P(y | do(x), do(z), w) = P(y | do(x), w)` if
  `(Y ⫫ Z | X, W)` holds in `G_{\bar X \bar{Z(W)}}`, where `Z(W)` is the set of nodes of `Z` that
  are not ancestors of `W` in `G_{\bar X}`.

## Back-door formula

Let `Z` satisfy the hypotheses of `BayesNet.backdoor_adjustment` for the effect of node `k`
(treatment `X`) on a different node `y` (outcome `Y`, `hky : k ≠ y`) not in `Z` (`hyZ`): no node
of `Z` is a descendant of `X` (`hdesc`), and `Z` blocks every path from `X` to `Y` that begins
with an arrow into `X` (`hblock`). Then

1. `P(y | do(x)) = ∑_z P(z | do(x)) P(y | do(x), z)` (the law of total probability in the
   intervened network `b.intervene k a`);
2. `P(z | do(x)) = P(z)` by rule 3 with an empty `W`: `(Z ⫫ X)` holds in `G_{\bar X}` because,
   with the arrows into `X` removed, every path between `X` and `Z` leaves `X` along an arrow out
   of `X` and must meet a collider before reaching `Z`, none of whose descendants is
   conditioned on (this is where `hdesc` is used; in Atlas it is
   `BayesNet.marginal_intervene_of_not_isDescendant`);
3. `P(y | do(x), z) = P(y | x, z)` by rule 2 with `W = Z`: `(Y ⫫ X | Z)` holds in
   `G_{\underline X}`, since the paths from `X` to `Y` that survive deleting the arrows out of `X`
   are exactly the back-door paths, all blocked by `Z` (`hblock`);

so `P(y | do(x)) = ∑_z P(z) P(y | x, z)`, the conclusion of `BayesNet.backdoor_adjustment`
(whose positivity hypothesis `hpos` makes the conditional probabilities in step 3 well defined).
A step-by-step numerical instance of the three steps on one network is in
`CSLibExtTest/MachineLearning/GraphicalModels/DoCalculusAdjustmentTests.lean`.

## Front-door formula

Let `M` satisfy the hypotheses of `BayesNet.frontdoor_adjustment` for the effect of `X` (node
`k`) on a different node `Y` (node `y`, `hky : k ≠ y`), with neither `X` nor `Y` in `M` (`hkM`,
`hyM`): `M` intercepts every directed path from `X` to `Y` (`hdir`), every path
from `X` to `M` beginning with an arrow into `X` is blocked by `∅` (`hkm`), and every path from
`M` to `Y` beginning with an arrow into `M` is blocked by `{X}` (`hmy`). Then

1. `P(y | do(x)) = ∑_m P(m | do(x)) P(y | do(x), m)` (total probability);
2. `P(m | do(x)) = P(m | x)` by rule 2: `(M ⫫ X)` holds in `G_{\underline X}` because every
   path from `X` to `M` that does not leave `X` along an arrow out of `X` is a back-door path,
   blocked by `∅` (`hkm`);
3. `P(y | do(x), m) = P(y | do(x), do(m))` by rule 2: `(Y ⫫ M | X)` holds in
   `G_{\bar X \underline M}` (the back-door paths from `M` to `Y` are blocked by `{X}`, `hmy`);
4. `P(y | do(x), do(m)) = P(y | do(m))` by rule 3: `(Y ⫫ X | M)` holds in `G_{\bar X \bar M}`,
   because every directed path from `X` to `Y` passes through `M` (`hdir`);
5. `P(y | do(m)) = ∑_{x'} P(y | x', m) P(x')` by the back-door formula with adjustment set
   `{X}`, which blocks the back-door paths from `M` to `Y` (`hmy`);

and combining, `P(y | do(x)) = ∑_m P(m | x) ∑_{x'} P(y | x', m) P(x')`, the conclusion of
`BayesNet.frontdoor_adjustment` (with positivity `hpos`). A non-vacuous instance of the
front-door hypotheses (the network `U → X → M → Y`, `U → Y`) is in
`CSLibExtTest/MachineLearning/GraphicalModels/CausalAdjustmentTests.lean`.

## References

* J. Pearl, *Causal diagrams for empirical research*, Biometrika 82(4) (1995), 669–688.
* J. Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed., Cambridge University Press
  (2009), §3.3–3.4.
-/
