# TV indistinguishability, replicability and approximate privacy are equivalent for PAC learning

A randomized algorithm $A(S; r)$ taking an i.i.d. sample $S$ from a distribution $D$ and internal randomness $r$ is **$\rho$-replicable** if $\Pr_{S, S' \sim D^n,\, r}[A(S; r) = A(S'; r)] \ge 1 - \rho$ for every $D$, where $S, S', r$ are independent and the same $r$ is used in both runs. Then:

- every $n$-sample $\rho$-replicable rule is $n$-sample $\rho$-TV indistinguishable;
- on a countable domain, every $n$-sample $\rho$-TV indistinguishable rule has an equivalent rule (with the same output distribution on every sample) that is $n$-sample $\tfrac{2\rho}{1+\rho}$-replicable, obtained by coupling the two output distributions through shared randomness;
- for $\gamma \in (0, 1/2)$, if a class $H \subseteq \{0,1\}^X$ is learnable by an $n$-sample $(\tfrac12 - \gamma, \tfrac12 - \gamma)$-accurate (error at most $\tfrac12 - \gamma$ with probability at least $\tfrac12 + \gamma$) $(0.1, 1/(n^2 \log n))$-differentially private learner, then for all $\alpha, \beta, \rho \in (0,1)$ it is learnable by an $(\alpha, \beta)$-accurate $\rho$-TV indistinguishable rule;
- on a countable domain, if $H$ is learnable by an $(\alpha, \beta)$-accurate $\rho$-TV indistinguishable learner with $\rho \in (0,1)$, $\alpha \in (0, \tfrac12)$ and $\beta \in \big(0, \tfrac{1-\rho}{1+\rho}\big)$, then for all $\alpha', \beta', \varepsilon, \delta \in (0,1)$ it is learnable by an $(\alpha + \alpha', \beta')$-accurate $(\varepsilon,\delta)$-differentially private learner.

Consequently, for every domain, $H$ is replicably learnable if and only if it is learnable by an approximately differentially private algorithm, if and only if $H$ has finite Littlestone dimension.

## Proof sketch

Replicability implies TV indistinguishability because for fixed samples the probability over shared randomness that two runs disagree upper bounds the total variation distance of the output distributions. The converse uses correlated sampling: given two distributions at total variation distance $t$, a shared random sequence of proposals with rejection sampling produces coupled outputs that agree with probability at least $(1-t)/(1+t)$. The privacy links go through global stability: a private learner forces finite Littlestone dimension, Littlestone classes have globally stable learners, and replicable heavy hitters turn global stability into replicability.

## Depends on

- [Replicable algorithms with shared randomness](../../../replicable-learning/replicable-algorithms-with-shared-seed.md)
- [Total-variation indistinguishable learning rules](tv-indistinguishable-learning-rule.md)
- [Private PAC learners and their sample complexity](../private-learning-and-littlestone-classes/private-pac-learner.md)
- [The Littlestone dimension is the optimal mistake bound](../../../../online-learning-and-boosting/the-littlestone-dimension-is-the-optimal-mistake-bound.md)

## Proof depends on

- [Replicable heavy hitters with domain-independent sample complexity](replicable-heavy-hitters.md)
- [Private learning requires log-star of the Littlestone dimension samples](../private-learning-and-littlestone-classes/private-learning-requires-log-star-littlestone.md)
- [Finite Littlestone dimension implies private learnability](../private-learning-and-littlestone-classes/littlestone-classes-are-privately-learnable.md)
- [Global stability and list replicability of learning rules](global-stability-and-list-replicability.md)

## Sources

- A. Kalavasis, A. Karbasi, S. Moran, G. Velegkas, "Statistical Indistinguishability of Learning Algorithms", ICML (2023), arXiv:2305.14311, Theorems 1–5 and Corollary 1.
- M. Bun, M. Gaboardi, M. Hopkins, R. Impagliazzo, R. Lei, T. Pitassi, S. Sivakumar, J. Sorrell, "Stability is Stable: Connections between Replicability, Privacy, and Adaptive Generalization", STOC (2023), arXiv:2303.12921.
