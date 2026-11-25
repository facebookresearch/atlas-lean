# HMM filtering is POMDP belief update

Let an HMM have finite hidden states $S$, transition probabilities $T(s' \mid s)$, emission probabilities
$E(o \mid s)$ and initial distribution $\pi_0$, with the first observation emitted from the state after
the first transition. Encode it as a POMDP with a single action $\star$, $P(s' \mid s, \star) = T(s' \mid s)$
and $Z(o \mid s', \star) = E(o \mid s')$. For an observation sequence $o_1, \dots, o_t$ whose prefix
probability is positive, the normalized forward vector $\alpha_t / \sum_s \alpha_t(s)$, where
$\alpha_t(s') = E(o_t \mid s') \sum_s T(s' \mid s)\, \alpha_{t-1}(s)$ and $\alpha_0 = \pi_0$, equals the
belief obtained from $b_0 = \pi_0$ by $t$ successive belief updates $b_j = \tau(b_{j-1}, \star, o_j)$. If the
HMM instead emits an observation from the initial state, the encoding conditions $b_0$ on that first
observation.

## Depends on

- [Hidden Markov model](hidden-markov-models/hmm.md)
- [Belief update](../../heuristic-search-and-planning/partially-observable-planning/belief-update.md)

## Sources

- L. P. Kaelbling, M. L. Littman and A. R. Cassandra, *Planning and acting in partially observable stochastic domains*, Artificial Intelligence 101 (1998) 99–134, Section 3.3 (the state estimator). The identity follows by induction on $t$: the unnormalized forward recursion and the unnormalized belief update are the same map, and normalization commutes with it. <https://cs.brown.edu/courses/csci2951-k/papers/kaelbling98.pdf>
