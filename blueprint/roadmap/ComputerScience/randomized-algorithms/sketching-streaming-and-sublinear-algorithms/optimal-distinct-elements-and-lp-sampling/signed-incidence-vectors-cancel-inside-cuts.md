# Signed vertex-incidence vectors sum to the indicator of a cut

Let $G = (V, E)$ be a simple graph with $V = \{1, \dots, n\}$. For $v \in V$ define $a_v \in \{-1, 0, 1\}^{\binom{V}{2}}$ by setting, for each pair $\{i, j\}$ with $i < j$,

$$
a_v[\{i,j\}] = \begin{cases} +1 & \text{if } \{i,j\} \in E \text{ and } v = i,\\ -1 & \text{if } \{i,j\} \in E \text{ and } v = j,\\ 0 & \text{otherwise.}\end{cases}
$$

Then for every $S \subseteq V$ the support of $\sum_{v \in S} a_v$ is exactly the set $\delta(S)$ of edges with one endpoint in $S$ and one in $V \setminus S$, each entry being $\pm 1$. Each $a_v$ is a linear function of the edge-indicator vector of $G$, so it can be maintained under edge insertions and deletions, and since sketches are linear, a sketch of $\sum_{v \in S} a_v$ is the sum of the sketches of the $a_v$.

## Proof sketch

An edge $\{i, j\}$ with both endpoints in $S$ contributes $+1$ through $a_i$ and $-1$ through $a_j$, which cancel; an edge with no endpoint in $S$ contributes nothing. An edge with exactly one endpoint in $S$ contributes exactly one nonzero entry $\pm 1$. Linearity of the sketches in the input vector gives the last claim.

## Depends on

- [Turnstile streams, support size and linear sketches of a frequency vector](turnstile-streams-and-support-size.md)
- [Edges of a cut](../../../approximation-algorithms/primal-dual-method-for-constrained-forests/cut-edges.md)

## Proof depends on

- [The one-pass sketch is linear in the frequencies](../../frequency-moments-of-data-streams/sketch-eq-sum-count-mul.md)

## Sources

- Kook Jin Ahn, Sudipto Guha, Andrew McGregor, "Analyzing Graph Structure via Linear Measurements", SODA (2012).
