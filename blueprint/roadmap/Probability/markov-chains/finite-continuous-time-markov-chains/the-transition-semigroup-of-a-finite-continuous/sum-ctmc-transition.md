# Rows of the transition function sum to one

Let $Q$ be a [rate matrix](../rate-matrices-of-finite-continuous-time-markov-c/is-rate-matrix.md)
indexed by a finite set $S$, with [transition function](ctmc-transition.md) $P(t) = e^{tQ}$. Then
for every real $t$ (also negative) and every $i \in S$, $\sum_{j \in S} P(t)(i, j) = 1$.
