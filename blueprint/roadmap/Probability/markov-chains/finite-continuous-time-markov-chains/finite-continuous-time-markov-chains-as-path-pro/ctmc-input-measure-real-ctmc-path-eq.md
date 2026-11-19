# Transition probabilities of the constructed chain

Let $Q$ be a [rate matrix](../rate-matrices-of-finite-continuous-time-markov-c/is-rate-matrix.md) on a
finite set $S$ and $\mathbb P$ the [law of the step sequence](ctmc-input-measure.md). The chain built
from the jump chain and the holding times has transition function $e^{tQ}$: for all $i, j \in S$
and $t \ge 0$,

$$\mathbb P\bigl(X_t(i, \cdot) = j\bigr) = e^{tQ}(i, j),$$

where $X(i, \cdot)$ is the [path](ctmc-path.md) started at $i$.

## Sources

- J. R. Norris, *Markov Chains*, Cambridge Series in Statistical and Probabilistic Mathematics 2, Cambridge University Press, 1997, Section 2.8, Theorem 2.8.2.
