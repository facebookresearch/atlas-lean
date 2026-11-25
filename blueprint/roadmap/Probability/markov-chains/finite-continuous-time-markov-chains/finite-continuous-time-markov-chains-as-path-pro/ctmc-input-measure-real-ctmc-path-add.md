# Restart law at a fixed time

Let $Q$ be a [rate matrix](../rate-matrices-of-finite-continuous-time-markov-c/is-rate-matrix.md) on a
finite set $S$, $\mathbb P$ the [law of the step sequence](ctmc-input-measure.md), $i, k \in S$,
$s \ge 0$, and $B$ a measurable set of paths $[0, \infty) \to S$. Then, with $X(i, \cdot)$ the
[path](ctmc-path.md) started at $i$,

$$\mathbb P\bigl(X_s(i, \cdot) = k,\ (X_{s+u}(i, \cdot))_{u \ge 0} \in B\bigr) = e^{sQ}(i, k)\; \mathbb P\bigl((X_u(k, \cdot))_{u \ge 0} \in B\bigr) .$$

This concerns only events of $X_s$ and of the path after $s$; it is weaker than the Markov property
with respect to the natural filtration, whose events of the path before $s$ it does not cover.

## Sources

- J. R. Norris, *Markov Chains*, Cambridge Series in Statistical and Probabilistic Mathematics 2, Cambridge University Press, 1997, Section 2.8 (compare the Markov property).
