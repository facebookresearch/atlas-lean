# Finite-dimensional distributions

Let $Q$ be a [rate matrix](../rate-matrices-of-finite-continuous-time-markov-c/is-rate-matrix.md) on a
finite set $S$, $\mathbb P$ the [law of the step sequence](ctmc-input-measure.md) and $i \in S$. Let
$s_0, \dots, s_{n-1} \ge 0$ be increments, $t_k = s_0 + \dots + s_k$, and $j_0, \dots, j_{n-1} \in S$.
Then, with $X(i, \cdot)$ the [path](ctmc-path.md) started at $i$ and $j_{-1} = i$,

$$\mathbb P\bigl(X_{t_k}(i, \cdot) = j_k \text{ for } k = 0, \dots, n-1\bigr) = \prod_{k=0}^{n-1} e^{s_k Q}(j_{k-1}, j_k) .$$

## Sources

- J. R. Norris, *Markov Chains*, Cambridge Series in Statistical and Probabilistic Mathematics 2, Cambridge University Press, 1997, Section 2.8, Theorem 2.8.2(c).
