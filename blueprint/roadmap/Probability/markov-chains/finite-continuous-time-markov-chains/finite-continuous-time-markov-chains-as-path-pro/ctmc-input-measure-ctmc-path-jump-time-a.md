# Strong Markov property at jump times

Let $Q$ be a [rate matrix](../rate-matrices-of-finite-continuous-time-markov-c/is-rate-matrix.md) on a
finite set $S$, $\mathbb P$ the [law of the step sequence](ctmc-input-measure.md), $i \in S$ and
$n \in \mathbb{N}$. Let $A$ be a measurable set of histories $(\omega_0, \dots, \omega_{n-1})$ of
the first $n$ steps such that the [jump time](ctmc-jump-time.md) $T_n(i, \omega)$ is finite whenever
the history of $\omega$ lies in $A$ (these histories determine $Y_0, \dots, Y_n$ and
$S_0, \dots, S_{n-1}$). Then for every state $k$ and every measurable set $B$ of paths
$[0, \infty) \to S$,

$$\mathbb P\bigl(\text{history} \in A,\ Y_n = k,\ (X_{T_n + s})_{s \ge 0} \in B\bigr) = \mathbb P\bigl(\text{history} \in A,\ Y_n = k\bigr)\, \mathbb P\bigl((X_s(k, \cdot))_{s \ge 0} \in B\bigr),$$

where $X = X(i, \cdot)$ is the [path](ctmc-path.md) started at $i$: given such a history and
$Y_n = k$, the path after $T_n$ is distributed as the chain started at $k$.

## Sources

- J. R. Norris, *Markov Chains*, Cambridge Series in Statistical and Probabilistic Mathematics 2, Cambridge University Press, 1997, Sections 2.6–2.7.
