# The jump chain up to step $n$ depends only on the first $n$ steps

Let $S$ be a set, $x \in S$ and $n \in \mathbb{N}$, and let $\omega, \omega'$ be step sequences,
$\omega_i = (\xi_i, E_i)$ with $\xi_i : S \to S$ and $E_i \in \mathbb{R}$, that agree in their
first $n$ steps: $\omega'_i = \omega_i$ for every $i < n$. Then their
[jump chains](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
started at $x$, given by $Y_0 = x$ and $Y_{j+1} = \xi_j(Y_j)$, agree up to step $n$:

$$Y_j(x, \omega) = Y_j(x, \omega') \qquad \text{for every } j \le n .$$
