# For $k < n$, the stopped chain is at $Y_k$ between $T_k$ and $T_{k+1}$

Let $S$ be a set, $q : S \to \mathbb{R}$ with $q(x) > 0$ for every $x \in S$, $x \in S$ and
$\omega = ((\xi_j, E_j))_{j \in \mathbb{N}}$ a step sequence with $E_j \ge 0$ for every $j$, with
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
$Y_k = Y_k(x, \omega)$ and [jump times](jump-time.md) $T_k = T_k(x, \omega)$. If $k < n$ and
$T_k \le s < T_{k+1}$, then the
[state at time $s$ of the chain stopped after $n$ jumps](state-at.md) is

$$X^{(n)}_s(x, \omega) = Y_k .$$
