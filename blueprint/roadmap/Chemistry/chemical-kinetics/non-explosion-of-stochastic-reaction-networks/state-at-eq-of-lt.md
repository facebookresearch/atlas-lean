# For $0 \le s < T_m$, later jumps do not change the state at time $s$

Let $S$ be a set, $q : S \to \mathbb{R}$, $x \in S$ and $\omega$ a step sequence, with
[jump times](jump-time.md) $T_k = T_k(x, \omega)$, and let $X^{(n)}_s = X^{(n)}_s(x, \omega)$ be the
[state at time $s$ of the chain stopped after $n$ jumps](state-at.md). If $m \le n$ and
$0 \le s < T_m$, then

$$X^{(n)}_s = X^{(m)}_s:$$

once $s$ lies before the $m$-th jump time, allowing more than $m$ jumps does not change the state at
time $s$. No sign condition on $q$ or on the clocks is needed.
