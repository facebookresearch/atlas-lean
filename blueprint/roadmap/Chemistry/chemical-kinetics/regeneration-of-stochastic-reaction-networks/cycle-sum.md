# Reward collected during the $k$-th regeneration cycle

Let $S$ be a set, $q, g : S \to \mathbb{R}$, $x_0, x \in S$, $k \in \mathbb{N}$ and $\omega$ a step
sequence. Let $V_j = V_j(x_0, x, \omega)$ be the [$j$-th visit](visit.md) to $x_0$, counting from
$0$, of the jump chain $Y$ started at $x$, and $R_m = R_m(x, \omega) = \sum_{i < m} g(Y_i)\, H_i$
its [reward](reward.md), with holding times $H_i = E_i / q(Y_i)$ (and $a / 0 = 0$). The $k$-th
cycle sum is

$$C_k(\omega) = R_{V_{k+1}} - R_{V_k} ,$$

where an infinite visit is replaced by the natural number $0$, so that $R_\infty$ means
$R_0 = 0$. Hence:

- if $V_{k+1} < \infty$, then $V_k < \infty$ and $C_k = \sum_{V_k \le i < V_{k+1}} g(Y_i)\, H_i$
  is the reward collected from the $k$-th to the $(k+1)$-st visit to $x_0$; for $g = 1$ it is the
  sum $\sum_{V_k \le i < V_{k+1}} H_i$ of the holding times of the cycle;
- if $V_k < \infty$ and $V_{k+1} = \infty$, then $C_k = -R_{V_k}$;
- if $V_k = \infty$, then $V_{k+1} = \infty$ and $C_k = 0$.
