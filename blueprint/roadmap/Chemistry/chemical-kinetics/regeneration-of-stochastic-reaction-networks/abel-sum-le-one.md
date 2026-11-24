# For $q > 0$, $E_k \ge 0$, $g \le 1$, the Abel functional is at most 1

Let $\sigma$ be a set, $q : \sigma \to \mathbb{R}$ positive rates ($q(y) > 0$ for every $y$),
$g : \sigma \to \mathbb{R}$ with $g(y) \le 1$ for every $y$, $a \ge 0$, $x \in \sigma$, and
$\omega = ((\xi_k, E_k))_{k \ge 0}$ a sequence of steps (maps $\xi_k : \sigma \to \sigma$ and real
clocks $E_k$) with nonnegative clocks, $E_k \ge 0$ for every $k$. Then the
[Abel functional](abel-sum.md) satisfies

$$A_a g(x, \omega) \le 1 .$$

No lower bound on $g$ is needed: the Abel functional uses $g^+ = \max(g, 0)$, so negative values
count as $0$. The holding times $H_k = E_k / q(Y_k)$ are nonnegative, so the weights
$e^{-a T_k} (1 - e^{-a H_k}) = e^{-a T_k} - e^{-a T_{k+1}}$ are nonnegative and telescope: the sum
of the first $n$ terms is at most $1 - e^{-a T_n} \le 1$.
