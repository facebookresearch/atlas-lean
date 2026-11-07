# The second-order Hedge bound

Let $\eta > 0$, and let $\ell_1, \dots, \ell_T$ be loss
vectors in $\mathbb{R}^n$ for $n$ experts with $\ell_t(j) \ge 0$ for all $t$ and $j$. Run Hedge
with learning rate $\eta$ from unit weights, that is $w_1(j) = 1$ and
$w_{t+1}(j) = w_t(j) e^{-\eta \ell_t(j)}$, and let $x_t(j) = w_t(j) / \sum_k w_t(k)$ be the
distribution played in round $t$. Then for every expert $i$,

$$\sum_{t=1}^T \sum_j x_t(j) \ell_t(j) \le \sum_{t=1}^T \ell_t(i) +
\eta \sum_{t=1}^T \sum_j x_t(j) \ell_t(j)^2 + \frac{\log n}{\eta}.$$

This is Theorem 1.3 of Hazan, *Introduction to Online Convex Optimization*. Unlike the
first-order Hedge loss bound, the losses need not be at most $1$.
