# A completed cycle's reward is the return reward of the shifted steps

Let $S$ be a set, $q, g : S \to \mathbb{R}$, $x_0, x \in S$, $k \in \mathbb{N}$ and $\omega$ a step
sequence, and let $V_j = V_j(x_0, x, \omega)$ be the [$j$-th visit](visit.md) to $x_0$, counting
from $0$, of the jump chain started at $x$. Suppose that $V_k = n$ for a natural number $n$ and that
$V_{k+1} < \infty$. Then the [$k$-th cycle sum](cycle-sum.md) equals the
[return reward](return-reward.md) of the [steps after $V_k$](shift-at.md),
$\theta_{V_k} \omega = \theta_n \omega$:

$$C_k(\omega) = \rho(\theta_n \omega) .$$

So the $k$-th regeneration cycle is the first excursion from $x_0$ of the chain restarted at $x_0$
with the shifted steps. The finiteness of $V_{k+1}$ is needed: when $V_k = n$ and
$V_{k+1} = \infty$, the left side is $-R_n(x, \omega)$ and the right side is $0$.
