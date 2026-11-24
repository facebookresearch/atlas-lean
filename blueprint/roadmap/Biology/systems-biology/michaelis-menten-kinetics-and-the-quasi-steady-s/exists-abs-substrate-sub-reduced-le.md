# One constant gives the first-order substrate bound for every e₀ > 0

Let $k_1 > 0$, $k_b \ge 0$, $k_2 > 0$ and $s_0 > 0$, with $K_M = (k_b + k_2)/k_1$ the
[Michaelis constant](michaelis-constant.md), and let $\bar S : \mathbb{R} \to \mathbb{R}$ be
differentiable at every $\tau \ge 0$ with $\bar S'(\tau) = -k_2 \bar S(\tau)/(K_M + \bar S(\tau))$
there, a solution of the reduced (Michaelis–Menten) equation, with $\bar S(0) = s_0$. Let $T$ be
real. Then there is a constant $C$ such that for every $e_0 > 0$, every [solution](is-solution.md)
$(s, c, e, p)$ of the Michaelis–Menten mass-action system with $s(0) = s_0$, $c(0) = 0$ and
$e(0) = e_0$, and every slow time $\tau \in [0, T]$,

$$|s(\tau/e_0) - \bar S(\tau)| \le C e_0.$$

The proof takes for $C$ the [constant of the substrate estimate](substrate-error-const.md) $C(T)$.
The [rigorous QSSA](abs-sub-reduced-le.md) is the special case with $T > 0$ and $e_0 \le 1$.
