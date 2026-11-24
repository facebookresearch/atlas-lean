# Reward collected until the first return to the starting state

Let $S$ be a set, $q, g : S \to \mathbb{R}$, $x_0 \in S$ and $\omega$ a step sequence. Let $Y$ be
the jump chain started at $x_0$, $H_i = E_i / q(Y_i)$ its holding times (with $a / 0 = 0$), and
$V_1 = V_1(x_0, x_0, \omega)$ its first return to $x_0$ (the [visit](visit.md) after $V_0 = 0$).
The return reward is the [reward](reward.md) collected by $g$ up to that return:

$$\rho(\omega) = R_{V_1}(x_0, \omega) = \sum_{i < V_1} g(Y_i) H_i \quad \text{if } V_1 < \infty ,$$

and $\rho(\omega) = 0$ if the chain never returns, $V_1 = \infty$, because $\infty$ converts to the
natural number $0$. For $g = 1$ and a finite return it is the jump time $T_{V_1}$ at which the chain
returns to $x_0$.
