# Optimal intervention for an SIR epidemic under a hospital capacity constraint

Consider the normalized SIR model with a time-dependent reduction of the contact rate,

$$
x' = -\gamma\,\sigma(t)\,x\,y, \qquad y' = \gamma\,\sigma(t)\,x\,y - \gamma\,y, \qquad t \in [0,T],
$$

where $x, y$ are the susceptible and infected fractions, $\gamma$ the recovery rate and $\sigma(t) \in [\sigma_s, \sigma_f]$ the controlled basic reproduction number, with $0 \le \sigma_s < \sigma_f$ and $\sigma_s < 1$ (strict intervention $\sigma_s$, no intervention $\sigma_f$). The intervention budget is the integral constraint $\int_0^T \sigma(t)\,dt \ge \sigma_s \tau + \sigma_f (T - \tau)$, i.e. at most a total time $\tau$ of strict measures, and the hospital constraint is $y(t) \le K$ for all $t$. The objective maximizes $x_\infty(x(T), y(T), \sigma_f)$, the limiting susceptible fraction when the epidemic runs free after $T$, i.e. it minimizes the final epidemic size.

**Theorem.** Let $\sigma^0$ be the (unique) optimal control without the hospital constraint and $(x^0, y^0)$ its trajectory. If $y^0(t) > K$ for some $t$, assume that every contact or exit point $s$ of the constrained extremal satisfies $x^*(s) > 1/\sigma_f$. Then the optimal control of the constrained problem is unique and has the form

$$
\sigma^*(t) = \begin{cases} \sigma_f, & 0 \le t \le t_1^*, \\ 1/x^*(t), & t_1^* < t \le t_2^*, \\ \sigma_s, & t_2^* < t \le t_2^* + \mu^*, \\ \sigma_f, & t_2^* + \mu^* < t \le T. \end{cases}
$$

If $y^0 \le K$ throughout, then $t_1^* = t_2^*$ and $\sigma^* = \sigma^0$ (no intervention, then one strict-intervention interval, then no intervention). Otherwise $t_1^*$ is the time at which the uncontrolled trajectory first reaches $y = K$, and the end $t_2^*$ of the boundary arc and the strict-intervention length $\mu^*$ are determined by the sign and size of an explicit switching function relative to $1/(\gamma K)$.

## Expansion

On the boundary arc the control $\sigma = 1/x$ makes $y' = \gamma y(\sigma x - 1) = 0$, holding the number of infected exactly at hospital capacity; it is admissible as long as $1/x \in [\sigma_s, \sigma_f]$, which the contact-point condition $x > 1/\sigma_f$ guarantees. Necessary conditions for state-constrained problems (Pontryagin with a measure multiplier) restrict optimal controls to bang–boundary–bang concatenations, and comparison of the remaining finitely many candidates gives uniqueness. The structure says: let the epidemic grow freely until hospitals fill, keep them exactly full, then spend the remaining strict-intervention budget in one block.

## Sources

- Rocío Balderrama, Mariana Inés Prieto, Constanza Sánchez de la Vega and Federico Vazquez, *Optimal control for a SIR model with limited hospitalised patients*, arXiv:2406.06770, Theorem 2.1 (Section 2) and Theorem 4.1 (Section 4). <https://doi.org/10.48550/arXiv.2406.06770> Published version: Mathematical Biosciences 378 (2024) 109317, <https://doi.org/10.1016/j.mbs.2024.109317>.
