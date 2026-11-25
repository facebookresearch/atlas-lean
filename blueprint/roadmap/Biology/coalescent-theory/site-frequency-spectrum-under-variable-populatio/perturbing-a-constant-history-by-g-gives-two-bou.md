# Two bounded size histories with equal first-coalescence times

Let $g$ be [a bounded function, nonzero on a set of positive measure, whose Laplace transform vanishes at every $\binom{m}{2}$](bounded-function-nonzero-on-a-set-of-positive-me.md), and let $0 < \varepsilon \le 1/2$. Set $h_1 = 1$ and $h_2 = 1 + \varepsilon g$, so $1/2 \le h_2 \le 3/2$. For $i = 1, 2$ let $U_i(u) = \int_0^u h_i$, $R_i = U_i^{-1}$ and $\eta_i = h_i \circ R_i$. Then:

1. $R_i(s) = \int_0^s \eta_i^{-1}$, so $R_i$ is the cumulative coalescence intensity of the size history $\eta_i$;
2. the [first-coalescence times](first-coal-mean.md) are, by the substitution $u = R_i(s)$,

$$c_m(\eta_i) = \int_0^\infty e^{-\binom{m}{2} u}\, h_i(u)\, du,$$

so $c_m(\eta_1) = c_m(\eta_2)$ for every $m \ge 2$;

3. $\eta_1$ and $\eta_2$ take values in $[1/2, 3/2]$;
4. $\eta_1 \ne \eta_2$ on a set of positive measure, because $h_2 \ne 1$ on a set of positive measure and $R_2$ is bi-Lipschitz.

This gives the pair of histories of the [non-identifiability of general histories](exists-ne-ae-first-coal-mean-eq.md).

## Depends on

- [A bounded function whose Laplace transform vanishes at every binomial coefficient](bounded-function-nonzero-on-a-set-of-positive-me.md)
- [Expected time to the first coalescence](first-coal-mean.md)

## Expansion

1. The bounds $1/2 \le \eta_2 \le 3/2$.
2. The change of variables that turns $c_m$ into the Laplace transform of $h_i$ at $\binom{m}{2}$.
3. The transport of the positive-measure difference through the bi-Lipschitz map $R_2$.

## Sources

- S. Myers, C. Fefferman and N. Patterson, Can one learn history from the allelic spectrum?, *Theor. Popul. Biol.* 73 (2008), 342–348 (construction).
