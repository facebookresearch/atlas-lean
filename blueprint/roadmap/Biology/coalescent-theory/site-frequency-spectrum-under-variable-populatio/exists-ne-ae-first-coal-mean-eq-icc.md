# Non-identifiability from a bounded sample size

For every natural number $n$, there are two measurable functions $\eta_1, \eta_2 : \mathbb{R} \to \mathbb{R}$ and constants $0 < a \le b$ such that

- $a \le \eta_1(s) \le b$ and $a \le \eta_2(s) \le b$ for every real $s$;
- $\eta_1$ and $\eta_2$ differ on a subset of $[0, \infty)$ of positive Lebesgue measure;
- their [first-coalescence times](first-coal-mean.md) agree: $c_m(\eta_1) = c_m(\eta_2)$ for every $2 \le m \le n$.

The two functions are $(n+2)$-piece histories from [the tightness of $n \ge 2K$](exists-ne-first-coal-mean-eq-of-lt.md), extended to $s < 0$ by their size at $0$. This is a finite-sample form of the statement of Myers, Fefferman and Patterson (2008), whose theorem gives one pair of functions with equal $c_m$ for every $m$.

## Sources

- S. Myers, C. Fefferman and N. Patterson, *Can one learn history from the allelic spectrum?*, Theoret. Population Biol. 73 (2008), 342–348.
