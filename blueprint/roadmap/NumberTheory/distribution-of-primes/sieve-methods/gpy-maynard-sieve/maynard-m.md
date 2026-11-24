# Maynard's variational quantity $M_k$

$$M_k = \sup_{F} \frac{\sum_{m=1}^{k} J_k^{(m)}(F)}{I_k(F)},$$

the supremum over [admissible profiles](is-maynard-profile.md) (Maynard (2015), Proposition 4.2). If the primes have level of distribution $\theta$, then every admissible $k$-tuple has infinitely many translates containing at least $\lceil \theta M_k / 2 \rceil$ primes; see [the reduction](infinite-lt-prime-shift-count-of-lt-mayn.md).

Relation to the source. Here the supremum is taken over bounded Borel-measurable profiles rather than Maynard's Riemann-integrable ones; this class contains an a.e.-equivalent, with the same ratio, of each of Maynard's profiles, so once the ratios are bounded this $M_k$ is at least Maynard's. The two suprema agree: by the Cauchy–Schwarz inequality in $t_m$, $J_k^{(m)}(F) \le I_k(F)$, so each $J_k^{(m)}$ is the square of the $L^2$ norm of a linear operator of norm at most $1$, and $I_k$ and the $J_k^{(m)}$ are continuous for the $L^2$ norm on $\mathcal R_k$; and finite combinations of indicators of boxes inside $\mathcal R_k$, which are Riemann-integrable, are dense in $L^2(\mathcal R_k)$. The same bound shows that the ratios are at most $k$, so the supremum is finite; it is taken over a nonempty set by [the existence of admissible profiles](exists-is-maynard-profile.md).

## Related topics

- [$M_5 > 2$](two-lt-maynard-m-five.md), [$M_{105} > 4$](four-lt-maynard-m-105.md), [growth of $M_k$](eventually-log-sub-lt-maynard-m.md): Maynard's lower bounds.

## Sources

- J. Maynard, "Small gaps between primes", *Ann. of Math.* 181 (2015), 383–413; theorem and display numbers are those of arXiv:1311.4600v3 (28 Oct 2019).
