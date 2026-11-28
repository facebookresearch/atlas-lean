# Global dynamics of the single-species chemostat

For the chemostat with dilution rate $D > 0$, feed concentration $S_f > 0$, yield $y > 0$ and an increasing $C^1$ growth rate $\mu$ with $\mu(0) = 0$ (for example the Monod rate $\mu(S) = \mu_m S/(K_s + S)$), $\dot S = D(S_f - S) - y^{-1}\mu(S) X$ and $\dot X = (\mu(S) - D) X$, let the break-even concentration $\lambda$ be the solution of $\mu(\lambda) = D$, with $\lambda = \infty$ when there is none; for the Monod rate $\lambda = K_s D/(\mu_m - D)$ when $\mu_m > D$. Then for every initial condition with $S(0) \ge 0$ and $X(0) > 0$: (i) if $\lambda \ge S_f$, then $X(t) \to 0$ and $S(t) \to S_f$ (washout); (ii) if $\lambda < S_f$, then $(S(t), X(t)) \to (\lambda, y(S_f - \lambda))$. This is the case of one species of the competitive exclusion principle in the form of Rapaport and Veruete (Proposition 1 and Lemma 1, stated with unit yield, which the rescaling $x = X/y$ achieves); the proof uses the conserved relaxation $\frac{d}{dt}(S + X/y) = D(S_f - S - X/y)$.

## Depends on

- [Chemostat equilibria and the washout threshold](../../../Biology/population-dynamics/chemostat/chemostat-equilibria-and-washout.md)

## Proof depends on

- [Chemostat: the total substrate equivalent relaxes to the feed](../../../Biology/population-dynamics/chemostat/chemostat-total-substrate-reduction.md)

## Expansion

1. The equilibria and the washout threshold: $\lambda < S_f$ exactly when $D < \mu(S_f)$, the critical dilution rate.
2. The relaxation of the total substrate equivalent to the feed (Lemma 1(1) of the source).
3. Washout when $\lambda \ge S_f$ (Lemma 1(2)). For $D > \mu(S_f)$ this is strengthened by the [exponential attraction to chemostat washout above the critical dilution rate](../../../Biology/population-dynamics/chemostat/exponential-attraction-to-chemostat-washout.md); the boundary case $\lambda = S_f$, that is $D = \mu(S_f)$, gives convergence to washout without an exponential rate.
4. Global convergence to the positive equilibrium when $\lambda < S_f$ (Proposition 1 with one species).
5. For the Monod rate, part (ii) is [global convergence of the chemostat](global-convergence-of-the-chemostat.md) and part (i) with $\lambda > S_f$ is the global counterpart of the local [unconditional exponential stability of washout](unconditional-exponential-stability-of-chemostat-washout.md), without a rate.

## Sources

- A. Rapaport and M. Veruete, A new proof of the competitive exclusion principle in the chemostat, Discrete Contin. Dyn. Syst. Ser. B 24 (2019), 3755–3764, Section 2, Definition 1, Proposition 1, Lemma 1. <https://doi.org/10.3934/dcdsb.2018314>
- Original result: S. B. Hsu, S. Hubbell and P. Waltman, A mathematical theory for single-nutrient competition in continuous cultures of micro-organisms, SIAM J. Appl. Math. 32 (1977), 366–383. <https://doi.org/10.1137/0132030> The global statements for Monod growth follow Rapaport and Veruete (2019), who attribute the first proof to this paper.
