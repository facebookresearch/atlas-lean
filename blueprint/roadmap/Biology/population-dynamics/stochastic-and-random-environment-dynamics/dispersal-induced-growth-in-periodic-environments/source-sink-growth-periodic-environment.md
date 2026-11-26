# Growth in a periodic source-sink patch system

This page covers Theorem 2 of Katriel (2022), the source-sink counterpart of the all-sink theorem. Notation is as on [growth rate of a linear patch model with periodic local growth rates](growth-rate-of-periodic-patch-model.md): $\Lambda_0(m) = \frac{1}{2\pi}\int_0^{2\pi}\lambda(R(\theta) + mL)\, d\theta$ and $\Lambda_\infty(m) = \lambda(\bar R + mL)$.

**Theorem (source-sink case).** Assume $r_1, \dots, r_N$ are continuous and $2\pi$-periodic with $\min_i\bar r_i < 0 < \max_i\bar r_i$, and let $\bar r = \frac1N\sum_i\bar r_i$.

- **(I)** If $\bar r > 0$, then $\Lambda(m, \omega) > 0$ for all $m, \omega > 0$.
- **(II)** If $\bar r < 0$, then $\Lambda_0(m) = 0$ has a unique root $m^* > 0$ and $\Lambda_\infty(m) = 0$ has a unique root $\hat m > 0$, with $\hat m \le m^*$. Unless all $r_i - r_j$ are constant, $\hat m < m^*$ and there is a continuous $\omega_c : (\hat m, m^*] \to [0, \infty)$, real-analytic on $(\hat m, m^*)$, with $\omega_c(m) \to +\infty$ as $m \to \hat m^+$, $\omega_c(m^*) = 0$ and $\omega_c > 0$ on $(\hat m, m^*)$, such that
  - for $m \in (0, \hat m]$: $\Lambda(m, \omega) > 0$ for all $\omega > 0$;
  - for $m \in (\hat m, m^*)$: $\Lambda > 0$ if $\omega < \omega_c(m)$ and $\Lambda < 0$ if $\omega > \omega_c(m)$;
  - for $m \ge m^*$: $\Lambda(m, \omega) < 0$ for all $\omega > 0$.

The threshold $\hat m$ is the persistence threshold of the time-averaged system with constant rates $\bar r_i$. Slow temporal variation therefore extends persistence to dispersal rates $\hat m < m < m^*$ at which the averaged system declines. If all $r_i - r_j$ are constant, $R(\theta) = \bar R + r_0(\theta)I$ with $r_0$ of mean zero, and $\Lambda(m, \omega) = \Lambda_\infty(m)$ for every $\omega$.

**Two patches (Example 3).** Take $L_{12} = L_{21} = 1$ (for $L_{12} = L_{21} = a$ replace $m$ by $ma$, so both thresholds below are divided by $a$). With $\bar r_1\bar r_2 < 0$, $\Lambda_\infty(m) = \tfrac12\big(\bar r_1 + \bar r_2 + \sqrt{(\bar r_1 - \bar r_2)^2 + 4m^2}\big) - m$ and

and, in case (II), that is when also $\bar r_1 + \bar r_2 < 0$,

$$\hat m = \Big( \frac{1}{\bar r_1} + \frac{1}{\bar r_2} \Big)^{-1} = \frac{\bar r_1 \bar r_2}{\bar r_1 + \bar r_2} > 0.$$

If instead $\bar r_1 + \bar r_2 \ge 0$ there is no positive root: for $(\bar r_1, \bar r_2) = (1, -1)$ the formula divides by zero, and for $(2, -1)$ it gives $-2$; this is case (I) or its boundary, where $\Lambda_\infty(m) > 0$ for every $m > 0$.

For $r_1(\theta) = -0.1 + 0.3\cos\theta$, $r_2(\theta) = 0.05 - 0.3\cos\theta$: $\hat m = 0.1$ and $m^* \approx 0.990$.

## Depends on

- [Growth rate of a linear patch model with periodic local growth rates](growth-rate-of-periodic-patch-model.md)

## Expansion

As $m \to \infty$ both $\Lambda_0(m)$ and $\Lambda_\infty(m)$ tend to $\bar r$ (Lemma 6), while at $m = 0$ they are $\chi \ge \max_i\bar r_i > 0$ and $\max_i\bar r_i > 0$; monotonicity in $m$ gives (I) when $\bar r > 0$ and the unique roots $m^*, \hat m$ when $\bar r < 0$. Since $\Lambda$ is nonincreasing in $\omega$ with limits $\Lambda_0$ at $\omega \to 0$ and $\Lambda_\infty$ at $\omega \to \infty$, we get $\Lambda_\infty \le \Lambda_0$, hence $\hat m \le m^*$, strictly when $\Lambda$ is strictly decreasing in $\omega$. The three regimes then follow from the signs of the two limits, by the same argument as in [dispersal-induced growth among sink patches](dispersal-induced-growth-all-sink-case.md); that page is a comparison sharing the setting, and its theorem is not used here.

## Sources

- G. Katriel, Dispersal-induced growth in a time-periodic environment, *J. Math. Biol.* 85 (2022), article 24, Theorem 2, <https://doi.org/10.1007/s00285-022-01791-7>; preprint <https://arxiv.org/abs/2104.01589>.
