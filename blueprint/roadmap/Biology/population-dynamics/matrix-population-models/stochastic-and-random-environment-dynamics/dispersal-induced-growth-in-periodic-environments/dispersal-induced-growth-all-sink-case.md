# Dispersal-induced growth among sink patches in a periodic environment

This page covers Theorem 1 of Katriel (2022). Notation is as on [growth rate of a linear patch model with periodic local growth rates](growth-rate-of-periodic-patch-model.md): $x' = [R(\omega t) + mL]x$, common growth rate $\Lambda(m, \omega)$, and $\Lambda_0(m) = \frac{1}{2\pi}\int_0^{2\pi}\lambda(R(\theta) + mL)\, d\theta$.

**Definition.** Dispersal-induced growth (DIG) occurs when every patch is a sink ($\bar r_i < 0$ for all $i$) but $\Lambda(m, \omega) > 0$: each population would go extinct in isolation, yet with dispersal all grow exponentially.

**Theorem (all-sink case).** Assume $r_1, \dots, r_N$ are continuous, $2\pi$-periodic, with $\bar r_i < 0$ for all $i$. Let

$$\chi = \frac{1}{2\pi}\int_0^{2\pi} \max_{1 \le i \le N} r_i(\theta)\, d\theta .$$

Then $\lim_{m \to 0^+}\lim_{\omega \to 0^+}\Lambda(m, \omega) = \chi$, and:

- **(I)** if $\chi < 0$, then $\Lambda(m, \omega) < 0$ for all $m, \omega > 0$ (no DIG);
- **(II)** if $\chi > 0$, the equation $\Lambda_0(m) = 0$ has a unique root $m^* > 0$, and there is a continuous $\omega_c : [0, m^*] \to [0, \infty)$, real-analytic on $(0, m^*)$, with $\omega_c(0) = \omega_c(m^*) = 0$ and $\omega_c > 0$ on $(0, m^*)$, such that
  - for $m \in (0, m^*)$: $\Lambda(m, \omega) > 0$ if $\omega < \omega_c(m)$ and $\Lambda(m, \omega) < 0$ if $\omega > \omega_c(m)$;
  - for $m \ge m^*$: $\Lambda(m, \omega) < 0$ for every $\omega > 0$.

So DIG requires $\chi > 0$, an intermediate dispersal rate $0 < m < m^*$, and slow enough environmental oscillation, $\omega < \omega_c(m) \le \max_{[0, m^*]}\omega_c$. The condition $\chi > 0$ forces some patch to have positive growth at some times, and no single patch to dominate all others at all times; it fails if $\max_{i,j,\theta}|r_i(\theta) - r_j(\theta)| < \max_i|\bar r_i|$. It can hold with all but one rate constant, and with all rates oscillating in phase but with different amplitudes.

**Two patches (Example 2).** With $L_{12} = L_{21} = 1$ (for $L_{12} = L_{21} = a$ replace $m$ by $ma$, so the root below becomes $m^*/a$), $\Lambda_0(m) = \tfrac12\big(\bar r_1 + \bar r_2 + \tfrac{1}{2\pi}\int_0^{2\pi}\sqrt{(r_1(\theta) - r_2(\theta))^2 + 4m^2}\, d\theta\big) - m$. For $r_1(\theta) = -0.03 + 0.3\cos\theta$, $r_2(\theta) = r_1(\theta - \pi)$, this gives $m^* \approx 0.7276$.

## Depends on

- [Growth rate of a linear patch model with periodic local growth rates](growth-rate-of-periodic-patch-model.md)

## Expansion

$\Lambda_0(0) = \chi$, since $\lambda(R(\theta)) = \max_i r_i(\theta)$, and $\Lambda_0$ is decreasing in $m$ (Lemmas 6 and 7, pointwise in $\theta$) with $\Lambda_0(m) \to \frac1N\sum_i\bar r_i < 0$ as $m \to \infty$; this gives the limit formula and the unique root $m^*$ when $\chi > 0$. If $\chi < 0$, $\Lambda_0(m) < 0$ for all $m > 0$, so $\Lambda < 0$ at small $\omega$ (Lemma 5) and hence for all $\omega$, since $\Lambda$ decreases in $\omega$ (Lemma 2). If $\chi > 0$ and $m < m^*$, $\Lambda > 0$ at small $\omega$, while at large $\omega$, $\Lambda \to \lambda(\bar R + mL) \le \max_i\bar r_i < 0$ (Lemmas 6 and 8). Strict monotonicity in $\omega$ gives a unique crossing $\omega_c(m)$, analytic by the implicit function theorem. For $m \ge m^*$, $\Lambda < \Lambda_0(m) \le 0$.

## Sources

- G. Katriel, Dispersal-induced growth in a time-periodic environment, *J. Math. Biol.* 85 (2022), article 24, Theorem 1, <https://doi.org/10.1007/s00285-022-01791-7>; preprint <https://arxiv.org/abs/2104.01589>.
