# Stabilizing proportional and PI gains for first- and second-order plants

For a strictly proper plant $P = n_P/d_P$ and a proper controller $C = n_C/d_C$ ($\deg n_P < \deg d_P$ and $\deg n_C \le \deg d_C$), with coprime polynomial numerators and denominators, the closed loop under unit negative feedback is well posed, its characteristic polynomial $a_{cl} = d_P d_C + n_P n_C$ has the same degree and leading coefficient as $d_P d_C$, so it is not zero, and the loop is stable when $a_{cl}$ is Hurwitz (all roots in the open left half-plane). Both plants below are strictly proper and both controllers proper. Without strict properness the loop can be singular: $P = 1$ and $C = -1$ give $a_{cl} = 0$.

1. **PI control of a first-order plant.** Let $P(s) = b/(s + a)$ with $b > 0$, and $C(s) = k_p + k_i/s$ with $k_i \ne 0$. Then $a_{cl}(s) = s^2 + (a + b k_p) s + b k_i$, which is Hurwitz if and only if $a + b k_p > 0$ and $k_i > 0$.
2. **Proportional control of an integrating plant.** Let $P(s) = b/(s(s + a))$ with $a, b > 0$, and $C = k$ with $k \ne 0$. Then $a_{cl}(s) = s^2 + a s + b k$, which is Hurwitz if and only if $k > 0$.
3. **Root locus.** As $k$ varies over $(0, \infty)$ in part 2, the closed-loop poles are

    $$s_\pm(k) = \frac{-a \pm \sqrt{a^2 - 4bk}}{2},$$

    real and distinct for $k < a^2/(4b)$, a double pole $-a/2$ at $k = a^2/(4b)$, and complex with real part $-a/2$ for $k > a^2/(4b)$.

The polynomials follow by clearing denominators: $s(s + a) + b(k_p s + k_i)$ and $s(s + a) + bk$. A monic real quadratic $s^2 + \beta s + \gamma$ has both roots in the open left half-plane exactly when $\beta > 0$ and $\gamma > 0$: the roots have sum $-\beta$ and product $\gamma$; if they are not real, they are conjugate with real part $-\beta/2$ and $\gamma = |\lambda|^2 > 0$, and if they are real, both are negative exactly when their sum is negative and their product positive. Apply it with $b > 0$ in part 1, and with $a > 0$, $b > 0$ in part 2. Part 3 is the quadratic formula.

## Background

- [Routh–Hurwitz criterion for $2 \times 2$ matrices](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/exists-eigenvalue-re-pos-iff.md): the non-strict form, applied to the companion matrix of $s^2 + \beta s + \gamma$: no root has positive real part exactly when $\beta \ge 0$ and $\gamma \ge 0$
- [Routh–Hurwitz criterion for cubic polynomials](routh-hurwitz-criterion-for-cubic-polynomials.md): the third-order analogue

## Sources

- K. J. Åström and R. M. Murray, *Feedback Systems: An Introduction for Scientists and Engineers*, 2nd ed., Princeton University Press, 2021 (electronic edition v3.0i, <http://fbsbook.org>), Section 2.3: PI control of the first-order process $b/(s + a)$ and its closed-loop characteristic polynomial $a_{cl}(s) = s^2 + (a + bk_p)s + bk_i$ (2.26) (p. 2-15), and Section 2.2, the second-order case of the Routh–Hurwitz conditions (p. 2-10).
