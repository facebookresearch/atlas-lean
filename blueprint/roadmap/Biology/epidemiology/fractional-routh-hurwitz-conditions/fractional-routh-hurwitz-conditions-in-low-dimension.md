# Fractional Routh–Hurwitz conditions in low dimension

**Setting.** For a Caputo system $D^\alpha x = f(x)$ with $\alpha \in [0,1)$, an equilibrium is locally asymptotically stable if every eigenvalue $\lambda$ of the Jacobian at the equilibrium satisfies

$$|\arg \lambda| > \frac{\alpha\pi}{2}. \tag{$\ast$}$$

Let $P(\lambda) = \lambda^n + a_1\lambda^{n-1} + \cdots + a_n$ be the characteristic polynomial, with real coefficients. For $n = 3$ its discriminant is

$$D(P) = 18a_1a_2a_3 + (a_1a_2)^2 - 4a_3a_1^3 - 4a_2^3 - 27a_3^2;$$

$D(P) > 0$ means three distinct real roots and $D(P) < 0$ means one real root and a pair of non-real complex conjugate roots. For $\alpha = 1$, $(\ast)$ for all roots is equivalent to the Routh–Hurwitz conditions; for $\alpha \in [0,1)$ the Routh–Hurwitz conditions remain sufficient but are not necessary.

**Proposition.** All roots of $P$ satisfy $(\ast)$ under the following conditions.
1. $n = 1$: iff $a_1 > 0$.
2. $n = 2$: iff either the Routh–Hurwitz conditions $a_1 > 0$, $a_2 > 0$ hold, or

$$a_1 < 0,\qquad 4a_2 > a_1^2,\qquad \Big|\tan^{-1}\frac{\sqrt{4a_2 - a_1^2}}{a_1}\Big| > \frac{\alpha\pi}{2}.$$

3. $n = 3$, $D(P) > 0$: iff the Routh–Hurwitz conditions $a_1 > 0$, $a_3 > 0$, $a_1a_2 > a_3$ hold.
4. $n = 3$, $D(P) < 0$: if $a_1 \ge 0$, $a_2 \ge 0$, $a_3 > 0$ and $\alpha < 2/3$, then $(\ast)$ holds.
5. $n = 3$, $D(P) < 0$: if $a_1 > 0$, $a_2 > 0$ and $a_1a_2 = a_3$, then $(\ast)$ holds for all $\alpha \in [0,1)$.
6. Any $n$: $a_n > 0$ is necessary.

## Expansion

(1) The root is $-a_1$. (2) Real roots or roots with negative real part reduce to Routh–Hurwitz; a complex pair with positive real part $-a_1/2 > 0$ has argument $\tan^{-1}\big(\sqrt{4a_2 - a_1^2}/a_1\big)$ in absolute value, which must exceed $\alpha\pi/2$. (3) Real roots satisfy $(\ast)$ only if negative, so the classical conditions are exact. (4) Write $P(\lambda) = (\lambda + b)(\lambda - \beta - i\gamma)(\lambda - \beta + i\gamma)$, so $a_1 = b - 2\beta$, $a_2 = \beta^2 + \gamma^2 - 2b\beta$, $a_3 = b(\beta^2 + \gamma^2)$ with $b > 0$. If $\beta > 0$, then $a_1 \ge 0$ gives $b \ge 2\beta$ and $a_2 \ge 0$ gives $\beta^2 + \gamma^2 \ge 2b\beta \ge 4\beta^2$, so $\gamma^2 \ge 3\beta^2$ and the complex roots have $|\arg\lambda| \ge \pi/3 > \alpha\pi/2$. (5) Then $P(\lambda) = (\lambda + a_1)(\lambda^2 + a_2)$, with roots $-a_1$ and $\pm i\sqrt{a_2}$ of argument $\pi/2 > \alpha\pi/2$. (6) Factoring over real and complex-conjugate roots gives $a_n = \prod_j b_j \prod_k (\beta_k^2 + \gamma_k^2)$, and a nonpositive real root violates $(\ast)$. The criterion is applied to disease-free equilibria of fractional epidemic models, where $a_n > 0$ typically reduces to a threshold on the reproduction number.

## Sources

- E. Ahmed, A. S. Elgazzar, "On fractional order differential equations model for nonlocal epidemics", Physica A 379:607–614 (2007), Section 2, Eqs (2)–(8), Definition 1 and Proposition 1, <https://doi.org/10.1016/j.physa.2007.01.010>, PMCID PMC7125871.
