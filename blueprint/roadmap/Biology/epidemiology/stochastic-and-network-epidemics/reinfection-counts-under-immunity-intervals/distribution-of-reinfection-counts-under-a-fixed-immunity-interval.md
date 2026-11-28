# Distribution of reinfection counts under a fixed immunity interval

**Model (discrete hardcore Poisson process).** An epidemic cycle lasts $N$ days. On each day an individual is exposed independently with probability $\beta$; an exposure on day $x$ produces an infection unless the individual is protected, and an infection on day $x$ confers immunity on days $x+1, \dots, x+L$ (exposures during immunity are ignored). This is a discrete, time-ordered Matérn type II process on $\{1,\dots,N\}$. Let $\pi_r = \pi_r(N,L)$ be the probability of exactly $r$ infections in the cycle, and $P(r,N,\beta) = \binom{N-Lr}{r}\beta^r(1-\beta)^{N-Lr-r}$ (zero if $r<0$ or $N < (L+1)r$).

**Theorem (finite $N$).** For $r \ge 0$,

$$\pi_r = P(r,N,\beta) + \beta\sum_{i=1}^{L} P(r-1, N-i, \beta),$$

equivalently, for $r > 0$ and $N - Lr > 0$, with $F_r(X) = \frac{d^{r-1}}{dX^{r-1}}\Big(X^{N-Lr}\frac{1-X^L}{1-X}\Big)$,

$$\pi_r = \binom{N-Lr}{r}\beta^r(1-\beta)^{N-Lr-r} + \frac{\beta^r}{(r-1)!}F_r(1-\beta).$$

$\pi_r > 0$ exactly for $r \le (N+L)/(L+1)$, $\sum_r \pi_r = 1$, and $\pi_0 = (1-\beta)^N$ does not depend on $L$.

**Theorem (continuous limit).** Let $N \to \infty$ with $\beta = \alpha/N$, $\alpha > 0$, and $L/N \to \nu \in [0,1]$. Write $\Pi(\lambda, r) = e^{-\lambda}\sum_{k=0}^{r}\lambda^k/k!$ for the Poisson$(\lambda)$ distribution function. Then for $0 \le r \le r_\flat = \lfloor 1/\nu \rfloor$,

$$\pi'_r = \lim_{N\to\infty}\pi_r = \Pi\big(\alpha(1-r\nu),\, r\big) - \Pi\big(\alpha(1-(r-1)\nu),\, r-1\big),$$

and if $1/\nu \notin \mathbb{Z}$ there is one more atom, $\pi'_{r_\flat+1} = 1 - \Pi\big(\alpha(1-r_\flat\nu), r_\flat\big)$. For $\nu = 0$ this reduces to the Poisson law $\pi'_r = e^{-\alpha}\alpha^r/r!$.

## Proof sketch

Infection days $x_1 < \dots < x_r$ satisfy $x_{i+1} > x_i + L$. Deleting each immunity window (exposures inside it are irrelevant) maps the configuration to $r$ distinct days among $N - Lr$; when the last window fits inside the cycle this gives $P(r,N,\beta)$, and when it overhangs the end by $i$ days it gives the boundary terms $\beta P(r-1, N-i, \beta)$. Summing the boundary terms as a geometric series and differentiating produces the $F_r$ form. In the limit each removed window shrinks the effective exposure time to $1 - r\nu$ of the cycle, and the boundary sum telescopes into the difference of two Poisson distribution functions, so the limiting law has at most $\lceil 1/\nu \rceil$ positive atoms. Several immunity lengths $L_1,\dots,L_s$ (several strains) give the analogous multi-index formulas.

## Sources

- Ivan Cherednik, "Discrete Poisson hardcore 1D model and applications", in *Contemporary Mathematics*, American Mathematical Society, 2025, 169–187, <https://doi.org/10.1090/conm/823/16496>. Preprint version: arXiv:2202.09176 (2022), Section 2 (formula for $\pi_r$, Theorem 2.1) and Section 3 (Theorem 3.1), <https://doi.org/10.48550/arXiv.2202.09176>.
