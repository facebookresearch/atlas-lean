# Double threshold for the final size of an epidemic with fixed dose resistance

**Setting.** In the [Kermack–McKendrick epidemic with dose-threshold resistance](kermack-mckendrick-epidemic-with-dose-threshold-resistance.md), take fixed resistance $\nu = \delta_m$ with $m > 0$, so that

$$
J(t) = \int_0^t S(0)\, f\bigl([J(t-a) - m]_+\bigr) P(a)\kappa(a)\,da + J_0(t),
$$

with $J_0^\infty$, $J^\infty$, $S^\infty$ and $\mathcal{R}_0$ as defined there.

**Statement.**

1. If $J_0^\infty \le m$, then $J = J_0$ and $S(t) \ge S(0)e^{-m}$ for all $t$: no newly infected host ever becomes infective.
2. If $J_0^\infty > m$, then $J^\infty$ is the unique solution $z > m$ of $z = \mathcal{R}_0 f(z - m) + J_0^\infty$, and $J^\infty$ is a continuous concave function of $J_0^\infty \in (m,\infty)$ with $J^\infty - J_0^\infty \to \mathcal{R}_0$ as $J_0^\infty \to \infty$. Moreover:
   - if $\mathcal{R}_0 \le 1$, then $J^\infty \to m$ and $S^\infty \to S(0)e^{-m}$ as $J_0^\infty \downarrow m$;
   - if $\mathcal{R}_0 > 1$, let $x > 0$ be the unique positive root of $x = \mathcal{R}_0(1 - e^{-x})$. Then $J^\infty \ge m + x$ and $S^\infty \le S(0)e^{-(m+x)}$ whenever $J_0^\infty > m$, and $J^\infty \to m + x$ as $J_0^\infty \downarrow m$.

So when $\mathcal{R}_0 > 1$ the final size jumps by a fixed amount as the initial dose crosses the resistance $m$: an Allee-type threshold in the initial infection sits on top of the usual $\mathcal{R}_0$ threshold. Equivalently, the $\mathcal{R}_0$ threshold is a threshold $S(0) > S^\sharp = \bigl(\int_0^\infty P\kappa\bigr)^{-1}$ on the initial susceptibles.

## Depends on

- [Kermack–McKendrick epidemic with dose-threshold resistance](kermack-mckendrick-epidemic-with-dose-threshold-resistance.md)
- [Final-size equation of the Kermack–McKendrick model](../../kermack-mckendrick-sir-model/final-size-eq.md)

## Expansion

Monotone convergence in the integral equation gives $J^\infty = \mathcal{R}_0 f([J^\infty - m]_+) + J_0^\infty$, and $J^\infty$ is the minimal solution, obtained as the limit of the increasing iteration $z_n = \mathcal{R}_0 f([z_{n-1} - m]_+) + J_0^\infty$. If $J_0^\infty \le m$ the iteration never leaves $[0,m]$, where $f([\cdot - m]_+) = 0$. Otherwise substitute $y = J^\infty - m$, $y_0 = J_0^\infty - m > 0$ to get $y = \mathcal{R}_0 f(y) + y_0$, the classical final-size problem without resistance. Since $f$ is strictly increasing and concave with $f(0) = 0$, $f'(0) = 1$, and $f(y)/y$ is strictly decreasing, the solution is unique and continuous in $y_0$; as $y_0 \downarrow 0$ it tends to $0$ if $\mathcal{R}_0 \le 1$ and to the positive root of $y = \mathcal{R}_0 f(y)$ if $\mathcal{R}_0 > 1$.

## Sources

- Joan Ponce and Horst R. Thieme, "A Kermack–McKendrick type epidemic model with double threshold phenomenon (and a possible application to Covid-19)", Journal of Mathematical Biology 92 (2026), 33, <https://doi.org/10.1007/s00285-026-02348-8>; numbering as in arXiv:2409.17278: Theorems 3.2 and 3.3 (previewed as Theorems 1.1 and 1.2).
