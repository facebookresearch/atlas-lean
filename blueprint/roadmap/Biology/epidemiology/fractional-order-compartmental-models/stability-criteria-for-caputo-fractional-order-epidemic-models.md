# Stability criteria for Caputo fractional-order epidemic models

**Fractional derivatives.** For $n - 1 < p \le n$, $n \in \mathbb N$, the Caputo derivative of a $C^n$ function is

$${}^{C}\!D^p_t X(t) = \frac{1}{\Gamma(n - p)} \int_0^t \frac{X^{(n)}(\zeta)}{(t - \zeta)^{p + 1 - n}}\, d\zeta, \qquad t > 0,$$

which tends to $X'(t)$ as $p \to 1$ for $n = 1$. The Atangana–Baleanu–Caputo derivative of order $\Phi \in (0, 1)$ replaces the power-law kernel by a Mittag-Leffler kernel,

$${}^{ABC}\!D^\Phi_t f(t) = \frac{B(\Phi)}{1 - \Phi} \int_0^t f'(\vartheta)\, E_\Phi\Bigl(-\frac{\Phi (t - \vartheta)^\Phi}{1 - \Phi}\Bigr) d\vartheta,$$

with normalization $B(0) = B(1) = 1$; its associated integral is $\frac{1 - \Phi}{B(\Phi)} f(t) + \frac{\Phi}{B(\Phi)\Gamma(\Phi)} \int_0^t (t - \vartheta)^{\Phi - 1} f(\vartheta)\, d\vartheta$.

**Model class.** A fractional compartmental model is ${}^{C}\!D^p_t x(t) = f(x(t))$, $p \in (0, 1]$, with $f$ the right-hand side of an ordinary compartmental model; its equilibria are the zeros of $f$, as in the integer-order model, and the disease-free equilibrium and $\mathcal R_0$ are unchanged.

**Results.**

1. *Linear stability (Matignon).* An equilibrium $x^*$ is locally asymptotically stable if every eigenvalue $\lambda_i$ of the Jacobian $Df(x^*)$ satisfies $|\arg \lambda_i| > p\pi/2$. Since $p \le 1$, any eigenvalue with negative real part qualifies, so integer-order stability ($\mathcal R_0 < 1$ at the disease-free equilibrium) implies fractional stability for every $p$.
2. *Fractional Lyapunov method.* If $L$ is continuously differentiable with $M_1(x) \le L(t, x) \le M_2(x)$ and ${}^{C}\!D^p_t L(t, x(t)) \le -M_3(x)$ for continuous positive definite $M_1, M_2, M_3$ on a neighbourhood of $x^*$, then $x^*$ is uniformly asymptotically stable. With a linear Lyapunov function $F = \sum_j A_j x_j$ on the infected compartments, this gives global asymptotic stability of the disease-free equilibrium on the feasible region when $\mathcal R_0 < 1$.
3. *Monotonicity.* If $H \in C[r_1, r_2]$ and ${}^{C}D^p_t H \in C(r_1, r_2]$, then $H(t) = H(r_1) + \frac{1}{\Gamma(p)}\, {}^{C}D^p_t H(\zeta)\,(t - r_1)^p$ for some $\zeta \in [r_1, t]$; hence ${}^{C}D^p_t H \ge 0$ (resp. $\le 0$) on $(r_1, r_2)$ implies $H$ non-decreasing (resp. non-increasing). This yields positivity and invariance of the non-negative orthant.
4. *Existence and uniqueness (ABC case).* Writing the model as a Volterra integral equation with the ABC integral, Picard iterates converge to a unique solution on $[0, b]$ when $\frac{1 - \Phi}{B(\Phi)}\eta_i + \frac{b^\Phi}{B(\Phi)\Gamma(\Phi)}\eta_i < 1$ for the Lipschitz constants $\eta_i$ of each right-hand side, and the solution is Hyers–Ulam stable.

## Depends on

- [Basic reproduction number of the next-generation matrix](../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

Linearizing at $x^*$ gives ${}^{C}D^p_t y = J y$, whose solutions are combinations of Mittag-Leffler functions $E_p(\lambda t^p)$; these decay (algebraically, not exponentially) exactly when $\lambda$ lies outside the sector $|\arg \lambda| \le p\pi/2$, which is the Matignon criterion. Memory slows convergence but enlarges the stability sector, so fractional order cannot destabilize an equilibrium that is stable for the classical model; it can stabilize equilibria whose eigenvalues have small positive real part. The Lyapunov argument uses the fact that ${}^{C}D^p_t$ of a linear combination is the linear combination of derivatives, so the same coefficient choice as in the integer-order proof works. For rational orders $p = m/n$ the characteristic equation becomes polynomial in $s = \lambda^{1/n}$, and stability requires $|\arg s| > \pi/(2n)$ for all its roots.

## Sources

- M. Awais, F. S. Alshammari, S. Ullah, M. A. Khan, S. Islam, "Modeling and simulation of the novel coronavirus in Caputo derivative", Results in Physics (2020), Definitions 1–2, Theorem 0.1 (fractional Lyapunov direct method), Lemma 0.1 and Corollary 1 (generalized mean value theorem and monotonicity), Theorem 0.2 (existence, uniqueness, positivity), Theorem 0.3 (Eq. 15, sector condition) and Theorem 0.4 (global stability with a linear Lyapunov function). <https://doi.org/10.1016/j.rinp.2020.103588> (PMC7671651).
- X.-P. Li, H. A. Bayatti, A. Din, A. Zeb, "A vigorous study of fractional order COVID-19 model via ABC derivatives", Results in Physics (2021), Theorem 1 (rational-order sector condition), Theorem 2, Theorem 3 (existence and uniqueness, Eq. 20) and Theorem 4 (Hyers–Ulam stability). <https://doi.org/10.1016/j.rinp.2021.104737> (PMC8401151).
