# Dynamical trichotomy for positively density-dependent stochastic matrix models

Consider the stochastic structured population model

$$ X_{t+1} = A(X_t, \xi_{t+1})\, X_t , \qquad X_t \in [0,\infty)^n , $$

under the standing assumptions: (A1) the environments $\xi_t$ are i.i.d. in a separable metric space; (A2) the nonnegative matrix entries $A_{ij}(x,\xi)$ are continuous; (A3) positive feedback, $A_{ij}(x,\xi) \ge A_{ij}(y,\xi)$ whenever $x \ge y$; (A4) primitivity, $A(x,\xi)^{\tau} \gg 0$ for some $\tau$ and all $x \gg 0$; (A5) finite logarithmic moments of $\|A(c\mathbf{1},\xi)\|$ and of the co-norm of products. Define the low-density and high-density growth rates

$$ r_0 = \lim_{t\to\infty} \frac{1}{t}\log\|A(0,\xi_t)\cdots A(0,\xi_1)\|, \qquad r_\infty = \lim_{c\to\infty} \lim_{t\to\infty}\frac1t \log\|A(c\mathbf{1},\xi_t)\cdots A(c\mathbf{1},\xi_1)\| , $$

which exist almost surely and are deterministic by the subadditive ergodic theorem ($r_c$ is nondecreasing in $c$).

**Theorem.**

- Unconditional persistence: if $r_0 > 0$, then $\|X_t\| \to \infty$ almost surely whenever $X_0 \gg 0$.
- Unconditional extinction: if $r_\infty < 0$, then $X_t \to 0$ almost surely.
- Conditional persistence and extinction: if $r_0 < 0 < r_\infty$, then for every $\varepsilon > 0$ there are $c^* > c_* > 0$ with $\mathbb{P}[X_t \to 0 \mid X_0 = x] \ge 1-\varepsilon$ for $x \le c_*\mathbf{1}$ and $\mathbb{P}[\|X_t\| \to \infty \mid X_0 = x] \ge 1-\varepsilon$ for $x \ge c^*\mathbf{1}$.

## Expansion

Positive feedback makes the system monotone after $\tau$ steps, so trajectories can be sandwiched between the linear random products $A(0,\xi_t)\cdots A(0,\xi_1)$ and $A(c\mathbf{1},\xi_t)\cdots A(c\mathbf{1},\xi_1)$. The random Perron–Frobenius theorem turns the norm growth of these products into growth of every positive vector. If $r_0 < 0$, a population started near zero stays in a region where it is dominated by a product with negative exponent with high probability and decays; if $r_c > 0$, a population started above $c\mathbf{1}$ dominates a product with positive exponent and escapes to infinity. Examples include mate-limited scalar models, spatial patch models with dispersal, and nonlinear Leslie matrices with mate-limited fecundity.

## Sources

- Sebastian J. Schreiber, "A Dynamical Trichotomy for Structured Populations Experiencing Positive Density-Dependence in Stochastic Environments", in Springer Proceedings in Mathematics & Statistics (2017), 55–66, <https://doi.org/10.1007/978-981-10-6409-8_3>. Published version of arXiv:1701.08443, cited next; locators there refer to the arXiv version.
- S. J. Schreiber, "A dynamical trichotomy for structured populations experiencing positive density-dependence in stochastic environments", arXiv:1701.08443 (2017), Section 2 (assumptions A1–A5 and Examples 1–3) and Section 3, Theorem 3.1. <https://doi.org/10.48550/arXiv.1701.08443>
