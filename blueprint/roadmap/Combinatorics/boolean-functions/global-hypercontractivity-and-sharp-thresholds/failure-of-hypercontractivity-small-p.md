# Ordinary hypercontractivity degrades as p tends to zero

For $0 < p \le 1/2$ the optimal constant $\rho_p$ in the $(2,4)$-hypercontractive inequality $\|T_\rho f\|_{L^4(\mu_p)} \le \|f\|_{L^2(\mu_p)}$, valid for all $f$ and all $\rho \le \rho_p$, satisfies $\rho_p = \Theta\bigl(p^{1/4}\bigr)$ as $p \to 0$. In particular, for the dictator $f(x) = (x_1 - p)/\sqrt{p(1-p)}$ one has $\|f\|_4^4 / \|f\|_2^4 = \Theta(1/p)$, so level-$1$ functions are not uniformly hypercontractive when $p = o(1)$.

## Proof sketch

A direct computation for the normalized dictator gives fourth moment $\frac{(1-p)^3 + p^3}{p(1-p)}$, which is $\Theta(1/p)$; testing $T_\rho$ on it shows that $\rho^4/p$ must be bounded. The matching upper bound $\rho_p = \Omega(p^{1/4})$ follows from the two-point inequality and tensorization.

## Depends on

- [Global functions on the p-biased cube](pbiased-global-function.md)

## Proof depends on

- [Hypercontractivity Theorem (Bonami–Beckner)](../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/hypercontractivity-theorem.md)

## Sources

- P. Keevash, N. Lifshitz, E. Long, D. Minzer, "Hypercontractivity for global functions and sharp thresholds", Journal of the American Mathematical Society 37 (2024), arXiv:1906.05568.
