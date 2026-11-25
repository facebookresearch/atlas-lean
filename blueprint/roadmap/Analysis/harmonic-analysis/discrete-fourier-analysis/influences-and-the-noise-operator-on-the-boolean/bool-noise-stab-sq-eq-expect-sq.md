# Noise stability as a squared norm

For every $f : \{-1, 1\}^n \to \mathbb{R}$ and every real $\sigma$,
$\mathrm{Stab}_{\sigma^2}[f] = \mathbb{E}\big[(T_\sigma f)^2\big] = \|T_\sigma f\|_2^2$. In particular
$\mathrm{Stab}_\rho[f] \ge 0$ for $\rho \ge 0$, and
$\mathrm{Stab}_\rho[f] = \|T_{\sqrt\rho} f\|_2^2$ turns hypercontractive bounds on $T_{\sqrt\rho}$
into bounds on noise stability.

## Sources

- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014 (arXiv:2105.10386), Section 2.4 and the introduction of Chapter 9.
