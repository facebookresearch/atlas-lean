# Reverse hypercontractivity theorem on the cube

For finite nonzero exponents $q < p \le 1$ and $0 \le \rho \le \sqrt{(1-p)/(1-q)}$, every positive (for $p \le 0$) or nonnegative (for $0 < p \le 1$) function $f$ on $\{-1,1\}^n$ satisfies $\|f\|_p \le \|T_\rho f\|_q$, where $\|f\|_p = (\mathbb{E}f^p)^{1/p}$ also for negative $p$. In two-function form: for $r, s \le 0$, $r, s \ne -1$, $rs \le 1$ and $0 \le \rho \le \sqrt{rs}$, $\mathbb{E}[f(x)g(y)] \ge \|f\|_{1+r}\|g\|_{1+s}$ for $\rho$-correlated $(x,y)$. In particular, for $0 \le \rho \le 1/2$ and arbitrary real $f, g$, $(\mathbb{E}|f|)^2(\mathbb{E}|g|)^2 \le \mathbb{E}[f(x)^2 g(y)^2]$.

## Proof sketch

Tensorize the one-bit inequality: reverse Hölder (valid for exponents below $1$) plays the role of Hölder in the forward proof, so the one-dimensional inequality extends coordinate by coordinate to the product space.

## Depends on

- [Noise operator on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-op.md)

## Proof depends on

- [Reverse hypercontractivity of a single bit](reverse-hypercontractivity-of-a-single-bit.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
