# Schwartz–Zippel on the cube and influences of low-degree functions

If $g : \{-1,1\}^n \to \mathbb{R}$ is nonzero of degree at most $d$, then $\Pr_x[g(x) \ne 0] \ge 2^{-d}$. Consequently, for a Boolean $f$ of degree at most $d$, every coordinate with nonzero influence has $\mathbf{Inf}_i[f] \ge 2^{1-d}$, and $\mathbf{I}[f] \le d$ while $\mathbf{I}[f] \le d \cdot \mathbb{E}[f^2]$ for real $f$ of degree at most $d$.

## Proof sketch

Induct on $d$: write $g = x_1 g_1 + g_0$; restricting $x_1$ to the value making the top-degree part survive reduces the degree, and averaging over the two values of $x_1$ loses a factor of $2$. The derivative $D_i f$ of a Boolean function of degree $d$ has degree at most $d - 1$ and values in $\{0, \pm 1\}$, so $\mathbf{Inf}_i[f] = \Pr[D_i f \ne 0] \ge 2^{1-d}$.

## Depends on

- [Boolean degree](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/boolean-degree.md)
- [Influence of a coordinate](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-influence.md)
- [Total influence on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence.md)

## Proof depends on

- [Total influence in Fourier form](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence-eq-sum-card-mul-sq.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
- N. Nisan and M. Szegedy, "On the Degree of Boolean Functions as Real Polynomials", Computational Complexity 4(4), 1994.
