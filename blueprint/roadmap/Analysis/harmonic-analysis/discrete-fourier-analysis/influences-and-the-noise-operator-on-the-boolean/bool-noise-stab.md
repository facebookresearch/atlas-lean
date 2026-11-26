# Noise stability on the Boolean cube

For $f : \{-1, 1\}^n \to \mathbb{R}$ and a real number $\rho$, the noise stability of $f$ at
$\rho$ is

$$\mathrm{Stab}_\rho[f] = \mathbb{E}_x\big[f(x)\, T_\rho f(x)\big],$$

where $x$ is uniform and $T_\rho$ is the noise operator. For $-1 \le \rho \le 1$ this is
$\mathbb{E}[f(x) f(y)]$ for a $\rho$-correlated pair $(x, y)$: $x$ uniform and each $y_i$
independently equal to $x_i$ with probability $(1 + \rho)/2$. For a $\pm 1$-valued $f$,
$\mathrm{Stab}_\rho[f] = 1 - 2\,\Pr[f(x) \ne f(y)]$.

## Sources

- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014 (arXiv:2105.10386), Section 2.4 (Definition 2.46, Fact 2.48).
