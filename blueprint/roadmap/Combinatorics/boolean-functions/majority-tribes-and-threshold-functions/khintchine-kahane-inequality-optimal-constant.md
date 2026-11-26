# Khintchine–Kahane inequality with the optimal constant

For vectors $w_1, \dots, w_n$ in a (semi)normed real vector space and independent uniform signs $x_i$,

$$\mathbb{E}\Big\|\sum_i x_i w_i\Big\|^2 \le 2\Big(\mathbb{E}\Big\|\sum_i x_i w_i\Big\|\Big)^2,$$

i.e. $\mathbb{E}\|\sum_i x_i w_i\| \ge \frac{1}{\sqrt 2}\big(\mathbb{E}\|\sum_i x_iw_i\|^2\big)^{1/2}$, and the constant $2$ is optimal already for $n = 2$ in $\mathbb{R}$.

## Proof sketch

Let $g(x) = \|\sum_i x_i w_i\|$. The Laplacian bound $Lg \le g$ (each coordinate contributes $g(x) - \|\sum_{j \ne i} x_j w_j\| \le$ its share) gives $\mathbf{I}[g] \le \mathbb{E}[g^2]$-type control and, since $g$ is even, $2\mathrm{Var}[g] \le \mathbf{I}[g] \le \mathbb{E}[g^2]$, which rearranges to $\mathbb{E}[g^2] \le 2(\mathbb{E} g)^2$. For $w = (1, 1)$ in $\mathbb{R}$, $\mathbb{E}|x_1 + x_2|^2 = 2$ and $\mathbb{E}|x_1 + x_2| = 1$.

## Depends on

- [Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-cube.md)
- [Total influence on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence.md)
- [Variance on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-variance.md)

## Proof depends on

- [Poincaré inequality on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-variance-le-bool-total-influence.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
- R. Latała and K. Oleszkiewicz, "On the Best Constant in the Khinchin-Kahane Inequality", Studia Mathematica 109(1), 1994.
