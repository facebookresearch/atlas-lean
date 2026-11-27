# Khintchine–Kahane inequality with the optimal constant

For vectors $w_1, \dots, w_n$ in a (semi)normed real vector space and independent uniform signs $x_i$,

$$\mathbb{E}\Big\|\sum_i x_i w_i\Big\|^2 \le 2\Big(\mathbb{E}\Big\|\sum_i x_i w_i\Big\|\Big)^2,$$

i.e. $\mathbb{E}\|\sum_i x_i w_i\| \ge \frac{1}{\sqrt 2}\big(\mathbb{E}\|\sum_i x_iw_i\|^2\big)^{1/2}$, and the constant $2$ is optimal already for $n = 2$ in $\mathbb{R}$.

## Proof sketch

Let $g(x) = \|\sum_i x_i w_i\|$ and $v = \sum_i x_i w_i$. Flipping $x_i$ gives $v - 2x_iw_i$, and the triangle inequality gives $\sum_i\|v - 2x_iw_i\| \ge \|(n - 2)v\|$; for $n \ge 2$ this says $Lg = \sum_i \frac{g - g(x^{\oplus i})}{2} \le g$ pointwise, and for $n \le 1$ it is immediate (O'Donnell, Ex. 2.55). Hence $\mathbf{I}[g] = \mathbb{E}[g\,Lg] \le \mathbb{E}[g^2]$. Since $g$ is even, $\hat g(S) = 0$ for odd $|S|$, so $\mathbf{I}[g] = \sum_S |S|\hat g(S)^2 \ge 2\mathrm{Var}[g]$. Thus $2\mathrm{Var}[g] \le \mathbb{E}[g^2]$, which rearranges to $\mathbb{E}[g^2] \le 2(\mathbb{E} g)^2$. For $w = (1, 1)$ in $\mathbb{R}$, $\mathbb{E}|x_1 + x_2|^2 = 2$ and $\mathbb{E}|x_1 + x_2| = 1$.

## Depends on

- [Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-cube.md)

## Proof depends on

- [Total influence on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence.md)
- [Variance on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-variance.md)
- [Total influence in Fourier form](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence-eq-sum-card-mul-sq.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
- R. Latała and K. Oleszkiewicz, "On the Best Constant in the Khinchin-Kahane Inequality", Studia Mathematica 109(1), 1994.
