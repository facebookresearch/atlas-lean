# Constant-step rate of mirror descent

In the setting of the [best-iterate rate](mirror-descent-exists-le.md) with $L > 0$, let $\Omega > 0$ bound $V_{x_0}(x^\star)$ (for instance the $\omega$-diameter $\max_{u \in X} V_{x_0}(u)$ when $x_0$ minimizes $\omega$ on $X$), and run $N \ge 1$ steps with the constant step $\gamma = \sqrt{2\alpha\Omega} / (L\sqrt{N})$. Then some iterate $t < N$ satisfies

$$
f(x_t) - f(x^\star) \le \frac{L\sqrt{2\Omega}}{\sqrt{\alpha N}} .
$$

With $\alpha = 1$ this is the efficiency estimate $\sqrt{2\Omega}\, L / \sqrt{N}$ of mirror descent. The dimension enters only through $\Omega$ and the norm in which $L$ is measured: the Euclidean setup gives the subgradient method's rate, while on the simplex the [entropy setup](entropic-mirror-descent-exists-le.md) has $\Omega \le \log n$ and measures $L$ in $\|\cdot\|_\infty$. This rate is nearly optimal in the large-scale regime: for convex functions $L$-Lipschitz with respect to $\|\cdot\|_p$, $p \in \{1, 2\}$, on the radius-$R$ ball of $\|\cdot\|_p$ in $\mathbb{R}^n$, every black-box first-order method needs at least of order $\min[n, L^2R^2/\epsilon^2]$ steps to reach accuracy $\epsilon$ on the whole class (Nemirovski and Yudin, 1983), while mirror descent with the Euclidean or the $\ell_1$ setup needs $O((\ln n)^{2/p - 1} L^2R^2/\epsilon^2)$.

## Background

- [Convergence of the subgradient method](../gradient-descent/subgradient-method-rate.md): the Euclidean case with decreasing steps $\propto 1/\sqrt{k+1}$, which loses a $\log t$ factor that the horizon-dependent constant step avoids.

## Sources

- A. Juditsky and A. Nemirovski, *First order methods for nonsmooth convex large-scale optimization, I: general purpose methods*, in S. Sra, S. Nowozin and S. J. Wright (eds.), *Optimization for Machine Learning*, MIT Press (2011); author PDF at <https://www2.isye.gatech.edu/~nemirovs/MLOptChapterI.pdf>, Section 5.2.3, Proposition 5.1(ii), (5.10)–(5.11), with $\alpha = 1$; the source also certifies the accuracy by an online lower bound $f_N \le \mathrm{Opt}$, not formalized here.
- A. Juditsky and A. Nemirovski, *First order methods for nonsmooth convex large-scale optimization, I: general purpose methods*, in S. Sra, S. Nowozin and S. J. Wright (eds.), *Optimization for Machine Learning*, MIT Press (2011); author PDF at <https://www2.isye.gatech.edu/~nemirovs/MLOptChapterI.pdf>, Section 5.1, example (a), for the lower complexity bound.
