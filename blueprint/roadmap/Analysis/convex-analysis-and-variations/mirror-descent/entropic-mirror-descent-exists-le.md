# Rate of entropic mirror descent on the simplex

Let $n \ge 2$, $L > 0$ and $N \ge 1$. Run mirror descent with the entropy setup on the [simplex](simplex.md) $\Delta_n$, starting from the [uniform point](uniform.md), with the constant step $\gamma = \sqrt{2\log n} / (L\sqrt{N})$: the iterates $x_t$ lie in the [relative interior](pos-simplex.md) and satisfy the prox optimality conditions for all $u \in \Delta_n$ (for instance they are the [multiplicative-weights updates](entropy-prox-multiplicative.md)), and $g_t$ is a subgradient of $f$ at $x_t$ relative to $\Delta_n$ with $\|g_t\|_* \le L$ (for instance $|g_t(e_i)| \le L$ for all $i$, by the [coordinate bound](norm-le-of-abs-apply-single-le.md)). Then for every $x^\star \in \Delta_n$ some iterate $t < N$ satisfies

$$
f(x_t) - f(x^\star) \le \frac{L \sqrt{2 \log n}}{\sqrt{N}} .
$$

Measured with $\ell_\infty$ bounds on the subgradients, the dimension enters only through $\sqrt{\log n}$, whereas the same $\ell_\infty$ bound only gives $\|g_t\|_2 \le \sqrt{n}\,L$ for the Euclidean setup; this is the point of non-Euclidean proximal setups for large-scale problems.

## Background

- [The $\sqrt{T}$ regret bound of Hedge](../../../ComputerScience/machine-learning/online-learning-and-boosting/hedge-algorithm/regret-le-two-sqrt.md): the same update run online, with regret $2\sqrt{T \log n}$ for losses in $[0, 1]$, proved there by the potential argument.

## Sources

- A. Juditsky and A. Nemirovski, *First order methods for nonsmooth convex large-scale optimization, I: general purpose methods*, in S. Sra, S. Nowozin and S. J. Wright (eds.), *Optimization for Machine Learning*, MIT Press (2011); author PDF at <https://www2.isye.gatech.edu/~nemirovs/MLOptChapterI.pdf>, Section 5.2.3, Proposition 5.1(ii), (5.11), in the entropy setup 2(c) of Section 5.7.1, and Section 5.7.1 (comparison of the Euclidean and $\ell_1$ setups).
- A. Nemirovski, A. Juditsky, G. Lan and A. Shapiro, *Robust stochastic approximation approach to stochastic programming*, SIAM J. Optim. 19(4) (2009), 1574–1609; PDF at <https://people.eecs.berkeley.edu/~brecht/cs294docs/week1/09.Nemirovski.pdf>, Section 2.3, Example ($\Omega = D_{\omega,X}^2 = \ln n$, $\alpha = 1$).
