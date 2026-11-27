# The weakly correlated moment bound is sharp up to a logarithm

In the regime $p \le n$, the moment inequality for weakly correlated sums cannot be improved beyond the $\log n$ factor using only the parameters $M$, $\beta$, $n$ and $p$ (Bousquet, Klochkov and Zhivotovskiy, Proposition 9): there is an absolute constant $\kappa > 0$ such that for all $n$ and $\beta, M \ge 0$ there are i.i.d. Rademacher signs $Z_1, \dots, Z_n$ and functions $g_1, \dots, g_n : \{-1, 1\}^n \to \mathbb{R}$ satisfying the three hypotheses of *Moment inequality for sums of weakly correlated functions* (conditional bound $M$, conditional mean zero given the other coordinates, bounded differences $\beta$ off the diagonal) with

$$
\Big\| \sum_{i=1}^n g_i(Z) \Big\|_p \gtrsim p n \beta + M\sqrt{pn} \qquad \text{for every } \kappa \le p \le n .
$$

The sharpness is a statement about the auxiliary moment inequality only. It does not show that the high-probability generalization bound for uniformly stable algorithms is optimal: the construction has $|g_i|$ as large as $M + \beta(n-1)/2$, whereas the functions arising from a uniformly stable learner with bounded loss are uniformly bounded, and the source leaves open whether a matching lower bound holds for learning algorithms.

## Proof sketch

Following Appendix B of the source, take $g_i(Z) = M Z_i + \frac{\beta}{2} Z_i \sum_{j \ne i} Z_j$. Then $\mathbb{E}[g_i \mid Z_{[n]\setminus\{i\}}] = 0$, $\mathbb{E}[g_i \mid Z_i] = M Z_i$ (so $|\mathbb{E}[g_i \mid Z_i]| = M$), and $g_i$ has bounded differences $\beta$ in every coordinate other than the $i$-th. With $S = \sum_i Z_i$, $\sum_i g_i = M S + \frac{\beta}{2} S^2 - \frac{\beta}{2} n$, so by the triangle inequality $\|\sum_i g_i\|_p \ge \|M S + \frac{\beta}{2}S^2\|_p - \frac{\beta}{2}n$. Restricting to $S_+ = S\,\mathbf{1}[S \ge 0]$ and applying Chebyshev's association inequality gives $\|M S_+ + \frac{\beta}{2}S_+^2\|_p \ge \|S_+\|_p \big(M \vee \frac{\beta}{2}\|S_+\|_p\big)$. Hitczenko's moment estimate for weighted Rademacher sums gives $\|S_+\|_p \ge \frac12\|S\|_p \gtrsim \sqrt{pn}$ for $p \le n$, so $\|\sum_i g_i\|_p \ge c\sqrt{pn}\big(M + \frac{c\beta}{2}\sqrt{pn}\big) - \frac{\beta}{2}n$ for an absolute $c > 0$, which is $\gtrsim pn\beta + M\sqrt{pn}$ once $p \ge \kappa$ for a suitable absolute constant $\kappa$.

## Depends on

- [Uniform stability](../is-uniformly-stable.md)
- [Moment inequality for sums of weakly correlated functions](weakly-correlated-sum-moment-inequality.md)

## Sources

- O. Bousquet, Y. Klochkov, N. Zhivotovskiy, "Sharper Bounds for Uniformly Stable Algorithms", COLT (2020), arXiv:1910.07833.
