# The weakly correlated moment bound is sharp up to a logarithm

The moment inequality for weakly correlated sums cannot be improved beyond the $\log n$ factor without further assumptions: for all $n$, $p \ge 2$ and $\beta, M > 0$ there are independent $Z_1, \dots, Z_n$ and functions $g_1, \dots, g_n$ satisfying the three hypotheses (conditional bound $M$, conditional mean zero given the other coordinates, bounded differences $\beta$ off the diagonal) with

$$
\Big\| \sum_{i=1}^n g_i(Z) \Big\|_p \gtrsim p n \beta + M\sqrt{pn}.
$$

Correspondingly, the high-probability generalization bound for uniformly stable algorithms is optimal up to the $\log n$ factor among bounds that use only uniform stability and boundedness of the loss.

## Proof sketch

For the $M\sqrt{pn}$ term take $g_i$ depending only on $Z_i$, which reduces to sums of independent bounded centred variables whose $p$-th moments grow like $\sqrt{pn}$ (Khintchine). For the $pn\beta$ term take Rademacher variables $Z_i$ and $g_i(Z) = \beta Z_i \sum_{j < i} Z_j$, which is centred given the other coordinates and has off-diagonal bounded differences of order $\beta$; the sum is a decoupled degree-two Rademacher chaos with variance of order $n^2\beta^2$ whose $p$-th moment grows linearly in $p$ by hypercontractivity, giving the $pn\beta$ lower bound.

## Depends on

- [Uniform stability](../algorithmic-stability/is-uniformly-stable.md)

## Proof depends on

- [Moment inequality for sums of weakly correlated functions](weakly-correlated-sum-moment-inequality.md)

## Sources

- O. Bousquet, Y. Klochkov, N. Zhivotovskiy, "Sharper Bounds for Uniformly Stable Algorithms", COLT (2020), arXiv:1910.07833.
