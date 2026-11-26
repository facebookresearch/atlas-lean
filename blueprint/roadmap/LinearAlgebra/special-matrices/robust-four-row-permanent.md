# A robust four-row permanent inequality

Let $I=\{0,1,2,3\}$ and let $u$ assign mass $1/24$ to each permutation of $I$. There exist real numbers $4/3<p<2$ and $\varepsilon>0$ such that the following holds for every law $\nu$ on the permutations of $I$. Assume that $\nu(\pi)\ge0$, $\sum_\pi\nu(\pi)=1$, $\tfrac12\sum_\pi|\nu(\pi)-1/24|<\varepsilon$, and $\sum_{\pi:\pi(i)=j}\nu(\pi)=1/4$ for every $i,j\in I$. Then every matrix $f:I\times I\to[0,\infty)$ satisfies

$$
\sum_{\pi}\nu(\pi)\prod_{i\in I} f(i,\pi(i))\;\le\;\prod_{i\in I}\left(\frac14\sum_{j\in I} f(i,j)^p\right)^{1/p}.
$$

The constants are uniform over both the law and the matrix. At $\nu=u$ the left-hand side is the matrix permanent divided by $24$; it is a weighted permutation average for general $\nu$. No mixing claim is included.

The probability mass function on the finite permutation group, its finite total-variation distance from $u$, and the normalized row power mean are given by the sums above.

## Depends on

- [Weighted permutation averages and four-row power means](weighted-four-row-permutation-average.md)

## Expansion

Normalize each nonzero row by $\sum_j f(i,j)^2=4$ and put $D=\sum_{i,j}(f(i,j)-1)^2$. The uniform permutation average is at most $1-D/1728$; the increase under $\nu$ is at most $6\,d_{\mathrm{TV}}(\nu,u)D$ when the marginals are uniform. For $9/5\le p\le2$, the product of row norms is at least $1-5(2-p)D/8$.

Separate these three quantitative inequalities for normalized rows. The marginal constraints cancel the linear part of the product perturbation, so the perturbation bound must vanish quadratically at constant rows. Combine the bounds with, for example, $p=2-10^{-5}$ and $\varepsilon=10^{-5}$, handle zero rows separately, and remove the normalization by homogeneity.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/FourRowPermanent.lean#L37-L44)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/238.md)
- [Accompanying manuscript: A strict four-row permanent inequality and permutation moments](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-strict-four-row-permanent-inequality-and-permutation-moments-September-26-2026/main.pdf)
