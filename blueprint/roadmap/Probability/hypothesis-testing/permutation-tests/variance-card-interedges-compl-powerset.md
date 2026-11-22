# Variance of the edge cut of a uniform $t$-subset

Let $G$ be a simple graph on a finite vertex set $V$ with $n \ge 4$ vertices and $M$ edges, let $S_2 = \sum_v \deg(v)^2$ and $1 \le t < n$. Put

$$a = \frac{2t(n - t)}{n(n - 1)}, \qquad b = \frac{4t(t - 1)(n - t)(n - t - 1)}{n(n - 1)(n - 2)(n - 3)}.$$

For $S$ uniform among the $t$-subsets of $V$, the population variance of the cut size $R(S) = e(S, S^c)$, that is, the average of $(R(S) - \bar R)^2$ with $\bar R$ the average of $R$, is

$$b\,M + \Big(\frac{a}{2} - b\Big) S_2 + (b - a^2)\, M^2.$$

It is not a sample variance, and it can be $0$ (for example for the complete graph); no positivity is asserted.
