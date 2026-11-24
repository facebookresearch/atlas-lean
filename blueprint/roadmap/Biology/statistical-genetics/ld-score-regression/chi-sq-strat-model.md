# Association statistic of the product-space model written out

For a probability measure $\nu$ on $\mathbb{R}$ satisfying the
[bounded unit law](is-bounded-unit-law.md) condition with bound $C$, $h^2 \in [0, 1]$, natural
numbers $N$ and $M$, a real $N \times M$ matrix $X$, a marker $j$ and
$\omega \in \mathbb{R}^{\mathbb{N}}$, the
[association statistic under stratification](chi-sq-strat.md) of the
[model on the product space](model-2.md) without stratification ($s = 0$, $c = 0$) is

$$
\chi^2_j(\omega) = \frac{1}{N} \Bigl(\sum_{i} X_{ij}\, y_i(\omega)\Bigr)^2, \qquad
y_i(\omega) = \sum_{k} X_{ik} \sqrt{h^2 / M}\, \omega_{2k} + \sqrt{1 - h^2}\, \omega_{2i+1},
$$

with the convention $x/0 = 0$ for $N = 0$.
