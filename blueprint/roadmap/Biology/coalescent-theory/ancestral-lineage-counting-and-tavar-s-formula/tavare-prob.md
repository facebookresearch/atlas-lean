# Tavaré's formula for the number of ancestral lineages

For natural numbers $i$ and $j$ and a real number $t$, let

$$q_{ij}(t) = \sum_{k=j}^{i} e^{-k(k-1)t/2}\, \frac{(2k-1)(-1)^{k-j}\, j^{\overline{k-1}}\, i^{\underline{k}}}{j!\,(k-j)!\, i^{\overline{k}}},$$

where $a^{\overline{m}} = a(a+1)\cdots(a+m-1)$ is the rising factorial, $a^{\underline{m}} = a(a-1)\cdots(a-m+1)$ the falling factorial, the exponent $k - 1$ of the rising factorial is read as $0$ when $k = 0$, division by $0$ gives $0$, and the sum is $0$ when $j > i$. For $t \ge 0$ and $1 \le j \le i$, this is Tavaré's closed form for the probability that $i$ lineages of Kingman's coalescent have $j$ ancestors $t$ time units (of $2N$ generations each) earlier; see [Tavaré's formula](exp-block-counting-generator-apply.md).
