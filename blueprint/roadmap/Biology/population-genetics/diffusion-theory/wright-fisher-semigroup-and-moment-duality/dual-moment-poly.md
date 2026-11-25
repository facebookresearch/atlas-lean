# Dual moment polynomial of Kingman's coalescent

For a real number $t$ and a natural number $n$, the polynomial

$$D_{t,n}(X) = \sum_{k=0}^{n} \bigl(e^{t G_n}\bigr)(n, k)\, X^k,$$

where $G_n$ is the [generator of Kingman's block-counting process](../../../coalescent-theory/ancestral-lineage-counting-and-tavar-s-formula/block-counting-generator.md). For $t \ge 0$, $(e^{t G_n})(n, k)$ is the probability that $n$ lineages of Kingman's coalescent have $k$ ancestors a time $t$ earlier (in units of $M = 2N$ generations), so $D_{t,n}(x)$ is the expectation of $x^{A_t}$ for the block-counting process $A$ started at $n$.
