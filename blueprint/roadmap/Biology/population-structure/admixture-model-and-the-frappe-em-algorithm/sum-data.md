# Sum over allele-copy data as a triple sum

Let $I$ and $J$ be finite and $g$ a genotype matrix with entries in $\{0, 1, 2\}$. For every real function $f$ of observations,

$$\sum_{n=0}^{N-1} f(x_n) = \sum_{i \in I} \sum_{j \in J} \sum_{c \in \{0, 1\}} f\bigl(o_g(i, j, c)\bigr),$$

where $x_0, \dots, x_{N-1}$ is the [allele-copy data](data.md) of $g$ and $o_g(i, j, c)$ the [observation of copy $c$](copy-allele.md).
