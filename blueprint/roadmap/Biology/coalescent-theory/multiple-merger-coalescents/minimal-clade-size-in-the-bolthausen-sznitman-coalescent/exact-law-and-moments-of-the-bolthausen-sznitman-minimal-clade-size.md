# Exact law and moments of the Bolthausen–Sznitman minimal clade size

Let $X_n$ be the [minimal clade size](minimal-clade-size-is-a-uniform-chinese-restaurant-table.md) of a uniformly chosen individual in the Bolthausen–Sznitman $n$-coalescent, $n \ge 2$. For $m \ge 1$ let $K_m$ be the number of occupied tables of a $\mathrm{CRP}(m)$, and set $K_0 = 0$.

**Lemma (Freund–Siri-Jégousse, representation (c)).** Let $B_1, B_2, \dots$ be independent Bernoulli variables with $P(B_i = 1) = 1/i$. For $j \in \{1,\dots,n-1\}$,

$$P(X_n = j+1) = \frac{1}{j}\, E\Big(\frac{1}{1 + K_{n-1-j}}\Big) = \frac{1}{j}\, E\Big(\frac{1}{1 + \sum_{i=1}^{n-1-j} B_i}\Big).$$

In particular $P(X_n = n) = 1/(n-1)$. Equivalently, with $\Delta(m,k)$ the compositions $(n_1,\dots,n_k)$ of $m$ into $k$ positive parts, for $1 \le j < n-1$

$$P(X_n = j+1) = \frac{1}{j} \sum_{k=1}^{n-1-j} \frac{1}{(k+1)!} \sum_{\Delta(n-1-j,k)} \frac{1}{n_1 \cdots n_k}.$$

**Theorem (Freund–Siri-Jégousse, moment asymptotics).** For every integer $k \ge 1$,

$$\frac{\log n}{n^k}\, E\big(X_n^k\big) \longrightarrow \frac{1}{k} \qquad (n \to \infty).$$

So $X_n$ is heavy-tailed on the scale of the sample: although $\log X_n/\log n$ is asymptotically uniform, the mean minimal clade size is of order $n/\log n$.

## Depends on

- [Minimal clade size is a uniform Chinese restaurant table](minimal-clade-size-is-a-uniform-chinese-restaurant-table.md)

## Expansion

Since $X_n - 1$ is a uniformly chosen table of a $\mathrm{CRP}(n-1)$, $P(X_n = j+1) = E(A^{(n-1)}_j / K_{n-1})$ where $A^{(n-1)}_j$ counts tables with $j$ customers. Fixing one table of size $j$ and seating the remaining $n-1-j$ customers exchangeably gives the factor $1/j$ times $E(1/(1+K_{n-1-j}))$. The number of cycles of a uniform permutation of $m$ elements is a sum of independent Bernoulli$(1/i)$ variables, $i = 1,\dots,m$ (Feller coupling), which gives the second expression and an efficient recursion. For the moments, $\frac{\log n}{1 + K_n} \to 1$ in $L^1$, so $P(X_n = j+1) \approx \frac{1}{j \log(n-j)}$, and summing $j^k \cdot \frac{1}{j\log n}$ over $j \le n$ gives $\frac{n^k}{k \log n}$.

## Sources

- F. Freund and A. Siri-Jégousse, *Minimal clade size in the Bolthausen–Sznitman coalescent*, *Journal of Applied Probability* 51 (2014), 657–668, <https://doi.org/10.1239/jap/1409932665>; preprint arXiv:1301.2908, <https://doi.org/10.48550/arXiv.1301.2908>.
