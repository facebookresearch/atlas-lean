# List sizes inversely proportional to a random rank have average O(log^2 n)

Let $G$ be an $n$-vertex graph, let $\pi : V \to \{1, \dots, n\}$ be a uniformly random bijection, and set

$$
\ell(v) = \min\Big(\deg(v) + 1, \; \Big\lceil \frac{40\, n \ln n}{\pi(v)} \Big\rceil\Big).
$$

Then deterministically $\sum_{v \in V} \ell(v) = O(n\log^2 n)$, and for all distinct $u, v \in V$,

$$
\mathbb{E}[\ell(v)] = O(\log^2 n), \qquad \mathbb{E}[\ell(u)\,\ell(v)] = O(\log^4 n).
$$

## Proof sketch

Since $\pi$ is a bijection, $\sum_v \ell(v) \le n + \sum_{i=1}^{n} 40 n\ln n / i = O(n\log^2 n)$ by the harmonic sum, and the distribution of $\ell(v)$ is the same for every $v$, giving the expectation. For the product, $\Pr[\pi(v) = i, \pi(u) = j] = 1/(n(n-1))$ for $i \ne j$, so $\mathbb{E}[\ell(u)\ell(v)] \le O(1) + \frac{(40 n \ln n)^2}{n(n-1)}\sum_{i \ne j}\frac{O(1)}{ij} = O(\log^4 n)$, again by the harmonic sum.

## Sources

- Sepehr Assadi, Helia Yazdanyar, "Simple Sublinear Algorithms for (Delta+1) Vertex Coloring via Asymmetric Palette Sparsification", SOSA (2025), arXiv:2502.17629.
