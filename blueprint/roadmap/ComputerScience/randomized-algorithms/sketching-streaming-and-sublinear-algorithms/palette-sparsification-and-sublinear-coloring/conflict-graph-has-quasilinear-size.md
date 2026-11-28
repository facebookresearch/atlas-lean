# The conflict graph of palette sparsification has O(n log^2 n) edges

In the palette sparsification experiment with $\Pi(v) = \{1, \dots, \Delta + 1\}$ and $\ell(v) = k$ for all $v$, where $1 \le k \le \Delta + 1$, every edge $\{u, v\}$ satisfies $\Pr[L(u) \cap L(v) \ne \emptyset] \le k^2/(\Delta + 1)$, so

$$
\mathbb{E}\,|E(G_L)| \le |E|\,\frac{k^2}{\Delta + 1} < \frac{n k^2}{2}.
$$

Moreover, for $k = \lceil C \log n \rceil$ and every $c > 0$, with probability at least $1 - n^{-c}$ every vertex has degree $O(\log^2 n)$ in $G_L$, so $|E(G_L)| = O(n\log^2 n)$, with constants depending on $C$ and $c$.

## Proof sketch

Each of the $k$ colors of $L(u)$ lies in $L(v)$ with probability $k/(\Delta + 1)$, so the union bound gives the first inequality, and $|E| \le n\Delta/2$ gives the expectation; the last inequality is strict because $\Delta/(\Delta + 1) < 1$ and $k \ge 1$ (at $k = 0$ both sides would be $0$). Conditioned on $L(v)$, the indicators that $v$'s neighbors sample a color of $L(v)$ are independent, each with probability at most $k^2/(\Delta + 1)$, so $\deg_{G_L}(v)$ is a sum of at most $\Delta$ independent indicators with mean less than $k^2$; a multiplicative Chernoff bound gives $\deg_{G_L}(v) = O(k^2 + \log n)$ with probability $1 - n^{-c-1}$, and a union bound over $v$ finishes.

## Depends on

- [Palette sparsification experiment, sampled lists and the conflict graph](palette-sparsification-experiment.md)

## Proof depends on

- [Multiplicative Chernoff bounds for independent [0,1]-valued scores](../../../../Probability/concentration-inequalities/chernoff-and-bernoulli-comparison-bounds/multiplicative-chernoff-bounds.md)

## Sources

- Sepehr Assadi, Yu Chen, Sanjeev Khanna, "Sublinear Algorithms for (Delta + 1) Vertex Coloring", SODA (2019), arXiv:1807.08886, Lemma 4.1.
- Sepehr Assadi, Helia Yazdanyar, "Simple Sublinear Algorithms for (Delta+1) Vertex Coloring via Asymmetric Palette Sparsification", SOSA (2025); TheoretiCS 5 (2026), Article 3, arXiv:2502.17629.
