# Packing lower bound for pure differential privacy

Let $M$ be $\varepsilon$-differentially private, and let $d_0, d_1, \dots, d_N$ be datasets, each $d_i$ joined to $d_0$ by a chain $d_i = z_0, z_1, \dots, z_k = d_0$ of exactly $k$ steps in which consecutive datasets are neighbours. Suppose that $M(d_0)$ is a probability measure and that $S_1, \dots, S_N$ are pairwise disjoint measurable sets of outputs with $M(d_i)(S_i) \ge 1/2$ for every $i \ge 1$. Then $N \le 2 e^{\varepsilon k}$. Consequently, for $\varepsilon > 0$, a pure differentially private mechanism whose outputs distinguish $N$ such datasets requires $k \ge \ln(N/2)/\varepsilon$.

The neighbouring relation is arbitrary. For a reflexive one, such as databases that differ in at most one row or histograms at $\ell_1$ distance at most $1$, the datasets joined to $d_0$ by such a chain are those at distance at most $k$ from $d_0$, since a shorter chain is padded by repeating a dataset; for other relations the chain must have exactly $k$ steps.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Section 8.2.1, Lemma 8.4, which states the bound for $2^s$ histograms at pairwise $\ell_1$ distance at most $\Delta$ as $\varepsilon \ge \ln(2)(s-1)/\Delta$
- M. Hardt and K. Talwar, "On the geometry of differential privacy", *Proceedings of the 42nd ACM STOC*, 2010, arXiv:0907.3754v3, proof of Theorem 3.3
