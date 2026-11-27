# Andoni-Krauthgamer-Razenshteyn: efficient sketching of norms is equivalent to embedding into l_{1-eps}

For a finite-dimensional normed space $X$ and $D > 1$, a *sketching scheme of size $s$ for the distance threshold estimation problem with approximation $D$* consists of public randomness, a map $\mathrm{sk} : X \to \{0,1\}^{s}$ and a decision rule which, for all $x, y \in X$, outputs "close" with probability at least $2/3$ when $\|x - y\| \le 1$ and "far" with probability at least $2/3$ when $\|x - y\| > D$, looking only at $\mathrm{sk}(x)$ and $\mathrm{sk}(y)$.

1. If $X$ admits such a scheme, then for every $0 < \varepsilon < 1/3$, $X$ embeds linearly into $\ell_{1-\varepsilon}$ with distortion $O(sD/\varepsilon)$, and it embeds linearly into $\ell_1$ with distortion $O(sD\log(\dim X))$.
2. Conversely, a linear embedding into $\ell_{1-\varepsilon}$ with distortion $D'$ yields a sketching scheme of size $O_{\varepsilon, D'}(1)$ with approximation $O(D')$, by sketching with $(1-\varepsilon)$-stable random projections.

Hence a family of norms admits sketches with $s, D = O(1)$ if and only if it embeds into $\ell_{1-\varepsilon}$ with distortion $O(1)$; with known non-embeddability results this rules out constant-size, constant-approximation sketches for the Earth Mover's Distance norm and the trace norm.

## Proof sketch

The information-theoretic part converts a sketch into a statement about one-way communication of threshold estimation, then into the absence of certain combinatorial obstructions to embeddings of the norm into $\ell_{1-\varepsilon}$. The analytic part uses classical results on uniform embeddings of normed spaces into Hilbert space and on factorization through $L_{1-\varepsilon}$ to upgrade this to a linear embedding, and the $\ell_1$ statement follows with a $\log(\dim X)$ loss. The converse uses Indyk's stable-distribution sketches.

## Depends on

- [Distortion of a metric embedding and the Euclidean dimension-reduction function](bi-lipschitz-distortion-of-metric-embeddings.md)
- [Stable distribution of a given index](../../../../Probability/infinite-divisibility-regular-variation/stable-distributions-and-domains-of-attraction/is-stable.md)

## Proof depends on

- [Yao's minimax principle](../../../../TheoryOfComputation/randomized-and-quantum-complexity/yao-s-minimax-principle/yao-minimax.md)

## Sources

- Alexandr Andoni, Robert Krauthgamer, Ilya Razenshteyn, "Sketching and Embedding are Equivalent for Norms", STOC (2015); SIAM J. Comput. 47 (2018), arXiv:1411.2577.
- Piotr Indyk, "Stable distributions, pseudorandom generators, embeddings, and data stream computation", J. ACM 53 (2006).
