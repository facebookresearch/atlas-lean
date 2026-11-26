# Minimal Colless trees have minimum Sackin index

The **Sackin index** of a rooted tree $T$ is the sum of the depths $\delta_T(x)$ of its leaves, equivalently the sum of the numbers of descendant leaves of its internal nodes:

$$S(T) = \sum_{x \text{ leaf}} \delta_T(x) = \sum_{v \in \mathring V(T)} \kappa_T(v).$$

**Lemma (characterization of Sackin-minimal trees, due to Fischer and quoted in the source).** Let $T = (T_a, T_b)$ be bifurcating with $n \ge 2$ leaves, $n_a \ge n_b$, and $k_n = \lceil \log_2 n \rceil$. Then $T$ has minimum Sackin index among bifurcating trees with $n$ leaves if and only if $T_a$ and $T_b$ have minimum Sackin index and $n_a - n_b \le \min\{n - 2^{k_n - 1},\ 2^{k_n} - n\}$.

**Proposition.** For every $n \ge 1$, every bifurcating tree with $n$ leaves that attains the [minimum Colless index](minimum-colless-index.md) also attains the minimum Sackin index. The converse fails: some Sackin-minimal trees are not Colless-minimal, so the Colless index is the finer of the two as a criterion for "most balanced".

## Depends on

- [Minimum Colless index](minimum-colless-index.md)

## Proof depends on

- [Characterization of minimal Colless trees](characterization-of-minimal-colless-trees.md)

## Expansion

Induction on $n$. Pending subtrees of a minimal Colless tree are minimal Colless, hence Sackin-minimal by the induction hypothesis. Writing $n = 2^m + p$ with $0 \le p < 2^m$, the case $p = 0$ is the fully symmetric tree. For $p > 0$ the explicit description of the admissible root splits $QB(n)$ shows that every $(n_a, n_b) \in QB(n)$ satisfies $n_a - n_b \le \min\{p, 2^m - p\}$, which is the lemma's bound since $k_n = m + 1$.

## Sources

- T. M. Coronado, M. Fischer, L. Herbst, F. Rosselló and K. Wicke, "On the minimum value of the Colless index and the bifurcating trees that achieve it", *Journal of Mathematical Biology* (2020), <https://doi.org/10.1007/s00285-020-01488-9> (Lemma 6 and Proposition 9; numbering as in the arXiv version 1907.05064v2).
