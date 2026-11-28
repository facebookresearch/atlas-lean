# Central limit theorem for the (n-2)- and (n-3)-RF distances

A *Cayley tree on $[n]$* is a tree with vertex set $[n] = \{1, \dots, n\}$; there are $n^{n-2}$ of them. For $k \in \{0, \dots, n-2\}$, the *$k$-local split* of a tree $T$ at edge $e = \{u, v\}$ is the pair $A \mid B$, where $A$ (resp. $B$) is the set of vertices of $T \setminus e$ within distance $k$ of $u$ (resp. $v$). The *$k$-RF distance* is

$$d_{k\text{-RF}}(T, T') = 2(n-1) - 2S_k(T, T'),$$

where $S_k(T, T')$ is the number of $k$-local splits shared by $T$ and $T'$; it is a metric. A $0$-local split is an edge, and an $(n-2)$-local split is an ordinary split (bipartition obtained by deleting an edge). Throughout, $\mathcal T, \mathcal T'$ are independent uniform random Cayley trees on $[n]$.

**Theorem.** Let $S_n$ be the number of $(n-2)$-local splits shared by $\mathcal T$ and $\mathcal T'$. Then $\mathbb E(S_n) \sim n e^{-2}$, $\mathrm{Var}(S_n) \sim n(e^{-2} - 3e^{-4})$, and

$$\frac{S_n - n e^{-2}}{\sqrt{(e^{-2} - 3e^{-4})n}} \xrightarrow{d} N(0, 1).$$

Equivalently,

$$\frac{d_{(n-2)\text{-RF}}(\mathcal T, \mathcal T') - 2n(1 - e^{-2})}{2\sqrt{(e^{-2} - 3e^{-4})n}} \xrightarrow{d} N(0,1).$$

For the number $\tilde S_n$ of shared splits with a single leaf on one side, $\mathbb E\big(\tilde S_n(\tilde S_n - 1)\cdots(\tilde S_n - k + 1)\big) = k!\binom nk\big(1 - \tfrac kn\big)^{2n-4}$, with the same mean and variance asymptotics.

**Theorem.** The number $U_n$ of shared $(n-3)$-local splits satisfies $\mathbb E|S_n - U_n| = o(1)$, so the same normal limit holds for $U_n$ and for $d_{(n-3)\text{-RF}}(\mathcal T, \mathcal T')$.

## Expansion

Almost all shared splits are trivial ones that cut off a single leaf: a vertex is a leaf of a uniform Cayley tree with probability $(1 - 1/n)^{n-2} \to e^{-1}$, so it is a leaf of both trees with probability about $e^{-2}$, which explains the mean $ne^{-2}$. Shared splits with two vertices on the smaller side contribute about $2e^{-4}$ in expectation and larger ones vanish, so they do not affect the normal limit. The factorial-moment formula for $\tilde S_n$ comes from counting trees in which $k$ given vertices are leaves, and the CLT follows by showing that the normalized central moments of $\tilde S_n$ converge to those of the standard normal. The $(n-3)$-local splits consist of the $(n-2)$-local splits together with splits $A \mid B$ in which $A$ is a singleton and $B$ omits one further vertex, and these extra shared splits have vanishing expected count.

## Sources

- M. Fuchs and M. Steel, "The asymptotic distribution of the k-Robinson-Foulds dissimilarity measure on labelled trees", *Journal of Computational Biology* 32(11) (2025), 1060–1073, Proposition 1, Theorem 2, Corollary 4, Lemma 12 and Theorem 13, <https://doi.org/10.1089/cmb.2025.0093> (preprint arXiv:2412.20012).