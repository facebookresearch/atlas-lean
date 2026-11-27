# Cayley graphs of the Boolean cube with small-bias generators are expanders

Let $s_1, \dots, s_d \in \mathbb{F}_2^\ell$, $d \ge 1$, and let the Cayley graph be the $d$-regular multigraph on $\mathbb{F}_2^\ell$ whose $j$-th edge joins $u$ to $u + s_j$. Suppose the uniform distribution on $\{s_1, \dots, s_d\}$ is $\varepsilon$-biased, $\varepsilon \ge 0$: $\bigl|\frac1d \sum_j (-1)^{\langle a, s_j\rangle}\bigr| \le \varepsilon$ for every nonzero $a \in \mathbb{F}_2^\ell$. Then the walk operator is diagonal in the character basis, multiplying the Fourier coefficient at $a$ by $\frac1d \sum_j (-1)^{\langle a, s_j \rangle}$, and the spectral expansion is at most $\varepsilon$. Hence for all $S, T \subseteq \mathbb{F}_2^\ell$ the edge count satisfies the expander mixing bound with $\lambda = \varepsilon$.

## Proof sketch

Translating by $s_j$ multiplies the character $\chi_a$ by $\chi_a(s_j)$, so each character is an eigenvector with eigenvalue the bias at $a$. The constant character is the only one with $a = 0$, so Plancherel bounds the norm on mean-zero functions by $\varepsilon$; the mixing lemma then applies.

## Depends on

- [Spectral expansion, second eigenvalue and edge expansion of a regular multigraph](../expander-graph-operations/spectral-expansion-second-eigenvalue-and-edge-expansion.md)

## Proof depends on

- [Expander mixing lemma](../expander-graphs/expander-mixing-lemma.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
- S. Hoory, N. Linial, A. Wigderson, "Expander Graphs and Their Applications", Bulletin of the American Mathematical Society, 2006.
