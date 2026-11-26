# LogDet distances on rooted triple networks

**LogDet distance.** For taxa $a, b$ with $k \times k$ matrix $F_{ab}$ of expected relative site-pattern frequencies (entries summing to $1$), row and column sums $f_a$, $f_b$, and $g_a$, $g_b$ the products of the entries of $f_a$, $f_b$, the (theoretical) logDet distance is

$$d_{LD}(a, b) = -\frac{1}{k}\Bigl(\ln\det F_{ab} - \tfrac12 \ln(g_a g_b)\Bigr).$$

**Model.** Under the *mixture of coalescent mixtures* model $\mathcal M$ on a level-1 ultrametric rooted network $N^+$, each site has its own gene tree drawn from the network multispecies coalescent, and its GTR substitution parameters are drawn independently from a fixed distribution over finitely many classes; the site pattern law is the resulting mixture.

**Propositions.** Let $N^+$ be a binary level-1 ultrametric rooted triple network on $\{a, b, c\}$ and let $T = ((a, b), c)$ be the tree obtained by suppressing all its cycles.

1. If $N^+$ has neither a 4-cycle nor a $3_2$-cycle, then $d_{LD}(a, c) = d_{LD}(b, c) > d_{LD}(a, b)$.
2. If $N^+$ has a $3_2$-cycle, then $d_{LD}(a, c) = d_{LD}(b, c)$.
3. If $N^+$ has a 4-cycle such that contracting all other cycles and deleting one of its hybrid edges gives $((a, b), c)$ and deleting the other gives $((a, c), b)$, then $d_{LD}(b, c) > d_{LD}(a, b)$ and $d_{LD}(b, c) > d_{LD}(a, c)$.

## Expansion

Under $\mathcal M$ all taxa share the same base distribution, so the $\ln(g_a g_b)$ term is the same for every pair and only $\det F_{xy}$ matters. Exchangeability of $a$ and $b$ (ultrametricity, no 4-cycle) gives $F_{ac} = F_{bc}$. For the strict inequality one decomposes $F_{ab}$ and $F_{ac}$ as convex combinations, over substitution classes, of symmetric positive definite matrices with $y^\top F^{(i)}_{ab} y \ge y^\top F^{(i)}_{ac} y$ for every $y$, strictly for some $y$ and some class, and applies the lemma that such combinations satisfy $\det F_{ab} > \det F_{ac}$. A 4-cycle mixes the two displayed topologies, which separates $c$ from $a$ and $b$ in both.

## Depends on

- [Log-det distance](../../phylogenetics/log-det-estimation-of-the-gtr-rate-matrix/log-det-distance.md)
- [Network multispecies coalescent: the gene-tree probability kernel of a fixed network](../multispecies-coalescent/network-multispecies-coalescent-fixed-network-ge.md)

## Sources

- E. S. Allman, H. Baños and J. A. Rhodes, "Identifiability of species network topologies from genomic sequences using the logDet distance", *Journal of Mathematical Biology* 84 (2022), <https://doi.org/10.1007/s00285-022-01734-2> (PMC9192096). Equation (1), Section 2 (model), Proposition 2, Lemma 14, Propositions 3–5.
