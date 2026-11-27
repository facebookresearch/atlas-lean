# LogDet distances on rooted triple networks

**LogDet distance.** For taxa $a, b$ with $k \times k$ matrix $F_{ab}$ of expected relative site-pattern frequencies (entries summing to $1$), row and column sums $f_a$, $f_b$, and $g_a$, $g_b$ the products of the entries of $f_a$, $f_b$, the (theoretical) logDet distance is

$$d_{LD}(a, b) = -\frac{1}{k}\Bigl(\ln\det F_{ab} - \tfrac12 \ln(g_a g_b)\Bigr).$$

**Model.** Under the *mixture of coalescent mixtures* model $\mathcal M$ on a level-1 ultrametric rooted network $N^+$, each site has its own gene tree drawn from the network multispecies coalescent, and its GTR substitution parameters are drawn independently from a fixed distribution over finitely many classes; the site pattern law is the resulting mixture.

**Propositions.** Let $N^+$ be a binary level-1 ultrametric rooted triple network on $\{a, b, c\}$.

1. Suppose $N^+$ has no 4-cycle, and label the taxa so that suppressing all cycles of $N^+$ gives the resolved triple $T = ((a, b), c)$. Then $d_{LD}(a, c) = d_{LD}(b, c)$. If moreover $N^+$ has no $3_2$-cycle, then $d_{LD}(a, c) = d_{LD}(b, c) > d_{LD}(a, b)$.
2. Suppose $N^+$ has a 4-cycle (suppressing that cycle gives the unresolved star, not a resolved triple), and label the taxa so that suppressing all other cycles and deleting one hybrid edge of the 4-cycle gives $((a, b), c)$ while deleting the other gives $((a, c), b)$. Then $d_{LD}(b, c) > d_{LD}(a, b)$ and $d_{LD}(b, c) > d_{LD}(a, c)$, and for generic parameters $d_{LD}(a, b) \ne d_{LD}(a, c)$, so the three distances are pairwise distinct.

## Expansion

Under $\mathcal M$ all taxa share the same base distribution, so the $\ln(g_a g_b)$ term is the same for every pair and only $\det F_{xy}$ matters. In case 1, exchangeability of $a$ and $b$ (ultrametricity, no 4-cycle) gives $F_{ac} = F_{bc}$. For the strict inequality one decomposes $F_{ab}$ and $F_{ac}$ as convex combinations, over substitution classes, of symmetric positive definite matrices with $y^\top F^{(i)}_{ab} y \ge y^\top F^{(i)}_{ac} y$ for every $y$, strictly for some $y$ and some class, using that the gene tree matching $((a,b),c)$ is strictly the most probable rooted triple, and applies the lemma that such combinations satisfy $\det F_{ab} > \det F_{ac}$. In case 2 the 4-cycle mixes the two resolutions $((a,b),c)$ and $((a,c),b)$, each of which separates $b$ from $c$, which gives the two inequalities for $d_{LD}(b,c)$; the remaining inequality $d_{LD}(a,b) \ne d_{LD}(a,c)$ fails only on a proper algebraic subset of the parameters, which is what genericity excludes.

## Depends on

- [Log-det distance](../../phylogenetics/gtr-identifiability-and-estimation/log-det-estimation-of-the-gtr-rate-matrix/log-det-distance.md)
- [Network multispecies coalescent: the gene-tree probability kernel of a fixed network](../multispecies-coalescent/network-multispecies-coalescent-fixed-network-ge.md)

## Proof depends on

- [No anomalous gene trees for three species](../multispecies-coalescent/triple-no-anomaly.md)

## Sources

- E. S. Allman, H. Baños and J. A. Rhodes, "Identifiability of species network topologies from genomic sequences using the logDet distance", *Journal of Mathematical Biology* 84 (2022), <https://doi.org/10.1007/s00285-022-01734-2> (PMC9192096). Equation (1), Section 2 (model), Proposition 2, Definition 8, Lemma 14, Propositions 3–5.
