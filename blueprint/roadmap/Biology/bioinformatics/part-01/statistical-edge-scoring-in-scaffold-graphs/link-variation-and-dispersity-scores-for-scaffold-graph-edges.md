# Link variation and dispersity scores for scaffold-graph edges

**Scaffold graph.** Given assembled contigs and a paired-read library whose insert size has mean $\mu$ and standard deviation $\sigma$, each contig $c_i$ contributes two vertices $c_{i,L}$ (5' end) and $c_{i,R}$ (3' end). A read pair whose mates align uniquely to two different contigs $c_k \neq c_m$ induces a relative orientation and an approximate distance, recorded as an edge between the corresponding contig ends. Scaffolding chooses, for each contig end, at most one partner, i.e. a matching on the vertex set.

**Edge score.** For an edge between contigs $c_i, c_j$ with estimated gap $d$ (a maximum likelihood gap estimate from the observed links), define two scores in $[0,1]$:

- *Link variation score*

    $$\pi_\sigma = \min\Big\{\frac{\hat\sigma_{o\mid d}}{\sigma_{o\mid d}},\ \frac{\sigma_{o\mid d}}{\hat\sigma_{o\mid d}}\Big\},$$

    where $\hat\sigma_{o\mid d}$ is the observed standard deviation of the link observations and $\sigma_{o\mid d}$ is the theoretical standard deviation of an observation given gap $d$ (Theorem 1 of the source),

    $$\sigma_{o\mid d} = \sqrt{\sigma^2 + \frac{q(d)\,\sigma^4}{g(d)} - \frac{g'(d)^2\,\sigma^4}{g(d)^2}},$$

    with $g$ and $q$ the functions of $d$ defined in the source's Additional file 1 from $\mu$, $\sigma$, the read length and the lengths of the shorter and longer contig. Agreement gives $\pi_\sigma$ near $1$.
- *Link dispersity score* $\pi_\zeta = 1 - D_n$: after translating and reflecting the $n$ link positions on each contig into a common coordinate, let $F_{1,n}$ and $F_{2,n}$ be the empirical distribution functions of the two samples, and

    $$D_n = \sup_x \big|F_{1,n}(x) - F_{2,n}(x)\big| \in [0,1],$$

    the two-sample Kolmogorov–Smirnov statistic.

The total edge score is

$$\pi = \pi_\sigma + \pi_\zeta \in [0,2],$$

with $\pi = \pi_\sigma + \pi_\zeta$ if $\pi_\sigma > 1/2$ and $\pi_\zeta > 1/2$, and $\pi = 0$ otherwise; so an edge is discarded when either component is at most $1/2$.

**Use on long contigs.** If every contig longer than $\mu + 4\sigma$ can be linked by the library to at most one such contig on each side, then in the subgraph of long contigs a vertex of degree greater than one signals a linking error (for example a repeat). In such regions the highest-scoring edge is chosen, and no decision is made if the ratio of the two highest scores exceeds a threshold (0.9). Correct regions are simple paths found in $O(|E|)$ time.

## Expansion

The two mates of a read pair are aligned independently, so the link positions on two genuinely adjacent contigs form two independent samples of the same shape after reflection; a repeat inside one contig concentrates links and inflates $D_n$. The variation score catches the complementary failure, links from several genomic locations mixed into one edge, which inflates the observed spread. Scores rather than $p$-values are used because $p$-values sharpen with the number of links and are not comparable across edges with different support.

## Sources

- K. Sahlin, F. Vezzi, B. Nystedt, J. Lundeberg, L. Arvestad, *BESST: efficient scaffolding of large fragmented assemblies*, BMC Bioinformatics 15 (2014), 281, Background ("Formalizing scaffolding") and Methods ("Link variation score", "Link dispersity score", "Scoring edges", Theorem 1). <https://doi.org/10.1186/1471-2105-15-281> (PMCID: PMC4262078)
