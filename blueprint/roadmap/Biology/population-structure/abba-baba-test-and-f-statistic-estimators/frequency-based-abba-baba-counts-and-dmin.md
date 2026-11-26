# Frequency-based ABBA–BABA counts and the minimum D statistic of a trio

Let $P_1, P_2, P_3$ be three populations and $O$ an outgroup, and let $\hat p_{ij}$ be the estimated derived-allele frequency in
$P_j$ at biallelic site $i \in \{1,\dots,n\}$, where the outgroup carries the ancestral allele ($\hat p_{iO} = 0$). Define

$$n_{ABBA} = \sum_{i=1}^n (1-\hat p_{i1})\,\hat p_{i2}\,\hat p_{i3}, \qquad
n_{BABA} = \sum_{i=1}^n \hat p_{i1}\,(1-\hat p_{i2})\,\hat p_{i3}, \qquad
n_{BBAA} = \sum_{i=1}^n \hat p_{i1}\,\hat p_{i2}\,(1-\hat p_{i3}),$$

the expected numbers of sites with each pattern when one allele is drawn per population, and

$$D = \frac{n_{ABBA} - n_{BABA}}{n_{ABBA} + n_{BABA}} .$$

For a trio $\{X, Y, Z\}$ there are three assignments of which population plays $P_3$; for each, $D$ is computed with
$P_1, P_2$ ordered so that $D \ge 0$. The **$D_{\min}$ score** of the trio is the minimum of these three values of $D$, i.e. the
value of $D$ in the arrangement minimizing $|n_{ABBA} - n_{BABA}|$. Under a tree with no gene flow and $P_3$ the outgroup to
$(P_1,P_2)$, $E[n_{ABBA}] = E[n_{BABA}]$ in the true arrangement, so $D_{\min} > 0$ significantly (by block jackknife) is evidence
of gene flow that holds regardless of the unknown topology of the trio.

When $\hat p_{iO} \ne 0$, using the unpolarized pattern sums
$n_{ABBA} = \sum_i [(1-\hat p_{i1})\hat p_{i2}\hat p_{i3}(1-\hat p_{iO}) + \hat p_{i1}(1-\hat p_{i2})(1-\hat p_{i3})\hat p_{iO}]$ and
$n_{BABA} = \sum_i [\hat p_{i1}(1-\hat p_{i2})\hat p_{i3}(1-\hat p_{iO}) + (1-\hat p_{i1})\hat p_{i2}(1-\hat p_{i3})\hat p_{iO}]$ recovers
Patterson's four-population $D$.

## Depends on

- [ABBA site-pattern frequency](abba.md)
- [BABA site-pattern frequency](baba.md)
- [The unpolarized D-statistic numerator vanishes on a tree](integral-sample-expect-abba-eq-baba.md)

## Expansion

Drawing one allele independently from each population at site $i$, the probability of pattern ABBA is
$(1-\hat p_{i1})\hat p_{i2}\hat p_{i3}$ when the outgroup is fixed ancestral, so the sums are expected site-pattern counts. The
minimum over arrangements is a conservative test: if the true topology is a tree without gene flow, the true arrangement
already has expected $D = 0$, so the minimum cannot be systematically positive. (Malinsky, Matschiner and Svardal 2021,
Equations 1–3 and the description of Dtrios.)

## Sources

- M. Malinsky, M. Matschiner, and H. Svardal, "Dsuite ‐ Fast D ‐statistics and related admixture evidence from VCF files", Molecular Ecology Resources (2020), <https://doi.org/10.1111/1755-0998.13265> (PMC7116594).
