# Frequency-based ABBA–BABA counts and the minimum D statistic of a trio

Let $P_1, P_2, P_3$ be three populations and $O$ an outgroup, and let $\hat p_{ij}$ be the estimated derived-allele frequency in
$P_j$ at biallelic site $i \in \{1,\dots,n\}$, where the outgroup carries the ancestral allele ($\hat p_{iO} = 0$). Define

$$n_{ABBA} = \sum_{i=1}^n (1-\hat p_{i1})\,\hat p_{i2}\,\hat p_{i3}, \qquad
n_{BABA} = \sum_{i=1}^n \hat p_{i1}\,(1-\hat p_{i2})\,\hat p_{i3}, \qquad
n_{BBAA} = \sum_{i=1}^n \hat p_{i1}\,\hat p_{i2}\,(1-\hat p_{i3}),$$

the expected numbers of sites with each pattern when one allele is drawn per population, and, when $n_{ABBA} + n_{BABA} > 0$,

$$D = \frac{n_{ABBA} - n_{BABA}}{n_{ABBA} + n_{BABA}} .$$

For a trio $\{X, Y, Z\}$ there are three assignments of which population plays $P_3$; each uses two of the three pattern totals
$n_{ABBA}, n_{BABA}, n_{BBAA}$ computed for one fixed labelling, and for each, $D$ is computed with $P_1, P_2$ ordered so that
$D \ge 0$. The **$D_{\min}$ score** of the trio is the minimum of these three values of $D$, that is

$$D_{\min} = \min_{\{u, v\}} \frac{|u - v|}{u + v},$$

the minimum over the three pairs $\{u, v\}$ of the totals $n_{ABBA}, n_{BABA}, n_{BBAA}$ (all assumed to have $u + v > 0$). It
minimizes the normalized differences, not their numerators: for totals $1, 3, 6$ the smallest raw difference $|1 - 3|$ gives
$2/4$, while $D_{\min} = 3/9$.

Under a tree with no gene flow, for the fixed true arrangement, with $P_3$ the outgroup to $(P_1, P_2)$, the expected counts
satisfy $E[n_{ABBA}] = E[n_{BABA}]$, and $D_{\min}$ is at most the absolute value of $D$ in that arrangement. A $D_{\min}$
significantly greater than $0$ (by block jackknife) is therefore evidence of gene flow that does not require knowing the topology
of the trio. Because the arrangement and the sign are chosen from the data, $D_{\min}$ is nonnegative and is not a finite-sample
statistic with expectation zero under the null.

When $\hat p_{iO} \ne 0$, using the unpolarized pattern sums
$n_{ABBA} = \sum_i [(1-\hat p_{i1})\hat p_{i2}\hat p_{i3}(1-\hat p_{iO}) + \hat p_{i1}(1-\hat p_{i2})(1-\hat p_{i3})\hat p_{iO}]$ and
$n_{BABA} = \sum_i [\hat p_{i1}(1-\hat p_{i2})\hat p_{i3}(1-\hat p_{iO}) + (1-\hat p_{i1})\hat p_{i2}(1-\hat p_{i3})\hat p_{iO}]$ recovers
Patterson's four-population $D$.

## Depends on

- [Polarized ABBA site-pattern indicator](abba-pol.md)
- [Polarized BABA site-pattern indicator](baba-pol.md)
- [Unpolarized ABBA site-pattern indicator](abba.md)
- [Unpolarized BABA site-pattern indicator](baba.md)

## Proof depends on

- [Sampling expectation of a product factorizes](sample-expect-prod.md)
- [The unpolarized D-statistic numerator vanishes on a tree](integral-sample-expect-abba-eq-baba.md)

## Expansion

Drawing one allele independently from each population at site $i$, the probability of pattern ABBA is
$(1-\hat p_{i1})\hat p_{i2}\hat p_{i3}$ when the outgroup is fixed ancestral, so the sums are expected site-pattern counts. Relabeling
which population plays $P_3$ permutes the roles of the three totals: with $P_1 = X$, $P_2 = Z$, $P_3 = Y$, for instance, the ABBA
total is unchanged and the BABA total is the original $n_{BBAA}$. On a tree without gene flow, the numerator of $D$ has expectation
zero in the true arrangement, so $D_{\min}$, being at most the absolute value of that $D$, is a conservative summary across the three
arrangements; this bounds $D_{\min}$ by a statistic whose numerator is centred, but the absolute value and the data-chosen
arrangement keep $D_{\min}$ itself from having mean zero. (Malinsky, Matschiner and Svardal 2021, Equations 1–3 and the description
of Dtrios.)

## Sources

- M. Malinsky, M. Matschiner, and H. Svardal, "Dsuite ‐ Fast D ‐statistics and related admixture evidence from VCF files", Molecular Ecology Resources (2020), <https://doi.org/10.1111/1755-0998.13265> (PMC7116594).
- M. Malinsky, H. Svardal, A. M. Tyers et al., "Whole-genome sequences of Malawi cichlids reveal multiple radiations interconnected by gene flow", Nature Ecology & Evolution 2 (2018), 1940–1955, <https://doi.org/10.1038/s41559-018-0717-x>.
