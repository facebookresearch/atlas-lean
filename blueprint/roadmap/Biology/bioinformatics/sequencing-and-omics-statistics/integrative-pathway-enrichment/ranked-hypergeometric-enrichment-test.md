# Ranked hypergeometric enrichment test

Let a background universe contain $N$ annotated genes, let a pathway contain $K$ of them, and let $g_1, g_2, \dots$ be a candidate gene list ranked by decreasing significance. For each prefix length $n$, let $k_n$ be the number of pathway genes among $g_1, \dots, g_n$ and

$$P(n) = \sum_{x = k_n}^{\min(n, K)} \frac{\binom{K}{x}\binom{N-K}{n-x}}{\binom{N}{n}}$$

the hypergeometric upper-tail probability. The ranked hypergeometric test reports

$$P_{\mathrm{pathway}} = \min_n P(n), \qquad G = \operatorname*{arg\,min}_n P(n),$$

the strongest enrichment over all prefixes and the length of the optimal prefix; the pathway's candidate genes are its members among $g_1, \dots, g_G$. Only prefixes ending in a pathway gene need to be evaluated: between two consecutive pathway genes $k_n$ is constant while $n$ grows, and for fixed $k$ the tail $\Pr(X \ge k)$ of a hypergeometric draw of size $n$ is nondecreasing in $n$, so each minimum is attained at a prefix ending in a pathway gene. The minimum p-values over pathways are then adjusted for multiple testing (Holm–Bonferroni), with the universe restricted to genes in the annotation sets for a conservative background.

## Depends on

- [Brown's method for combining dependent p-values](brown-method-for-combining-dependent-p-values.md)

## Expansion

Drawing a larger sample can only add pathway genes to the count, so $X_{n+1}$ stochastically dominates $X_n$ and $\Pr(X_{n+1} \ge k) \ge \Pr(X_n \ge k)$. Scanning prefixes avoids committing to one significance cutoff for the gene list: a pathway concentrated in the top 50 genes and one spread over the top 500 can both be found. Because $P_{\mathrm{pathway}}$ is a minimum over many prefixes, it is a score rather than an exactly calibrated p-value; its null behaviour depends on the number of prefixes scanned. Running the same test on each single-source gene list and on the Brown-integrated list shows which enriched pathways appear only after data integration.

## Sources

- M. Paczkowska, J. Barenboim, N. Sintupisut, et al., "Integrative pathway enrichment analysis of multivariate omics data", Nature Communications 11 (2020), Methods ("ActivePathways", ranked hypergeometric test equation), <https://doi.org/10.1038/s41467-019-13983-9> (PMC7002665).
