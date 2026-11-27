# Leading-edge target selection on a recovery curve

**Setting.** Use the rankings $\pi_1, \dots, \pi_N$, the query set $Q$ and the recovery curves $\mathrm{rec}_m$ of [the recovery-curve AUC](recovery-curve-auc-and-normalized-enrichment-score.md). For each rank $x$ let $\bar r(x)$ and $s_r(x)$ be the mean and standard deviation of $\mathrm{rec}_1(x), \dots, \mathrm{rec}_N(x)$, and define the background curve $b(x) = \bar r(x) + 2\,s_r(x)$. Fix a rank threshold $X_{\max} \le G$.

**Definition.** For an enriched motif $m$, the leading edge is

$$x_m^\ast = \operatorname*{arg\,max}_{1 \le x \le X_{\max}} \big(\mathrm{rec}_m(x) - b(x)\big)$$

(the smallest maximizer, by convention), and the predicted direct targets of $m$ are $\{\, g \in Q : \pi_m(g) \le x_m^\ast \,\}$, a set of size $\mathrm{rec}_m(x_m^\ast)$.

**Proposition.** The maximum is attained at a rank where $\mathrm{rec}_m$ has just increased: either $x_m^\ast = 1$ or $\mathrm{rec}_m(x_m^\ast) > \mathrm{rec}_m(x_m^\ast - 1)$, provided $b$ is nondecreasing on $[1, X_{\max}]$.

## Depends on

- [Recovery-curve AUC and normalized enrichment score](recovery-curve-auc-and-normalized-enrichment-score.md)

## Remarks

If $\mathrm{rec}_m(x) = \mathrm{rec}_m(x-1)$ and $b(x) \ge b(x-1)$, then rank $x - 1$ scores at least as high as $x$, so the smallest maximizer sits at a jump; every predicted target is therefore a query gene recovered at or before that jump. The construction mirrors the leading edge of gene set enrichment analysis, but measures the excess over the motif library rather than over a uniform null. Applied to p53-induced genes, it predicted 307 direct p53 targets that the source then compared with ChIP-seq peaks.

## Sources

- R. Janky, A. Verfaillie, H. Imrichová, B. Van de Sande, L. Standaert, V. Christiaens, G. Hulselmans, K. Herten, M. Naval Sanchez, D. Potier, D. Svetlichnyy, Z. Kalender Atak, M. Fiers, J.-C. Marine and S. Aerts, *iRegulon: from a gene list to a gene regulatory network using large motif and track collections*, PLoS Comput. Biol. 10 (2014), e1003731. <https://doi.org/10.1371/journal.pcbi.1003731> (PMCID: PMC4109854). Materials and Methods, "Detection of the target genes"; Fig. 1B.
