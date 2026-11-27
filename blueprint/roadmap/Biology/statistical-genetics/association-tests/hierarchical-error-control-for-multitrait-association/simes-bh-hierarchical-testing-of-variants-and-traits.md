# Simes–BH hierarchical testing of variants and traits

**Setting.** Variant families $F_i = \{H_{it} : t = 1, \dots, P\}$, $i = 1, \dots, M$, with P-values $p_{it}$ and global nulls $H_{i\bullet} = \bigcap_t H_{it}$, as in the [variant-family error rates](error-rates-for-variant-families-of-trait-hypotheses.md). Let $p_{i(1)} \le \dots \le p_{i(P)}$ be the ordered P-values of family $i$.

**Testing Procedure 1.** Fix levels $q_1, q_2 \in (0, 1)$.

- *Stage 0.* Compute the Simes P-value of each family, $p_{i\bullet} = \min_{t = 1, \dots, P} \dfrac{P\, p_{i(t)}}{t}$ (Eq. (1)).
- *Stage 1.* Apply the [Benjamini–Hochberg (BH) procedure](../../../../Probability/hypothesis-testing/benjamini-hochberg-procedure/bh-rejections.md) to $\{p_{i\bullet} : i = 1, \dots, M\}$ at level $q_1$; let $\mathcal S(\mathbf p)$ be the indices of the rejected $H_{i\bullet}$.
- *Stage 2.* In each family $F_i$ with $i \in \mathcal S(\mathbf p)$, apply BH to $p_{i1}, \dots, p_{iP}$ at the selection-adjusted level $q_2 |\mathcal S(\mathbf p)|/M$. No hypothesis outside the selected families is rejected.

**Guarantees.**

1. *vFDR $\le q_1$* whenever the Simes P-values are valid for the intersection nulls and BH on them controls FDR.
2. *sFDR $\le q_2$* whenever BH controls FDR within each family and the P-values of different families are independent, or more generally whenever the pooled collection of P-values is positively regression dependent on the subset of true nulls (PRDS), which is the condition under which pooled BH controls gFDR.
3. *Consistency between stages.* If $q_1 \le q_2$, every variant selected in Stage 1 has at least one trait hypothesis rejected in Stage 2.

## Depends on

- [Error rates for variant families of trait hypotheses](error-rates-for-variant-families-of-trait-hypotheses.md)
- [Benjamini–Hochberg rejection set](../../../../Probability/hypothesis-testing/benjamini-hochberg-procedure/bh-rejections.md)
- [False discovery proportion](../../../../Probability/hypothesis-testing/valid-p-values-and-false-discovery-proportion/false-discovery-proportion.md)

## Proof depends on

- [Benjamini–Hochberg FDR control](../../../../Probability/hypothesis-testing/benjamini-hochberg-procedure/integral-false-discovery-proportion-bh-r.md)

## Expansion

Guarantee 2 is the selective-inference result of Benjamini and Bogomolov: after a data-dependent selection of $|\mathcal S|$ out of $M$ families, controlling FDR inside each selected family at $q_2|\mathcal S|/M$ controls the average false discovery proportion over the selected families at $q_2$. The factor $|\mathcal S|/M$ interpolates between no penalty (all families selected) and a Bonferroni-type penalty over families (one family selected; with Bonferroni inside families this gives the threshold $q_2/(MP)$ of a global Bonferroni correction).

Guarantee 3 follows from the BH step-up rule. If $H_{i\bullet}$ is rejected in Stage 1, then $p_{i\bullet} \le q_1 |\mathcal S|/M$, so some $t$ has $p_{i(t)} \le t\, q_1 |\mathcal S|/(MP) \le t\, q_2 |\mathcal S|/(MP)$. That is exactly the BH condition at rank $t$ for level $q_2|\mathcal S|/M$ in family $i$, so BH there rejects at least $t \ge 1$ hypotheses.

With these two levels and Simes P-values for the parent hypotheses, Testing Procedure 1 is the two-level case of the TreeBH procedure of Bogomolov, Peterson, Benjamini and Sabatti, whose selective FDR at the two levels is vFDR and sFDR here; its consonance and selective-FDR results give guarantees 3 and 2.

Because BH is run separately in each selected family, Stage 2 adapts to the family-specific fraction of non-nulls, so a pleiotropic variant that affects many traits has those effects detected more easily. In simulations with $M = 100{,}000$ variants and $P = 100$ traits, the procedure kept vFDR and sFDR at or below $0.05$, where pooled BH exceeded both, with overall power at least that of pooled BH, at some cost in power for variants affecting a single trait (Figures 3 and 4 of the source).

## Sources

- C. B. Peterson, M. Bogomolov, Y. Benjamini, C. Sabatti, "Many phenotypes without many false discoveries: error controlling strategies for multitrait association studies", Genetic Epidemiology 40 (2016) 45–56, Eq. (1), Testing Procedure 1, sections "Hierarchical Testing Procedure" and "GWAS Dependence Structure", Figures 3–4, <https://doi.org/10.1002/gepi.21942>, PMCID PMC4738479.
- M. Bogomolov, C. B. Peterson, Y. Benjamini, C. Sabatti, "Hypotheses on a tree: new error rates and testing strategies", Biometrika 108 (2021) 575–590, <https://doi.org/10.1093/biomet/asaa086>.
- Y. Benjamini, M. Bogomolov, "Selective inference on multiple families of hypotheses", Journal of the Royal Statistical Society Series B 76 (2014) 297–318, Theorem 3, <https://doi.org/10.1111/rssb.12028>.
