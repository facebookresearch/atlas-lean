# Benjamini–Hochberg on selected hypotheses at level $q|S|/M$

**Setting.** Hypotheses $H_1, \dots, H_M$ (for example, no association between the trait and SNP $j$) have P-values $p_1, \dots, p_M$; null P-values are uniform on $[0, 1]$. A data-dependent selection rule picks a subset $S = S(y) \subseteq \{1, \dots, M\}$ of representative hypotheses (in GWAS, one representative SNP per cluster of correlated SNPs), and decisions are made only for hypotheses in $S$. The selective false discovery rate is

$$\mathrm{FDR}_s = \mathbb{E}\left[ \frac{\sum_{j \in S} \mathbf{1}(H_j \text{ rejected}) \, \mathbf{1}(H_j \text{ true})}{1 \vee \sum_{j \in S} \mathbf{1}(H_j \text{ rejected})} \right].$$

**Procedure.** Apply the Benjamini–Hochberg step-up procedure to the selected P-values $\{p_j : j \in S\}$ at target level $q|S|/M$; equivalently, compare the $k$-th smallest selected P-value with $qk/M$, the same thresholds BH would use on all $M$ hypotheses.

**Theorem.** Suppose the P-values satisfy positive regression dependence on the subset of true nulls (PRDS), and the selection rule is such that the number of rejections $R_S(p_1, \dots, p_M)$ is nonincreasing in each $p_i$. Then $\mathrm{FDR}_s \le q M_0 / M \le q$, where $M_0$ is the number of true nulls.

A rule that satisfies the monotonicity hypothesis: partition the hypotheses into groups fixed in advance and select the smallest P-value in each group. The data-driven GWAS rule of the source (screen SNPs with marginal P-value at most $\pi$, then repeatedly take the most significant remaining SNP as a cluster representative and discard SNPs whose sample correlation with it exceeds $\rho$) can violate monotonicity for rare P-value configurations, and its $\mathrm{FDR}_s$ control is supported there by simulation rather than by the theorem.

## Depends on

- [Benjamini–Hochberg rejection set](../../../../../Probability/hypothesis-testing/benjamini-hochberg-procedure/bh-rejections.md)
- [False discovery proportion](../../../../../Probability/hypothesis-testing/valid-p-values-and-false-discovery-proportion/false-discovery-proportion.md)
- [Hypothesis imposed by a dependence regime](../../../../../Probability/hypothesis-testing/fisher-s-exact-test/holds.md)

## Expansion

Write $q_k = qk/M$ and $V_i = \mathbf{1}(H_i \text{ rejected})$. For a true null $i$,

$$\mathbb{E}\frac{V_i}{\max(1, R)} = \sum_{k=1}^{M} \frac{1}{k}\,\mathbb{E}\bigl[\mathbf{1}(i \in S, \, p_i \le q_k)\,\mathbf{1}(R = k)\bigr] \le \frac{q}{M} \sum_{k=1}^{M} \Pr(R = k \mid p_i \le q_k).$$

Because $R$ is nonincreasing in the P-values, $\{R \le k\}$ is an increasing set, and PRDS gives $\Pr(R \le k \mid p_i \le q_k) \le \Pr(R \le k \mid p_i \le q_{k+1})$. Telescoping as in Benjamini and Yekutieli (2001) bounds the sum by $\Pr(R \le M \mid p_i \le q_M) = 1$, so each true null contributes at most $q/M$. The factor $|S|/M$ is the price of having chosen the hypotheses after seeing the data: naive BH at level $q$ on a single selected minimum P-value would ignore all multiplicity. Counting one discovery per locus also avoids the deflation of the BH threshold that occurs when one causal locus produces many correlated rejections.

## Sources

- D. Brzyski, C. B. Peterson, P. Sobczyk, E. J. Candès, M. Bogdan and C. Sabatti, "Controlling the rate of GWAS false discoveries", Genetics 205 (2017), 61–75, Eq. (1), Theorem 1 and its proof in the Appendix, and Procedure 1. <https://doi.org/10.1534/genetics.116.193987> PMCID: PMC5223524.
- Y. Benjamini and D. Yekutieli, "The control of the false discovery rate in multiple testing under dependency", Annals of Statistics 29 (2001), 1165–1188. <https://doi.org/10.1214/aos/1013699998>
