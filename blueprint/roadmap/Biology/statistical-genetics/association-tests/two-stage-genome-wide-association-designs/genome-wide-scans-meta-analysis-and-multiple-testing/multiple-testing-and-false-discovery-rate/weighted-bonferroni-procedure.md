# Weighted Bonferroni procedure

Let $p_1,\dots,p_m$ be p-values for hypotheses $H_1,\dots,H_m$, each valid in the sense that $P(p_j \le u) \le u$ for all $u \in [0,1]$ when $H_j$ is true. Let $w_1,\dots,w_m \ge 0$ be fixed weights, chosen independently of the p-values, with mean one: $\frac1m\sum_{j=1}^m w_j = 1$.

**Procedure.** At level $\alpha \in (0,1)$, reject $H_j$ when $p_j \le \alpha w_j/m$. The rule is stated through thresholds, so that no $p_j/0$ arises: a hypothesis with $w_j = 0$ has threshold $0$ and is rejected only if $p_j = 0$, an event of probability $0$ under a true $H_j$. For $w_j > 0$ the rule is equivalent to the weighted p-value $p_j/w_j$ being at most $\alpha/m$.

**Theorem.** The family-wise error rate is at most $\alpha$: if $\mathcal H_0$ is the set of true nulls,

$$P\Big(\bigcup_{j\in\mathcal H_0}\{p_j \le \alpha w_j/m\}\Big) \le \frac{\alpha}{m}\sum_{j\in\mathcal H_0} w_j \le \alpha.$$

No independence between p-values is required. With all $w_j = 1$ it is the ordinary Bonferroni procedure.

## Proof sketch

The union bound gives $P(\bigcup_{j\in\mathcal H_0}\{p_j \le \alpha w_j/m\}) \le \sum_{j\in\mathcal H_0} P(p_j \le \alpha w_j/m) \le \sum_{j\in\mathcal H_0}\alpha w_j/m$, and the last sum is at most $\frac{\alpha}{m}\sum_{j=1}^m w_j = \alpha$ because the weights are non-negative with mean one. Weights shift the rejection budget toward hypotheses believed more likely to be non-null; good weights raise power while the mean-one constraint keeps the error guarantee. The theorem needs the weights fixed, or independent of the null p-values; a small number of distinct data-dependent weights does not by itself control the family-wise error rate. For example, split $m$ independent uniform null p-values into two fixed bins of equal size, and give weight $2$ to the bin containing the smallest p-value and $0$ to the other: there are only two bin weights and their mean is one, but the probability of at least one rejection is $1 - (1 - 2\alpha/m)^m$, which exceeds $\alpha$ (about $0.095$ at $\alpha = 0.05$ and large $m$). Weights estimated from the same statistics need the extra hypotheses of a method-specific result, or empirical calibration.

## Depends on

- [Valid p-value](../../../../../../Probability/hypothesis-testing/valid-p-values-and-false-discovery-proportion/is-valid-pvalue.md)

## Sources

- C. R. Genovese, K. Roeder and L. Wasserman, "False discovery control with p-value weighting", Biometrika 93 (2006), 509–524, <https://doi.org/10.1093/biomet/93.3.509>.
- G. Kichaev, G. Bhatia, P.-R. Loh et al., "Leveraging polygenic functional enrichment to improve GWAS power", American Journal of Human Genetics 104 (2019), 65–75, Material and Methods, Equations 1–3, <https://doi.org/10.1016/j.ajhg.2018.11.008> (PMC6323418).
