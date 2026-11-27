# Sure screening and ranking consistency of normalized trend statistics

**Setting.** A binary trait $Y$ (case $Y = 1$ with probability $p$, control with $q = 1-p$) and SNPs $G_1,\dots,G_m$ with genotypes $G_k \in \{0,1,2\}$. Let $p_{ik} = P(G_k = i, Y = 1)$, $q_{ik} = P(G_k = i, Y = 0)$ and $f_{ik} = p_{ik} + q_{ik}$. For the recessive, additive and dominant score vectors $X_{\cdot,0} = (0,0,1)$, $X_{\cdot,1/2} = (0,\tfrac12,1)$, $X_{\cdot,1} = (0,1,1)$, define

$$\omega_{j,k} = \frac{\sum_{i=0}^2 X_{i,j}\,(q\,p_{ik} - p\,q_{ik})}{\sqrt{p\,q\,\bigl[\sum_i X_{i,j}^2 f_{ik} - (\sum_i X_{i,j} f_{ik})^2\bigr]}}, \qquad \nu_k = \max_{j \in \{0, 1/2, 1\}} |\omega_{j,k}| .$$

If $G_k$ is independent of $Y$ then $\omega_{j,k} = 0$ for all $j$ and $\nu_k = 0$.

**Estimators.** From $n$ subjects with $r$ cases and $s$ controls, plug in empirical frequencies. The estimate $\hat\omega_{j,k}$ equals $Z_{j,k}/\sqrt n$, where $Z_{j,k}$ is the Cochran–Armitage trend statistic with score vector $X_{\cdot,j}$, and $\hat\nu_k$ ranks SNPs exactly as the MAX3 statistic $\max_j |Z_{j,k}|$ does. Screening keeps

$$\hat A_j = \{k : |\hat\omega_{j,k}| \ge c_0 n^{-\tau}\}, \qquad \hat A = \{k : \hat\nu_k \ge c_0 n^{-\tau}\},$$

or, in practice, the $d$ top-ranked SNPs; the active sets are $A_j = \{k : |\omega_{j,k}| > 0\}$ and $A = \{k : \nu_k > 0\}$.

**Conditions.** (C1) Every nonzero $p_{ik}$ and $q_{ik}$ lies in $(\zeta_{\min}, \zeta_{\max}) \subset (0,1)$. (C2) $\min_{k \in A_j} \omega_{j,k} \ge 2c_0 n^{-\tau}$ (C3: the same for $\nu_k$ on $A$), with $c_0 > 0$, $0 \le \tau < 1/2$. (C4)/(C5) With $\log m = o(n^{1-2\tau} \wedge n^{1/2})$, the gap between the smallest active and largest inactive $\omega_{j,k}$ (resp. $\nu_k$) eventually exceeds $2c_0 n^{-\tau}$.

**Theorem 1 (sure screening, single model).** Under (C1), for each $j$,

$$P\Bigl(\max_{k \le m} |\hat\omega_{j,k} - \omega_{j,k}| \ge c_0 n^{-\tau}\Bigr) < O\bigl(m\, e^{-c_1 n^{1-2\tau} - c_2 n^{1/2}}\bigr),$$

and under (C1)–(C2), $P(A_j \subseteq \hat A_j) \ge 1 - O\bigl(\kappa\, e^{-c_1 n^{1-2\tau} - c_2 n^{1/2}}\bigr)$ with $\kappa = |A_j|$.

**Theorem 2 (sure screening, maximum over models).** The same bounds hold for $\hat\nu_k$ under (C1), and $P(A \subseteq \hat A) \ge 1 - O\bigl(\kappa\, e^{-c_3 n^{1-2\tau} - c_4 n^{1/2}}\bigr)$ under (C1) and (C3).

**Theorems 3–4 (ranking consistency).** Under (C1) and (C4), $\liminf_{n} \bigl(\min_{k \in A_j} |\hat\omega_{j,k}| - \max_{k \notin A_j} |\hat\omega_{j,k}|\bigr) \ge 0$ almost surely; under (C1) and (C5) the same holds for $\hat\nu_k$ on $A$.

## Expansion

Each $\hat\omega_{j,k}$ is a smooth function of a handful of empirical cell frequencies bounded away from $0$ and $1$ by (C1), so exponential concentration of the frequencies plus a union bound over $m$ SNPs gives the uniform deviation bound (proofs are in the supplementary material of the source). If every estimate is within $c_0 n^{-\tau}$ of its target and every active target is at least $2c_0 n^{-\tau}$, all active SNPs pass the threshold, which is the sure screening statement; the union over active SNPs only costs a factor $\kappa$. Ranking consistency follows similarly from the gap conditions, and justifies keeping the top $d$ SNPs: for $d \ge |\hat A|$ the top-$d$ set contains $\hat A$, so it inherits the coverage probability. Normalizing by $\sqrt n$ makes the measures comparable across sample sizes while keeping the ranking of the classical trend tests; maximizing over the three score vectors protects against misspecifying the genetic model.

## Depends on

- [Cochran–Armitage statistic of the first N subjects](../ca-stat.md)
- [Cochran–Armitage trend statistic](../../../genomic-prediction-from-summary-statistics/trend-stat.md)
- [Generalized genetic model and the MAX3 trend test](../order-restricted-genetic-models-and-max3/generalized-genetic-model-and-the-max3-trend-test.md)

## Sources

- Z. Jiang, H. Guo, J. Wang, "Screening properties of trend tests in genetic association studies", Scientific Reports 13 (2023) 9139, Equations (3)–(18), Conditions (C1)–(C5) and Theorems 1–4, <https://doi.org/10.1038/s41598-023-35929-4>, PMCID PMC10241885.
