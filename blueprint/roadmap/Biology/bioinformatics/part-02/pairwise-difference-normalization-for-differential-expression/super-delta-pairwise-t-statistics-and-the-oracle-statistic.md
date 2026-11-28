# Super-delta pairwise t-statistics and the oracle statistic

**Model.** For genes $i = 1,\dots,m$, samples $j$ and groups $a \in \{A, B\}$ of sizes $N_A, N_B$ ($N = N_A + N_B$), log-expression is

$$y^a_{ij} = \mu^a_i + \alpha^a_j + \varepsilon^a_{ij}, \qquad \alpha^a_j \sim N(0,\eta^2), \quad \varepsilon^a_{ij} \overset{iid}{\sim} N(0,\sigma^2),$$

with a per-sample random effect $\alpha^a_j$ shared by all genes, typically $\eta^2 \gg \sigma^2$. The oracle expression is $x^a_{ij} = \mu^a_i + \varepsilon^a_{ij}$, and the hypotheses are $H_0(i): d_i = \mu^A_i - \mu^B_i = 0$.

**Normalization bias.** Global normalization $y^{a,*}_{ij} = y^a_{ij} - \bar y^a_{\cdot j}$ removes $\alpha^a_j$ but gives $E[y^{A,*}_{ij} - y^{B,*}_{ij}] = d_i + (\bar\mu^A - \bar\mu^B)$, biased unless up- and down-regulation balance across genes.

**Super-delta statistics.** For each pair $i \neq i'$, the differences $\delta^a_{ii',j} = y^a_{ij} - y^a_{i'j} = x^a_{ij} - x^a_{i'j}$ are free of $\alpha^a_j$ and have variance $2\sigma^2$. Let $t_{ii'}$ be the pooled two-sample $t$-statistic of $\delta_{ii',\cdot}$ between groups. The oracle statistic is the pooled $t$-statistic $t^*_i$ computed from $x^a_{ij}$.

**Theorem 1.** Assume a common variance $\sigma_i^2 \equiv \sigma^2$. For $k$ in the set $S_0$ of non-differentially expressed genes, conditionally on the noise $\varepsilon_{i\cdot}$ of gene $i$,

$$E(t_{ik} \mid \varepsilon_{i\cdot}) \xrightarrow{P} \frac{1}{\sqrt 2}\, t^*_i + O(N^{-1}), \qquad \operatorname{Med}(t_{ik} \mid \varepsilon_{i\cdot}) \xrightarrow{P} \frac{1}{\sqrt 2}\, t^*_i + O(N^{-1}).$$

**Representative statistic.** Hence for gene $i$ one takes the median-fold-trim median: drop a fraction (e.g. 20%) of the $t_{ii'}$ with largest $|t_{ii'}|$ and set

$$t^{\mathrm{MFTM}}_i = \sqrt 2 \cdot \operatorname{Med}\bigl(t^{\mathrm{trim}}_i\bigr),$$

compute p-values from it, and apply a multiple-testing correction. The gene attaining the trimmed median serves as an empirical housekeeping (pairing) gene for gene $i$.

## Expansion

Pairing with a non-differentially expressed gene $k$ subtracts $x_{kj}$, whose group means agree, so the numerator of $t_{ik}$ estimates $d_i$ without bias while the variance doubles; averaging over many such partners concentrates the statistic at the oracle value scaled by $1/\sqrt 2$, the ratio of standard deviations. Partners that are themselves differentially expressed produce extreme $t_{ik}$; since such genes are a minority, the median, especially after trimming the extremes, is barely affected even when regulation is strongly one-sided, which is where global, quantile and rank normalization inflate type I error. Simulations and microarray data show better error control and power than those normalizations.

## Sources

- Y. Liu, J. Zhang, X. Qiu, "Super-delta: a new differential gene expression analysis procedure with robust data normalization", BMC Bioinformatics 18 (2017) 582, Equations (3)–(14) and Theorem 1, <https://doi.org/10.1186/s12859-017-1992-2>, PMCID PMC5740711.
