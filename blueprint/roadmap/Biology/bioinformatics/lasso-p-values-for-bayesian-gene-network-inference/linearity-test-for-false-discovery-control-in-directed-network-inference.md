# Linearity test for false discovery control in directed network inference

**Setting.** A directed (Bayesian) gene network is inferred by pruning a prior DAG $\mathcal{N}_0 = \{i\to j\}$ of candidate regulations, for example one obtained from cis-eQTL causal anchors: for each target gene $j$ a separate variable selection assigns a p-value $p_{ij}$ to every candidate regulator $i$ (for instance the [lasso p-value of the critical regularization strength](lasso-p-value-of-the-critical-regularization-strength.md)). Let $N_j = \#\{i : i\to j\in\mathcal{N}_0\}$ be the number of candidate regulators of $j$.

**Null calibration requirement.** Consistent false discovery control across targets requires that, when no regulation is genuine, every $p_{ij}$ be $\mathrm{Uniform}(0,1)$, whatever $N_j$ is. Then, for any threshold $p_{\rm thres}$, the number $K_j$ of significant regulators of target $j$ satisfies
$$K_j \sim \mathrm{Binomial}(N_j, p_{\rm thres}) \approx \mathcal{N}\bigl(N_jp_{\rm thres},\,N_jp_{\rm thres}(1-p_{\rm thres})\bigr),$$
so $\mathbb{E}[K_j] = p_{\rm thres}N_j$ is **linear in $N_j$ through the origin** with slope equal to the false positive rate.

**Tests.** (i) *Histogram test*: pooled null p-values against the uniform histogram. (ii) *Kolmogorov–Smirnov test* per target $j$ against $U(0,1)$, plotted against $N_j$ with Bonferroni-corrected thresholds. (iii) *Linearity test*: scatter of $K_j$ against $N_j$ at a fixed threshold. (iv) *$R^2$ test*: the goodness of the linear fit of $K_j$ on $N_j$ as a function of the overall proportion of significant hypotheses; a larger area under this curve, especially at small thresholds, indicates better false discovery control. Tests (iii)–(iv) apply even when a method returns only a list of significant edges. On real data, an exclusion cutoff removes the enrichment of small p-values due to genuine regulations before testing.

Applied to null and Geuvadis lymphoblastoid expression data, lasso critical-strength p-values pass these tests, while covariance-test and post-selection-inference lasso p-values show target-size-dependent biases.

## Depends on

- [Lasso p-value of the critical regularization strength](lasso-p-value-of-the-critical-regularization-strength.md)

## Expansion

The point of the test is that a ranking statistic which is not a calibrated p-value (a raw correlation, a regularization strength, or a miscalibrated p-value) induces different false positive rates for targets with different numbers of candidate regulators. Thresholding such a statistic over the whole network then mixes inconsistent error levels, which lowers overall accuracy just as using odds ratios instead of p-values would bias a multi-disease association study towards diseases with fewer samples. Deviations from linearity in $K_j$ versus $N_j$ expose this bias without access to the true network.

## Sources

- L. Wang and T. Michoel, *Controlling false discoveries in Bayesian gene networks with lasso regression p-values*, arXiv:1701.07011 (2017), Approach section, Methods ("False discovery control using p-values in network inference"), and Results. <https://doi.org/10.48550/arXiv.1701.07011>
