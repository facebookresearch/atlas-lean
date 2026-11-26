# Identifiability and consistency of the eight-group replicability mixture

**Parameter space.** Let $\Xi=\bigl((\xi_{klr})_{(k,l,r)\in S},f_{11},f_{21},f_{31}\bigr)\in\Omega=\Delta\times\mathcal G^3$, where $\Delta$ is the probability simplex on the eight states $S=\{0,1\}^3$ and $\mathcal G$ the non-increasing densities on $(0,1)$. The model density of a triple of p-values is

$$f_\Xi(x,y,z)=\sum_{(k,l,r)\in S}\xi_{klr}f_{1k}(x)f_{2l}(y)f_{3r}(z),\qquad f_{10}=f_{20}=f_{30}\equiv1 .$$

Measure distance between parameters by

$$\tau(\Xi,\Xi^*)=\sum_{(k,l,r)\in S}|\xi_{klr}-\xi^*_{klr}|+\|f_{11}-f^*_{11}\|_1+\|f_{21}-f^*_{21}\|_1+\|f_{31}-f^*_{31}\|_1,$$

and between densities by the Hellinger distance $h(f_\Xi,f_{\Xi^*})=\bigl(\tfrac12\int_{(0,1)^3}(f_\Xi^{1/2}-f_{\Xi^*}^{1/2})^2\bigr)^{1/2}$.

**Theorem 1 (identifiability).** If $\Xi,\Xi^*\in\Omega$ both satisfy the paper's identifiability condition (C1) and $f_\Xi=f_{\Xi^*}$, then $\xi_{klr}=\xi^*_{klr}$ for all $(k,l,r)\in S$ and $f_{j1}=f^*_{j1}$ almost everywhere for $j=1,2,3$.

**Theorem 2 (consistency).** Under (C1) and a further regularity condition (C2), the semiparametric maximum-likelihood estimator $\hat\Xi_m$ satisfies $\tau(\hat\Xi_m,\Xi_0)\to_p0$ as $m\to\infty$.

**Theorem 3 (FDR control).** Under conditions (C1)–(C5), the step-up procedure on the plug-in local FDRs $\widehat{\mathrm{Lfdr}}_i$ built from $\hat\Xi_m$ controls the FDR of the composite replicability nulls asymptotically at level $\alpha$.

**Estimation.** The maximum-likelihood estimator is computed by EM over the hidden states; in the M-step each non-null density is updated by a weighted isotonic (non-increasing) fit obtained by the pool-adjacent-violators algorithm, which keeps the iterates in $\mathcal G$.

## Expansion

Without a shape restriction a two-component mixture with a uniform null is not identifiable, since part of the non-null density can be traded for uniform mass. Restricting non-null densities to be non-increasing, together with (C1), pins down the decomposition. Consistency follows the standard route: Hellinger consistency of the nonparametric MLE, $h(f_{\hat\Xi_m},f_\Xi)\to_p0$, is transferred to the parameters by identifiability. FDR control then follows because the plug-in Lfdr values converge to the oracle ones and the oracle step-up rule controls the FDR.

## Depends on

- [Covariate-assisted local FDR for replicability](covariate-assisted-replicability-lfdr.md)
- [Hellinger distance](../../../../Probability/convergence-of-measures/hellinger-distance/hellinger-dist.md)

## Sources

- Y. Li, Y. Li, H. Ma, Z. Yue, X. Zhang, "Coconut: covariate-assisted composite null hypothesis testing with applications to replicability analysis of high-throughput experimental data", *BMC Bioinformatics* 26 (2025), Methods: estimation of the unknowns (EM with PAVA), Theorem 1, Theorem 2 and Theorem 3 with conditions (C1)–(C5), <https://doi.org/10.1186/s12859-025-06163-8>, PMCID PMC12210505.
