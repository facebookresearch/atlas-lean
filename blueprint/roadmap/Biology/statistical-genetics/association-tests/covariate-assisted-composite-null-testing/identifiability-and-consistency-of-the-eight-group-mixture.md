# Identifiability and consistency of the eight-group replicability mixture

**Parameter space.** Let $\Xi=\bigl((\xi_{klr})_{(k,l,r)\in S},f_{11},f_{21},f_{31}\bigr)\in\Omega=\Delta\times\mathcal G^3$, where $\Delta$ is the probability simplex on the eight states $S=\{0,1\}^3$ and $\mathcal G$ the non-increasing densities on $(0,1)$. The model density of a triple of p-values is

$$f_\Xi(x,y,z)=\sum_{(k,l,r)\in S}\xi_{klr}f_{1k}(x)f_{2l}(y)f_{3r}(z),\qquad f_{10}=f_{20}=f_{30}\equiv1 .$$

Measure distance between parameters by

$$\tau(\Xi,\Xi^*)=\sum_{(k,l,r)\in S}|\xi_{klr}-\xi^*_{klr}|+\|f_{11}-f^*_{11}\|_1+\|f_{21}-f^*_{21}\|_1+\|f_{31}-f^*_{31}\|_1,$$

and between densities by the Hellinger distance $h(f_\Xi,f_{\Xi^*})=\bigl(\tfrac12\int_{(0,1)^3}(f_\Xi^{1/2}-f_{\Xi^*}^{1/2})^2\bigr)^{1/2}$.

**Conditions.** The source's conditions, with $\mathrm{Lfdr}_i$ the oracle local FDRs of the covariate-assisted model at the true parameter, are:

- (C1) $\lim_{x\to1}f_{11}(x)=\lim_{y\to1}f_{21}(y)=\lim_{z\to1}f_{31}(z)=0$.
- (C2) There are an envelope $F>0$ on $(0,1)$ and constants $C,c>0$ with $\int_0^1F<\infty$ and $\int_0^1F^2<C$, such that every $\Xi\in\Omega$ has $f_{11},f_{21},f_{31}<F$ and $\xi_{000}\ge c$.
- (C3) $f_{11},f_{21},f_{31}\in\mathcal G$.
- (C4) For every $\lambda\in(0,1)$, $\frac1m\sum_{i=1}^m\mathbf 1\{\mathrm{Lfdr}_i\le\lambda\}\to_pB_1(\lambda)$ and $\frac1m\sum_{i=1}^m\mathrm{Lfdr}_i\,\mathbf 1\{\mathrm{Lfdr}_i\le\lambda\}\to_pB_2(\lambda)$ for continuous functions $B_1,B_2$ on $(0,1)$.
- (C5) Some $\lambda_0\in(0,1)$ has $B_1(\lambda_0)>0$ and $B_2(\lambda_0)/B_1(\lambda_0)\le\alpha$.

**Theorem 1 (identifiability).** If $\Xi,\Xi^*\in\Omega$ both satisfy (C1) and $f_\Xi=f_{\Xi^*}$, then $\xi_{klr}=\xi^*_{klr}$ for all $(k,l,r)\in S$ and $f_{j1}=f^*_{j1}$ almost everywhere for $j=1,2,3$.

**Theorem 2 (consistency).** Under (C1) and (C2), the semiparametric maximum-likelihood estimator $\hat\Xi_m$ satisfies $\tau(\hat\Xi_m,\Xi_0)\to_p0$ as $m\to\infty$, where $\Xi_0$ is the true parameter.

**Theorem 3 (FDR control).** Under (C1)–(C5), the step-up procedure on the plug-in local FDRs $\widehat{\mathrm{Lfdr}}_i$ built from $\hat\Xi_m$ controls the FDR of the composite replicability nulls asymptotically at level $\alpha$.

**Estimation.** The maximum-likelihood estimator is computed by EM over the hidden states; in the M-step each non-null density is updated by a weighted isotonic (non-increasing) fit obtained by the pool-adjacent-violators algorithm, which keeps the iterates in $\mathcal G$.

## Expansion

Without a shape restriction a two-component mixture with a uniform null is not identifiable, since part of the non-null density can be traded for uniform mass. Restricting non-null densities to be non-increasing, together with (C1), pins down the decomposition. Consistency follows the standard route: Hellinger consistency of the nonparametric MLE, $h(f_{\hat\Xi_m},f_\Xi)\to_p0$, is transferred to the parameters by identifiability. FDR control then follows because the plug-in Lfdr values converge to the oracle ones and the oracle step-up rule controls the FDR.

## Depends on

- [Covariate-assisted local FDR for replicability](covariate-assisted-replicability-lfdr.md)
- [Hellinger distance](../../../../Probability/convergence-of-measures/hellinger-distance/hellinger-dist.md)

## Sources

- Y. Li, Y. Li, H. Ma, Z. Yue, X. Zhang, "Coconut: covariate-assisted composite null hypothesis testing with applications to replicability analysis of high-throughput experimental data", *BMC Bioinformatics* 26 (2025), Methods: estimation of the unknowns (EM with PAVA), Theorem 1, Theorem 2 and Theorem 3 with conditions (C1)–(C5), <https://doi.org/10.1186/s12859-025-06163-8>, PMCID PMC12210505.
