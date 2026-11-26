# Identification of bidirectional causal effects from GWAS summary statistics by noisy ICA

**Model.** Two traits $\mathbf T=(T_1,T_2)^\top$ and standardized genotypes $\mathbf Z\in\mathbb R^N$ with LD matrix $\mathbf R=\operatorname{Cov}(\mathbf Z)$ satisfy the cyclic structural system

$$\mathbf T=\mathbf B\mathbf T+\boldsymbol\alpha^\top\mathbf Z+\mathbf U+\boldsymbol\varepsilon,\qquad \mathbf B=\begin{pmatrix}0&\beta_{12}\\ \beta_{21}&0\end{pmatrix},$$

where $\boldsymbol\alpha\in\mathbb R^{N\times2}$ holds the direct genetic effects and the zero diagonal forbids self-feedback. Under **stability** $|\beta_{12}\beta_{21}|<1$ the reduced form has total-effect matrix

$$\mathbf A=(\mathbf I_2-\mathbf B)^{-1}=\frac{1}{1-\beta_{12}\beta_{21}}\begin{pmatrix}1&\beta_{12}\\ \beta_{21}&1\end{pmatrix},$$

and the GWAS marginal associations are $\widehat{\boldsymbol\Gamma}=\mathbf R\boldsymbol\alpha\mathbf A^\top+\mathbf E$ with Gaussian summary errors $\mathbf e_j\sim\mathcal N(\mathbf 0,\boldsymbol\Sigma_j)$ independent of $\boldsymbol\alpha$.

**Assumption (direct effects).** The rows $\boldsymbol\alpha_{j\cdot}$ are i.i.d. across variants, mean zero, with *independent* components of finite positive variances (no correlated pleiotropy at the level of direct effects), and at most one component is Gaussian.

**LD-score normalization.** With LD scores $\ell_j=\sum_r R_{jr}^2$, the rows $\mathbf x_j=\ell_j^{-1/2}\widehat{\boldsymbol\Gamma}_{j\cdot}$ satisfy the heteroscedastic noisy ICA model

$$\mathbf x_j=\mathbf A\mathbf s_j+\widetilde{\mathbf e}_j,\qquad \mathbf s_j=\ell_j^{-1/2}\sum_r R_{jr}\boldsymbol\alpha_{r\cdot},\qquad \operatorname{Cov}(\mathbf s_j)=\operatorname{diag}(\sigma^2_{\alpha,1},\sigma^2_{\alpha,2}),$$

with independent source coordinates and $\operatorname{Cov}(\widetilde{\mathbf e}_j)=\ell_j^{-1}\boldsymbol\Sigma_j$.

**Theorem (identification).**
1. If $\mathbf A$ is invertible, it is identified from the distribution of $\mathbf x_j$ up to column scaling and permutation.
2. Given $\mathbf A$ up to scaling and permutation and $|\beta_{12}\beta_{21}|<1$, $\mathbf B$ is recovered uniquely: invert the identified mixing matrix, normalize each admissible row ordering to unit diagonal (no self-feedback), and keep the ordering satisfying stability.

Hence $(\beta_{12},\beta_{21})$ is identified from the summary statistics and their error covariances, without selecting instruments or specifying a valid-instrument subset.

**Proposition (selection breaks independence).** If $\mathbf s_j$ has independent components, $\mathbf x^{(0)}_j=\mathbf A\mathbf s_j$ with $\mathbf A$ nonsingular, and variants are selected by an event $\{\mathbf x^{(0)}_j\in\mathcal C\}$ of probability in $(0,1)$ such that $\mathbf A^{-1}\mathcal C$ is not a Cartesian product (up to null sets), then the source components are dependent given selection. Thresholding on significance in either trait therefore invalidates the ICA premise.

**Theorem (inference).** Under moment and strong-mixing (local LD) conditions and a nondegenerate fourth-order contrast, the moment-based estimator built from noise-adjusted second- and fourth-order cumulants satisfies $\widehat{\mathbf B}\to\mathbf B$ in probability and $\sqrt N(\widehat{\boldsymbol\beta}-\boldsymbol\beta)\to\mathcal N(\mathbf 0,\boldsymbol\Sigma_\beta)$; a chromosome-respecting moving block bootstrap with block length $l_N\to\infty$, $l_N=o(N^{1/2})$, consistently estimates $\boldsymbol\Sigma_\beta$.

## Expansion

Because $\mathbf B^2=\beta_{12}\beta_{21}\mathbf I_2$, stability makes $\mathbf I_2-\mathbf B$ invertible. Normalizing by $\ell_j^{1/2}$ removes the variant-specific scale of the LD-aggregated direct effects without touching $\mathbf A$, so classical ICA identifiability (non-Gaussian independent sources, Comon–Darmois–Skitovich) applies after subtracting the known Gaussian error contribution from the moment tensors. The scale and permutation ambiguities of ICA are exactly the freedoms that the unit-diagonal and stability constraints remove: the two row orderings give $\mathbf B$ and a candidate with product $1/(\beta_{12}\beta_{21})$, of which only one is stable.

## Sources

- Liyuan Mo, Qingyuan Zhao, "Identification and Inference of Bi-directional Causal Effects in Mendelian Randomization without Instrument Selection", arXiv:2611.18291 (2026): structural model and Assumptions (stability, summary error, direct-effect distribution), Section 3.1, Theorem 1, Proposition 1, Theorem 2, Proposition 2, and supplementary Theorem 3 and Proposition 3. <https://doi.org/10.48550/arXiv.2611.18291>
