# Entropy increase under mixing, disturbance and network decoupling

For a $p$-variate expression profile $\mathbf Y$ with density $f$, the heterogeneity is measured by the differential entropy $H(\mathbf Y)=-\int f\log f$; for $\mathbf Y\sim\mathcal N(\boldsymbol\mu,\boldsymbol\Sigma)$, $H(\mathbf Y)=\tfrac12\log\det(2\pi e\,\boldsymbol\Sigma)$.

**Proposition 1 (mixtures).** If $f_z$ is a density for each $z$ in a domain $D$, $G$ is a probability distribution on $D$ and $f_G=\int_Df_z\,dG(z)$, then

$$-\int f_G\log f_G\ \ge\ -\int_D\int f_z\log f_z\,d\mathbf Y\,dG(z):$$

a population mixing regulatory states (e.g. modules with different DNA copy number) is at least as heterogeneous as the average of its components.

**Proposition 2 (disturbances).** Let $\mathbf Y_t=\boldsymbol\nu+\mathbf A\mathbf Y_{t-1}+\boldsymbol\varepsilon_t$ be a Gaussian VAR(1) process with $\boldsymbol\varepsilon_t\sim\mathcal N(\mathbf 0,\boldsymbol\Sigma_\varepsilon)$ independent and $\mathbf Y_0=\mathbf 0$, and let $\mathbf Y^{(\tau)}_t$ add an independent disturbance $\boldsymbol\delta_\tau\sim\mathcal N(\mathbf 0,\boldsymbol\Sigma_\delta)$ at time $\tau$. Then for every $t\ge\tau$, $H(\mathbf Y^{(\tau)}_t)\ge H(\mathbf Y_t)$, with strict inequality when the propagated covariance $\mathbf A^{t-\tau}\boldsymbol\Sigma_\delta(\mathbf A^{t-\tau})^\top$ is nonzero and the baseline covariance $\operatorname{Cov}(\mathbf Y_t)$ is positive definite: a disturbance never lowers heterogeneity. No ordering by the time of the disturbance holds in general: in the scalar model with $A=1/2$ and unit-variance shocks, a disturbance at $t-2$ adds $1/16$ to the variance at $t$ and one at $t-1$ adds $1/4$, so the later disturbance leaves more entropy.

**Proposition 3 (decoupling).** Let $\mathbf X\sim\mathcal N(\mathbf 0,\boldsymbol\Sigma_X)$ and $\mathbf Y\sim\mathcal N(\mathbf 0,\boldsymbol\Sigma_Y)$ have equal marginal variances, and suppose their partial correlation matrices (standardized concentration matrices) have the block form

$$\boldsymbol\Omega_{\boldsymbol\gamma}=\begin{pmatrix}\boldsymbol\Omega_{11}&\gamma_{12}\boldsymbol\Omega_{12}&\cdots&\gamma_{1r}\boldsymbol\Omega_{1r}\\ \gamma_{12}\boldsymbol\Omega_{12}^\top&\boldsymbol\Omega_{22}&&\vdots\\ \vdots&&\ddots&\vdots\\ \gamma_{1r}\boldsymbol\Omega_{1r}^\top&\cdots&\cdots&\boldsymbol\Omega_{rr}\end{pmatrix},\qquad \boldsymbol\gamma\in[0,1]^{r(r-1)/2},$$

with the same blocks and coupling vectors $\boldsymbol\gamma^{(x)}$, $\boldsymbol\gamma^{(y)}$. If $\boldsymbol\gamma^{(x)}\le\boldsymbol\gamma^{(y)}$ elementwise, then $H(\mathbf Y)\le H(\mathbf X)$: weaker conditional dependence between gene modules gives larger entropy.

## Proof depends on

- [Jensen's inequality](../../../../MeasureTheory/integration/jensen-s-inequality-for-integrals/jensen-s-inequality/jensen-inequality.md)

## Expansion

Proposition 1 is concavity of $u\mapsto-u\log u$ with Jensen's inequality (the gap is the mutual information between $\mathbf Y$ and the latent state). For the first claim of Proposition 2, $\mathbf Y^{(\tau)}_t=\mathbf Y_t+\mathbf A^{t-\tau}\boldsymbol\delta_\tau$ for $t\ge\tau$ with independent summands, so its covariance exceeds that of $\mathbf Y_t$ by the positive semidefinite term $\mathbf A^{t-\tau}\boldsymbol\Sigma_\delta(\mathbf A^{t-\tau})^\top$ and the Gaussian entropy $\tfrac12\log\det(2\pi e\boldsymbol\Sigma)$ does not decrease, since $\det(\boldsymbol\Sigma+\mathbf D)\ge\det\boldsymbol\Sigma$ for positive semidefinite $\mathbf D$, with equality for positive definite $\boldsymbol\Sigma$ only when $\mathbf D=\mathbf 0$. With $\mathbf A=\mathbf 0$ the disturbance has no effect after time $\tau$. The source's Proposition 2 also states an ordering by disturbance time; the scalar example above shows it needs a further hypothesis. Proposition 3 is proved in the paper's supplementary material. Proposition 3 formalizes that in a fully connected network each gene is constrained by the others, while in a disconnected one each varies freely. Biologically, cancer-related loss of regulatory control between modules shows up as increased transcriptomic heterogeneity.

## Sources

- W. N. van Wieringen and A. W. van der Vaart, "Transcriptomic heterogeneity in cancer as a consequence of dysregulation of the gene–gene interaction network", Bulletin of Mathematical Biology 77(9) (2015) 1768–1786, <https://doi.org/10.1007/s11538-015-0103-7>, PMCID PMC4644214. Models (4)–(5) and Propositions 1–3.
