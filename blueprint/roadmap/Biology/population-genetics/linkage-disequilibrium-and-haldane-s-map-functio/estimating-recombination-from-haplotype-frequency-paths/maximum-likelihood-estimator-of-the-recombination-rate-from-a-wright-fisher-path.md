# Maximum likelihood estimator of the recombination rate from a continuously observed Wright–Fisher path

**Model.** Consider two loci with $K$ alleles at locus A and $L$ alleles at locus B, and let $X(t)=(X_{ij}(t))$ be the haplotype frequencies, a Wright–Fisher diffusion on the simplex $\Delta_{KL-1}$ with diffusion coefficient $V_{(ij),(kl)}(x)=x_{ij}(\delta_{(ij),(kl)}-x_{kl})$ and drift $c(x)+a(x;\rho)$, where

$$a_{ij}(x;\rho)=\rho\,\big(x_{i\cdot}x_{\cdot j}-x_{ij}\big),\qquad x_{i\cdot}=\sum_l x_{il},\quad x_{\cdot j}=\sum_k x_{kj},$$

is recombination at rate $\rho\ge0$ and $c(x)$ is a known drift (for example, parent-dependent mutation at rates $\theta_A/2$, $\theta_B/2$). The coefficient of linkage disequilibrium of haplotype $(i,j)$ is $D_{ij}=x_{ij}-x_{i\cdot}x_{\cdot j}$.

**Likelihood and estimator.** For a path observed on $[0,T]$, with $\widetilde X_{ij}(t)=X_{ij}(t)-\int_0^t c_{ij}(X(s))\,ds$, and on the event that the observed information $I_T$ below is finite (the source's standing condition for the likelihood to be a Radon–Nikodym derivative), the log-likelihood relative to complete linkage ($\rho=0$) is the quadratic

$$\log L_T(\rho)=\rho\int_0^T\sum_{i,j}\frac{X_{i\cdot}X_{\cdot j}}{X_{ij}}\,d\widetilde X_{ij}-\frac{\rho^2}{2}\,I_T,\qquad I_T=\int_0^T\sum_{i,j}\frac{D_{ij}(t)^2}{X_{ij}(t)}\,dt.$$

If moreover $I_T>0$ (that is, $D(t)\ne0$ on a set of times of positive measure, so the path is not in linkage equilibrium almost all the time), the quadratic has negative leading coefficient and its unique maximiser is

$$\hat\rho_T=\frac{1}{I_T}\int_0^T\sum_{i,j}\frac{X_{i\cdot}(t)X_{\cdot j}(t)}{X_{ij}(t)}\,d\widetilde X_{ij}(t).$$

Let $S=\inf\{t\ge0:I_t=\infty\}$ and define the corrected estimator

$$\hat\rho_{\mathrm{MLE}}=\mathbf 1_{\{T<S\}}\max\{0,\hat\rho_T\}+\mathbf 1_{\{T\ge S\}}\lim_{t\uparrow S}\hat\rho_t .$$

**Results.**

1. (Error representation) On $\{T<S\}\cap\{I_T>0\}$, writing the path as the solution of $dX=[c(X)+a(X;\rho)]dt+\sigma(X)\,dW$ with $\sigma\sigma^\top=V$,

    $$\hat\rho_T-\rho=-\frac{1}{I_T}\int_0^T\sum_{i,j}\frac{D_{ij}(t)}{X_{ij}(t)}\sum_{k}\sigma_{(ij),k}(X(t))\,dW_k(t).$$

2. If $S\le T$, then $\hat\rho_{\mathrm{MLE}}=\rho$ almost surely: infinite information identifies $\rho$ without error.
3. $\hat\rho_{\mathrm{MLE}}$ is the maximum likelihood estimator of $\rho$ on $[0,\infty)$.

In the deterministic recombination model ($\theta_A=\theta_B=0$, no noise) with $\rho>0$ and an interior initial point with some $D_{ij}(0)\ne0$, one has $\hat\rho_T=\rho$ exactly for every $T>0$, while $I_T$ increases to the finite limit $\rho^{-1}\sum_{i,j}x_{i\cdot}(0)x_{\cdot j}(0)\log\big(x_{i\cdot}(0)x_{\cdot j}(0)/x_{ij}(0)\big)$ as $T\to\infty$. The hypothesis $\rho>0$ is needed: for $\rho=0$ the deterministic path is constant, so $I_T$ grows linearly in $T$ whenever $D(0)\ne0$.

## Expansion

The likelihood comes from Girsanov's theorem applied to the first $KL-1$ coordinates, whose covariance matrix $V^*$ is invertible with an explicit inverse; the singular last coordinate drops out because $\sum_{ij}d\widetilde X_{ij}=0$. Since the drift is linear in $\rho$, the log-likelihood is quadratic with leading coefficient $-I_T/2$, which is negative when $0<I_T<\infty$. Substituting the SDE into $\hat\rho_T$ gives the error formula. The numerator $N_T$ of the error is a continuous martingale whose quadratic variation equals $I_T$ (a direct computation using $\sigma\sigma^\top=V$), so the error is $N_T/\langle N\rangle_T$; on $\{\langle N\rangle_T\to\infty\}$ the strong law for martingales gives $N_T/\langle N\rangle_T\to0$, which proves statement 2. The rectification $\max\{0,\cdot\}$ handles paths that point to negative $\rho$.

## Depends on

- [Linkage disequilibrium of a two-locus gamete law](../linkage-diseq.md)
- [Pairwise linkage disequilibria of two multi-allelic loci](../linkage-diseq-2.md)

## Sources

- Robert C. Griffiths and Paul A. Jenkins, "An estimator for the recombination rate from a continuously observed diffusion of haplotype frequencies", *Journal of Mathematical Biology* 86 (2023), 98, <https://doi.org/10.1007/s00285-023-01931-7>. Numbering as in the preprint arXiv:2212.07747v2, <https://arxiv.org/abs/2212.07747v2>: Section 2.2, Theorem 1; Section 3.2, Proposition 1, Theorem 2 and Corollaries 1–2.
