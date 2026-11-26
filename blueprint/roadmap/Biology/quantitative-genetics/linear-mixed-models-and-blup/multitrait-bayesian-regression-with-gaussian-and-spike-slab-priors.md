# Multitrait Bayesian regression with Gaussian, spike–slab and kernel priors

Let $Y$ be an $n\times t$ phenotype matrix (individuals in rows, traits in columns; entries may be missing). The multitrait data equation is

$$Y=\mathbf 1\mu^\top+X_1B_1+X_2B_2+\cdots+U_1+U_2+\cdots+E,$$

where $\mu\in\mathbb R^t$ holds trait intercepts, each $X_*$ is an $n\times p_*$ matrix of predictors (for example SNP genotypes) with a $p_*\times t$ effect matrix $B_*$, each $U_*$ is an $n\times t$ matrix of random effects, and the rows of $E$ are independent $\mathrm{MVN}(0,R_0)$. Writing $\theta=(\mu,B_1,B_2,\ldots,U_1,U_2,\ldots,R_0)$ and $\eta_i=\mu+B_1^\top x_{1i}+B_2^\top x_{2i}+\cdots+u_{1i}+u_{2i}+\cdots$ for the conditional mean of row $i$,

$$p(Y\mid\theta)=\prod_{i=1}^{n}\mathrm{MVN}(y_i\mid\eta_i,R_0)$$

is the **complete-data** density, for rows with all $t$ entries present. When row $i$ has observed coordinates $O_i\subseteq\{1,\ldots,t\}$, the **observed-data** likelihood replaces its factor by the marginal density $\mathrm{MVN}(y_{i,O_i}\mid\eta_{i,O_i},R_{0,O_iO_i})$ of the observed entries, with the subvector of the mean and the submatrix of $R_0$ on $O_i$ (a row with no observed entry contributes the factor $1$).

The prior factorizes over the terms, $p(\theta)=p(\mu)\,p(B_1)p(B_2)\cdots p(U_1)p(U_2)\cdots p(R_0)$, with the following priors (and, for a regression term with variable selection, the spike–slab prior below):

- **Intercepts:** $\mu\sim\mathrm{MVN}(0,mI)$ with $m$ large (diffuse).
- **Kernel random effects:** $\operatorname{vec}(U_*)\sim\mathrm{MVN}(0,\Omega_*\otimes K_*)$, where $\operatorname{vec}$ stacks columns, $\Omega_*$ is an unknown $t\times t$ covariance between traits and $K_*$ is a known $n\times n$ covariance structure such as a genomic relationship matrix.
- **Gaussian regression:** the rows $b_{*j}$ of $B_*$ are independent $\mathrm{MVN}(0,\Omega_*)$, $j=1,\ldots,p_*$.
- **Covariances:** each $\Omega_*$ and $R_0$ is either unstructured with an inverse-Wishart prior $\mathrm{IW}(S_0,\mathrm{df}_0)$, or structured (diagonal with scaled inverse-$\chi^2$ variances, factor analytic, or recursive).

**Spike–slab regression (multitrait BayesC).** The effects are $b_{*jk}=\alpha_{*jk}\,d_{*jk}$ with $d_{*jk}\in\{0,1\}$ and prior

$$p(A_*,D_*)=\prod_{j=1}^{p_*}\mathrm{MVN}(\alpha_{*j}\mid0,\Omega_*)\times\prod_{j=1}^{p_*}\prod_{k=1}^{t}\pi_{*k}^{d_{*jk}}(1-\pi_{*k})^{1-d_{*jk}},$$

where $\pi_{*k}$ is the prior proportion of predictors with a nonzero effect on trait $k$, given independent Beta priors. A predictor may thus affect some traits and not others.

All full conditional distributions are of closed form, so the joint posterior is sampled by Gibbs sampling; missing phenotypes are drawn at each iteration from their (multivariate normal) full conditional given the observed entries of the row (data augmentation), after which the complete-data density applies.

**Genetic covariance under variable selection.** Because only a fraction of the $\alpha_{*j}$ are active, $\Omega_*$ is not itself the genetic covariance. Three plug-in estimators, each averaged over Gibbs samples, are: (1) the sample covariance of the columns of $B=A\# D$ (elementwise product); (2) the sample covariance matrix of the realized genomic values $U=XB$, which accounts for linkage disequilibrium among predictors; and (3) $G_{0kk}=c\,\Omega_{kk}\,p_k$ and $G_{0kk'}=c\,\Omega_{kk'}\,p_{kk'}$, where $c=\sum_j\operatorname{Var}(x_j)$, $p_k$ is the proportion of markers with a nonzero effect on trait $k$ and $p_{kk'}$ the proportion with nonzero effects on both $k$ and $k'$.

## Depends on

- [BLUP as a conditional law](cond-distrib-mixed-model.md)
- [Genetic relationship matrix entry](../genomic-relationship-matrices/grm.md)

## Proof depends on

None: the page defines the model, its priors and the plug-in estimators; the closed-form full conditionals follow from conjugacy, as the Expansion describes.

## Expansion

- With a single Gaussian term, $\Omega$ and $R_0$ fixed and $t=1$, the model is the Gaussian mixed model and the posterior mean of the random effects is BLUP.
- Conditional on the covariances, the Gaussian priors are conjugate to the Gaussian likelihood, giving normal full conditionals for $\mu$, each row of $B_*$ and each $U_*$; the indicators $d_{*jk}$ have Bernoulli full conditionals obtained by comparing the likelihood with $b_{*jk}=\alpha_{*jk}$ and with $b_{*jk}=0$; inverse-Wishart priors give inverse-Wishart full conditionals for unstructured covariances; Beta priors give Beta full conditionals for the $\pi_{*k}$.
- In the paper's simulations, estimator (2) had the smallest bias for genetic (co)variances under the spike–slab prior.

## Sources

- P. Pérez-Rodríguez, G. de los Campos, *Multitrait Bayesian shrinkage and variable selection models with the BGLR-R package*, Genetics 222 (2022), iyac112, <https://doi.org/10.1093/genetics/iyac112>, PMCID PMC9434216 (Equations 1–6; section Estimation of variance components).
