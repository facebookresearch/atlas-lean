# Heteroscedasticity identification of a causal effect on a censored survival outcome

**Model.** Let $T$, $C$ be the logarithms of a survival time and a censoring time, $Y=\min(T,C)$ and $\delta=\mathbf 1\{T\le C\}$. Let $A$ be an exposure, $Z=(Z_1,\dots,Z_m)$ candidate genetic instruments, $X$ observed covariates and $U$ unobserved confounders; write $O=(Y,\delta,A,Z,X)$ and $O_A=(A,Z,X)$. The structural accelerated failure time model is

$$
T=\beta_0A+\alpha(Z,X)+\omega_T(X,U)+\varepsilon,\qquad \mathbb{E}(A\mid Z,X,U)=\gamma(Z,X)+\omega_A(X,U),
$$

with $\mathbb{E}(\varepsilon\mid A,Z,X,U)=0$ and unspecified functions $\alpha,\gamma,\omega_T,\omega_A$. A nonzero $\alpha$ is a direct (pleiotropic) effect of the instruments on the outcome, so the instruments may violate the exclusion restriction.

**Assumptions.** (Censoring) the original-scale survival and censoring times are conditionally independent given $O_A$, and $G_0(y\mid O_A)=\mathbb{P}(C>y\mid O_A)>0$. (Identification) (i) $Z\perp U\mid X$; (ii) $\mathbb{E}\{R_A(T-\beta_0A)\mid Z,X\}=\mathbb{E}\{R_A(T-\beta_0A)\mid X\}$, where $R_A=A-\mathbb{E}(A\mid Z,X)$; (iii) $\mathrm{Cov}(Z,\mathrm{Var}(A\mid Z,X)\mid X)\ne0$ (the instruments induce heteroscedasticity in the exposure).

**Uncensored case.** For any scalar $h$ put $R_Z^h=h(Z)-\mathbb{E}(h(Z)\mid X)$ and $R_T=T-\mathbb{E}(T\mid Z,X)$. The influence function of $\beta_0$ is $g(\beta;O_T)=R_Z^h\{R_AR_T-\beta R_A^2-\mathbb{E}(R_AR_T-\beta R_A^2\mid X)\}$ and

$$
\beta_0=\frac{\mathbb{E}\bigl(R_Z^h\{R_AR_T-\mathbb{E}(R_AR_T\mid X)\}\bigr)}{\mathbb{E}\bigl(R_Z^h\{R_A^2-\mathbb{E}(R_A^2\mid X)\}\bigr)}.
$$

**Theorem (identification under censoring).** Let $\xi_0(\beta;O_A)=\mathbb{E}[g(\beta;O_T)\mid O_A]$ and define the augmented inverse-probability-of-censoring-weighted moment

$$
\psi(\beta;O)=\frac{\delta}{G_0(Y\mid O_A)}\,g(\beta;O)+\Bigl(1-\frac{\delta}{G_0(Y\mid O_A)}\Bigr)\xi_0(\beta;O_A).
$$

Under the assumptions above, $\mathbb{E}\psi(\beta;O)=0$ has the unique solution $\beta=\beta_0$, and with $R_Y=Y-\mathbb{E}(Y\mid Z,X)$,

$$
\beta_0=\frac{\mathbb{E}\Bigl(R_Z^h\Bigl\{\frac{\delta}{G_0}R_AR_Y+\bigl(1-\frac{\delta}{G_0}\bigr)R_A\,\mathbb{E}(R_Y\mid O_A)-\mathbb{E}(R_AR_Y\mid X)\Bigr\}\Bigr)}{\mathbb{E}\bigl(R_Z^h\{R_A^2-\mathbb{E}(R_A^2\mid X)\}\bigr)}.
$$

Moreover, the nuisances $\mathbb{E}(Z\mid X)$, $\mathbb{E}(A\mid Z,X)$, $\mathbb{E}(Y\mid Z,X)$, $\mathbb{E}(R_A^2\mid X)$, $\mathbb{E}(R_AR_Y\mid X)$ and $\xi_0$ are Neyman orthogonal for $\psi$, whereas the censoring distribution $G(\cdot\mid O_A)$ is not, so its estimation error enters the first-order asymptotics of the resulting estimator.

## Expansion

Without censoring, the pleiotropic term $\alpha(Z,X)$ is removed by centring $T$ given $(Z,X)$, and the confounding term contributes $\mathrm{Cov}(\omega_T,\omega_A\mid X)$, which does not vary with $Z$ by (i); multiplying by $R_Z^h$ and centring given $X$ therefore leaves only $\beta_0$ times the $Z$-dependence of $\mathrm{Var}(A\mid Z,X)$, which is nonzero by (iii). This is the heteroscedasticity (no-interaction) identification strategy used for robust Mendelian randomization. Under censoring, uncensored subjects are reweighted by $1/G_0$ and censored subjects contribute the conditional expectation $\xi_0$; since $\psi$ is linear in $\beta$ and $\mathbb{E}[\psi\mid O_T,O_A]$ reduces to $g$ by conditional independence of censoring, the same denominator appears and identification again rests on (iii). With $G_0\equiv1$ the formula reduces to the uncensored one. Stacking $h(Z)=Z_j$, $j=1,\dots,m$, gives an over-identified moment vector used for generalized empirical likelihood estimation and an over-identification test.

## Sources

- Qiushi Bu, Wen Su, Xingqiu Zhao, Zhonghua Liu, *Semiparametric causal inference for right-censored outcomes with many weak invalid instruments*, arXiv (2025). Lemma 1 (influence function), Theorem 1 (identification), Proposition 1 (Neyman orthogonality). <https://doi.org/10.48550/arXiv.2509.13176>
