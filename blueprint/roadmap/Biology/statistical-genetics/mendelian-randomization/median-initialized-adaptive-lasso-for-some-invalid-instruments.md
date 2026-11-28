# Median-initialized adaptive Lasso for some invalid instruments

In Mendelian randomization with individual-level data, consider $n$ observations of an outcome $y$, an exposure $d$ and $L$ genetic instruments $Z$ in the linear model

$$y = d\beta + Z\alpha + \varepsilon, \qquad d = Z\gamma + v,$$

where $\alpha_j \ne 0$ means instrument $j$ is **invalid** (a direct, pleiotropic effect on $y$). Let $A = \{j : \alpha_j \ne 0\}$ with $|A| = s$, and let $\Gamma = \gamma\beta + \alpha$ be the reduced-form coefficients, so the per-instrument ratios are

$$\pi_j = \frac{\Gamma_j}{\gamma_j} = \beta + \frac{\alpha_j}{\gamma_j}.$$

$\beta$ is identified when the valid instruments form the largest group of equal $\pi_j$; a sufficient condition is $s < L/2$.

**Assumptions** (source, Section 2 and Assumptions 1–4). The data $(y_i, D_i, Z_{i\cdot})$, $i = 1, \dots, n$, are an **i.i.d. sample**, with $Z_{i\cdot}$ the $i$-th row of $Z$ (a $1 \times L$ row vector), $D_i$ the exposure and $u_i = (\varepsilon_i, v_i)^{\mathsf T}$. The outcome error has **conditional mean zero** and **constant conditional variance**, $\mathbb{E}[\varepsilon_i \mid Z_{i\cdot}] = 0$ and $\mathbb{E}[\varepsilon_i^2 \mid Z_{i\cdot}] = \sigma_\varepsilon^2$ (source, after (3)), while the first-stage coefficient $\gamma = Q^{-1}\mathbb{E}[Z_{i\cdot}^{\mathsf T}D_i]$ is defined by linear projection so $\mathbb{E}[Z_{i\cdot}^{\mathsf T}v_i] = 0$ (source, after (8)), and Assumption 2 specifies the unconditional second-moment matrix $\mathbb{E}[u_iu_i^{\mathsf T}] = \Sigma$ (without imposing $\mathbb{E}[v_i^2 \mid Z_{i\cdot}]$ constant). The parameters $\beta, \alpha, \gamma$ and the number $L$ of instruments are fixed as $n \to \infty$, and:

1. $\mathbb{E}[Z_{i\cdot}^{\mathsf T}Z_{i\cdot}] = Q$ is a finite $L \times L$ matrix of full rank;
2. $\mathbb{E}[u_i] = 0$ and $\mathbb{E}[u_iu_i^{\mathsf T}] = \Sigma$ has finite entries;
3. $n^{-1}Z^{\mathsf T}Z \to_p Q$, $n^{-1}Z^{\mathsf T}d \to_p \mathbb{E}[Z_{i\cdot}^{\mathsf T}D_i]$, $n^{-1}Z^{\mathsf T}\varepsilon \to_p 0$, $n^{-1}Z^{\mathsf T}v \to_p 0$, $n^{-1}\sum_i u_i \to_p 0$ and $n^{-1}\sum_i u_iu_i^{\mathsf T} \to_p \Sigma$;
4. $\gamma = Q^{-1}\mathbb{E}[Z_{i\cdot}^{\mathsf T}D_i]$ with $\gamma_j \ne 0$ for every $j = 1, \dots, L$.

The valid-ratio limit uses the CLT for $n^{-1/2}Z^{\mathsf T}\varepsilon$ and consistency of $\hat\gamma$; no joint CLT with the first-stage residual is needed.

The ratio estimates are $\hat\pi_j = \hat\Gamma_j/\hat\gamma_j$, from the least-squares reduced-form and first-stage coefficients $\hat\Gamma = (Z^{\mathsf T}Z)^{-1}Z^{\mathsf T}y$ and $\hat\gamma = (Z^{\mathsf T}Z)^{-1}Z^{\mathsf T}d$. The Lasso approach (sisVIVE) estimates $\alpha$ by $\ell_1$-penalized regression of $y$ on $Z$ after projecting out $\hat d = Z\hat\gamma$.

**Selection failure of the Lasso.** Two irrepresentable conditions on the limit $C$ of $n^{-1}\tilde Z^{\mathsf T}\tilde Z$, where $\tilde Z$ is $Z$ with $\hat d$ projected out, must be distinguished. The **strict** condition $\|C_{21}C_{11}^{-1}\operatorname{sign}(\alpha_1)\|_\infty < 1$ (source (15)) is, together with the tuning assumptions, **sufficient** for consistent selection; the **necessary** condition is the weak inequality $\|C_{21}C_{11}^{-1}\operatorname{sign}(\alpha_1)\|_\infty \le 1$ (source (16)). Both depend on the instrument strengths as well as their correlations: if $|\gamma_1^{\mathsf T} \operatorname{sign}(\alpha_1)| > \|\gamma_2\|_1$ ($\gamma_1$, $\gamma_2$ the first-stage coefficients of the invalid and valid instruments), the norm is **greater than** $1$ (source Proposition 2), so even the necessary condition (16) fails and the Lasso cannot select consistently. The remaining statements in this paragraph concern the strict condition (15). With equal-strength instruments the condition can fail for some sign configurations of $\alpha_1$ once $s > L/2$; for uncorrelated equal-strength instruments it holds for every configuration when $s < L/2$. With $s < L/2$ it can still fail when the instrument strengths differ (as in the condition above) or the instruments are correlated, so the Lasso can select the wrong instruments even when $\beta$ is identified.

**Theorem (median estimator; source Theorem 1).** Under Assumptions 1–4, if $s < L/2$, then $\hat\beta_m = \operatorname{median}(\hat\pi_1,\dots,\hat\pi_L)$ satisfies $\operatorname{plim}\hat\beta_m = \beta$. Order the instruments so that $1, \dots, s$ are the invalid ones, and let $\hat\pi_2$ be the vector of the $L - s$ valid ratios $\hat\pi_j$, $j = s+1, \dots, L$. Then $\sqrt n(\hat\beta_m - \beta) \to_d q_{[l],L-s}$, where:

- for $L$ odd, $q_{[l],L-s}$ is the $l$-th order statistic of the limiting normal distribution of $\sqrt n(\hat\pi_2 - \beta\iota_{L-s})$, with $l$ determined by $L$, $s$ and the signs of $\delta_j = \alpha_j/\gamma_j$, $j = 1, \dots, s$;
- for $L$ even, $q_{[l],L-s}$ is the average of two neighbouring order statistics of that distribution, either the $[l]$-th and $[l-1]$-th or the $[l]$-th and $[l+1]$-th.

For even $L$ the limit is generally not a single order statistic: with $L = 2$ and $s = 0$ it is the mean of the two coordinates of a bivariate normal vector. The limit is generally not centred at zero, so $\hat\beta_m$ has an asymptotic bias.

**Proposition (adaptive Lasso; source Proposition 3 and Corollary 2).** Under Assumptions 1–4 and $s < L/2$ (so that $\sqrt n(\hat\alpha_m - \alpha) = O_p(1)$ by the Theorem), with weights $w_j = |\hat\alpha_{m,j}|^{-\nu}$ built from the median-based estimates $\hat\alpha_m = \hat\Gamma - \hat\gamma\hat\beta_m$, and a tuning parameter $\lambda_n = o(\sqrt n)$ with $n^{(\nu-1)/2}\lambda_n \to \infty$, the adaptive Lasso selects $A$ with probability tending to one, and $\sqrt n(\hat\alpha_{ad,A} - \alpha_A)$ is asymptotically normal. Consequently $\sqrt n(\hat\beta_{ad} - \beta) \to N(0, \sigma^2_{\beta,\mathrm{or}})$, the limit of the oracle two-stage least squares estimator that knows which instruments are invalid.

## Depends on

- [Linear moment model for instrumental variables](linear-moment-model.md)
- [The sisVIVE estimator](sisvive-estimator.md)

## Proof depends on

Its proof is that of the source below, as the Expansion describes.

## Expansion

The median is robust because, when fewer than half the ratios $\pi_j$ are shifted away from $\beta$ by pleiotropy, the middle order statistic is a valid ratio in the limit; but its $\sqrt n$ limit (an order statistic of the valid ratios' limit for odd $L$, the average of two neighbouring ones for even $L$) is generally not centred at zero, so it serves only as a consistent pilot. Adaptive weights inflate the penalty on instruments whose pilot $\hat\alpha_{m,j}$ is near zero and shrink it on clearly invalid ones, restoring oracle selection without any irrepresentable condition. The methods are illustrated on a UK Biobank Mendelian randomization study of the effect of body mass index on diastolic blood pressure with 96 SNPs as candidate instruments.

## Sources

- F. Windmeijer, H. Farbmacher, N. Davies and G. Davey Smith, "On the use of the Lasso for instrumental variables estimation with some invalid instruments", Journal of the American Statistical Association 114 (2019), Eqs. (3)–(9), Propositions 1–3, Corollaries 1–2 and Theorem 1, <https://doi.org/10.1080/01621459.2018.1498346>, PMCID: PMC6817329.
