# Dynamical BLUP update of mean reaction-norm parameters

**Model.** For $p$ traits and $q$ environmental cues $u_t=(u_{1,t},\dots,u_{q,t})$ measured from a reference environment $u=0$, individual $i$ in generation $t$ expresses

$$y_{j,i,t}=\big(\bar a_{j,t}+a'_{j,i,t}+v_{j,i,t}\big)+\sum_{k=1}^q\big(\bar b_{jk,t}+b'_{jk,i,t}+\eta_{jk,i,t}\big)u_{k,t},\qquad j=1,\dots,p,$$

where $\bar a,\bar b$ are population mean intercepts and slopes, $x_{i,t}=(a'_{\cdot,i,t},b'_{\cdot\cdot,i,t})$ are zero-mean additive genetic deviations with covariance $G$, and $v,\eta$ are zero-mean non-additive effects with variances giving the residual covariance $R_t$ (diagonal, depending on $u_t$). Writing $y_{i,t}=\bar y_t+Z_tx_{i,t}+e_{i,t}$ with design matrix $Z_t=[\,I_p\ \ I_p\otimes u_t^\top]$, Henderson's mixed-model equations with the $n\times n$ additive relationship matrix $A_t$ give BLUP predictions $\hat x_{i,t}$ of the individual reaction-norm deviations from phenotypes alone. Let $w_{i,t}$ be relative fitness (number of descendants normalized to mean 1), and let $\hat z'_{i,t}$ denote any component of $\hat x_{i,t}$ and $\hat z'^{\,\mathrm{desc}}_{i,t}$ its mean over the descendants of $i$ after selection but before reproduction.

**Assumption 7 (no transmission bias).** $E\big[w_{i,t}\big(\hat z'^{\,\mathrm{desc}}_{i,t}-\hat z'_{i,t}\big)\big]=0$ for every component: the predicted additive deviations carry no expected fitness-weighted change from parents to descendants, so the second (transmission) term of the Price equation $\bar z^{\,\mathrm{offspring}}_t-\bar z^{\,\mathrm{parents}}_t=\operatorname{cov}(w_{i,t},\hat z'_{i,t})+E\big[w_{i,t}(\hat z'^{\,\mathrm{desc}}_{i,t}-\hat z'_{i,t})\big]$ vanishes.

**Theorem.**

**Part 1 (update rule).** In a population described by this model and satisfying Assumption 7, the generation-to-generation change of every mean reaction-norm parameter $\bar z_t\in\{\bar a_{j,t},\bar b_{jk,t}\}$ is given by Robertson's secondary theorem of natural selection applied to the BLUP-predicted deviations,

$$\Delta\bar z_t=\operatorname{cov}\big(w_{i,t},\hat z'_{i,t}\big).$$

**Part 2 (selection-gradient form).** Under Assumption 7 and with unrelated individuals, $A_t=I_n$, the update can be written

$$\Delta\begin{pmatrix}\bar a_t\\ \bar b_t\end{pmatrix}=G\,Z_t^\top P_{yy,t}^{-1}\operatorname{cov}(w_{i,t},y_{i,t}),\qquad P_{yy,t}=Z_tPZ_t^\top,$$

where $P$ is the phenotypic covariance of the individual reaction-norm parameters and $P_{yy,t}^{-1}\operatorname{cov}(w,y)$ is the selection gradient on the expressed traits.

(The source's Theorem 1 box states only "In a population that is adequately described by Equation (7), the incremental changes in mean reaction norm parameter values from generation to generation are found from Robertson's secondary theorem of natural selection", without Assumption 7; the text before the box introduces Assumption 7 for exactly this step, and without it the Price equation keeps the transmission term, so Parts 1–2 state it.)

**Part 3 (consistency).** Assume in addition the standard assumptions of the multivariate breeder's equation (additive plus i.i.d. non-additive effects, multivariate normality, fitness acting only through phenotype, no non-selective change of breeding values) and $A_t=I_n$, and let $\theta_{i,t}$ be the individual reaction-norm parameters (intercepts $\bar a+a'+v$ and slopes $\bar b+b'+\eta$), so that $y_{i,t}=Z_t\theta_{i,t}$.

- *Without plasticity* (all slopes zero, so $y_{j,i,t}=\bar y_{j,t}+a'_{j,i,t}+v_{j,i,t}$), the dynamical BLUP update and the multivariate breeder's equation $\Delta\bar y_t=G_{aa}P_{aa}^{-1}\operatorname{cov}(w_{i,t},y_{i,t})$ give identical results in every generation.
- *With plasticity*, the BLUP update equals the selection-gradient form of Part 2 exactly, but the breeder's equation in parameter form, $\Delta\bar\theta_t=GP^{-1}\operatorname{cov}(w_{i,t},\theta_{i,t})$, agrees with it only in the limit of infinite population size $n\to\infty$: in expectation $\operatorname{cov}(w,\theta)=PZ_t^\top P_{yy,t}^{-1}\operatorname{cov}(w,y)$ under normality and selection through $y$ alone, but the sample covariances in a finite population do not satisfy this identity, so the two updates differ by a term that vanishes as $n\to\infty$.

## Expansion

Robertson's secondary theorem says the response of a mean breeding value equals the covariance between relative fitness and breeding value; BLUP supplies the breeding values of intercepts and slopes, which are never observed directly, from the single expressed phenotype per environment. The BLUP predictor is linear in the phenotypes, $\hat x_{i}=GZ_t^\top P_{yy,t}^{-1}(y_i-\bar y_t)$ for unrelated individuals, so the fitness covariance of $\hat x$ becomes $GZ_t^\top P_{yy,t}^{-1}\operatorname{cov}(w,y)$, which is Lande's selection-gradient equation for the plastic traits $y=Z_t\theta$; it reproduces the parameter-form breeder's equation only through the population identity $\operatorname{cov}(w,\theta)=PZ_t^\top P_{yy,t}^{-1}\operatorname{cov}(w,y)$, hence only as $n\to\infty$. The value of the BLUP formulation is that it accommodates relatedness ($A_t\ne I$), overlapping generations and field data where the breeder's equation in parameter form cannot be identified; normality is not needed for the BLUP equations themselves.

## Depends on

- [Breeder's equation](../breeder-s-equation/response-eq.md)
- [Lande's equation for multivariate traits](../lande-s-selection-gradient/selection-differential-mv-eq.md)
- [The Lande–Arnold selection gradient](../lande-s-selection-gradient/selection-differential-div-eq.md)
- [BLUP is the conditional expectation](../linear-mixed-models-and-blup/cond-exp-mixed-model.md)
- [Solution of Henderson's mixed-model equations](../../../Probability/linear-models-multivariate/generalized-least-squares/is-mmesolution.md)

## Proof depends on

- [Price equation](../../population-genetics/natural-selection-fisher-s-theorem-and-the-price/price.md)

## Sources

- R. Ergon, "Dynamical BLUP modeling of reaction norm evolution, accommodating changing environments, overlapping generations, and multivariate data", *Ecology and Evolution* 13(7):e10194 (2023), Section 2 (Assumptions 1–7, equations (2), (4)–(9), and the remark after (5) that (4) and (5) agree only as $n\to\infty$), Theorems 1–4 and equations (10), (12), (13), <https://doi.org/10.1002/ece3.10194>, PMCID: PMC10323147.
