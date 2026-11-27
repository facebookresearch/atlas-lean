# De-biased deviance test for latent Granger causality

**Model.** Sensor measurements $y_t \in \mathbb R^N$ and latent source activities $x_t \in \mathbb R^{rM}$ ($M$ cortical patches, $r$ components each) satisfy the state-space model

$$y_t = C x_t + n_t,\qquad x_t = \sum_{k=1}^K A_k x_{t-k} + w_t,\qquad t = 1,\dots,T,$$

with known lead-field matrix $C$ and independent Gaussian noises $n_t$, $w_t$. For a link $(j \mapsto i)$ the full model has $M_f = K(rM)^2$ VAR parameters, and the reduced model sets the cross-coefficients from patch $j$ to patch $i$ to zero, leaving $M_r = M_f - Kr^2$. The Granger-causality measure is $\mathcal F(j\mapsto i) = \log(\sigma^2_{i\setminus j}/\sigma^2_i)$, the log ratio of prediction-error variances of source $i$ without and with source $j$. Parameters are estimated by maximizing the log-likelihood $\ell(\theta) = \log p(y_{1:T};\theta)$ with an $\ell_1$ penalty on the VAR coefficients (expectation–maximization with Kalman smoothing in the E-step).

**Statistic.** With the deviance difference $\mathcal D(j\mapsto i) = 2\big(\ell(\hat\theta_f) - \ell(\hat\theta_r)\big)$ and the empirical regularization bias $\mathcal B(\theta) = -\dot\ell(\theta)^{\mathsf T}\,\ddot\ell(\theta)^{-1}\,\dot\ell(\theta)$, define the de-biased deviance

$$\mathcal D^{db}(j\mapsto i) = \mathcal D(j\mapsto i) - \mathcal B(\hat\theta_r) + \mathcal B(\hat\theta_f).$$

**Theorem.** As $T \to \infty$, with $M_d = M_f - M_r = Kr^2$,

$$\mathcal D^{db}(j\mapsto i) \mid H_0 \ \xrightarrow{d}\ \chi^2(M_d),\qquad \mathcal D^{db}(j\mapsto i) \mid H_1 \ \xrightarrow{d}\ \chi^2(M_d, \nu_{j\mapsto i}),$$

the central and non-central chi-square distributions, where $H_0$ is the reduced model (no link) and $H_1$ the full model.

**Consequences.** The link is declared at level $1-\alpha$ if $\mathcal D^{db} > F^{-1}_{\chi^2(M_d)}(1-\alpha)$, with Benjamini–Yekutieli control of the false discovery rate over the $M(M-1)$ candidate links. From $L$ independent trials the non-centrality is estimated by $\hat\nu = \max\{\frac1L\sum_{l}\mathcal D^{db,(l)} - M_d,\,0\}$, giving the false-negative rate $\eta(\alpha) = F_{\chi^2(M_d,\hat\nu)}\big(F^{-1}_{\chi^2(M_d)}(1-\alpha)\big)$.

## Expansion

Without regularization, Wilks' theorem gives the chi-square limits through asymptotic normality of the maximum-likelihood estimator; the $\ell_1$ penalty biases the estimates so that normality fails. The correction $\mathcal B$ is the one-step Newton (de-sparsifying) adjustment: a quadratic expansion of $\ell$ around each penalized estimate shows that adding $-\dot\ell^{\mathsf T}\ddot\ell^{-1}\dot\ell$ recovers the log-likelihood at the unpenalized optimum to first order, after which the classical nested-model argument applies with $M_d$ degrees of freedom. The non-centrality estimator uses that a $\chi^2(q,\nu)$ variable has mean $q + \nu$.

## Sources

- B. Soleimani, P. Das, I. M. D. Karunathilake, S. E. Kuchinsky, J. Z. Simon, B. Babadi, "NLGC: Network localized Granger causality with application to MEG directional functional connectivity analysis", NeuroImage 260:119496 (2022), Section 4 (state-space model, Eqs (8), (19)–(22), Theorem 1 and Appendix B), <https://doi.org/10.1016/j.neuroimage.2022.119496>, PMCID PMC9435442.
