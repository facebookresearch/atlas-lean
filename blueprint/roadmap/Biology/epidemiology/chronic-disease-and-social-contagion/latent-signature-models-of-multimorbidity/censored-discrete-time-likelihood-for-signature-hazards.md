# Censored discrete-time likelihood and posterior mode for signature hazards

In the [signature-mixture hazard model](signature-mixture-disease-hazard-with-gaussian-process-loadings.md), let $Y_{idt} \in \{0,1\}$ indicate the first diagnosis of disease $d$ in individual $i$ at time $t$, and let $E_{id}$ be the event time if $d$ was diagnosed and otherwise the last time $i$ was observed (censoring). Conditionally on the hazards, the disease histories have negative log-likelihood

$$\mathcal{L}_{NLL} = -\sum_{i=1}^{N}\sum_{d=1}^{D}\Biggl[\sum_{t=1}^{E_{id}-1}\log\bigl(1-\pi_{idt}\bigr) + Y_{idE_{id}}\log\pi_{idE_{id}} + \bigl(1 - Y_{idE_{id}}\bigr)\log\bigl(1-\pi_{idE_{id}}\bigr)\Biggr],$$

the three terms being survival before $E_{id}$, the event at $E_{id}$, and disease-free censoring at $E_{id}$. Only times at which the individual was at risk and observed enter. The negative log densities of the Gaussian-process priors are

$$\mathcal{L}_{GP\lambda} = \sum_{i,k}\tfrac12(\boldsymbol\lambda_{ik} - \boldsymbol\mu_{ik})^{\top}\Omega_\lambda^{-1}(\boldsymbol\lambda_{ik} - \boldsymbol\mu_{ik}), \qquad \mathcal{L}_{GP\phi} = \sum_{k,d}\tfrac12(\boldsymbol\phi_{kd} - \mu_d - \psi_{kd})^{\top}\Omega_\phi^{-1}(\boldsymbol\phi_{kd} - \mu_d - \psi_{kd}),$$

with $\boldsymbol\mu_{ik} = r_k + \boldsymbol\Gamma_k^{\top}\mathbf{g}_i$, up to additive constants. With diffuse priors on the remaining parameters, the maximum a posteriori estimate minimizes

$$\mathcal{L}_{NLL} + \mathcal{L}_{GP\lambda} + \mathcal{L}_{GP\phi}.$$

**Prediction.** For prospective prediction at time $t_0$, the population parameters ($\phi$, $\psi$, $\Gamma$, $\kappa$) are fixed from training individuals and only the new individual's $\lambda$ is fitted to data up to $t_0$. Under the discrete-time hazard model, the probability that disease $d$ occurs within the next $h$ time units, given no occurrence by $t_0$, is

$$1 - \prod_{t=t_0+1}^{t_0+h}\bigl(1 - \pi_{idt}\bigr).$$

## Depends on

- [Signature-mixture disease hazard with Gaussian-process loadings](signature-mixture-disease-hazard-with-gaussian-process-loadings.md)

## Proof depends on

- [Product-limit identity before a point](../../../../Probability/nonparametric-survival/consistency-of-the-kaplan-meier-estimator/prod-lt-one-sub-hazard.md)
- [Discrete product-limit identity](../../../../Probability/nonparametric-survival/consistency-of-the-kaplan-meier-estimator/prod-one-sub-hazard.md)

## Proof sketch

In a discrete-time hazard model the probability of a first event exactly at $E$ is $\pi_E\prod_{t<E}(1-\pi_t)$, and the probability of remaining event-free through a censoring time $E$ is $\prod_{t \le E}(1-\pi_t)$; taking logarithms and summing over individuals and diseases, which are conditionally independent, gives $\mathcal{L}_{NLL}$. The prior terms are the Gaussian log densities of the latent trajectories evaluated on the time grid, so the objective is a negative log posterior, minimized by gradient methods. The multi-step risk is the complement of surviving each future step in turn.

## Sources

- S. M. Urbut, Y. Ding, T. Nakao et al., "A Bayesian framework for longitudinal EHR and genetic discovery", Nature (2026), Methods, "Censored data and detailed E matrix formation methodology", "Likelihood function" (Eq. 5), "Objective function for maximum a posteriori computation" (Eq. 6) and "Prospective analysis", <https://doi.org/10.1038/s41586-026-10780-5>, PMCID PMC13518248.
