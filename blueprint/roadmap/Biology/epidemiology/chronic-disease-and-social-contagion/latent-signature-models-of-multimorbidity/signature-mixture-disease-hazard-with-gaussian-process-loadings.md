# Signature-mixture disease hazard with Gaussian-process loadings

**Model.** For individual $i = 1,\dots,N$, disease $d = 1,\dots,D$ and discrete time (age) $t = 1,\dots,T$, the hazard $\pi_{idt}$, the probability that disease $d$ first occurs at $t$ given that $i$ is still at risk, is a mixture over $K$ latent *signatures*:

$$\pi_{idt} = \kappa\sum_{k=1}^{K}\theta_{ikt}\,\operatorname{sigmoid}(\phi_{kdt}), \qquad \operatorname{sigmoid}(u) = \frac{1}{1+e^{-u}},$$

with a global calibration constant $\kappa$, individual time-varying loadings

$$\theta_{ikt} = \frac{\exp(\lambda_{ikt})}{\sum_{k'=1}^{K}\exp(\lambda_{ik't})},$$

and signature–disease log-odds $\phi_{kdt}$. The latent trajectories carry Gaussian-process priors,

$$\boldsymbol{\lambda}_{ik} \sim \mathcal{GP}\bigl(r_k + \boldsymbol{\Gamma}_k^{\top}\mathbf{g}_i,\; \Omega_\lambda\bigr), \qquad \boldsymbol{\phi}_{kd} \sim \mathcal{GP}\bigl(\mu_d + \psi_{kd},\; \Omega_\phi\bigr),$$

where $r_k$ is a signature baseline, $\mathbf{g}_i$ a vector of individual covariates (polygenic scores, sex and genetic principal components) with effects $\boldsymbol{\Gamma}_k \sim \mathcal{N}(\mathbf{0}, \sigma_\gamma^2 I)$, $\mu_d$ the logit of the prevalence of disease $d$, $\psi_{kd}$ a time-invariant signature–disease association, and the kernels are squared-exponential,

$$\Omega_\lambda(t,t') = \alpha_\lambda^2\exp\Bigl(-\frac{(t-t')^2}{2l_\lambda^2}\Bigr), \qquad \Omega_\phi(t,t') = \alpha_\phi^2\exp\Bigl(-\frac{(t-t')^2}{2l_\phi^2}\Bigr).$$

**Structure.** Given $\theta$ and $\phi$, diseases are conditionally independent; every correlation between diseases arises from shared signatures. Because $\sum_k\theta_{ikt} = 1$ and $0 < \operatorname{sigmoid} < 1$, every $\pi_{idt}$ lies in $(0, \kappa)$, so $\kappa \le 1$ makes it a valid probability. The hazard is a mixture of probabilities, not the probability of a mixture as in factor models on the log-odds scale, which lets an individual carry several disease processes at once and lets the model predict future onsets. Placing the Gaussian processes around the mean structure separates smooth temporal fluctuation from systematic effects such as genetic predisposition ($\boldsymbol\Gamma_k$) and fixed signature–disease association ($\psi_{kd}$).

## Depends on

- [Softmax](../../../../ComputerScience/machine-learning/attention-and-low-rank-adaptation/softmax-attention-basics/softmax.md)

## Remarks

The softmax maps unconstrained latent trajectories to a point of the probability simplex at each time, so $\theta_{i\cdot t}$ is a time-varying membership profile of the individual over signatures. Each signature contributes its own age-dependent disease probability $\operatorname{sigmoid}(\phi_{kdt})$, and the individual's hazard is the membership-weighted average, scaled by $\kappa$. Genetic effects enter only through the prior mean of $\lambda$, so a polygenic score shifts an individual's propensity toward a signature, which then changes the hazards of all diseases loaded on it. Summaries of the fitted trajectories, such as the area under $\theta_{ikt}$, can serve as quantitative phenotypes for association studies.

## Sources

- S. M. Urbut, Y. Ding, T. Nakao et al., "A Bayesian framework for longitudinal EHR and genetic discovery", Nature (2026), "Methods overview" (Eqs. 1–4) and Methods, "Mathematical formulation", <https://doi.org/10.1038/s41586-026-10780-5>, PMCID PMC13518248.
