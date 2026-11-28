# Marked point process model and de-biased deviance test for simultaneous spiking

Discretize the spiking of $C$ neurons into bins of width $\Delta$. Each bin either contains no spike or exactly one **mark** $m \in \mathcal K$, a nonempty pattern of simultaneously spiking neurons, so the ensemble is a marked point process whose ground intensity is $\lambda^{(g)}_t = \sum_m \lambda^{(m)}_t$. The joint law is a multinomial generalized linear model with multinomial logistic link,

$$x_t^\top \omega^{(m)}_t = \log\frac{\lambda^{(m)}_t\Delta}{1 - \lambda^{(g)}_t\Delta}, \qquad \omega^{(m)}_t = [\mu^{(m)}_t, \theta^{(m)\top}_t]^\top,$$

with baseline $\mu^{(m)}$ and ensemble-history modulation $\theta^{(m)}$ (Mukherjee and Babadi 2024, Eq. 1). This representation avoids the regularity conditions that force conditionally independent neurons in single-neuron point process GLMs.

**Testing $r$th-order coordination.** Let $\mathcal K_r$ be the marks with exactly $r$ spiking neurons and $M^{(r)} = |\mathcal K_r|$. The null hypothesis constrains the baselines of marks in $\mathcal K_r$ to the values implied by conditionally independent spiking; parameters are estimated adaptively with an exponential forgetting factor $\beta$ by a greedy (orthogonal matching pursuit) filter. The test statistic is the adaptive de-biased deviance difference

$$D^{(r)}_{k,\beta} = \frac{1+\beta}{1-\beta}\left[2\left(\ell^\beta_k(\hat\omega^{(F)}_k) - \ell^\beta_k(\hat\omega^{(R)}_k)\right) - \left(B^{(F)}_k - B^{(R)}_k\right)\right]$$

between full and reduced models, with bias corrections $B$ (Eq. 9). As $\beta \to 1$ it is asymptotically $\chi^2_{M^{(r)}}$ under the null and, assuming the base rate parameters of $r$th-order interactions scale at least as $O((1-\beta)/(1+\beta))$, noncentral $\chi^2_{M^{(r)}}(\nu^{(r)}_k)$ under the alternative (Theorem 2), and the result extends to any nested hypothesis on the marks, giving adaptive Granger-causality tests (Corollary 2.2). Significance is summarized by Youden's statistic $J^{(r)}_k = 1 - \alpha - F_{\chi^2(M, \hat\nu_k)}\big(F^{-1}_{\chi^2(M)}(1-\alpha)\big)$ (Eq. 10).

## Expansion

The forgetting factor gives an effective window of order $(1-\beta)^{-1}$, and the factor $(1+\beta)/(1-\beta)$ rescales the exponentially weighted log-likelihood ratio to the usual likelihood-ratio scale. The greedy estimator selects a sparse support, so the classical Wilks theorem does not apply directly; subtracting the estimated biases of the full and reduced fits restores the chi-square limit with degrees of freedom equal to the number of constrained marks. The noncentrality is smoothed over windows by a state-space filter, and the sign of the net excess log-odds distinguishes excess from suppressed synchrony.

## Sources

- S. Mukherjee and B. Babadi, *Adaptive modeling and inference of higher-order coordination in neuronal assemblies: a dynamic greedy estimation approach*, PLoS Computational Biology (2024), e1011605, Eqs. (1), (8)–(10), Theorem 2, Corollary 2.2 and Algorithm 1. <https://doi.org/10.1371/journal.pcbi.1011605> (PMCID: PMC11161120)
