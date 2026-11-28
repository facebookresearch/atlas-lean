# Normalized forward sensitivity index

**Definition.** Let $Q(\theta) > 0$ be a differentiable function of a positive parameter $\theta$ (typically $Q = R_0$ of an epidemic model and $\theta$ a transmission, recovery or mortality rate). The normalized forward sensitivity index (elasticity) of $Q$ with respect to $\theta$ is

$$\Upsilon^Q_\theta = \frac{\partial Q}{\partial \theta}\cdot \frac{\theta}{Q} = \frac{\partial \log Q}{\partial \log \theta}.$$

To first order, a $1\%$ increase in $\theta$ changes $Q$ by $\Upsilon^Q_\theta\,\%$.

**Proposition.**
1. *(Products of powers.)* If $Q = c \prod_k \theta_k^{p_k}$ with $c$ independent of the $\theta_k$, then $\Upsilon^Q_{\theta_k} = p_k$.
2. *(Chain and sum rules.)* $\Upsilon^{Q_1 Q_2}_\theta = \Upsilon^{Q_1}_\theta + \Upsilon^{Q_2}_\theta$, $\Upsilon^{Q^p}_\theta = p\,\Upsilon^{Q}_\theta$, and for $Q = Q_1 + Q_2$ with $Q_i > 0$, $\Upsilon^Q_\theta = \frac{Q_1}{Q}\Upsilon^{Q_1}_\theta + \frac{Q_2}{Q}\Upsilon^{Q_2}_\theta$.
3. *(Maxima.)* If $Q = \max\{Q_1, Q_2\}$ and $Q_1 > Q_2$ near $\theta$, then $\Upsilon^Q_\theta = \Upsilon^{Q_1}_\theta$.
4. *(Scale invariance.)* The index does not depend on the units of $\theta$ or $Q$, and if $Q$ depends on $\theta$ only through a dimensionless group the indices of the parameters in that group are proportional to their exponents in it.

**Example (vector-borne co-infection).** In a malaria–visceral-leishmaniasis co-infection model with mosquito and sandfly vectors and an animal reservoir, the next-generation spectral radius is $R_0 = \max\{R_m, R_l\}$, the larger of the two single-disease numbers, with the Ross–Macdonald form

$$R_m = \sqrt{\frac{a_m^2\, b_m\, c_m\, m}{\mu_{v_m}(\gamma_1 + \delta_1 + \mu_h)}},$$

($a_m$ biting rate, $b_m, c_m$ transmission probabilities, $m$ vector-to-host ratio, $\mu_{v_m}$ vector mortality, $\gamma_1 + \delta_1 + \mu_h$ host exit rate). When $R_m > R_l$ the indices are $\Upsilon_{a_m} = 1$, $\Upsilon_{b_m} = \Upsilon_{c_m} = \tfrac12$, $\Upsilon_{\mu_{v_m}} = -\tfrac12$ and $\Upsilon_{\gamma_1} = -\tfrac12\,\gamma_1/(\gamma_1 + \delta_1 + \mu_h)$.

**Example (SIQ model).** For an SIQ COVID-19 model with $R_0=\dfrac{\Lambda\gamma(d_0+\mu+\sigma)}{d_0\big[(d_0+k)(d_0+\mu+\sigma)+\eta(d_0+\mu)\big]}$, rule 1 gives $\Upsilon^{R_0}_\Lambda=\Upsilon^{R_0}_\gamma=1$, and the product and power rules give

$$
\Upsilon^{R_0}_\sigma=\frac{\sigma}{d_0+\mu+\sigma}-\frac{\sigma(d_0+k)}{(d_0+k)(d_0+\mu+\sigma)+\eta(d_0+\mu)}=\frac{\sigma\,\eta(d_0+\mu)}{(d_0+\mu+\sigma)\big[(d_0+k)(d_0+\mu+\sigma)+\eta(d_0+\mu)\big]}>0 ,
$$

so a higher rate of return from quarantine to the infected class raises $R_0$, while $\Upsilon^{R_0}_\eta<0$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

All rules follow from $\Upsilon^Q_\theta = d\log Q / d\log\theta$: logarithms turn products and powers into sums and multiples, the sum rule is the derivative of $\log(Q_1 + Q_2)$, and a strict maximum coincides with one branch on a neighbourhood. For the co-infection example, the infected subsystem decouples at the disease-free equilibrium into a malaria block and a leishmaniasis block, so the next-generation matrix is block diagonal and its spectral radius is the larger block radius; the square root reflects the two-step host–vector–host cycle. The index is local: it describes the effect of small changes at a baseline parameter set and can change sign or ranking elsewhere in parameter space, and $R_0 < 1$ need not suffice for elimination when the model has a backward bifurcation, as this co-infection model can. Parameters with the largest $|\Upsilon^{R_0}_\theta|$ are the most effective control targets, since equal relative changes in them move $R_0$ the most toward the threshold $1$; for interactions between parameters, global methods such as partial rank correlation are used.

## Sources

- F. B. Agusto and I. M. ELmojtaba, "Optimal control and cost-effective analysis of malaria/visceral leishmaniasis co-infection", PLoS ONE 12 (2017), e0171102, Section 2 (basic reproduction number, Theorems 2.1–2.2) and Section 3 (Eq. (2), Table 4), <https://doi.org/10.1371/journal.pone.0171102>, PMCID: PMC5293207.
- N. Chitnis, J. M. Hyman and J. M. Cushing, "Determining important parameters in the spread of malaria through the sensitivity analysis of a mathematical model", Bulletin of Mathematical Biology 70 (2008), 1272–1296, <https://doi.org/10.1007/s11538-008-9299-0>.
- A. Din, Y. Li, T. Khan, G. Zaman, "Mathematical analysis of spread and control of the novel corona virus (COVID-19) in China", Chaos, Solitons & Fractals 141 (2020) 110286, Section 5.1, <https://doi.org/10.1016/j.chaos.2020.110286> (PMC7510499).
