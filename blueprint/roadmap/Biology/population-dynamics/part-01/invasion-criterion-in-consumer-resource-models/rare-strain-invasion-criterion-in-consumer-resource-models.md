# Rare-strain invasion criterion in consumer-resource models

**Model.** Strains $\sigma$ with abundances $N_\sigma \ge 0$ interact through chemical species $x_i$ (nutrients or toxins) according to

$$\frac{dN_\sigma}{dt} = N_\sigma\big(\lambda_\sigma(N,x) - \delta_\sigma\big), \qquad \frac{dx_i}{dt} = g_i(N,x) - \sum_\sigma N_\sigma\, d_{i\sigma}(N,x),$$

where $\lambda_\sigma$ is the per capita growth rate, $\delta_\sigma > 0$ the dilution rate, $g_i$ the net influx or production rate of species $i$ and $d_{i\sigma}$ its uptake rate by strain $\sigma$, all continuously differentiable. Nutrient competition appears as a positive dependence of $\lambda_\sigma$ on shared nutrients; interference competition as a negative dependence on toxins or on weapon-carrying competitors.

**Criterion.** Let $(N_1^*,\dots,N_{\tau-1}^*, x^*)$ be a hyperbolic, locally asymptotically stable equilibrium of the resident system (all strains other than $\tau$, with $N_\tau = 0$). Then the boundary equilibrium with $N_\tau = 0$ of the full system is unstable, so that a rare strain $\tau$ invades, if

$$\lambda_\tau\big(N_1^*,\dots,N_{\tau-1}^*, N_\tau = 0, x^*\big) > \delta_\tau,$$

and it is locally asymptotically stable against invasion by $\tau$ if the reverse strict inequality holds.

**Two-strain example.** A resident $N_R$ and an invader $N_I$ share a nutrient $x$, each has a private nutrient ($x_R$, $x_I$), and the invader diverts a fraction $z \in [0,1]$ of its proteome to a toxin $y$ of potency $p$:

$$\dot N_R = N_R\Big(\frac{r_R x/k_R + R_R x_R/K_R}{1 + x/k_R + x_R/K_R} - \frac{p\,y}{y+K} - \delta\Big), \qquad \dot N_I = N_I\Big((1-z)\frac{r_I x/k_I + R_I x_I/K_I}{1 + x/k_I + x_I/K_I} - \delta\Big),$$

with nutrients supplied at rates $m, m_R, m_I$, diluted at rate $D$ and consumed with Monod uptake, and $\dot y = zgN_I - dy - N_R s y/(y+K)$. At the resident equilibrium the toxin is absent ($N_I = 0$ gives $y = 0$), so the invader's growth rate at invasion depends only on the nutrients left by the resident: toxins cannot help a rare invader establish, whereas a private nutrient ($m_I > 0$) can; once the invader is abundant, its toxin can drive the resident out.

## Expansion

At the boundary equilibrium the Jacobian is block triangular with respect to the split $(N_\tau \mid \text{rest})$, because $\partial \dot N_\tau/\partial(\text{rest}) = N_\tau\,\partial\lambda_\tau/\partial(\text{rest}) = 0$ when $N_\tau = 0$. Its spectrum is therefore that of the resident Jacobian together with the single eigenvalue $\lambda_\tau(N^*,0,x^*) - \delta_\tau$. Stability of the resident equilibrium places the other eigenvalues in the open left half-plane, so the sign of this invasion eigenvalue decides local stability (linearization theorem). In the example the invader's toxin production is proportional to $N_I$, so interference competition acts only after nutrient competition has allowed growth from rarity, matching experiments in which colicin-producing strains displaced residents only when given a private nutrient.

## Sources

- E. Bakkeren, V. Piskovsky, M. N. Y. Lee, M. T. Jahn, K. R. Foster, "Strain displacement in microbiomes via ecological competition", Nature Microbiology (2025), Results Eqs. (1)–(2) with Theorem 1 of the Supplementary Information, and Methods Eq. (3), <https://doi.org/10.1038/s41564-025-02162-w>, PMCID PMC12669036.
