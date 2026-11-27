# Selection coefficient from a pairwise competition assay

**Setting.** Two asexual strains, resistant ($R$) and susceptible ($S$), compete in serial batch culture. Let $N_R(t), N_S(t) > 0$ be their abundances after $t$ generations and $\mathcal{R}(t) = N_R(t)/N_S(t)$ the ratio. Assume constant relative fitness $w_R / w_S = e^{s}$ per generation, with $s \in \mathbb{R}$ independent of the frequencies.

**Proposition.** For every $t \ge 0$,

$$\ln \mathcal{R}(t) = \ln \mathcal{R}(0) + s\,t, \qquad \text{so} \qquad s = \frac{\ln\big(\mathcal{R}(t)/\mathcal{R}(0)\big)}{t} \quad (t > 0).$$

Given measurements at times $t_1, \dots, t_n$, the regression estimate of $s$ is the least-squares slope of $\ln \mathcal{R}(t_\ell)$ on $t_\ell$. The selection coefficient does not depend on the initial ratio $\mathcal{R}(0)$; $s < 0$ in the absence of drug measures the fitness cost of resistance.

## Depends on

- [Log-odds grow linearly under repeated haploid selection on two types](../log-odds-iterate-select.md)

## Expansion

With frequency $p_t = N_R/(N_R + N_S)$ the ratio is the odds $p_t/(1 - p_t)$, so the linear growth of the log-odds under constant haploid fitnesses with $\ln(w_R/w_S) = s$ is exactly the displayed identity. The source counts about $10^5$ fluorescently tagged cells per time point, which resolves $|s|$ down to about $0.003$, and observes the same $s$ from initial resistant fractions of $10^{-4}$ and $1/2$, as frequency independence predicts.

## Sources

- E. Gullberg, S. Cao, O. G. Berg, C. Ilbäck, L. Sandegren, D. Hughes and D. I. Andersson, *Selection of resistant bacteria at very low antibiotic concentrations*, PLoS Pathog. 7 (2011), e1002158. <https://doi.org/10.1371/journal.ppat.1002158> (PMCID: PMC3141051). Results; Materials and Methods, "Competition experiments".
