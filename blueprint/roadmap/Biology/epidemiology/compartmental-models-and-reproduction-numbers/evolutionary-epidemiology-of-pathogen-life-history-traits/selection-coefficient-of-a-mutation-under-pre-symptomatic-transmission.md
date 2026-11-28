# Selection coefficient of a mutation under pre-symptomatic transmission

Consider an epidemic model with susceptible fraction $S$, exposed class $E$, asymptomatic class $A$, pre-symptomatic class $P$, symptomatic class $I$ and recovered class $R$. A fraction $f$ of new infections become asymptomatic, the rest pre-symptomatic; class $X \in \{A, P, I\}$ transmits at rate $\beta_X$; pre-symptomatic individuals develop symptoms at rate $\kappa_P$; symptomatic individuals die at rate $\alpha$ (virulence). Suppose symptomatic individuals are isolated at once and asymptomatic transmission is negligible ($\beta_I, \beta_A \approx 0$), and that the exposed stage is very short. Let a mutant differ from the wild type by $\Delta\beta_P$, $\Delta f$ and $\Delta\kappa_P$, and let $q_P$ be the mutant fraction among pre-symptomatic infections. Then

$$\frac{dq_P}{dt} = s\, q_P (1 - q_P), \tag{1a}$$

$$s = S(1 - f)\,\Delta\beta_P - S\beta_P\,\Delta f - \Delta\kappa_P. \tag{1b}$$

Since the genetic variation $q_P(1 - q_P)$ is positive, the mutant increases exactly when $s > 0$: when it transmits more while pre-symptomatic, produces fewer asymptomatic infections, or stays pre-symptomatic (infectious) longer.

## Depends on

- [Negative-binomial extinction probability is the least fixed point](../../superspreading-and-negative-binomial-offspring/is-least-extinction-prob-nb-offspring.md)

## Expansion

Under these assumptions the pre-symptomatic class of each type grows at per-capita rate $S(1 - f)\beta_P - \kappa_P$ (new pre-symptomatic infections minus progression to isolated symptomatic infection). For two exponentially growing types, the mutant frequency satisfies $dq/dt = q(1 - q)(r_m - r_w)$, and the difference of growth rates is (1b) to first order in the trait differences (the exact difference also contains the product term $-S\,\Delta\beta_P\,\Delta f$). Because $s$ is proportional to $S$ in its transmission terms, selection on transmission weakens as susceptibles are depleted or contacts are reduced, while selection on $\kappa_P$ does not. In the full model, selection favours higher transmission rates, a shorter latent period, longer infectious stages (including lower virulence) and, while pre-symptomatic and symptomatic hosts dominate transmission, a smaller asymptomatic fraction. Before selection acts, a new mutant must escape stochastic loss; with mean $R_0 \approx 2.5$ new infections per case, the escape probability falls from 89% to 31% as the variance of new infections grows from 1 to 10 times the mean. These values match the survival probability of a negative-binomial branching process with that mean and variance.

## Sources

- T. Day, S. Gandon, S. Lion, S. P. Otto, "On the evolutionary epidemiology of SARS-CoV-2", Current Biology (2020), model of Figure 2, section "Modeling evolution", Eqs. (1a) and (1b), <https://doi.org/10.1016/j.cub.2020.06.031> (PMC7287426).
