# Measurement-error sensitivity of the Steiger direction

**Setting.** As in the [MR Steiger test](mr-steiger-test-of-causal-direction.md), let $g$ be a valid instrument for $x$ with $x \to y$, so $\rho_{gy} = \rho_{gx}\rho_{xy}$, and take all correlations nonnegative. The traits are observed with non-differential measurement error, $x_o = \alpha_x + \beta_x x + \varepsilon_x$ and $y_o = \alpha_y + \beta_y y + \varepsilon_y$, with errors independent of $g$ and of the true traits and of each other.

**Proposition.** The observed instrument correlations are attenuated by the reliabilities $\rho_{x,x_o}$ and $\rho_{y,y_o}$:

$$\rho_{g,x_o} = \rho_{gx}\,\rho_{x,x_o}, \qquad \rho_{g,y_o} = \rho_{gx}\,\rho_{xy}\,\rho_{y,y_o}.$$

Hence the population version of the Steiger comparison on observed traits orients the effect correctly ($\rho_{g,x_o} > \rho_{g,y_o}$) if and only if

$$d = \rho_{x,x_o} - \rho_{xy}\,\rho_{y,y_o} > 0 .$$

When $d < 0$ the test is consistent for the **wrong** direction, and larger samples make it more confident in that wrong answer.

Consequences: with no measurement error in $x$ ($\rho_{x,x_o} = 1$) the inferred direction cannot be reversed by any error in $y$; reversal needs the exposure to be measured markedly worse than the outcome, more easily when the causal correlation $\rho_{xy}$ is large. Scanning plausible values of $(\rho_{x,x_o}, \rho_{y,y_o})$ and comparing how much of that space supports each direction gives a reliability score for an observed result.

## Depends on

- [MR Steiger test of causal direction](mr-steiger-test-of-causal-direction.md)

## Expansion

Scale changes $\alpha, \beta$ do not affect correlations; only the noise $\varepsilon$ does. Since $\varepsilon_x$ is independent of $g$, $\operatorname{Cov}(g, x_o) = \beta_x\operatorname{Cov}(g,x)$ and $\operatorname{Var}(x_o) = \beta_x^2\operatorname{Var}(x) + \operatorname{Var}(\varepsilon_x)$, which gives $\rho_{g,x_o} = \rho_{gx}\,\rho_{x,x_o}$; the same computation for $y$ uses $\rho_{gy} = \rho_{gx}\rho_{xy}$. Dividing by $\rho_{gx} > 0$ yields the condition on $d$. The same attenuation explains why mediation-based tests (such as the causal inference test) can confidently report the reverse direction: conditioning on a noisily measured mediator leaves residual association with the instrument.

## Sources

- G. Hemani, K. Tilling and G. Davey Smith, "Orienting the causal relationship between imprecisely measured traits using GWAS summary data", PLoS Genetics 13 (2017), e1007081, Model, Results and Methods ("Causal direction sensitivity analysis for measurement error"), <https://doi.org/10.1371/journal.pgen.1007081> (PMC5711033).
