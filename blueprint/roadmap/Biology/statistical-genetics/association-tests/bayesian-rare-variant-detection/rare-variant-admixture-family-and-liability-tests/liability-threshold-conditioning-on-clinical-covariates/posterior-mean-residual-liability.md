# Posterior mean residual liability

In the liability threshold model with clinical covariates, an individual with covariate values $t = (t_1, \dots, t_J)$ has liability

$$\phi = \sum_{j=1}^{J} c_j (t_j - \bar t_j) + m + \varepsilon, \qquad \varepsilon \sim N(0, 1),$$

and is a case ($z = 1$) iff $\phi \ge 0$, a control ($z = 0$) otherwise. Here $c_j$ are covariate effects on the liability scale, $\bar t_j$ population covariate means, and $m$ an affine term fixing the prevalence $\Phi(m)$ at the covariate means. Write $\mu(t) = \sum_j c_j(t_j - \bar t_j) + m$, $\varphi$ and $\Phi$ for the standard normal density and distribution function.

**Proposition.** The posterior mean of the residual liability $\varepsilon$ given status and covariates is

$$\mathbb{E}[\varepsilon \mid z = 1, t] = \frac{\varphi(\mu(t))}{\Phi(\mu(t))}, \qquad \mathbb{E}[\varepsilon \mid z = 0, t] = -\frac{\varphi(\mu(t))}{1 - \Phi(\mu(t))}.$$

The case value is decreasing in $\mu(t)$ and the control value is decreasing in $\mu(t)$ as well: a case whose covariates already confer high risk needs less residual liability, while a control with high-risk covariates must have a more negative residual to stay below the threshold.

## Depends on

- [Case indicator of the threshold model](../../../../liability-scale-heritability-from-ld-score-regre/case-ind.md)

## Expansion

Given $t$, the event $z = 1$ is $\varepsilon \ge -\mu(t)$, which has probability $\Phi(\mu(t))$; the truncated normal mean is $\int_{-\mu}^\infty x \varphi(x)\,dx / \Phi(\mu) = \varphi(-\mu)/\Phi(\mu) = \varphi(\mu)/\Phi(\mu)$, and symmetrically for the lower tail. Monotonicity follows because the inverse Mills ratio $x \mapsto \varphi(x)/(1-\Phi(x))$ is increasing; $\varphi(\mu)/\Phi(\mu)$ is its value at $-\mu$, and $-\varphi(\mu)/(1-\Phi(\mu))$ is minus its value at $\mu$. When age at onset is observed, the residual at the threshold crossing is known exactly and can be used in place of the conditional mean. In Zaitlen et al.'s type 2 diabetes example ($c = 0.08$ per BMI unit, $m = -1.44$, mean BMI $26.5$), a case with BMI $24$ gets posterior mean $2.09$ versus $1.37$ for BMI $35$.

## Sources

- N. Zaitlen, S. Lindström, B. Pasaniuc et al., "Informed conditioning on clinical covariates increases power in case-control association studies", PLoS Genetics 8 (2012), e1003032, Methods "Liability threshold model" and "Association test using posterior mean value of underlying quantitative trait", Eqs. (1)–(2), <https://doi.org/10.1371/journal.pgen.1003032>, PMCID PMC3493452.
