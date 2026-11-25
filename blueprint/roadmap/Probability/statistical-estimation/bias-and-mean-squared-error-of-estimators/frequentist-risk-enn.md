# Extended frequentist risk

Let $S$ be a measurable space, $\delta : S \to A$ a decision
rule, $(P_\theta)_{\theta \in \Theta}$ a family of probability measures on $S$, and
$\ell : \Theta \times A \to [0, \infty)$ a loss. The extended frequentist risk of $\delta$ at
$\theta \in \Theta$ is the Lebesgue integral $\int_S \ell(\theta, \delta(x)) \, dP_\theta(x)$, taken
in $[0, \infty]$.

When the loss is $P_\theta$-integrable for every $\theta$, this is the frequentist risk; when it is
measurable but not integrable at $\theta$, it equals $\infty$.

## Sources

- G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury, 2002, §7.3.4, equation (7.3.16) (risk function).
