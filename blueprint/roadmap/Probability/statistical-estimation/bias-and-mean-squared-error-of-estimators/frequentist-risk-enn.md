# Extended frequentist risk

Let $S$ be a measurable space, $\delta : S \to A$ a decision
rule, $(P_\theta)_{\theta \in \Theta}$ a family of probability measures on $S$, and
$\ell : \Theta \times A \to [0, \infty)$ a loss. The extended frequentist risk of $\delta$ at
$\theta \in \Theta$ is the Lebesgue integral $\int_S \ell(\theta, \delta(x)) \, dP_\theta(x)$, taken
in $[0, \infty]$.

When the loss is $P_\theta$-integrable for every $\theta$, this is the frequentist risk; when it is
measurable but not integrable at $\theta$, it equals $\infty$.

## Sources

- blueprint `af_36871388da7326a07a5e4f71`.
