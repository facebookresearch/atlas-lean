# Extended frequentist risk of a measurable non-integrable loss is infinite

Let $S$ be a
measurable space, $\delta : S \to A$ a decision rule, $(P_\theta)_{\theta \in \Theta}$ a family of
probability measures on $S$, $\ell : \Theta \times A \to [0, \infty)$ a loss, and
$\theta \in \Theta$. If the function $x \mapsto \ell(\theta, \delta(x))$ is almost everywhere
strongly measurable with respect to $P_\theta$ but not $P_\theta$-integrable, then the extended
frequentist risk $\int_S \ell(\theta, \delta(x)) \, dP_\theta(x) \in [0, \infty]$ of $\delta$ at
$\theta$ equals $\infty$.

So a measurable non-integrable loss is never assigned a finite extended risk.

## Sources

- G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury, 2002, §7.3.4, equation (7.3.16) (risk function).
