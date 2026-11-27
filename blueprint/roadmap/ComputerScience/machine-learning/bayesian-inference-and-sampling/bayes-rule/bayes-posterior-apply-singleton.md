# Bayes' rule for countably many hypotheses

Let $\Theta$ be a countable measurable space and
$\mathcal X$ a measurable space, both with measurable singletons, let $\kappa$ be a kernel from
$\Theta$ to $\mathcal X$ (the likelihood) and $\mu$ a measure on $\Theta$ (the prior). For every
observation $x \in \mathcal X$ and every $\theta \in \Theta$, the Bayes posterior $\pi_x$ of $\mu$
after observing $x$ satisfies

$$\pi_x(\{\theta\}) = \frac{\mu(\{\theta\}) \, \kappa_\theta(\{x\})}
{\sum_{\theta' \in \Theta} \mu(\{\theta'\}) \, \kappa_{\theta'}(\{x\})},$$

where the quotient is taken in $[0, \infty]$ with $0 / 0 = 0$ and $a / \infty = 0$ for every $a$.
The denominator is the evidence of $x$.
