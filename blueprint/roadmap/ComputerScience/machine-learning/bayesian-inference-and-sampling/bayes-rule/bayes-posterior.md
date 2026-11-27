# Bayes posterior

Let $\kappa$ be a kernel from a measurable space $\Theta$ of hypotheses to
a measurable space $\mathcal X$ of observations (the likelihood) and $\mu$ a measure on $\Theta$
(the prior). The Bayes posterior after observing $x \in \mathcal X$ is the measure $\pi_x$ on
$\Theta$ with

$$\pi_x(s) = E(x)^{-1} \int_s \kappa_\theta(\{x\}) \, d\mu(\theta)$$

for every measurable $s \subseteq \Theta$, where $E(x) = (\kappa \circ \mu)(\{x\})$ is the evidence
of $x$: the mass of $\{x\}$ under the composition $\kappa \circ \mu$ of $\mu$ with $\kappa$, the
marginal law of the observation. The inverse is taken in $[0, \infty]$, with $0^{-1} = \infty$,
$\infty^{-1} = 0$ and $\infty \cdot 0 = 0$; in particular $\pi_x$ is the zero measure when the
evidence is zero.
