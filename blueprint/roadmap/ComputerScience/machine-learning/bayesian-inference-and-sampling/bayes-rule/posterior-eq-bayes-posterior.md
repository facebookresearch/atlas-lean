# Bayes' rule for discrete observations

Let the parameter space $\Theta$ be a nonempty
standard Borel space and the observation space $\mathcal X$ be countable with measurable
singletons. Let $\kappa$ be a Markov kernel from $\Theta$ to $\mathcal X$ (the likelihood),
writing $\kappa_\theta$ for the probability measure it assigns to $\theta \in \Theta$, let $\mu$
be a finite measure on $\Theta$ (the prior), and let $\kappa^\dagger\mu$ be the posterior
kernel from $\mathcal X$ to $\Theta$, the disintegration of the joint law of hypothesis and observation along the observation. If the observation $x \in \mathcal X$ has nonzero evidence
$(\kappa \circ \mu)(\{x\})$, where $\kappa \circ \mu$ is the law of the observation under the
prior, then the posterior measure $\kappa^\dagger\mu(x)$ equals the Bayes posterior after
observing $x$: the prior $\mu$ reweighted by the likelihood $\theta \mapsto \kappa_\theta(\{x\})$
and divided by the evidence.
