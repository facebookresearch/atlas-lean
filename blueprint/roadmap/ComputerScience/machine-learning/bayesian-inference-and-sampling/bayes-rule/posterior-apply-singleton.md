# Bayes' rule for Mathlib's posterior kernel with countably many hypotheses and observations

**Bayes' rule for Mathlib's posterior kernel with countably many hypotheses and
observations.** Let the parameter space $\Theta$ be a nonempty countable standard Borel space and
the observation space $\mathcal X$ be countable, both with measurable singletons. Let $\kappa$ be
a Markov kernel from $\Theta$ to $\mathcal X$ (the likelihood), writing $\kappa_\theta$ for the
probability measure it assigns to $\theta \in \Theta$, let $\mu$ be a finite measure on $\Theta$
(the prior), and let $\kappa^\dagger\mu$ be Mathlib's posterior kernel from $\mathcal X$ to
$\Theta$. If the observation $x \in \mathcal X$ has nonzero evidence $(\kappa \circ \mu)(\{x\})$,
where $\kappa \circ \mu$ is the law of the observation under the prior, then for every
$\theta \in \Theta$

$$
\kappa^\dagger\mu(x)(\{\theta\}) = \frac{\mu(\{\theta\})\,\kappa_\theta(\{x\})}
{\sum_{\theta' \in \Theta} \mu(\{\theta'\})\,\kappa_{\theta'}(\{x\})}.
$$
