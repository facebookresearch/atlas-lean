# MAP hypotheses through the posterior kernel

Let $\Theta$ be a nonempty countable standard
Borel space, $\mathcal X$ a countable measurable space with measurable singletons, $\kappa$ a Markov
kernel from $\Theta$ to $\mathcal X$, $\mu$ a finite measure on $\Theta$, and $x \in \mathcal X$ an
observation with $(\kappa \circ \mu)(\{x\}) \neq 0$, where $\kappa \circ \mu$ is the composition of
$\mu$ with $\kappa$. Write $\kappa^\dagger_\mu$ for the posterior kernel from $\mathcal X$ to
$\Theta$, the fixed disintegration of the joint law of hypothesis and observation along the
observation. Then $\theta \in \Theta$ is a MAP hypothesis for $x$ under the prior $\mu$ and the
likelihood $\kappa$ if and only if
$\kappa^\dagger_\mu(x)(\{\theta'\}) \le \kappa^\dagger_\mu(x)(\{\theta\})$ for every
$\theta' \in \Theta$.
