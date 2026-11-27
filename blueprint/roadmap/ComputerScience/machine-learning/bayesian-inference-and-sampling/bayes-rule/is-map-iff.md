# MAP hypotheses maximize prior times likelihood

Let $\Theta$ and $\mathcal X$ be countable
measurable spaces with measurable singletons, $\kappa$ a Markov kernel from $\Theta$ to
$\mathcal X$, $\mu$ a finite measure on $\Theta$, and $x \in \mathcal X$ an observation with
$(\kappa \circ \mu)(\{x\}) \neq 0$, where $\kappa \circ \mu$ is the composition of $\mu$ with
$\kappa$. Then $\theta \in \Theta$ is a MAP hypothesis for $x$ under the prior $\mu$ and the
likelihood $\kappa$ if and only if
$\mu(\{\theta'\}) \, \kappa_{\theta'}(\{x\}) \le \mu(\{\theta\}) \, \kappa_\theta(\{x\})$ for every
$\theta' \in \Theta$.

The evidence $(\kappa \circ \mu)(\{x\})$ is a common factor of all posterior masses.
