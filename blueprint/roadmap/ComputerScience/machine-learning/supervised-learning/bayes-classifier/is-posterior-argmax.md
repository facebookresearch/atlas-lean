# Posterior argmax classifier

Let the set $C$ of classes be countable and nonempty with
measurable singletons, let $P$ be a finite kernel from $C$ to the observation space $\mathcal X$
and $\pi$ a finite measure on $C$, write $P \circ \pi$ for the marginal measure on $\mathcal X$
and $P^\dagger_\pi$ for the posterior kernel from $\mathcal X$ to $C$. A map
$f : \mathcal X \to C$ is a posterior argmax classifier for $P$ and $\pi$ if $f$ is measurable
and, for $(P \circ \pi)$-almost every $x$,
$P^\dagger_\pi(x)(\{y\}) \le P^\dagger_\pi(x)(\{f(x)\})$ for every $y \in C$.

Countably many classes with measurable singletons make the posterior masses of classes
meaningful, and give the standard Borel structure the posterior needs.
