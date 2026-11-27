# Existence of a posterior argmax classifier

Let the set $C$ of classes be finite and
nonempty with measurable singletons, let $P$ be a finite kernel from $C$ to the observation space
$\mathcal X$ and $\pi$ a finite measure on $C$. Then there is a posterior argmax classifier
$f : \mathcal X \to C$ for $P$ and $\pi$.

The classifier constructed takes, at each observation, the first maximizer of the posterior
probability in an enumeration of the classes.
