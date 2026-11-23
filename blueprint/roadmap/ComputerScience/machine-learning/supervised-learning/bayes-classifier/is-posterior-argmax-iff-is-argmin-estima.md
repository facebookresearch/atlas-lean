# Posterior argmax classifiers are exactly the argmin estimators for the 0-1 loss

Let the
set $C$ of classes be countable and nonempty with measurable singletons, let $P$ be a finite
kernel from $C$ to the observation space $\mathcal X$ and $\pi$ a finite measure on $C$, write
$P \circ \pi$ for the marginal measure on $\mathcal X$, $P^\dagger_\pi$ for the posterior kernel
from $\mathcal X$ to $C$, and $\ell(c, y)$ for the 0-1 loss ($0$ if $y = c$, $1$ otherwise). A
map $f : \mathcal X \to C$ is a posterior argmax classifier for $P$ and $\pi$ if and only if it
is an argmin estimator for $\ell$: $f$ is measurable and, for $(P \circ \pi)$-almost every $x$,
$\int_C \ell(c, f(x))\,P^\dagger_\pi(x)(dc)$ equals
$\inf_{y \in C} \int_C \ell(c, y)\,P^\dagger_\pi(x)(dc)$.
