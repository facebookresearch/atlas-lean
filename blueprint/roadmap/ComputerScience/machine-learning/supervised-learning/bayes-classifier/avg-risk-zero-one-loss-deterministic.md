# The 0-1 risk of a deterministic classifier

Let $C$ be a measurable space of classes with
measurable singletons, $P$ a kernel from $C$ to the observation space $\mathcal X$, $\pi$ a
measure on $C$, $f : \mathcal X \to C$ a measurable map, and $\ell(c, y)$ the 0-1 loss ($0$ if
$y = c$, $1$ otherwise). Then the average 0-1 risk of the deterministic kernel
$\delta_f : x \mapsto \delta_{f(x)}$,
$\int_C \int_C \ell(c, y)\,(\delta_f \circ P)(c)(dy)\,\pi(dc)$ with
$(\delta_f \circ P)(c) = \int_{\mathcal X} \delta_{f(x)}\,P(c)(dx)$, equals
$\int_C P(c)(\{x \in \mathcal X : f(x) \ne c\})\,\pi(dc)$.

When each $P(c)$ is a probability measure, $P(c)(\{x : f(x) \ne c\})$ is the probability that
$f$ misclassifies an observation of class $c$.
