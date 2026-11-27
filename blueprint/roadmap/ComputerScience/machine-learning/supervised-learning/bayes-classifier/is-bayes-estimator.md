# The Bayes classifier is optimal

Let the set $C$ of classes be countable and nonempty with measurable singletons, let $P$ be a
finite kernel from $C$ to the observation space $\mathcal X$ and $\pi$ a finite measure on $C$. If
$f : \mathcal X \to C$ is a [posterior argmax classifier](is-posterior-argmax.md) for $P$ and
$\pi$, then the deterministic kernel $x \mapsto \delta_{f(x)}$ attains the Bayes risk for the 0-1
loss: its average 0-1 risk
$\int_C \int_C \ell(c, y)\,(\delta_f \circ P)(c)(dy)\,\pi(dc)$ equals the infimum of the average
0-1 risks of all Markov kernels from $\mathcal X$ to $C$.
