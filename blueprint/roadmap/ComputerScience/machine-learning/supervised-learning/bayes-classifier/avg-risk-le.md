# A posterior argmax classifier has minimal 0-1 risk

Let the set $C$ of classes be countable
and nonempty with measurable singletons, let $P$ be a finite kernel from $C$ to the observation
space $\mathcal X$ and $\pi$ a finite measure on $C$, and let $\ell(c, y)$ be the 0-1 loss
($0$ if $y = c$, $1$ otherwise). For a kernel $\kappa$ from $\mathcal X$ to $C$, its average 0-1
risk is $\int_C \int_C \ell(c, y)\,(\kappa \circ P)(c)(dy)\,\pi(dc)$, where
$(\kappa \circ P)(c) = \int_{\mathcal X} \kappa(x)\,P(c)(dx)$. If $f : \mathcal X \to C$ is a
posterior argmax classifier for $P$ and $\pi$, then for every Markov kernel $\kappa$ from
$\mathcal X$ to $C$ (a randomized classifier), the average 0-1 risk of the deterministic kernel
$x \mapsto \delta_{f(x)}$ is at most the average 0-1 risk of $\kappa$.
