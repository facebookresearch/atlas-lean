# Detailed balance implies invariance

Let $\alpha$ be a finite state space with a measurable
structure in which singletons are measurable, $\pi$ a probability distribution on $\alpha$ and $P$
a transition rule assigning to each $x \in \alpha$ a probability distribution $P(x, \cdot)$ on
$\alpha$. If $\pi(x) P(x, y) = \pi(y) P(y, x)$ for all $x, y \in \alpha$, then $\pi$, viewed as a
measure, is invariant for the Markov kernel $\kappa$ of $P$: for every measurable set $B$,
$\int \kappa(x, B) \, d\pi(x) = \pi(B)$.
