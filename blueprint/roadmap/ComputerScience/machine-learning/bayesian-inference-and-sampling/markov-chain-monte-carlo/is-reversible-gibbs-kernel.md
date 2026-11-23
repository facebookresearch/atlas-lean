# Gibbs updates are reversible

Let $\pi$ be a probability distribution on the
configurations $x : \iota \to S$, with $\iota$ and $S$ finite, such that $\pi(x) \neq 0$ for every
$x$. For every coordinate $i$, the Markov kernel $K$ of the Gibbs update of coordinate $i$ is
reversible with respect to $\pi$: for all measurable sets $A$ and $B$ of configurations,
$\int_A K(x, B) \, d\pi(x) = \int_B K(x, A) \, d\pi(x)$.
