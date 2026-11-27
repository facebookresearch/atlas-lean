# Gibbs sampling leaves the target stationary

Let $\pi$ be a probability distribution on
the configurations $x : \iota \to S$, with $\iota$ and $S$ finite, such that $\pi(x) \neq 0$ for
every $x$. For every coordinate $i$, $\pi$ is an invariant measure of the Markov kernel of the
Gibbs update of coordinate $i$: if $x$ is drawn from $\pi$ and coordinate $i$ is resampled from
its conditional law given the other coordinates, the result is again distributed as $\pi$.
