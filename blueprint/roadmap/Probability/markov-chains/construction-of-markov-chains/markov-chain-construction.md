# Markov chain construction theorem

Let $S$ be a nonempty standard Borel space, let
$\kappa$ be a Markov kernel from $S$ to $S$ and let $\mu$ be a probability measure on $S$. Then
there is a probability measure $P$ on the path space $S^{\mathbb{N}}$ such that, writing
$X_n(\omega) = \omega_n$ for the coordinates, the law of $X_0$ under $P$ is $\mu$, and for every
$n \in \mathbb{N}$ the regular conditional distribution of $X_{n+1}$ given $(X_0, \dots, X_n)$
under $P$ agrees with the kernel $(x_0, \dots, x_n) \mapsto \kappa(x_n, \cdot)$ for almost every
$(x_0, \dots, x_n)$ with respect to the law of $(X_0, \dots, X_n)$ under $P$.

That is, the coordinate process $(X_0, X_1, \dots)$ under $P$ is a Markov chain with initial
distribution $\mu$ and transition kernel $\kappa$.
