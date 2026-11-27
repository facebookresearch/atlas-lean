# Markov chain with respect to a filtration

Let $\mu$ be a measure on $\Omega$, let
$(\mathcal{F}_n)_{n \in \mathbb{N}}$ be a filtration on $\Omega$, and let $\kappa$ be a Markov
kernel from a measurable space $S$ to itself. A sequence of random variables
$X_n : \Omega \to S$ is a Markov chain with respect to $(\mathcal{F}_n)$ with transition kernel
$\kappa$ under $\mu$ if it is adapted to $(\mathcal{F}_n)$ and, for every $n \in \mathbb{N}$ and
every measurable $B \subseteq S$,

$$\mathbb{E}_\mu[\mathbf{1}_B(X_{n+1}) \mid \mathcal{F}_n] = \kappa(X_n, B)$$

$\mu$-almost everywhere. This is the standard form
$P(X_{n+1} \in B \mid \mathcal{F}_n) = \kappa(X_n, B)$ of the Markov property.
