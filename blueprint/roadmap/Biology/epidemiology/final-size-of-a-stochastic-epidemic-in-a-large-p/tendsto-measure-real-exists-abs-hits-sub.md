# Uniform law of large numbers for the hits among up to K N contacts

For each $k \in \mathbb{N}$ let the offspring numbers $\xi^{(k)}_{n,i}$ and the contact targets
$U^{(k)}_j$ form a [final-size epidemic model](is-final-size-epidemic.md) on a probability space
$(\Omega_k, P_k)$, in a population of size $N_k$ with a set $S_0^{(k)}$ of $\#S_0^{(k)}$ initially
susceptible individuals, all with the same offspring law $\nu$, a probability measure on
$\mathbb{N}$. Assume $N_k \to \infty$ and $(N_k - \#S_0^{(k)})/N_k \to 0$ as $k \to \infty$. Let
$H^{(k)}_c$ be the [number of hits](hits.md) among the first $c$ contacts of the targets
$U^{(k)}_j(\omega)$, relative to $S_0^{(k)}$. For all reals $0 < \varepsilon \le 1$ and $K \ge 0$,
the probability under $P_k$ that some $c \in \mathbb{N}$ with $c \le K N_k$ has
$|H^{(k)}_c - N_k (1 - e^{-c/N_k})| > \varepsilon N_k$ tends to $0$ as $k \to \infty$: with
probability tending to $1$, $H^{(k)}_c$ is within $\varepsilon N_k$ of $N_k(1 - e^{-c/N_k})$
simultaneously for all $c \le K N_k$.
