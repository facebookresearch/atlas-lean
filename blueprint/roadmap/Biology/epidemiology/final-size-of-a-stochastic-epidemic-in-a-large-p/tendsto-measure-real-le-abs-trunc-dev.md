# The centered contact count with cap N + 1 is o(N) in probability

For each $k \in \mathbb{N}$ let the offspring numbers $\xi^{(k)}_{n,i}$ and the contact targets
$U^{(k)}_j$ form a [final-size epidemic model](is-final-size-epidemic.md) on a probability space
$(\Omega_k, P_k)$, in a population of size $N_k$ with a set $S_0^{(k)}$ of $\#S_0^{(k)}$ initially
susceptible individuals, all with the same offspring law $\nu$, a probability measure on
$\mathbb{N}$, with $\int x^2 \, d\nu(x) < \infty$; let $m$ be its [real mean](offspring-mean.md).
Assume $N_k \to \infty$; the sets $S_0^{(k)}$ are arbitrary. For every real $\varepsilon > 0$,
$P_k(|T^{(k)}_{m,\,N_k+1}(w^{(k)}(\omega))| \ge \varepsilon N_k) \to 0$ as $k \to \infty$, where
$T^{(k)}_{m,\,N_k+1}$ is the [centered contact count](trunc-dev.md) of model $k$, with centering $m$
and cap $N_k + 1$, and $w^{(k)}(\omega)$ the [configuration at $\omega$](config-2.md). Since the
final size is at most $N_k$, this count equals $C - m(F + 1)$, with $C$ the total number of contacts
and $F$ the final size ([centered count once all infectives count](trunc-dev-eq.md)).
