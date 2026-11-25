# Integrated Chapman–Kolmogorov equation for functions

Let $X = (X_n)_{n \in \mathbb{N}}$ be a [Markov chain](is-markov-chain.md) with state space $S$
with respect to a filtration, with Markov transition kernel $\kappa$, under a probability measure
$\mu$, and let $\kappa^n$ be the $n$-fold composition of $\kappa$ (the identity kernel for
$n = 0$). Let $f : S \to \mathbb{R}$ be strongly measurable and bounded. Then for all
$m, n \in \mathbb{N}$,

$$\int_\Omega f(X_{m+n}) \, d\mu = \int_\Omega \left( \int_S f(y) \, \kappa^n(X_m(\omega), dy) \right) d\mu(\omega) .$$
