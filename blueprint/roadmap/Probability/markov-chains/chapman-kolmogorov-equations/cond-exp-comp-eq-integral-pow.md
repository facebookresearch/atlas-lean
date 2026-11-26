# Chapman–Kolmogorov equations for bounded measurable functions

Let $\mu$ be a probability measure on $\Omega$, let $(\mathcal{F}_n)_{n \in \mathbb{N}}$ be a
filtration, and let $X = (X_n)_{n \in \mathbb{N}}$ be a [Markov chain](is-markov-chain.md) with
state space $S$ with respect to $(\mathcal{F}_n)$, with Markov transition kernel $\kappa$, under
$\mu$. Let $f : S \to \mathbb{R}$ be strongly measurable and bounded ($|f| \le C$ for some
constant $C$). Then for all $m, n \in \mathbb{N}$,

$$\mathbb{E}_\mu[f(X_{m+n}) \mid \mathcal{F}_m](\omega) = \int_S f(y) \, \kappa^n(X_m(\omega), dy)$$

for $\mu$-almost every $\omega$, where $\kappa^n$ is the $n$-fold composition of $\kappa$ (the
identity kernel for $n = 0$). For $n = 1$ this is the one-step function form of the Markov
property.
