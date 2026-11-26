# Sojourn times as the rare-mutation derivative of the stationary distribution

Consider the replacement chain of [the setup](reproductive-value-and-neutral-fixation.md), at any fixed
selection intensity, with transition probabilities $P_{x \to y}$, absorbing states $\{\mathbf{A}, \mathbf{B}\}$
and transient states $\mathbb{B}_T^N = \mathbb{B}^N \setminus \{\mathbf{A}, \mathbf{B}\}$. Fix
$\xi \in \mathbb{B}_T^N$, and for $x \in \mathbb{B}^N$ let $t_\xi(x)$ be the expected number of visits to $x$
before absorption, starting from $\xi$. For $u \in (0, 1]$, define the amended chain with transition
probabilities

$$P_{x \to y}^{(\xi)} = \begin{cases} (1 - u)\,\delta_{x,y} + u\,\delta_{\xi,y} & x \in \{\mathbf{A}, \mathbf{B}\}, \\ P_{x \to y} & x \notin \{\mathbf{A}, \mathbf{B}\}. \end{cases}$$

It has a single closed communicating class, the states reachable from $\xi$, which contains $\mathbf{A}$ or
$\mathbf{B}$; hence it has a unique stationary distribution $\pi_{(\xi)} = \pi_{(\xi)}^{u}$. (It need not be
aperiodic at $u = 1$.) For every $x \in \mathbb{B}_T^N$, $\pi_{(\xi)}^{u}(x) \to 0$ as $u \downarrow 0$, and the
right derivative at $u = 0$ of $u \mapsto \pi_{(\xi)}^{u}(x)$, extended by this limit, is the sojourn time:

$$\lim_{u \downarrow 0} \frac{\pi_{(\xi)}^{u}(x)}{u} = t_\xi(x).$$

Consequently, for every $\phi : \mathbb{B}^N \to \mathbb{R}$ with $\phi(\mathbf{A}) = \phi(\mathbf{B}) = 0$,

$$\langle \phi \rangle_\xi := \lim_{u \downarrow 0} \frac{\mathbb{E}_{(\xi)}^{u}[\phi]}{u} = \sum_{x \in \mathbb{B}_T^N} \phi(x)\, t_\xi(x) = \sum_{t=0}^\infty \mathbb{E}[\phi(x_t) \mid x_0 = \xi],$$

the series converging absolutely. Here $\mathbb{E}_{(\xi)}^{u}$ is expectation under $\pi_{(\xi)}^{u}$, and
$\langle \cdot \rangle_\xi^\circ$ denotes this operator for the neutral chain.

## Depends on

- [Reproductive values and neutral fixation probability](reproductive-value-and-neutral-fixation.md)

## Proof depends on

- [Absorption probabilities and mean times of a finite Markov chain](../../../../Probability/markov-chains/finite-markov-chains/absorption-probabilities-and-mean-absorption-tim.md)

## Expansion

Every state reaches $\{\mathbf{A}, \mathbf{B}\}$, from which the amended chain moves to $\xi$, so every closed
class contains $\xi$ and there is only one. Cut the amended chain started at $\xi$ into cycles **only at its
transitions from a monoallelic state to $\xi$** (a reset), not at every entrance to $\xi$: the original chain
can return to $\xi$ before absorption. A cycle is then one run of the original chain from $\xi$ until
absorption, followed by the holding time in $\{\mathbf{A}, \mathbf{B}\}$ until the next reset. In the first
part it spends on average $t_\xi(x)$ steps at each transient $x$, and
$T = \sum_{y \in \mathbb{B}_T^N} t_\xi(y) = \mathbb{E}_\xi[\text{absorption time}] < \infty$ steps in all,
finite because the absorption time of the finite original chain has finite mean; the second part is
geometric with mean $1/u$. The resets are regeneration times, so by the renewal-reward theorem the long-run
fraction of time at $x$ is $t_\xi(x) / (T + 1/u)$, and this long-run fraction is the unique stationary law
whether or not the chain is aperiodic, in particular at $u = 1$. Hence
$\pi_{(\xi)}^{u}(x) = u\, t_\xi(x) / (1 + uT)$, which gives both limits. Multiplying by $\phi(x)$ and summing over the finitely many transient states gives the
operator identity, and $\sum_x \phi(x) t_\xi(x) = \sum_t \mathbb{E}[\phi(x_t) \mid x_0 = \xi]$ by Fubini, since
$\sum_t \mathbb{P}(x_t \in \mathbb{B}_T^N) = T < \infty$.

## Sources

- A. McAvoy and B. Allen, "Fixation probabilities in evolutionary dynamics under weak selection", Journal of Mathematical Biology 82 (2021), 14, <https://doi.org/10.1007/s00285-021-01568-4>. (Proposition 1 and Corollary 1, which take $u > 0$; the bound $u \le 1$ keeps the amended probabilities in $[0, 1]$.)
