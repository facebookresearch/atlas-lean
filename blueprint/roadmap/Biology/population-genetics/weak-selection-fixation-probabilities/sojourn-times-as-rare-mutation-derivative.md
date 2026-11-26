# Sojourn times as the rare-mutation derivative of the stationary distribution

In the finite-population replacement chain on $\mathbb{B}^N$ with absorbing states
$\{\mathbf{A}, \mathbf{B}\}$, fix a non-monoallelic initial state $\xi \in \mathbb{B}^N \setminus \{\mathbf{A}, \mathbf{B}\}$.
For $x \in \mathbb{B}^N$, let $t_\xi(x)$ be the expected sojourn time (number of visits to $x$
before absorption) starting from $\xi$. For $u \in (0, 1]$, define the amended ergodic Markov chain
with transition kernel
$$P_{x \to y}^{(\xi)} = \begin{cases} (1 - u)\,\delta_{x,y} + u\,\delta_{\xi,y} & x \in \{\mathbf{A}, \mathbf{B}\} \\ P_{x \to y} & x \notin \{\mathbf{A}, \mathbf{B}\} \end{cases}$$
and unique stationary distribution $\pi_{(\xi)}$.

Then for every non-monoallelic state $x \in \mathbb{B}^N \setminus \{\mathbf{A}, \mathbf{B}\}$,
$$\left.\frac{d}{du} \pi_{(\xi)}(x)\right|_{u=0} = t_\xi(x).$$
Consequently, for any state function $\phi : \mathbb{B}^N \to \mathbb{R}$ with
$\phi(\mathbf{A}) = \phi(\mathbf{B}) = 0$,
$$\langle \phi \rangle_\xi := \left.\frac{d}{du} \mathbb{E}_{(\xi)}[\phi]\right|_{u=0} = \sum_{t=0}^\infty \mathbb{E}[\phi(x_t) \mid x_0 = \xi].$$

## Depends on

- [Reproductive values and neutral fixation probability](reproductive-value-and-neutral-fixation.md)

## Expansion

In the amended chain, stationarity at $x \notin \{\mathbf{A}, \mathbf{B}\}$ gives
$\pi_{(\xi)}(x) = \sum_{y \notin \{\mathbf{A}, \mathbf{B}\}} \pi_{(\xi)}(y) P_{y \to x} + u \delta_{\xi,x} (\pi_{(\xi)}(\mathbf{A}) + \pi_{(\xi)}(\mathbf{B}))$.
Differentiating at $u = 0$ and using $\lim_{u \to 0} (\pi_{(\xi)}(\mathbf{A}) + \pi_{(\xi)}(\mathbf{B})) = 1$
recovers the unique recurrence defining the sojourn times $t_\xi(x)$. Multiplying by $\phi(x)$ and
summing over non-monoallelic states yields the operator identity.

## Sources

- A. McAvoy and B. Allen, "Fixation probabilities in evolutionary dynamics under weak selection", Journal of Mathematical Biology 82 (2021), 14, <https://doi.org/10.1007/s00285-021-01567-5>. (Proposition 1 and Corollary 1.)
