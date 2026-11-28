# Weak selection for cooperation from any configuration on regular graphs

Players occupy the vertices of a connected $k$-regular graph on $N$ vertices and play the donation game with all neighbours: a cooperator pays $c$ to give each neighbour $b$, with $b > c > 0$. Payoff $\pi$ becomes fitness $f = 1 + w\pi$ with selection intensity $w \ge 0$. Under birth–death (BD) updating an individual reproduces with probability proportional to fitness and its offspring replaces a uniformly random neighbour; under death–birth (DB) updating a uniformly random individual dies and a neighbour, chosen proportionally to fitness, fills the vacancy. For a configuration $\xi$ with $n$ cooperators, let $\rho_{\xi,C}(w)$ be the probability that cooperators take over; under neutral drift $\rho_{\xi,C}(0) = n/N$. Weak selection favours cooperation from $\xi$ if $\rho_{\xi,C}(w) > n/N$ for all sufficiently small $w > 0$.

1. Under BD updating, weak selection never favours cooperation, from any configuration on any regular graph.
2. Under DB updating, for each configuration $\xi$ there is an explicit critical ratio $(b/c)^*(\xi) \in (0, \infty]$ such that weak selection favours cooperation from $\xi$ if and only if $b/c > (b/c)^*(\xi)$. It is a rational function of averaged local frequencies: the fractions $f_1(x,\xi)$ and $f_0(x,\xi)$ of cooperating and defecting neighbours of $x$ and the fraction $f_{10}(x,\xi)$ of length-two paths from $x$ that visit a cooperator and then a defector, averaged over vertices; it can be computed in $O(k^2 N)$ time.
3. $\xi$ and the configuration obtained by swapping cooperators and defectors have the same critical ratio.
4. For a single cooperator, and for a uniformly random configuration with any fixed number $n$ of cooperators ($0 < n < N$), the critical ratio does not depend on the configuration: it equals $\frac{N-2}{N/k - 2}$ if $N > 2k$, and is infinite if $N \le 2k$.
5. For fixed $k \ge 2$, $(b/c)^*(\xi) \to k$ uniformly in $\xi$ as $N \to \infty$, recovering the rule $b/c > k$.

On small graphs, the placement and number of cooperators matter: there are graphs on which no single-cooperator start is favoured but some multi-cooperator configuration is, and graphs where the reverse happens.

## Depends on

- [Moran fixation probability](../../../isothermal-theorem-for-evolutionary-graph-dynami/moran-fixation.md)

## Expansion

Under weak selection, the derivative of the fixation probability at $w = 0$ is a sum over the neutral process of the expected change in cooperator frequency caused by selection. On a regular graph the neutral process is a voter model, so this sum can be expressed through quantities computed at the initial configuration and coalescence properties of random walks, which reduce to the local frequencies $f_1$, $f_0$ and $f_{10}$. Under BD updating, local competition exactly offsets the benefit of clustering, so the selection term is never positive. Under DB updating, its sign is that of an affine function of $b/c$ whose root gives the critical ratio; averaging over random configurations reproduces the classical single-mutant threshold.

## Sources

- Y.-T. Chen, A. McAvoy and M. A. Nowak, "Fixation probabilities for any configuration of two strategies on regular graphs", *Scientific Reports* 6 (2016), 39181, Introduction, Eqs. (1)–(2), and Results, "Critical benefit-to-cost ratios", Eqs. (3)–(7). <https://doi.org/10.1038/srep39181> (PMC5177945)
