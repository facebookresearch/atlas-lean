# Exactness of the stochastic simulation algorithm

For a well-mixed reaction system modelled as a continuous-time Markov jump process with state $x$, propensities $a_j(x)$ for $j = 1, \dots, M$, state-change vectors $\nu_j$ and total propensity $a_0(x) = \sum_j a_j(x) > 0$, the waiting time $\tau$ until the next reaction is exponentially distributed with rate $a_0(x)$, and the joint density of the waiting time and the index $j$ of the next reaction is

$$p(\tau, j \mid x) = a_j(x)\, e^{-a_0(x)\tau}$$

(Wikipedia, Gillespie algorithm, Mathematical formulation). Writing $p(\tau, j \mid x) = a_0(x)e^{-a_0(x)\tau} \cdot a_j(x)/a_0(x)$ shows that $\tau$ and $j$ are independent, with $j$ chosen with probability $a_j(x)/a_0(x)$. The direct method draws independent uniforms $r_1, r_2$ on $(0, 1)$, sets $\tau = a_0(x)^{-1}\ln(1/r_1)$ and takes $j$ to be the smallest index with $\sum_{j' \le j} a_{j'}(x) > r_2 a_0(x)$, then updates $t \leftarrow t + \tau$ and $x \leftarrow x + \nu_j$; by inverse-transform sampling each step has exactly the law $p(\tau, j \mid x)$, so each realization is a sample path of the jump process (Gillespie 1976, 1977, as presented in the same source).

## Expansion

1. The model: the reaction-count Markov jump process, its propensities and its jump chain and holding time description.
2. The joint law of the first jump time and reaction index from competing exponential clocks, and the factorization showing independence.
3. Inverse-transform sampling of $\tau$ and $j$ from two independent uniforms.
4. Equality in law of the simulated path with the jump process, by the strong Markov property and induction on jumps up to the explosion time; the forward equation of this process is the chemical master equation.

## Sources

- Gillespie algorithm, Wikipedia, sections Mathematical formulation and Direct method. <https://en.wikipedia.org/wiki/Gillespie_algorithm>
- Original result: D. T. Gillespie, Exact stochastic simulation of coupled chemical reactions, J. Phys. Chem. 81 (1977), 2340–2361. <https://doi.org/10.1021/j100540a008> The joint density and the direct method follow the Wikipedia article on the Gillespie algorithm.
