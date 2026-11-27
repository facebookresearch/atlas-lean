# Retrieval below the capacity thresholds of the Hopfield associative memory

Store $m$ patterns $x^{(1)}, \dots, x^{(m)} \in \{-1, 1\}^n$, drawn independently and uniformly, in a Hopfield network of $n$ neurons with the outer-product (Hebbian) weights $T_{ij} = \sum_\mu x^{(\mu)}_i x^{(\mu)}_j$ for $i \ne j$ and $T_{ii} = 0$; a pattern is stable if it is a fixed point of the threshold update $x_i \mapsto \operatorname{sgn}(\sum_j T_{ij} x_j)$. McEliece, Posner, Rodemich and Venkatesh (1987) prove the following retrieval bounds. Let $m = m(n)$ and fix $\varepsilon \in (0, 1)$. As $n \to \infty$,

1. if $m(n) \le (1 - \varepsilon)\, n/(4 \ln n)$ for all large $n$, then the probability that all $m$ patterns are stable tends to $1$;
2. if $m(n) \le (1 - \varepsilon)\, n/(2 \ln n)$ for all large $n$, then for each fixed index $\mu$ the probability that pattern $\mu$ is stable tends to $1$, so the expected fraction of stable patterns tends to $1$.

The paper also identifies $n/(4 \ln n)$ and $n/(2 \ln n)$ as the asymptotic capacities, the largest such rates; those converse statements are not part of this page (see the Expansion). Komlós and Paturi (1988) restate these thresholds and add the radius of the domains of attraction and convergence times.

## Expansion

1. The model: random $\pm 1$ patterns, the outer-product weights, the threshold update and the notion of a stable pattern (with a fixed convention for $\operatorname{sgn}(0)$).
2. The reduction of the stability of pattern $\mu$ at neuron $i$ to the event that a sum of $(m-1)(n-1)$ independent $\pm 1$ variables exceeds $-(n-1)$.
3. A union bound with Gaussian tail estimates, giving the threshold $n/(4\log n)$ for all patterns and $n/(2\log n)$ for one pattern.
4. The two statements above.
5. Separate target: the converses of the 1987 paper for $m(n) \ge (1 + \varepsilon)$ times each threshold, with their exact events and quantifiers, which identify the two thresholds as capacities.
6. The basins of attraction and convergence-time results of Komlós and Paturi as separate statements.

## Sources

- Original result: R. J. McEliece, E. C. Posner, E. R. Rodemich and S. S. Venkatesh, The capacity of the Hopfield associative memory, IEEE Trans. Inform. Theory 33 (1987), 461–482. <https://doi.org/10.1109/TIT.1987.1057328> The thresholds are those of its abstract; Komlós and Paturi (1988) restate them.
- J. Komlós and R. Paturi, Convergence results in an associative memory model, Neural Networks 1 (1988), 239–250. <https://doi.org/10.1016/0893-6080(88)90029-9>
- S. S. Venkatesh, *Linear Maps with Point Rules: Applications to Pattern Classification and Associative Memory*, Ph.D. thesis, California Institute of Technology (1987). <https://doi.org/10.7907/1YSB-Q028>
