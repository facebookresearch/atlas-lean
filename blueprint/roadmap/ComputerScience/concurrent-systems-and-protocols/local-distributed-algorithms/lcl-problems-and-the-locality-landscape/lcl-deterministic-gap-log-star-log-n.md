# Deterministic LCL complexities between log-star and log n collapse

For every LCL problem $\Pi$ on bounded-degree graphs, if $D_\Pi(n) = o(\log n)$ then $D_\Pi(n) = O(\log^* n)$. Moreover the deterministic and randomized complexities, the latter with global error probability $1/n$, are related by $D_\Pi(n) \le R_\Pi\bigl(2^{n^2}\bigr)$. Consequently $D_\Pi(n) = O(\log^* n)$ whenever $R_\Pi(n) = o(\log\log n)$, and every randomized lower bound $R_\Pi(n) = \omega(\log^* n)$ implies the deterministic lower bound $D_\Pi(n) = \Omega(\log n)$.

## Proof sketch

Given a fast deterministic algorithm, simulate it on a virtual graph with fewer vertices: compute in $O(\log^* n)$ rounds a distance-$k$ colouring with a constant number of colours and treat colours as identifiers of a much smaller virtual instance, on which the algorithm's running time $o(\log n_{\mathrm{virtual}})$ is a constant independent of $n$. For the randomized-to-deterministic relation, a union bound over all $n$-vertex instances with polynomial identifiers fixes random bits that work for all of them simultaneously when the randomized algorithm is run with a pretended size $2^{n^2}$. The last claim follows because $D_\Pi(n) = o(\log n)$ would force $D_\Pi(n) = O(\log^* n)$ and hence $R_\Pi(n) = O(\log^* n)$.

## Depends on

- [Deterministic and randomized LOCAL complexity of an LCL problem](lcl-deterministic-randomized-complexity.md)

## Sources

- Y.-J. Chang, T. Kopelowitz, S. Pettie, "An Exponential Separation between Randomized and Deterministic Complexity in the LOCAL Model", FOCS 2016; SIAM Journal on Computing 48(1) (2019), arXiv:1602.08166, Theorem 3.
- Y.-J. Chang, S. Pettie, "A Time Hierarchy Theorem for the LOCAL Model", FOCS 2017; SIAM Journal on Computing 48(1) (2019), arXiv:1704.06297.
