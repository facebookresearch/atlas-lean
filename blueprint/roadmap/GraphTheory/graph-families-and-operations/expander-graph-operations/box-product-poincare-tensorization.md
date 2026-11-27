# Spectral gaps of box products of permutation multigraphs tensorize

Let $(\sigma_k)_{k \in K}$ be permutations of a finite set $V$ and $(\tau_{k'})_{k' \in K'}$ permutations of a finite set $W$, $K, K'$ nonempty. The box family on $V \times W$ consists of the moves $\sigma_k \times \mathrm{id}$ and $\mathrm{id} \times \tau_{k'}$, and its permutation multigraph is the Cartesian product walk. If both families satisfy a Poincare inequality with constant $c$, namely $c\, \mathbb{E} f^2 \le \sum_k \mathbb{E}(f \circ \sigma_k - f)^2$ for every mean-zero $f$ (and likewise for $\tau$), then so does the box family on $V \times W$ with the same $c$. Consequently, writing $\lambda_2$ for the second eigenvalue of a permutation multigraph,

$$\lambda_2(\text{box}) \le 1 - \frac{\min\{|K|(1 - \lambda_2(\sigma)),\ |K'|(1 - \lambda_2(\tau))\}}{|K| + |K'|},$$

and for $J$ factors with the same number of moves and gap $\gamma$ the product has gap at least $\gamma / J$.

## Proof sketch

Decompose a mean-zero $f$ on $V \times W$ orthogonally into its fibre averages $\bar f(v) = \mathbb{E}_w f(v, w)$ and a remainder with mean zero on every fibre $\{v\} \times W$. The $\tau$-moves control the remainder fibrewise, and the $\sigma$-moves control $\bar f$ because, by Jensen, the change of $\bar f$ along $\sigma_k$ is at most the average change of $f$. Iterating over coordinates gives the $J$-factor statement.

## Depends on

- [Regular multigraph of a family of permutations (Schreier-type graph)](permutation-multigraph.md)
- [Spectral expansion, second eigenvalue and edge expansion of a regular multigraph](spectral-expansion-second-eigenvalue-and-edge-expansion.md)

## Sources

- S. Hoory, N. Linial, A. Wigderson, "Expander Graphs and Their Applications", Bulletin of the American Mathematical Society, 2006.
- S. Arora, B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
