# Graph of a function on `P(ω)`

For a function $f : P(\omega) \to P(\omega)$, its graph is the set of codes

$$\operatorname{graph}(f) = \{\langle n, m\rangle \mid m \in f(e_n)\} \subseteq \mathbb{N},$$

where $e_n$ is the $n$-th finite set and $\langle n, m\rangle$ is a pairing of natural numbers (D. Scott, *Data types as lattices*, SIAM J. Comput. 5(3) (1976), 522–587, §1, definition of $\operatorname{graph}$). Interpreted as an operation, $\operatorname{graph}$ is λ-abstraction in the graph model.

Scott uses the Cantor pairing $\langle n, m\rangle = \tfrac12 (n+m)(n+m+1) + m$; here $\langle n, m\rangle = m^2 + n$ if $n < m$ and $\langle n, m\rangle = n^2 + n + m$ otherwise, a different bijection $\mathbb{N} \times \mathbb{N} \to \mathbb{N}$ that also satisfies $n \le \langle n, m\rangle$.

## Background

- [The `n`-th finite set of the graph model](fin-set.md): the finite sets $e_n$ at which $f$ is sampled.
- [Application in the graph model](app.md): the operation that reads a function back from its graph.

## Sources

- D. Scott, *Data types as lattices*, SIAM Journal on Computing 5(3) (1976), 522–587, doi:10.1137/0205037.
