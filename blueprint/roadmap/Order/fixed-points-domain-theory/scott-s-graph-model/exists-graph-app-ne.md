# The graph model is not extensional

There is a set $u \subseteq \mathbb{N}$ with $\operatorname{graph}(x \mapsto \operatorname{app}(u, x)) \ne u$. For instance $u = \{\langle n_0, 0\rangle\}$ with $e_{n_0} = \emptyset$ works: the graph of the constant function it determines also contains $\langle n_1, 0\rangle$ for $e_{n_1} = \{0\}$.

So the retraction of $P(\omega)$ onto the continuous functions is not a bijection, and the η-rule fails in $P(\omega)$. Scott's conversion theorem validates only the rules α, β and ξ in $P(\omega)$ (D. Scott, *Data types as lattices*, SIAM J. Comput. 5(3) (1976), 522–587, Theorem 2.2), and he notes that "the failure of (η) simply means that not every set in $P\omega$ is the graph of a function" (Appendix A).

## Background

- [Scott's graph theorem, part (ii)](subset-graph-app.md): the inclusion that is strict here.
- [The η-rule is not sound in the graph model](../../../ComputerScience/programming-language-semantics/models-of-the-untyped-lambda-calculus/exists-denote-eta-ne.md): the same fact for λ-terms.

## Sources

- D. Scott, *Data types as lattices*, SIAM Journal on Computing 5(3) (1976), 522–587, doi:10.1137/0205037.
