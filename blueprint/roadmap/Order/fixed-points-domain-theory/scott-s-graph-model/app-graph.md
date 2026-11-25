# Scott's graph theorem, part (i)

Every Scott-continuous $f : P(\omega) \to P(\omega)$ is recovered from its graph:

$$\operatorname{app}(\operatorname{graph}(f), x) = f(x) \quad \text{for all } x \subseteq \mathbb{N}$$

(D. Scott, *Data types as lattices*, SIAM J. Comput. 5(3) (1976), 522–587, Theorem 1.2 (i)). Read with $\operatorname{app}$ as application and $\operatorname{graph}$ as λ-abstraction, this is the β-rule of the graph model. Together with part (ii), it makes the continuous self-maps of $P(\omega)$ a retract of $P(\omega)$.

## Informally uses

- [Scott's characterisation theorem for `P(ω)`](mem-iff-exists-finset-of-scott-continuou.md): Scott's proof notes that the equation "is just another way of writing the definition of continuity".

## Background

- [Scott's graph theorem, part (ii)](subset-graph-app.md): the other half of the retraction.
- [Soundness of a β-contraction in the graph model](../../../ComputerScience/programming-language-semantics/models-of-the-untyped-lambda-calculus/denote-eq-of-beta.md): this theorem applied to λ-terms.

## Sources

- D. Scott, *Data types as lattices*, SIAM Journal on Computing 5(3) (1976), 522–587, doi:10.1137/0205037.
