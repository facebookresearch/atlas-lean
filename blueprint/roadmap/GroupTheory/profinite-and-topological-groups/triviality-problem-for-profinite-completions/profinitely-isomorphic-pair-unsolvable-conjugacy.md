# Profinite completions do not detect solvability of the conjugacy problem

There are finitely presented residually finite groups $P \hookrightarrow \Gamma$ such that the inclusion induces an isomorphism of profinite completions, the conjugacy problem in $P$ is unsolvable, and the conjugacy problem in $\Gamma$ is solvable in quadratic time.

For a group $G$ let $\hat G$ be its profinite completion, the inverse limit of its finite quotients. There exist pairs of finitely presented, residually finite groups $u\colon P \hookrightarrow \Gamma$ such that $\hat u\colon \hat P \to \hat \Gamma$ is an isomorphism, the conjugacy problem in $P$ is unsolvable, and the conjugacy problem in $\Gamma$ can be solved in quadratic time (Theorem A of the source; Theorem 2.1 sharpens the bound to RAM-linear time).

With $P$ only finitely generated, $\Gamma$ can moreover be taken conjugacy separable (Proposition 2.4).

## Depends on

- [Profinite completion](../profinite-rigidity/profinite-completion.md)
- [Group](../../group-basics/group.md)
- [Residually finite groups](../../geometric-group-theory/branch-and-thompson-groups/just-infinite-groups/is-residually-finite.md)
- [Solvable conjugacy problem for a quotient of a free group](../../presentations-and-decision-problems/decision-problems-in-free-abelianized-extensions/conjugacy-problem-solvable.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Conjugacy separable groups](../../soluble-finite-groups/solubility-nilpotency-and-subnormality/is-conjugacy-separable.md)

## Proof depends on

- [Novikov–Boone theorem (unsolvability of the word problem)](../../presentations-and-decision-problems/word-problem-for-groups/novikov-unsolvable.md)

## Expansion

The construction combines the fibre products of Baumslag, Bridson, Miller and Short, the Collins–Miller sequence of aspherical presentations with undecidable triviality, and the Bridson–Grunewald method: starting from a finitely presented group $Q$ with no non-trivial finite quotients and suitable homological properties, and a hyperbolic group mapping onto $Q$, the fibre product $P$ of a product of two copies of the hyperbolic group over $Q$ is profinitely isomorphic to the product, while unsolvability of the word problem in $Q$ gives unsolvable conjugacy problem in $P$.

## Sources

- M. R. Bridson, "Decision problems and profinite completions of groups", Journal of Algebra 326 (2011), no. 1, 59–73, https://doi.org/10.1016/j.jalgebra.2010.06.019; read in arXiv:0810.0390v1 (Theorem A of the introduction, Theorem 2.1 and Proposition 2.4 of arXiv:0810.0390v1).
