# Post's functional completeness criterion

A family $G$ of positive-arity Boolean operations (possibly infinite, of unbounded arities) generates every positive-arity Boolean operation if and only if $G$ is contained in none of the five classes $T_0, T_1, M, S, L$. Equivalently, for $G$ to be complete it must contain an operation not preserving $0$, one not preserving $1$, a non-monotone one, a non-self-dual one and a non-affine one. For example $\{\mathrm{NAND}\}$ and $\{\wedge, \neg\}$ are complete, while $\{\wedge, \vee, 0, 1\}$ (monotone) and $\{\oplus, \neg\}$ (affine) are not.

## Proof sketch

Necessity: each class is a clone, so a family inside one generates only members of it. Sufficiency: from witnesses outside $T_0$ and $T_1$ and outside $S$, obtain the constants or negation by identifying variables; from a non-monotone witness obtain negation; from a non-affine witness and negation obtain conjunction by fixing variables in a nonlinear monomial; $\{\wedge, \neg\}$ is complete by functional completeness of propositional logic.

## Depends on

- [Post's five maximal clones](posts-five-maximal-clones.md)
- [Boolean clones](boolean-clones.md)

## Proof depends on

- [Operations computed by circuits over a family lie in its generated clone](generated-operations-are-formula-definable.md)
- [Functional completeness](../../functional-completeness/exists-eval-bool-eq.md)

## Sources

- E. L. Post, The Two-Valued Iterative Systems of Mathematical Logic, Annals of Mathematics Studies 5, Princeton University Press, 1941.
- F. J. Pelletier and N. M. Martin, "Post's Functional Completeness Theorem", Notre Dame Journal of Formal Logic 31(3), 462–475, 1990.
