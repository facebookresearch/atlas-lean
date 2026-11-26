# Every Boolean clone is essentially unary or contains AND, OR, majority or minority

Let $C$ be a positive-arity Boolean clone. Then either every operation of $C$ is essentially unary, or $C$ contains at least one of the four operations $\wedge$, $\vee$, $\mathrm{maj}$, $x \oplus y \oplus z$. This is the algebraic core shared by Post's criterion and Schaefer's dichotomy.

## Proof sketch

Take $f \in C$ not essentially unary. If $C$ contains a non-idempotent operation, use identification minors to obtain a negation or constants and reduce to idempotent operations. A binary idempotent minor that is not a projection is $\wedge$ or $\vee$. Otherwise all binary idempotent minors are projections; then the ternary partition minors of $f$ are idempotent operations whose binary minors are projections, and such a ternary operation is a projection, majority or minority; a projection-only outcome for all such minors forces $f$ to be essentially unary.

## Depends on

- [Essentially unary operations](essentially-unary-operations.md)
- [Boolean clones](boolean-clones.md)

## Sources

- H. Chen, "A Rendezvous of Logic, Complexity, and Algebra", SIGACT News 37(4), 85–114, 2006 (extended version ACM Computing Surveys 42(1), 2009).
- E. L. Post, The Two-Valued Iterative Systems of Mathematical Logic, Annals of Mathematics Studies 5, Princeton University Press, 1941.
