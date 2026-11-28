# Hilbert's tenth problem over the natural numbers is undecidable with nine unknowns

There is no algorithm that decides, for an arbitrary polynomial $f(x_1, \dots, x_9)$ with integer coefficients, whether it has a zero with all nine unknowns in the natural numbers; equivalently, detecting a point with coordinates in $\mathbb{N}$ on a general hypersurface of (complex) dimension eight is undecidable.

Let $\mathbb{N} = \{0, 1, 2, \dots\}$.

**Theorem (Jones).** There is no algorithm that decides, for an arbitrary polynomial $f \in \mathbb{Z}[x_1, \dots, x_9]$, whether there are $x_1, \dots, x_9 \in \mathbb{N}$ with $f(x_1, \dots, x_9) = 0$.

Conventions: the number of unknowns is fixed at $9$ and the polynomial, of unbounded degree, is the input; unknowns range over $\mathbb{N}$, not $\mathbb{Z}$; the version over $\mathbb{Z}$ is [Hilbert's tenth problem over the integers is undecidable with eleven unknowns and degree at most 1.69·10^63](h10-over-z-with-eleven-unknowns.md).

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

By the Davis–Putnam–Robinson–Matiyasevich theorem every recursively enumerable set $A \subseteq \mathbb{N}$ is Diophantine. Jones showed that nine unknowns suffice: every recursively enumerable set has a representation $a \in A \iff \exists x_1, \dots, x_9 \in \mathbb{N} \; P(a, x_1, \dots, x_9) = 0$ with a single polynomial $P$. Taking $A$ recursively enumerable but not recursive, each fixed $a$ gives a polynomial $f_a(x_1, \dots, x_9) = P(a, x_1, \dots, x_9)$ in nine unknowns, and an algorithm for the problem would decide membership in $A$. A good expansion links a page for Jones's representation of every recursively enumerable set with nine natural-number unknowns.

## Sources

- J. Maurice Rojas, *On the complexity of Diophantine geometry in low dimensions*, in: Proceedings of the 31st Annual ACM Symposium on Theory of Computing (STOC 1999), ACM, 1999, pp. 527–536, https://doi.org/10.1145/301250.301395, read in the copy arXiv:math/9811088v1, where the statement is recalled as established, with the reference to Jones, in the introduction.
- J. P. Jones, *Universal Diophantine equation*, J. Symbolic Logic 47 (1982), no. 3, 549–571, https://doi.org/10.2307/2273588, cited beside the source above.
