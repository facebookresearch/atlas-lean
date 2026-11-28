# Hilbert's tenth problem over the integers is undecidable with eleven unknowns and degree at most 1.69·10^63

No algorithm decides, for every Diophantine equation with integer coefficients, at most eleven unknowns ranging over $\mathbb{Z}$ and total degree at most $1.69 \cdot 10^{63}$, whether it has an integer solution. This sharpens Matiyasevich's negative solution of Hilbert's tenth problem.

A pair $(\nu, \delta)$ of positive integers is *universal over $\mathbb{Z}$* when every Diophantine subset of $\mathbb{N}$ (every recursively enumerable set) has the form $\{a \in \mathbb{N} : \exists z \in \mathbb{Z}^{\nu},\ P(a, z) = 0\}$ for a polynomial $P \in \mathbb{Z}[a, z_1, \dots, z_\nu]$ of total degree at most $\delta$; universality over $\mathbb{N}$ is defined the same way with unknowns in $\mathbb{N}$.

**Theorem (Bayer–David, after Sun).** If $(\nu, \delta)$ is universal over $\mathbb{N}$, then $(11, \eta(\nu, \delta))$ is universal over $\mathbb{Z}$, where

$$
\eta(\nu, \delta) = 15\,616 + 233\,856\, \delta + 233\,952\, \delta (2\delta + 1)^{\nu + 1} + 467\,712\, \delta^2 (2\delta + 1)^{\nu + 1} .
$$

In particular $(11, 1.68105 \cdot 10^{63})$ is universal over $\mathbb{Z}$, and **Hilbert's tenth problem is undecidable for the class of Diophantine equations with at most $11$ unknowns and degree at most $1.69 \cdot 10^{63}$**: there is no algorithm that decides, for every equation in this class, whether it has a solution in integers.

Conventions: unknowns range over $\mathbb{Z}$; the parameter $a$ is a natural number and is not counted among the unknowns of a representation, while in the undecidable class each equation is a polynomial in its unknowns with integer coefficients. The bound $1.68105 \cdot 10^{63}$ uses the universal pair $(58, 4)$ over $\mathbb{N}$; the source also states $(11, 9.50818 \cdot 10^{53})$ from Jones' pair $(32, 12)$ over $\mathbb{N}$, whose proof it notes is unpublished.

## Depends on

- [Hilbert's tenth problem over a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/hilbert-s-tenth-problem-over-a-ring.md)
- [Diophantine sets](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/is-diophantine.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The core step, due to Sun, is an explicit construction (Theorem 3 of the source): for every $P \in \mathbb{Z}[a, z_1, \dots, z_\nu]$ there is $\tilde Q \in \mathbb{Z}[a, \tilde z_1, \dots, \tilde z_{11}]$ such that for all $a \in \mathbb{N}$, $P(a, z) = 0$ has a solution in $\mathbb{Z}^{\nu}$ exactly when $\tilde Q(a, \tilde z) = 0$ has one in $\mathbb{Z}^{11}$. Bayer and David track the degree of $\tilde Q$ through the construction, which produces the bound $\eta(\nu, \delta)$. The naive conversion from natural-number unknowns to integer unknowns by Lagrange's four-square theorem would turn the $9$ unknowns of Matiyasevich's universal pair over $\mathbb{N}$ into $36$, and the three-square theorem into $27$. Undecidability for the class follows because, by the Davis–Putnam–Robinson–Matiyasevich theorem, some recursively enumerable set that is not decidable is represented by a polynomial in the class, so deciding solvability for the class would decide membership in that set. A good expansion links pages for Sun's eleven-unknown construction, with its coding, Lucas sequence and relation-combining steps, and for a universal pair over $\mathbb{N}$.

## Sources

- Jonas Bayer and Marco David, *A formal proof of complexity bounds on Diophantine equations*, in: 16th International Conference on Interactive Theorem Proving (ITP 2025), Leibniz International Proceedings in Informatics 352, Schloss Dagstuhl, 2025, 3:1–3:18, https://doi.org/10.4230/LIPIcs.ITP.2025.3; Theorem 1 and Corollary 2 of arXiv:2505.16963v2 (that version's numbering).
