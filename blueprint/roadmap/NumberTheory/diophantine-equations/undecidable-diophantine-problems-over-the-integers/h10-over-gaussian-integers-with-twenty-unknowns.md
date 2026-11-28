# Hilbert's tenth problem is undecidable over the Gaussian integers with twenty unknowns

There is no algorithm that decides, for an arbitrary polynomial $P(x_1, \dots, x_{20})$ with integer coefficients, whether the equation $P = 0$ has a solution with all twenty unknowns in the ring $\mathbb{Z}[i]$ of Gaussian integers.

Let $\mathbb{Z}[i] = \{a + bi : a, b \in \mathbb{Z}\}$ be the ring of Gaussian integers, the ring of integers of $\mathbb{Q}(i)$.

**Theorem (Matiyasevich–Sun).** There is no algorithm that decides, for any polynomial $P(x_1, \dots, x_{20}) \in \mathbb{Z}[x_1, \dots, x_{20}]$, whether the equation

$$
P(x_1, \dots, x_{20}) = 0
$$

has a solution with $x_1, \dots, x_{20} \in \mathbb{Z}[i]$.

Conventions: the polynomials have integer coefficients, not Gaussian ones, and exactly $20$ unknowns; the count is a fixed bound, and the problem is undecidable already for polynomials in $20$ unknowns. Hilbert's tenth problem over $\mathbb{Z}[i]$ without a bound on the number of unknowns was known to be undecidable since Denef's work on imaginary quadratic fields; the earlier record for a bounded number of unknowns over $\mathbb{Z}[i]$ was $52$.

## Depends on

- [Hilbert's tenth problem over a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/hilbert-s-tenth-problem-over-a-ring.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The key new ingredient is an economical way to recognize rational integers among the integers of an imaginary quadratic field $K = \mathbb{Q}(\sqrt{-d})$: for $x_1, \dots, x_n \in \mathcal{O}_K$ and $y = 2 \prod_{k=1}^{n} (3 x_k + 1)$, all $x_k$ lie in $\mathbb{Z}$ exactly when $y + \sum_{k=1}^{n} x_k / y^k$ lies in $\mathbb{Q}$. Start from a recursively enumerable set $\mathcal{A} \subseteq \mathbb{N}$ that is not recursive and Sun's representation $a \in \mathcal{A}$ if and only if $P(a, z_1, \dots, z_{10}) = 0$ for some integers $z_1, \dots, z_{10}$ with $z_{10} \neq 0$. Applying the criterion with $n = 10$ forces the ten unknowns, taken in $\mathbb{Z}[i]$, to be rational integers; the condition "rational" is rewritten as the existence of a nonzero integer $t$ with $t \cdot (y + \sum z_k / y^k) \in \mathbb{Z}$ and $t y^{10} \mid \sum z_k y^{10 - k}$, and integrality of $t$ and the divisibility are expressed with a few extra unknowns over $\mathbb{Z}[i]$ through Pell-type equations. Counting all unknowns gives $20$; deciding the resulting equations would decide membership in $\mathcal{A}$. A good expansion links pages for the criterion for rational integers in imaginary quadratic fields (Theorem 1.2 of the source), for Sun's representation of recursively enumerable sets with ten integer unknowns, and for the Pell-type equations that express integrality and divisibility over $\mathbb{Z}[i]$.

## Sources

- Yuri Matiyasevich and Zhi-Wei Sun, *Undecidability on Diophantine equations over $\mathbb{Z}[i]$ with $20$ unknowns*, J. Number Theory 290 (2027), 210–219, https://doi.org/10.1016/j.jnt.2026.05.009, read in the copy arXiv:2510.18794v1: the statement is Theorem 1.1 there, the criterion for rational integers is Theorem 1.2, and the proof of Theorem 1.1 is in its Section 3.
