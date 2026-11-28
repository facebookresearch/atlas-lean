# Diophantine equations with unknowns restricted to squares or polygonal numbers are undecidable with seventeen or eighteen unknowns

No algorithm decides whether an integer polynomial in $17$ variables has a zero all of whose coordinates are perfect squares, nor, with $18$ variables, a zero whose coordinates are triangular, pentagonal or octagonal numbers.

Let $\square = \{x^2 : x \in \mathbb{Z}\}$ be the set of integer squares, and let

$$
\mathrm{Tri} = \{ T_x : x \in \mathbb{Z} \}, \qquad \mathrm{Pen} = \{ p_5(x) : x \in \mathbb{Z} \}, \qquad \mathrm{Octa} = \{ p_8(x) : x \in \mathbb{Z} \},
$$

where $T_x = x(x+1)/2$ are the triangular numbers, $p_5(x) = x(3x - 1)/2$ the generalized pentagonal numbers and $p_8(x) = x(3x - 2)$ the generalized octagonal numbers. For a set $S \subseteq \mathbb{Z}$ and $n \ge 1$, say that *$\exists^n$ over $S$ is undecidable* when there is no algorithm that decides, for an arbitrary polynomial $P(z_1, \dots, z_n) \in \mathbb{Z}[z_1, \dots, z_n]$, whether $P(z_1, \dots, z_n) = 0$ for some $z_1, \dots, z_n \in S$.

**Theorem (Sun).** $\exists^{17}$ over $\square$, $\exists^{18}$ over $\mathrm{Tri}$, $\exists^{18}$ over $\mathrm{Pen}$ and $\exists^{18}$ over $\mathrm{Octa}$ are all undecidable.

Conventions: equivalently, for squares, there is no algorithm deciding whether $P(x_1^2, \dots, x_{17}^2) = 0$ has an integer solution. The source conjectures that $\exists^3$ over $\square$ is already undecidable; that is not part of the theorem.

## Depends on

- [Polygonal numbers](../../quadratic-forms-sums-of-squares/waring-figurate/polygonal-numbers/polygonal-number.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

Sun proves that every recursively enumerable set $\mathcal{A} \subseteq \mathbb{N}$ has a representation with unknowns from these sets: there is a polynomial $P_4(z_0, z_1, \dots, z_{17})$ with integer coefficients such that, for every $a \in \mathbb{N}$, $a \in \mathcal{A}$ exactly when $P_4(a, z_1, \dots, z_{17}) = 0$ for some $z_1, \dots, z_{17} \in \square$, and similar polynomials $P_3$, $P_5$, $P_8$ in $18$ unknowns for $\mathrm{Tri}$, $\mathrm{Pen}$ and $\mathrm{Octa}$. The proof modifies the proof of Sun's representation theorem in nine integer unknowns so that the unknowns appear through squares, and uses identities such as $8 T_z + 1 = (2z + 1)^2$, $3 p_8(z) + 1 = (3z - 1)^2$ and $24 p_5(z) + 1 = (6z - 1)^2$ to pass between squares and polygonal numbers, together with representations of integers such as $2^{\delta}(x^2 - y^2)$ with $\delta \in \{0, 1\}$. Taking $\mathcal{A}$ recursively enumerable but not recursive gives the undecidability. A good expansion links pages for Sun's representation of recursively enumerable sets with nine integer unknowns, which the proof of Theorem 1.6 modifies, for Lemma 6.1 and for the existence of a recursively enumerable set that is not recursive.

## Sources

- Zhi-Wei Sun, *Further results on Hilbert's tenth problem*, Sci. China Math. 64 (2021), no. 2, 281–306, https://doi.org/10.1007/s11425-020-1813-5, read in the copy arXiv:1704.03504v7: the statement is Corollary 1.7 there and the representation theorem is Theorem 1.6; the fact that every integer has the form $2^{\delta}(x^2 - y^2)$ with $\delta \in \{0, 1\}$ is Lemma 6.1 (i) of that version, and the proof of Theorem 1.6 is in Section 6.
