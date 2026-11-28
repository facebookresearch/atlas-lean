# Hilbert's tenth problem over a ring of integers is undecidable given a rank-one elliptic curve

Let $F \subseteq K$ be number fields. If some elliptic curve over $F$ has rank one over both $F$ and $K$, then the ring of integers of $F$ is Diophantine over that of $K$; when moreover $F$ is totally real, a quadratic extension of a totally real field, or has exactly one pair of nonreal embeddings, Hilbert's tenth problem over the ring of integers of $K$ is undecidable.

Let $F \subseteq K$ be number fields with rings of integers $\mathcal{O}_F \subseteq \mathcal{O}_K$. Suppose that there is an elliptic curve $E$ over $F$ with

$$
\operatorname{rk} E(F) = \operatorname{rk} E(K) = 1 .
$$

Then:

1. $\mathcal{O}_F$ has a Diophantine definition over $\mathcal{O}_K$: there is a polynomial $g(t, y_1, \dots, y_m)$ with coefficients in $\mathcal{O}_K$ such that an element $t \in \mathcal{O}_K$ lies in $\mathcal{O}_F$ if and only if $g(t, y) = 0$ for some $y \in \mathcal{O}_K^m$.
2. If in addition $F$ is totally real, or $F$ is a quadratic extension of a totally real number field, or $F$ has exactly one pair of complex conjugate nonreal embeddings, then Hilbert's tenth problem over $\mathcal{O}_K$ is undecidable: no algorithm decides, for a polynomial with coefficients in $\mathcal{O}_K$, whether it has a zero in $\mathcal{O}_K^n$.

The case $F = \mathbb{Q}$ reads: if some elliptic curve $E$ over $\mathbb{Q}$ satisfies $\operatorname{rk} E(\mathbb{Q}) = \operatorname{rk} E(K) = 1$, then Hilbert's tenth problem over $\mathcal{O}_K$ is undecidable. Clause 1 is the main theorem of the source and clause 2 its corollary.

Conventions: the rank of $E$ over $K$ is that of its base change; elements of $\mathcal{O}_K$ are encoded by their integer coordinates in a fixed integral basis; the three types of $F$ in clause 2 are those for which a Diophantine definition of $\mathbb{Z}$ over $\mathcal{O}_F$ was known when the source appeared.

## Depends on

- [Hilbert's tenth problem over a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/hilbert-s-tenth-problem-over-a-ring.md)
- [Mordell–Weil rank of an elliptic curve](../../arithmetic-geometry/mordell-weil-rank-of-an-elliptic-curve.md)
- [Integral closure of ℤ in a field and the ring of integers of a number field](../../algebraic-number-theory/number-fields-embeddings/ring-of-integers.md)
- [Diophantine subsets of a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/is-diophantine-set.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)
- [The halting problem is recognizable by multi-stack machines](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/tm2-recognizable-halting.md)
- [The halting problem is undecidable by multi-stack machines](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halting.md)

## Expansion

For clause 1, the proof follows the older Denef–Lipshitz argument with the elliptic curve in place of the one-dimensional torus of a Pell equation. Over $\mathcal{O}_K$, divisibility between fractional ideals, and in particular between the denominator ideals of elements of $K$, is Diophantine. Because $\operatorname{rk} E(F) = \operatorname{rk} E(K) = 1$, the group $E(F)$ has finite index in $E(K)$, so a fixed multiple of any point of $E(K)$ lies in $E(F)$. The denominators of the $x$-coordinates of the multiples $nP$ of a point $P$ of infinite order grow and divide each other in a controlled way. Combined with a bound saying that if $\mu \in \mathcal{O}_K$ and $\mu(\mu+1)\cdots(\mu+[K:\mathbb{Q}])$ divides a nonzero nonunit ideal $I$ of $\mathcal{O}_K$, then the coordinates $a_i$ of $\mu$ in a fixed power basis of $K$ over $F$ with discriminant $D$ satisfy $N_{K/\mathbb{Q}}(D a_i) \le N_{K/\mathbb{Q}}(I)^c$ for a constant $c$, and with the fact that an element $\mu \in \mathcal{O}_K$ congruent modulo $I\mathcal{O}_K$ to an element of $\mathcal{O}_F$, for a nonzero ideal $I$ of $\mathcal{O}_F$ whose norm is large compared with every $N_{K/\mathbb{Q}}(D a_i)$, lies in $\mathcal{O}_F$ (Lemmas 4 and 5 of the source), these divisibilities give a Diophantine condition that cuts $\mathcal{O}_F$ out of $\mathcal{O}_K$.

For clause 2, the cited works of Denef, Denef and Lipshitz, Pheidas, and Shlapentokh give a Diophantine definition of $\mathbb{Z}$ over $\mathcal{O}_F$ for the three types of $F$. Composing it with clause 1 gives a Diophantine definition of $\mathbb{Z}$ over $\mathcal{O}_K$, which reduces Hilbert's original problem over $\mathbb{Z}$ to the problem over $\mathcal{O}_K$. The original problem is undecidable because every listable subset of $\mathbb{Z}$, including one with non-listable complement such as the halting set, is Diophantine. A good expansion adds and links pages for the Diophantine definitions of $\mathbb{Z}$ over $\mathcal{O}_F$ due to Denef, Denef and Lipshitz, Pheidas, and Shlapentokh, and for the Diophantine divisibility and denominator facts of clause 1.

## Sources

- Bjorn Poonen, *Using elliptic curves of rank one towards the undecidability of Hilbert's tenth problem over rings of algebraic integers*, in: Algorithmic Number Theory (ANTS-V, Sydney, 2002), Lecture Notes in Computer Science 2369, Springer, 2002, pp. 33–42, https://doi.org/10.1007/3-540-45455-1_4; the version read is arXiv:math/0204001v1, the only arXiv version. Clause 1 is the main theorem and clause 2 its corollary, both in the section on Hilbert's tenth problem over rings of integers.
- Jochen Koenigsmann, *Undecidability in number theory*, in: Model Theory in Algebra, Analysis and Arithmetic, Lecture Notes in Mathematics 2111, Springer, 2014, pp. 159–195, https://doi.org/10.1007/978-3-642-54936-6_5; the case $F = \mathbb{Q}$ is Theorem 5.1 of arXiv:1309.0441v1.
