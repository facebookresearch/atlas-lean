# Every Turing degree contains a set of primes whose subring of the rationals has Hilbert's tenth problem as hard as its jump

For a set $W$ of primes let $R_W = \mathbb{Z}[W^{-1}]$. Every Turing degree contains a set $W$ such that Hilbert's tenth problem over $R_W$ is $1$-equivalent to the jump $W'$; in particular this problem is not computable from $W$.

For a set $W$ of prime numbers let $R_W = \mathbb{Z}[W^{-1}]$, the subring of $\mathbb{Q}$ in which exactly the primes of $W$ are invertible. Let $HTP(R_W)$ be the set of polynomials in $\mathbb{Z}[X_1, X_2, \dots]$, under a fixed computable coding, that have a zero with coordinates in $R_W$. Write $A \le_1 B$ when there is a total computable injective function $h$ with $x \in A \iff h(x) \in B$ for all $x$, and $A \equiv_1 B$ when $A \le_1 B$ and $B \le_1 A$; $W'$ denotes the Turing jump of $W$, the halting set relative to the oracle $W$.

Since an oracle for $W$ lists the elements of $R_W$, the set $HTP(R_W)$ is computably enumerable in $W$, so $HTP(R_W) \le_1 W'$ always holds. A set $W$ of primes is *HTP-complete* when the reverse reduction also holds, that is, when $W' \le_1 HTP(R_W)$, equivalently $HTP(R_W) \equiv_1 W'$.

**Theorem (Miller).** Every Turing degree contains an HTP-complete set $V$. Indeed, there is a uniform procedure that, given any set $C \subseteq \mathbb{N}$, computes an HTP-complete set of primes $V$ with $V \equiv_T C$.

Since $W'$ is not computable from $W$, for an HTP-complete $W$ the set $HTP(R_W)$ is not computable relative to $W$, and in particular Hilbert's tenth problem over $R_W$ is undecidable. Conventions: $\emptyset$ is HTP-complete by the Davis–Putnam–Robinson–Matiyasevich theorem, since $R_\emptyset = \mathbb{Z}$; whether the set of all primes, with $R_W = \mathbb{Q}$, is HTP-complete is open. By earlier work cited in the source, the HTP-complete sets form a meager set of Lebesgue measure zero (Theorem 3.2 of the source).

## Depends on

- [Hilbert's tenth problem over a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/hilbert-s-tenth-problem-over-a-ring.md)
- [Turing degree of a predicate](../../../TheoryOfComputation/degrees-and-hierarchies/turing-degrees-and-the-turing-jump/turing-degree-of.md)
- [The Turing jump](../../../TheoryOfComputation/degrees-and-hierarchies/turing-degrees-and-the-turing-jump/jump.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The construction is a finite-injury priority argument relative to the oracle $C$. It starts from the set of all primes and removes primes in stages, so the resulting $V$ is $\Pi^0_1$ relative to $C$; the proof then shows $V \le_T C$ and $C \le_T V$. For the $e$-th odd prime $q_e$, call a prime $p$ $q_e$-appropriate when $p$ is odd, $p \neq q_e$ and $-q_e$ is a square modulo $p$; the odd prime factors of the common denominator of a rational solution of $x^2 + q_e y^2 = 1$ are $q_e$-appropriate. Requirement $e$ asks that a polynomial $g_e$, built from $x^2 + q_e y^2 = 1$ with $y > 0$, be solvable in $R_V$ exactly when the $e$-th oracle computation relative to $C$ halts: while the computation has not halted, the requirement removes $q_e$-appropriate primes from $V$, and once it halts, it protects certain $q_e$-appropriate primes so that solutions survive. Julia Robinson's existential definitions of the semilocal subrings $R_{\mathbb{P} \setminus \{p\}}$ in $\mathbb{Q}$ are used to replace each $f_e$ by a $g_e$ adapted to a semilocal subring fixed in advance, which handles the finitely many injuries. A good expansion links pages for the priority construction, for Julia Robinson's existential definitions of the semilocal subrings of $\mathbb{Q}$, and for the $1$-reduction of $W'$ to $HTP(R_W)$ that the requirements produce.

## Sources

- Russell Miller, *HTP-complete rings of rational numbers*, J. Symbolic Logic 87 (2022), no. 1, 252–272, https://doi.org/10.1017/jsl.2021.96, read in the copy arXiv:1907.03147v2: the theorem is Theorem 4.1 there, HTP-completeness is Definition 3.1, and the measure and category statement is Theorem 3.2.
