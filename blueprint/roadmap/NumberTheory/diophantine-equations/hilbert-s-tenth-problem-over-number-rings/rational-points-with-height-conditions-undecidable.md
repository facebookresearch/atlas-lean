# Existence of rational points with height comparison conditions is undecidable

There is no algorithm that decides, for a system of polynomial equations over $\mathbb{Q}$ together with conditions comparing logarithmic heights of tuples of unknowns, whether it has a rational solution: the positive existential theory of $\mathbb{Q}$ with height comparison relations is undecidable.

For a rational number $q = a/b$ with $a, b$ coprime integers, its logarithmic height is $h(q) = \log \max\{|a|, |b|\}$. For a tuple $\mathbf{q} = (q_1, \dots, q_m) \in \mathbb{Q}^m$ with least common denominator $d \ge 1$, let

$$
h_m(\mathbf{q}) = \log \max\{ d, |d q_1|, \dots, |d q_m| \} ,
$$

so $h_1 = h$. For $m, n \ge 1$ define the height comparison relation $H_{m,n}$ on $\mathbb{Q}^m \times \mathbb{Q}^n$ by $H_{m,n}(\mathbf{x}, \mathbf{y})$ if and only if $h_m(\mathbf{x}) \le h_n(\mathbf{y})$. Let $\mathcal{L}_h$ be the language with constants $0, 1$, function symbols $+$ and $\times$, and relation symbols $=$ and $H_{m,n}$ for all $m, n \ge 1$, interpreted on $\mathbb{Q}$ in the obvious way.

**Theorem (Garcia-Fritz–Pasten–Vidaux).** The positive existential theory of $\mathbb{Q}$ in the language $\mathcal{L}_h$ is undecidable. Thus there is no algorithm that takes as input a system of polynomial equations with integer coefficients in unknowns ranging over $\mathbb{Q}$, together with height comparison conditions $H_{m,n}$ between tuples of polynomial expressions in the unknowns, and decides whether a rational solution satisfying these conditions exists.

Conventions: positive existential sentences are built from atomic formulas by conjunction, disjunction and existential quantification; the relation $\neq$ is positive existentially definable over any field in the language of rings, so inequalities may be used. Without the height relations this is Hilbert's tenth problem over $\mathbb{Q}$, whose decidability is open; the theorem shows that adding comparisons of heights, as in effective versions of results on rational points, already makes the problem undecidable.

## Depends on

- [Hilbert's tenth problem over a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/hilbert-s-tenth-problem-over-a-ring.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The main step is a positive existential interpretation of the semiring $(\mathbb{N}; 0, 1, +, \times, =)$ in the structure $(\mathbb{Q}; \mathcal{L}_h)$. Using the theory of heights on elliptic curves, the source interprets positive existentially the structure $(\mathbb{N}; 0, 1, +, B, =)$, where $B(a, b)$ holds when $a$ and $b$ are consecutive squares, $a = n^2$ and $b = (n + 1)^2$; multiplication is positive existentially definable in that structure. Only the relations $H_{m,n}$ with $m, n \le 3$ are needed. Since the positive existential theory of $(\mathbb{N}; 0, 1, +, \times, =)$ is undecidable by the negative solution of Hilbert's tenth problem, so is that of $(\mathbb{Q}; \mathcal{L}_h)$. A good expansion links pages for the positive existential interpretation of $(\mathbb{N}; 0, 1, +, \times, =)$ in $(\mathbb{Q}; \mathcal{L}_h)$ (Theorem 1.1 of the source), for the heights on an elliptic curve with Mordell–Weil group $\mathbb{Z}$ that it uses, and for the transfer of undecidability along a positive existential interpretation (Proposition 2.1 of the source).

## Sources

- Natalia Garcia-Fritz, Hector Pasten and Xavier Vidaux, *Effectivity for existence of rational points is undecidable*, J. Number Theory 276 (2025), 81–97, https://doi.org/10.1016/j.jnt.2025.01.023, read in the copy arXiv:2311.01958v2: the statement is Theorem 1.2 there, deduced from the interpretation of Theorem 1.1, with heights and $H_{m,n}$ defined in its introduction.
