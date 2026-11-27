# Hilbert's tenth problem is undecidable over function fields of positive characteristic not containing the algebraic closure of a finite field

Let $K$ be a function field of positive characteristic $p$ whose constant field does not contain the algebraic closure of $\mathbb{F}_p$. Then no algorithm decides whether polynomial equations with coefficients in a suitable finitely generated subfield of $K$ have solutions in $K$; for countable $K$, Hilbert's tenth problem over $K$ is undecidable.

A *function field in $n$ variables* over a field $F$, for $n \ge 1$, is a field $K$ containing $F$ and elements $x_1, \dots, x_n$ algebraically independent over $F$ such that $K$ is a finite algebraic extension of $F(x_1, \dots, x_n)$. Here $K$ has characteristic $p > 0$, and "$K$ does not contain the algebraic closure of a finite field" means that $K$ does not contain an algebraic closure $\overline{\mathbb{F}}_p$ of $\mathbb{F}_p$.

**Theorem (Eisenträger–Shlapentokh).** Let $K$ be a function field of positive characteristic $p$ that does not contain the algebraic closure of a finite field.

1. There is a finitely generated subfield $K_0 \subseteq K$ such that Hilbert's tenth problem over $K$ with coefficients in $K_0$ is undecidable: there is no algorithm that decides, for a polynomial equation with coefficients in $K_0$, whether it has a solution in $K$.
2. If $K$ is countable, then Hilbert's tenth problem over $K$ is undecidable.

Conventions: the number of variables $n$ and the field of constants are arbitrary apart from the stated restriction; $K_0$ depends on $K$; in clause 2, as in the source's setting of recursive rings, elements of $K$ are encoded as finite strings so that the ring operations are computable. The remaining case, a function field over a field of constants containing $\overline{\mathbb{F}}_p$, includes the open case of one-variable function fields over an algebraically closed field.

## Depends on

- [Hilbert's tenth problem over a ring](../../diophantine-equations/hilbert-s-tenth-problem-over-number-rings/hilbert-s-tenth-problem-over-a-ring.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

For a prime $p$ and positive integers $n, m$, write $n \mid_p m$ when $m = n p^s$ for some $s \ge 0$. Pheidas proved that the existential theory of $(\mathbb{Z}_{>0}, +, \mid_p)$ is undecidable, by defining multiplication of positive integers existentially from $+$ and $\mid_p$, which reduces Hilbert's original problem to it. The reduction to $K$ needs existential definitions over $K$ of the set $P(K) = \{(x, x^{p^s}) : x \in K,\ s \ge 0\}$ and of a set $\mathrm{INT}(K, \mathfrak{p}, t)$ of elements integral at a prime $\mathfrak{p}$ of $K$, for a nonconstant $t$ with $\operatorname{ord}_{\mathfrak{p}} t > 0$, that contains every element of $k_0(t)$ integral at $\mathfrak{p}$, where $k_0$ is the algebraic closure of a finite field in $K$. A positive integer $n$ is represented by the elements of $\mathrm{INT}(K, \mathfrak{p}, t)$ of order $n$ at $\mathfrak{p}$, so addition of integers becomes multiplication in $K$, and $\mid_p$ is expressed through $P(K)$. The new part of the source is an existential definition of $P(K)$ in every function field of positive characteristic, including those with algebraically closed constant field; the hypothesis that $K$ does not contain $\overline{\mathbb{F}}_p$ is used to define $\mathrm{INT}(K, \mathfrak{p}, t)$.

## Sources

- Kirsten Eisenträger (Eisentraeger) and Alexandra Shlapentokh, *Hilbert's tenth problem over function fields of positive characteristic not containing the algebraic closure of a finite field*, J. Eur. Math. Soc. 19 (2017), no. 7, 2103–2138, https://doi.org/10.4171/JEMS/714; clause 1 is Theorem 1.2 and clause 2 is Theorem 1.1 of arXiv:1306.2669v1.
