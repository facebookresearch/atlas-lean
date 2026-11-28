# Everywhere positivity of polynomials in the variables and their sines is undecidable

There is an integer polynomial P such that, for an integer parameter a, the function P(a, x, sin πx) on ℝⁿ is either everywhere greater than 1 or takes values below −1 and above 1, and no algorithm decides which, given a. This is a form of Richardson's theorem.

**Theorem (a variant of Richardson's theorem).** There is a polynomial $P \in \mathbb Z[t, x_1, \ldots, x_n, y_1, \ldots, y_n]$ such that for each $a \in \mathbb Z$ the real analytic function

$$
x \mapsto P(a, x_1, \ldots, x_n, \sin \pi x_1, \ldots, \sin \pi x_n)
$$

on $\mathbb R^n$ is either everywhere greater than $1$, or else takes values less than $-1$ and values greater than $1$, and it is impossible to decide, given $a$, which of the two cases holds.

In particular, no algorithm decides whether a function in $\mathbb Z[x_1, \ldots, x_n, \sin \pi x_1, \ldots, \sin \pi x_n]$ is everywhere nonnegative on $\mathbb R^n$, although Tarski's quantifier elimination decides nonnegativity of real polynomials. The number $n$ of variables is fixed by the construction.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)
- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

By the Davis–Putnam–Robinson–Matiyasevich theorem there is a polynomial $p \in \mathbb Z[t, x_1, \ldots, x_n]$ defining a Diophantine subset $A$ of $\mathbb Z$ that is not computable (take a Diophantine representation of a recursively enumerable set that is not decidable, such as the halting set). One then chooses a second polynomial $G \in \mathbb Z[t, x_1, \ldots, x_n]$ with positive and fast-growing values and sets

$$
L_a(x) = -2 + 4\, p(a, x)^2 + G(a, x) \sum_{i=1}^n \sin^2 \pi x_i .
$$

Then $L_a(x) \le 1$ only in small neighborhoods of the integer zeros of $p(a, \cdot)$: if $a \in A$, the function $L_a$ equals $-2$ at such a zero and is large at some half-integer points; otherwise $L_a > 1$ on $\mathbb R^n$. Richardson's original statement and proof predate the solution of Hilbert's tenth problem and used the undecidability of exponential Diophantine equations instead (Remark 9.3 of the survey). A good expansion links a page for the analytic lemma giving the fast-growing polynomial $G$.

## Sources

- Daniel Richardson, "Some undecidable problems involving elementary functions of a real variable", *Journal of Symbolic Logic* 33(4), 1968, pp. 514–520, <https://doi.org/10.2307/2271358>: Section 1, Corollary to Theorem One (cited after the survey below, which presents the result as established).
- B. Poonen, "Undecidable problems: a sampler", in *Interpreting Gödel: Critical Essays* (J. Kennedy, ed.), Cambridge University Press, 2014, pp. 211–241, <https://doi.org/10.1017/CBO9780511756306.015>; read as arXiv:1204.0299v2, <https://arxiv.org/abs/1204.0299v2>: Theorem 9.2 and the sketch of its proof, with Remark 9.3, in Section 9.1.3 ("Adjoining the sine function") of that version.
