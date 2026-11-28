# Associative second-order unification with one function variable and no first-order variables is undecidable

Second-order unification modulo associativity is undecidable already for problems with a single function variable and no individual variables, over a signature with one constant and one binary associative symbol.

**Theorem (Cerna and Parsert).** There is an $n \geq 1$ such that $n$-ASOGU is undecidable: no algorithm decides whether an [$n$-second-order ground $\mathcal{A}$-unification problem](second-order-unification-problems.md) has a unifier (Theorem 4.12).

The proof uses a signature containing a constant $a$ and a binary symbol $g$ with $\mathcal{A} = \{g(x, g(y,z)) \approx g(g(x,y),z)\}$, and the source notes that, with $a$ the only constant, only the weaker *power associativity* $g(x, g(x,x)) \approx g(g(x,x),x)$ is needed. The source leaves open whether second-order ground unification without associative symbols is decidable, and remarks that the arity $n$ of the function variable produced by the reduction is at least $9$.

## Depends on

- [Second-order unification problems](second-order-unification-problems.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The proof reduces Hilbert's tenth problem over the natural numbers. A polynomial equation $p(x_1, \dots, x_n) = 0$ with integer coefficients is computably encoded as a unification problem with one function variable $F$ of arity $n$, whose $i$-th argument stands for the unknown $x_i$; the example in the source encodes $(x-1)(x-2)(y-1)(y-2) = 0$ by one equation. A substitution $F \mapsto \lambda y_1 \dots y_n.\, t$ is relevant only through how often each $y_i$ occurs in $t$, and an "$n$-counter" construction (Section 3) tracks how these numbers determine the number of occurrences of the constant $a$ on each side. Since $g$ is associative and $a$ is the only other symbol, the two sides are equal modulo $\mathcal{A}$ exactly when they contain equally many occurrences of $a$, which happens exactly for the substitutions coming from natural-number solutions of $p = 0$.

## Sources

- D. M. Cerna and J. Parsert, "One is all you need: second-order unification without first-order variables", *Logical Methods in Computer Science* 22(2), paper 3, 2026, doi:10.46298/lmcs-22(2:3)2026; read as arXiv:2404.10616v10, <https://arxiv.org/abs/2404.10616v10>: Theorem 4.12 and its proof, the definitions of Section 2, the $n$-counter of Section 3, and the example and discussion following Theorem 4.12 in Section 4.
