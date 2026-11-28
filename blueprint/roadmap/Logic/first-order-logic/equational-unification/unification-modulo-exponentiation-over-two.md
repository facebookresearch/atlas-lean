# Unification modulo exponentiation over two abelian groups is undecidable

For an equational theory of exponentiation with multiplication at the base and at the exponent level, unification with free constants is undecidable once both multiplications are abelian group operations, although it is decidable when nothing is assumed of them.

**The theory $\mathcal E_1$.** The signature has a binary operation $*$ with inverse $(\cdot)^{-1}$ and unit $1$ (the base group, modeling multiplication modulo a prime $p$), a binary operation $\circledast$ with inverse $i(\cdot)$ and the same unit $1$ (the exponent group, modeling multiplication modulo $p-1$), a binary exponentiation $\exp$ and a unary generator symbol $g$. The equational theory $\mathcal E_1$ makes $*$ and $\circledast$ the operations of abelian groups and adds the identities

$$
\exp(X,1)=X,\quad\exp(1,Z)=1,\quad\exp(Z^{-1},X)=\exp(Z,X)^{-1},
$$

$$
\exp(g(X),Y)=g(X\circledast Y),\quad\exp(X*Y,Z)=\exp(X,Z)*\exp(Y,Z).
$$

*Unification with free constants* modulo $\mathcal E_1$ asks, given finitely many equations between terms built from these symbols, variables and additional free constants, whether some substitution makes both sides of every equation equal modulo $\mathcal E_1$ (see [equational unification problems](equational-unification-problems.md)).

**Theorem (Kapur, Marshall and Narendran).** Unification modulo $\mathcal E_1$ with free constants is undecidable (Theorem 5.8 of the source).

By contrast, for the partial theory of exponentiation in which no property is assumed of the multiplication operators, the source gives a terminating unification algorithm, so that unification problem is decidable.

## Depends on

- [Equational unification problems](equational-unification-problems.md)
- [Abelian group](../../../GroupTheory/group-basics/abelian-group.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)
- [Some multi-stack machine has an undecidable halting set](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/exists-not-tm2-decidable-tm2-halts-on.md)
- [Lagrange's four-square theorem](../../../NumberTheory/quadratic-forms-sums-of-squares/sums-of-squares/lagrange-four-square-theorem.md)

## Expansion

The proof reduces Hilbert's tenth problem over the integers (solvability of polynomial equations over $\mathbb Z$), which is undecidable by the DPRM theorem applied to an undecidable recursively enumerable set, the natural numbers being Diophantine in the integers by Lagrange's four-square theorem. With a free constant $b$, the integer $n$ is represented by $\bigcirc_n(b)$, the $n$-fold $\circledast$-power of $b$ for $n > 0$, the unit $1$ for $n = 0$ and the $|n|$-fold $\circledast$-power of $i(b)$ for $n < 0$ (Definition 5.1 of the source); equations involving $g$ force values of variables into this form, using that $g(s)=_{\mathcal E_1}g(t)$ implies $s=_{\mathcal E_1}t$, addition is simulated directly by $\bigcirc_i(b)\circledast\bigcirc_j(b)=\bigcirc_{i+j}(b)$, and multiplication is simulated through exponentiation, a second free constant $c$ being used to copy values. A system of Diophantine equations thus becomes a unification problem modulo $\mathcal E_1$ that is solvable exactly when the system has a solution in integers (Lemmas 5.3 and 5.4 cover every $n \in \mathbb Z$).

## Sources

- D. Kapur, A. Marshall and P. Narendran, "Unification modulo a partial theory of exponentiation", in *Proceedings of the 24th International Workshop on Unification (UNIF 2010)*, Electronic Proceedings in Theoretical Computer Science 42, pp. 12–23, 2010, doi:[10.4204/EPTCS.42.2](https://doi.org/10.4204/EPTCS.42.2); read in arXiv:1012.4891v1 ([arXiv](https://arxiv.org/abs/1012.4891v1)): the convergent system for $\mathcal E_1$ and Theorem 5.8 with Definition 5.1 and Lemmas 5.3 to 5.7 in Section 5 (Undecidability of unification of partial exponentiation with two Abelian group operators), and Theorem 4.6 and Algorithm 1 of Section 4 (decidability of the partial theory).
