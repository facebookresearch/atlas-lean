# Containment of conjunctive queries under inclusion dependencies is PSPACE-complete

For a set $\Sigma$ of integrity constraints and conjunctive queries $q, q'$, write $q \subseteq_\Sigma q'$ when
$q(D) \subseteq q'(D)$ for every (finite) database $D$ that satisfies $\Sigma$. The problem of deciding, for conjunctive queries $q, q'$ and a set $\Sigma$ of
inclusion dependencies with nonempty attribute sequences, whether $q \subseteq_\Sigma q'$ is PSPACE-complete (in PSPACE, and PSPACE-hard under polynomial-time many-one
reductions), in contrast with NP-completeness under
functional dependencies. Hardness is by reduction from implication of inclusion dependencies; membership uses the
possibly infinite chase of $q$ by $\Sigma$, explored one atom at a time. Every inclusion dependency here has nonempty attribute sequences ($k \ge 1$), as in the cited definition. The [linked
syntax](../dependencies-and-the-chase/ind.md) also allows arity zero, where $R[\,] \subseteq S[\,]$ says that $S$ is nonempty whenever $R$ is; such
dependencies are excluded. Dropping such a premise
can change containment: $R[\,] \subseteq S[\,]$ makes $\exists x\, R(x)$ contained in $\exists y\, S(y)$, which fails for
$R = \{0\}$ and $S = \emptyset$.

## Depends on

- [Answers of a conjunctive query](answers-of-a-conjunctive-query.md)
- [Satisfaction of an inclusion dependency](../dependencies-and-the-chase/inclusion-dependencies-and-finite-implication.md)
- [Polynomial space for decision problems](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pspace.md)
- [Polynomial-time many-one reduction](../../../TheoryOfComputation/np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md)
- [Syntax of an inclusion dependency](../dependencies-and-the-chase/ind.md)

## Proof depends on

- [Finite controllability of conjunctive-query containment under inclusion dependencies](finite-controllability-of-cq-containment-under-inds.md)
- [Implication of inclusion dependencies is PSPACE-complete](../dependency-reasoning/implication-of-inclusion-dependencies-is-pspace-complete.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definition 11.2 with $k \ge 1$ (pp. 77–78), the problem CQ-Containment-IND and Theorem 17.6 (p. 135), Theorem 17.9 (p. 136), Corollary 17.11 and Lemma 17.12 (pp. 137–139).
