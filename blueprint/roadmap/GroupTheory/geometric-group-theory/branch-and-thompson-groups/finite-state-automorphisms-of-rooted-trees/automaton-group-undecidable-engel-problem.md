# Some automaton group has undecidable Engel problem

There is an automaton group in which no algorithm decides, for elements $g$ and $h$, whether some iterated commutator $[\dots[[g, h], h], \dots, h]$ is trivial. This answers a question of Bartholdi.

With the commutator $[g, h] = g^{-1}h^{-1}gh$, a pair $(g, h)$ of elements of a group is an Engel pair if there is $n \ge 1$ such that the $n$-fold iterated commutator $[\dots[[g, h], h], \dots, h]$, with $h$ appearing $n$ times, is the identity. The Engel problem for a group with a finite generating set asks for an algorithm that decides, given two words $v, w$, whether the pair of elements they represent is an Engel pair.

There exists an automaton group $G$ whose Engel problem is undecidable; the same group also has undecidable order problem (Theorem 1.2 and Theorem 6.1 of the source).

## Depends on

- [Automaton group](automaton-group.md)
- [Order problem and torsion problem of a finitely generated group](../../../presentations-and-decision-problems/conjugacy-order-and-power-problems/order-and-power-problems/order-problem.md)
- [Group](../../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Iterated commutators for Engel lengths](../../../commutators-and-engel-conditions/engel-elements/engel-comm.md)

## Proof depends on

- [Some automaton group has undecidable order problem](automaton-group-undecidable-order-problem.md)

## Expansion

In the group $G(M)$ that simulates a Turing machine $M$, there is a fixed element $h$ such that, for every element $g$ constructed from an input, the $n$-fold iterated commutator $[\dots[[g, h], h], \dots, h]$ equals $g^{\pm 2^n}$. So $(g, h)$ is an Engel pair exactly when $g$ has finite order, a power of $2$, exactly when $M$ halts on the input; for universal $M$ the Engel problem is undecidable.

## Sources

- P. Gillibert, "An automaton group with undecidable order and Engel problems", Journal of Algebra 497 (2018), 363–392, https://doi.org/10.1016/j.jalgebra.2017.11.049; arXiv:1710.09733v2 (Theorem 1.2 and Theorem 6.1 of arXiv:1710.09733v2, with the commutator convention of Section 2).
