# Existence of least-squares fixes under aggregation constraints is undecidable

When integrity constraints may include aggregation constraints, no algorithm decides whether a database with integer fixable attributes has a least-squares fix. Consistent query answering under the skeptical and the majority semantics is undecidable as well. The database and the constraints are both part of the input.

**Theorem (Bertossi, Bravo, Franconi and Lopatenko).** Consider the [least-squares fixes](least-squares-fixes-of-numerical-databases.md) of databases with fixable integer attributes, where the flexible constraints $IC$ are extended linear denials together with complex, filtering, multi-attribute, single-relation aggregation constraints. Then the following problems are undecidable:

- $\mathit{NE}$: given an instance $D$ (satisfying its key constraints) and such a set $IC$, does $D$ have an LS-fix with respect to $IC$?
- $\mathit{CQA}$ under the skeptical semantics, and $\mathit{CQA}$ under the majority semantics, with the database and the set of constraints as input parameters.

The source does not define "complex" separately; the aggregation constraint in its reduction equates two filtered sums, over the same relation, of products of attributes. Without aggregation constraints and with the constraints fixed (data complexity), the source gives complexity bounds instead: for a fixed set of linear denials the database fix problem (an LS-fix within square distance $k$) is NP-complete, and for a fixed set of extended linear denials $\mathit{NE}$ is NP-complete and CQA under the skeptical and majority semantics is coNP-hard (Theorems 2 and 3 of the source).

## Depends on

- [Least-squares fixes of databases with numerical attributes](least-squares-fixes-of-numerical-databases.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

For $\mathit{NE}$ the proof reduces from Hilbert's tenth problem, the existence of integer solutions of a Diophantine equation. Each monomial of the equation becomes a relation (or a block of one relation) with one tuple per unit of its coefficient, one fixable attribute per occurrence of a variable in the monomial and one for the constant, plus a key. Fixable values $0$ mark the variable occurrences, extended linear denials with $x \ne y$ force all occurrences of the same variable to take one common value and pin the other attributes to $1$ or to the constant, and a single aggregation constraint equates the sum of the products of the attributes over the left-hand monomials with the same sum over the right-hand monomials. A fix then is exactly an integer solution, and by Proposition 1 a fix exists if and only if an LS-fix exists. For $\mathit{CQA}$, Proposition 2 reduces $\mathit{NE}(IC)$ in polynomial time to the complements of $\mathit{CQA}(\mathit{False}, IC, \mathit{Skeptical})$ and $\mathit{CQA}(\mathit{True}, IC, \mathit{Majority})$, where $\mathit{False}$ and $\mathit{True}$ are ground queries false (true) in every instance sharing the key values of the input.

A good expansion links the undecidability of Hilbert's tenth problem over the integers (which follows from the theorem linked above), the existence of an LS-fix whenever a fix exists (Proposition 1) and the reduction of Proposition 2.

## Sources

- Leopoldo Bertossi, Loreto Bravo, Enrico Franconi and Andrei Lopatenko, "Complexity and Approximation of Fixing Numerical Attributes in Databases Under Integrity Constraints", Database Programming Languages (DBPL 2005), Lecture Notes in Computer Science 3774, pp. 262–278, Springer, 2005, <https://doi.org/10.1007/11601524_17>. Read in arXiv:cs/0503032v3, <https://arxiv.org/abs/cs/0503032v3>; Theorem 1 (undecidability), Propositions 1 and 2, Theorems 2 and 3, the proof of Theorem 1 in Appendix A.1 and its worked example in Appendix A.2, numbering of arXiv:cs/0503032v3.
- Leopoldo Bertossi, Loreto Bravo, Enrico Franconi and Andrei Lopatenko, "The complexity and approximation of fixing numerical attributes in databases under integrity constraints", Information Systems 33(4–5), pp. 407–434, 2008, <https://doi.org/10.1016/j.is.2008.01.005> (journal version, not read).
