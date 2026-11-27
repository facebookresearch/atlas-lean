# Conjunctive queries of bounded fractional hypertree width have polynomial-delay evaluation

For every $r \ge 1$ there is a polynomial-delay algorithm that, given a conjunctive query $Q$ of
[fractional hypertree width](fractional-hypertree-decompositions-and-width.md) at most $r$ and a database $D$, computes $Q(D)$: it
outputs the first answer within time polynomial in $\|Q\| + \|D\|$ and each further answer, or the end of the output, within
polynomial time of the previous one. The same holds for listing all solutions of CSP instances of fractional hypertree width at
most $r$.

## Depends on

- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Fractional hypertree decompositions and width](fractional-hypertree-decompositions-and-width.md)
- [Constraint satisfaction instances and their hypergraphs](constraint-satisfaction-instances-and-their-hypergraphs.md)

## Proof depends on

- [Bounded fractional hypertree width makes constraint satisfaction polynomial](bounded-fractional-hypertree-width-makes-csp-polynomial.md)

## Sources

- M. Grohe and D. Marx, "Constraint solving via fractional edge covers", *ACM Trans. Algorithms* 11(1) (2014) 4; arXiv:1711.04506 <https://arxiv.org/abs/1711.04506>, Theorems 4.13 and 4.14.
