# Bounded fractional hypertree width makes constraint satisfaction polynomial

For every $r \ge 1$ there is a polynomial-time algorithm that, given a [CSP instance](constraint-satisfaction-instances-and-their-hypergraphs.md)
of [fractional hypertree width](fractional-hypertree-decompositions-and-width.md) at most $r$, decides whether it has a solution
and computes one if so; the running time is $\|I\|^{O(r^3)}$. Consequently, for every class $\mathcal H$ of hypergraphs of bounded
fractional hypertree width, $\mathrm{Csp}(\mathcal H)$ and the homomorphism problem for structures whose hypergraphs lie in
$\mathcal H$ are polynomial-time solvable.

## Depends on

- [Constraint satisfaction instances and their hypergraphs](constraint-satisfaction-instances-and-their-hypergraphs.md)
- [Fractional hypertree decompositions and width](fractional-hypertree-decompositions-and-width.md)

## Proof depends on

- [Solutions of a constraint satisfaction instance can be listed within the fractional edge cover bound](csp-solutions-within-the-fractional-edge-cover-bound.md)
- [Fractional hypertree width can be approximated](fractional-hypertree-width-can-be-approximated.md)

## Sources

- M. Grohe and D. Marx, "Constraint solving via fractional edge covers", *ACM Trans. Algorithms* 11(1) (2014) 4; arXiv:1711.04506 <https://arxiv.org/abs/1711.04506>, Lemma 4.9, Theorem 4.10 and Corollary 4.11.
