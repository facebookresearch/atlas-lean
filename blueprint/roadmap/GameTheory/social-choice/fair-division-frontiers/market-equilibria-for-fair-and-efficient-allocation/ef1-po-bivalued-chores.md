# EF1 and Pareto optimal allocations of bivalued chores

Let $n$ agents have additive cost functions $c_i : 2^M \to \mathbb{R}_{\ge 0}$ on a finite set $M$ of chores, with $c_i(e) \in \{a, b\}$ for constants $0 < a < b$. An allocation is EF1 for chores if for all $i, j$ with $X_i \ne \emptyset$ there is a chore $e \in X_i$ with $c_i(X_i \setminus \{e\}) \le c_i(X_j)$. For bivalued cost functions, an allocation that is EF1 and fractionally Pareto optimal (no fractional allocation weakly lowers every cost and strictly lowers one) exists and can be computed in polynomial time.

## Proof sketch

Use the chores analogue of a Fisher market: agents earn payments for chores they perform, chores are assigned only along minimum pain-per-buck edges, and payments of the highest earner's component are lowered. With two cost levels, the earning restriction becomes a two-level structure that guarantees termination after polynomially many payment drops; at termination the allocation is payment-EF1, hence EF1, and fPO by the first welfare theorem for chores.

## Depends on

- [Fractional Pareto optimality](fractional-pareto-optimality.md)
- [Is EF1](../../../not-yet-classified/part-01/indivisible/is-ef1.md)

## Proof depends on

- [First welfare theorem: price-supported allocations are fractionally Pareto optimal](first-welfare-theorem-mbb-fpo.md)

## Sources

- S. Ebadian, D. Peters, N. Shah, "How to Fairly Allocate Easy and Difficult Chores", AAMAS 2022, arXiv:2110.11285.
