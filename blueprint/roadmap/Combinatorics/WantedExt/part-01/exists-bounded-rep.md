---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.DisjunctiveRadoWanted.exists_bounded_rep
---

# Proposition 4

**Proposition 4**: let `a, λ, n` be natural numbers
with `a ≥ 3`, `n ≥ 1` and `λ ≥ a - 1`. Then for each
`N ∈ {0, …, λ (a + n)}` the equation
`∑ i in Finset.range n, x i + a * y = N` admits a
solution with each part in `{0, …, λ}`. (The endpoint
`N = 0` is included as in the paper's displayed range
`{0, …, λ(a + n)}`; that case is trivial, all parts
being `0`.)

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Combinatorics.DisjunctiveRadoWanted](../../../../sources/v2/WantedExt.md)
- Srashti Dwivedi and Amitabha Tripathi, "On the Two-Color Disjunctive Rado Number for the Equations `∑_{i=1}^{m-2} x_i + a x_{m-1} - x_m = c_j`, `j = 1, 2`", Proposition 4.
