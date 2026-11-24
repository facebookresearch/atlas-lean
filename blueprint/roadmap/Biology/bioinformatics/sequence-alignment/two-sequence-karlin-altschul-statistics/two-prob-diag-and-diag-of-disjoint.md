# Diagonals reading disjoint sets of letters are independent

Let `p` and `q` be
[probability vectors](../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/expectation-maximization-algorithm/is-dist.md)
on a finite alphabet, `s` a real score on pairs of letters and `m`, `n`, `i ≤ m` and `j ≤ n`
natural numbers. For independent words `u` and `v` of `m` and `n` independent letters with laws
`p` and `q`, consider the [diagonal of offset](diag.md) `-i`, which starts at the cell `(i, 0)`,
and the diagonal of offset `j`, which starts at `(0, j)`. Suppose the first has
[length](diag-len.md) at most `j` and the second has length at most `i`. Then the first reads only
letters `u_k` with `k ≥ i` and `v_k` with `k < j`, the second only letters `u_k` with `k < i` and
`v_k` with `k ≥ j`, and for all properties `A` and `B` of score lists
`P(A(first) and B(second)) = P(A(first)) P(B(second))` ([two-sequence probability](two-prob.md)):
the two diagonals are independent. Diagonals that share a letter need not be independent.
