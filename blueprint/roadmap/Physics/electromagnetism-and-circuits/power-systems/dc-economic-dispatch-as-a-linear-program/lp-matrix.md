# Constraint matrix of the dispatch linear program

For the data of a dispatch problem, the constraint matrix `A` of the linear program is `[F, -F]`,
where `F` is the [constraint matrix on generation and angles](free-constraint-matrix.md): `F` acts
on the first nonnegative coordinate block of the variables and `-F` on the second. The linear
program maximizes `c_LP · x` subject to `x ≥ 0` and `A x ≤ rhs`, with the
[objective](lp-objective.md) `c_LP` and the [right-hand side](lp-rhs.md).
