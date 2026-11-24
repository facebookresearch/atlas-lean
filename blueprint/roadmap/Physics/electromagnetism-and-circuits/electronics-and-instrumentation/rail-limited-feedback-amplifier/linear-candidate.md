# Linear Candidate

The linear (unclamped) candidate `A * vi / (1 + A * beta)`: under
`0 < A` and `0 < beta` it is the unique solution of the unclamped
equation `vo = A * (vi - beta * vo)` (see `linearCandidate_satisfies`
and `fixedPoint_unique`). As a bare definition it carries no such
claim for nonpositive gain or feedback.
