# Cost-bounded free monad computations

A two-phase bound counting only the operations selected by `costly`:
`CostBoundedWith costly cont q c` holds when, along every path of `c`, at most
`q` operations `a` with `costly a = true` occur (the others are free) and the
output `x` satisfies `cont x j`, where `j` is the budget left. With `costly =
fun _ => true` it is the query bound `IsQueryBoundedWith`.
