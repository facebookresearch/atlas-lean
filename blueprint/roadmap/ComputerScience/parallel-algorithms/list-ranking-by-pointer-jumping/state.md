# State of pointer jumping for suffix sums

For $n$ nodes and a type $M$, a state assigns
to each node $v$ a pointer, which is either a node or none (past the end of the list), and an
accumulated value in $M$. The accumulated value is meant to be the sum of the node values from
$v$ up to, but not including, the pointer's target.
