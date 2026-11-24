# AVL rebalancing costs at most five units

For all binary trees $l$, $r$ with cached heights and every key $x$, with no balance, cache or order hypothesis, the cost of counted rebalancing of $l$, $x$, $r$ is at most $5$. The bound is attained by a double rotation, which inspects a heavy child and an inner grandchild and performs three node rebuilds.

In this operation-count model one unit is charged for each visit to a nonempty node in a recursive traversal, each executed key comparison ($<$), each inspection of a nonempty heavy child or inner grandchild during rebalancing, and each node rebuild; reading and comparing cached heights, arithmetic on them, pattern matching, recursive calls themselves and returning existing subtrees cost nothing. The count is not CPU time or Turing-machine time.
