# The cost-counted FIND auxiliary returns the uncounted result

For a union-find
structure $S$ and a node $x < |S|$, the value returned by the cost-counted FIND auxiliary on $x$
(the compressed node array together with the root of $x$), with its cost discarded, equals the
result of the Batteries path-compression auxiliary routine of FIND on $x$.
