# The cost-counted FIND returns the FIND result

For a union-find structure $S$ and a node
$x < |S|$, the value returned by the cost-counted FIND on $x$ (the compressed union-find
structure together with the root of $x$), with its cost discarded, equals the result of the
Batteries FIND with path compression on $x$.
