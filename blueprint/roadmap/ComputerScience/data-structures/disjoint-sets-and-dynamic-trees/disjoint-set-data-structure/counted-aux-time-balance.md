# Root tests exceed parent writes by one

For a union-find structure $S$ and a node
$x < |S|$, if the cost-counted FIND auxiliary on $x$ has cost $(t, w)$, where $t$ counts root
tests and $w$ counts parent writes, then $t = w + 1$.
