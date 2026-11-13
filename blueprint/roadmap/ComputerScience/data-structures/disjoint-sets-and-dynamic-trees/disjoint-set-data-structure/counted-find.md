# Cost-counted FIND

For a union-find structure $S$ and a node $x < |S|$, this runs the
cost-counted FIND auxiliary on $x$, obtaining a node array $A'$, a root $r$ and a cost $(t, w)$.
It returns the union-find structure with node array $A'$, together with $r$ as a node of that
structure (whose size equals $|S|$), at cost $(t, w)$.

It reuses the array and root of that single run; FIND is not run a second time.
