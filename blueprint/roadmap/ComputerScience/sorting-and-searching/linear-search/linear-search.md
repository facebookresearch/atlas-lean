# Linear search

Given a predicate $p$ on a type $\alpha$ and a list $L$ of elements of
$\alpha$, linear search scans $L$ from the front and returns the index of the first element of $L$
that satisfies $p$, or no index if no element does, together with a cost that counts one unit for
each evaluation of $p$. On the empty list it returns no index at cost $0$. On a list with head $x$
and tail $T$ it evaluates $p(x)$ at a cost of one unit; if $p(x)$ is true it returns the index $0$,
and otherwise it searches $T$, adds one to the index found there (if any), and adds the cost of
that search.

No cost is charged for list operations, index arithmetic, or control flow.
