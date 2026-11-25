# Instrumented search in a one-entry tree

Let $e$ be an entry whose interval is $[a, b]$,
let $q = [c, d]$ be a query interval, and let $k = 2$ if $a \le d$ and $k = 1$ otherwise.
Consider the single-node tree built from $e$ with empty subtrees and exact cached fields. If
$[a, b]$ and $[c, d]$ overlap (that is, $a \le d$ and $c \le b$), the instrumented overlap search
of $q$ in this tree returns $e$ with a cost record of one node visit and $k$ endpoint
comparisons. Otherwise it returns no entry with a cost record of two node visits (the root and
its empty right subtree) and $k$ endpoint comparisons. All other counters are zero in both
cases.
