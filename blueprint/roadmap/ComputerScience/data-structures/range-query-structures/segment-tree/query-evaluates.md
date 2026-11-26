# Evaluation rules for range queries

For a range query over an additive monoid with
natural-number endpoints $l,r$, the empty-tree rule returns zero.
At a leaf the rule returns its value if $l=0\lt r$, and zero otherwise.
At a node of cached size $s$ and aggregate $a$, the first satisfied guard among
$r\le l$, $s\le l$, and $l=0\land s\le r$ returns zero, zero, or $a$, respectively.
Otherwise the rule adds the results of the left call at $(l,r)$ and the right call
at $(l-m,r-m)$, where $m$ is the left child's size and subtraction is truncated.
The trace records both subtraces in order in the last case and no children otherwise.
