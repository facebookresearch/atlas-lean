# Call trace of a range query

For natural-number endpoints $l,r$, a range query
stops on an empty tree or a leaf. At an internal node of cached size $s$,
it stops if $r\le l$, if $s\le l$, or if $l=0$ and
$s\le r$. Otherwise it calls both children, at bounds $l,r$ on the left and $l-m,r-m$
on the right for left child size $m$, using truncated natural subtraction.
