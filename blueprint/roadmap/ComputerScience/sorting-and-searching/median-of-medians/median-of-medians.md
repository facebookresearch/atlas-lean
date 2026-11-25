# Median-of-medians selection

Given a list $L$ over a linear order and a zero-based rank
$k$, median-of-medians selection returns either an element of $L$ or nothing, charging one unit
of cost per order comparison. If $k \ge |L|$, where $|L|$ is the length of $L$, it returns
nothing at no cost. Otherwise it runs the following recursive procedure on $(L, k)$ with a budget
of $|L|$ nested calls, returning nothing if the budget runs out. A list of length at most $140$
is handled by deterministic quickselect at the current rank. A longer list is cut into
consecutive groups of five entries, the last possibly shorter; each group is sorted by insertion
sort and its lower median is kept, giving a list $M$ of $m$ medians. The procedure recursively
selects the entry of $M$ at rank $\lfloor m/2 \rfloor$ as the pivot $x$ (returning nothing if
that call does), and splits the list by a three-way partition into the entries below $x$, equal
to $x$ and above $x$, with $b$ entries below and $e$ equal. If the current rank $r$ satisfies
$r < b$ it recurses on the lower part with rank $r$; if $b \le r < b + e$ it returns $x$;
otherwise it recurses on the upper part with rank $r - b - e$.
