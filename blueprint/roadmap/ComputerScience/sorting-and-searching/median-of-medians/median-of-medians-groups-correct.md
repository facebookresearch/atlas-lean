# Group medians are lower medians of their blocks

Let $xs$ be a list over a linear
order, and let $g_1, \dots, g_m$ be its consecutive blocks of five elements, the last of which
may be shorter. Then the list of group medians of $xs$ has the same length $m$, say
$x_1, \dots, x_m$, and for each $i$, writing $k_i = \lfloor (|g_i| - 1)/2 \rfloor$ and counting
elements of $g_i$ with multiplicity: $x_i$ belongs to $g_i$, at most $k_i$ elements of $g_i$
are less than $x_i$, and more than $k_i$ elements of $g_i$ are less than or equal to $x_i$.
