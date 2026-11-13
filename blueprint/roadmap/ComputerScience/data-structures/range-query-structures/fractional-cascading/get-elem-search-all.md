# Search positions are lower bounds, index by index

For every value $x$, list of catalogs
$C_0, \dots, C_{k-1}$ and index $i$: if $i < k$, the $i$-th position returned by searching all
catalogs for $x$ is the lower bound of $x$ in $C_i$; if $i \ge k$, the search result has no
$i$-th entry.
