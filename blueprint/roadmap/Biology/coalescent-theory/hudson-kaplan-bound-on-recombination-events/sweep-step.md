# One step of the Hudson–Kaplan sweep

For a sample $M$ of $n$ haplotypes over $s$ biallelic sites, a list $A$ of pairs of sites (the intervals kept so far, most recent first) and a site $j$: let $\ell$ be the right end of the first interval of $A$, or $\ell = 0$ if $A$ is empty, and let $C$ be the set of sites $i$ with $\ell \le i < j$ such that $i$ and $j$ show [all four gametes](four-gametes.md). If $C$ is nonempty, the step returns $A$ with the interval $(\max C, j)$ added at the front, the shortest admissible four-gamete interval ending at $j$; otherwise it returns $A$ unchanged.
