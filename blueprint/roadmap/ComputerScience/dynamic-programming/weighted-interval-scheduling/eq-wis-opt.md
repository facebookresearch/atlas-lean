# The value of an optimal schedule is the brute-force optimum

For intervals indexed by the
positive integers with start times $s$ and finish times $f$ in a linear order and natural weights
$w$, if $S$ is an optimal schedule of the first $j$ intervals with value $v$, then $v$ is the
brute-force optimum over $\{1, \dots, j\}$: the supremum, over the subsets $F$ of
$\{1, \dots, j\}$ whose distinct members are pairwise compatible, of $\sum_{i \in F} w(i)$.
