# Correctness and optimality of earliest-finish interval scheduling

Let $s$ and $f$ assign
start and finish times in a linear order to activities, and let $L$ be a list of activities with
$s(a) < f(a)$ for every $a$ in $L$. Let $S$ be the list returned by the earliest-finish schedule
of $L$. Then $S$ is a subpermutation of $L$ (each activity occurs in $S$ at most as often as in
$L$), any two entries of $S$ at distinct positions are compatible, and every subpermutation $M$
of $L$ whose entries at distinct positions are pairwise compatible has length at most the length
of $S$.
