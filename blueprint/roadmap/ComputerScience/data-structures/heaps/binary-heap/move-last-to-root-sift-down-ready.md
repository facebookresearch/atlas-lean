# Moving the last entry to the root prepares a sift-down

Let $a$ be a heap-ordered array
over a linearly ordered type with at least two entries, and let $b$ be the array obtained from $a$
by moving its last entry to the root. Then $b$ is ready for sifting down at index $0$: index $0$ is
valid in $b$, and for every index $j > 0$ of $b$ whose parent index $\lfloor (j - 1)/2 \rfloor$ is
not $0$, the entry of $b$ at the parent index is at most $b_j$.
