# Correctness of median-of-medians selection

Let $L$ be a list over a linearly ordered type
and let $k$ be a natural number. If median-of-medians selection of rank $k$ in $L$ returns an
element $x$, then $x$ occurs in $L$, the number of entries of $L$ less than $x$, counted with
multiplicity, is at most $k$, and $k$ is less than the number of entries of $L$ that are at
most $x$.
