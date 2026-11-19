# Rank inequalities determine the quickselect value

Let $L$ be a list over a linear
order, let $k$ be a natural number and let $x$ be an element. Counting entries of $L$ with
multiplicity, if the number of entries less than $x$ is at most $k$ and $k$ is less than the
number of entries at most $x$, then quickselect on $L$ with zero-based rank $k$ returns $x$.
