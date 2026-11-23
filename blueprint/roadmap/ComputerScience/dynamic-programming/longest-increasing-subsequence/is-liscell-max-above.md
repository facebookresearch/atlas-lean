# The step of the LIS recurrence

Let $x$ be an element, $rest$ a list, and $t$ a table of
triples $(y, k, zs)$ that satisfies the invariant of the LIS table for $rest$. Let $(b, w)$ be the
result of the scan of $t$ for entries above $x$. Then $(b + 1, w)$ is a table cell for $x$ followed
by $rest$: $w$ is a subsequence of $rest$, the list $x$ followed by $w$ is strictly increasing and
has length $b + 1$, and every strictly increasing list $x$ followed by a subsequence of $rest$ has
length at most $b + 1$.
