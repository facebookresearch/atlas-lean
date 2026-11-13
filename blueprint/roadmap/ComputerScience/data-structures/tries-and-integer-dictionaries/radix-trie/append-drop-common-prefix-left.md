# A list is its common prefix with another list followed by the rest

Let $s$ and $t$ be
lists over a type with decidable equality, and let $p$ be the longest common prefix of $s$ and
$t$. Then $s$ is $p$ followed by the list obtained by dropping the first $|p|$ elements of $s$,
where $|p|$ is the length of $p$.
