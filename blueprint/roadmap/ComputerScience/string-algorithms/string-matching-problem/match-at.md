# Pattern match at an offset

For lists $p$ (the pattern) and $t$ (the text) over a type
$\alpha$ and a natural number $k$, the pattern $p$ matches the text $t$ at the zero-based offset
$k$ when $k$ is at most the length of $t$ and $p$ is a prefix of the list obtained from $t$ by
dropping its first $k$ entries.

The explicit bound on $k$ excludes offsets beyond the end of the text for an empty pattern.
