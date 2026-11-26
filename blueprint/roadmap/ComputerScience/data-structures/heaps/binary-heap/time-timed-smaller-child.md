# Cost of child selection

Let $a$ be an array over a linearly ordered type and $i$ an
index, and count cost as the pair (value comparisons, array swaps). The timed child selection at
$i$ in $a$ has cost $(1, 0)$ if the right child index $2i + 2$ is less than the size of $a$, and
cost $(0, 0)$ otherwise.
