# KMP returns the first match

Let $p$ and $t$ be lists over a type with a lawful boolean
equality, and write $|t|$ for the length of $t$. For every natural number $i$, KMP search for
$p$ in $t$ returns the offset $i$ if and only if $p$ matches $t$ at $i$ and at no $j < i$, where
$p$ matches $t$ at $i$ when $i \le |t|$ and $p$ is a prefix of the list obtained from $t$ by
dropping its first $i$ elements.
