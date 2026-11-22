# Removing the minimum preserves interval validity

Let $T$ be an interval tree in which
every stored interval is valid (its low endpoint is at most its high endpoint). If the
instrumented removal of the leftmost entry of $T$ succeeds, returning that entry $m$, the
remaining tree $T'$ and a cost record $c$, then every interval stored in $T'$ is valid.
