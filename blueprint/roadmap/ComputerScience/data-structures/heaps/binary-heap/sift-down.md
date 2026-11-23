# Sift-down

Sifting down an array $a$ over a linearly ordered type from index $i$ works as
follows. If $i$ has a child in $a$, that is, if $2i+1$ is a valid index, let $c$ be the child of
$i$ (among $2i+1$ and $2i+2$, if valid) holding the smaller value, preferring the left child
$2i+1$ on ties. If $a_c < a_i$, swap the entries at $i$ and $c$ and continue sifting down from
$c$; otherwise, or if $i$ has no child, return the array unchanged.
