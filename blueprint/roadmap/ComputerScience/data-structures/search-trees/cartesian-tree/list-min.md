# Minimum of a nonempty list

For an element $a$ and a list $as$ over a linear order, the
left-fold minimum of $a$ and $as$ is the minimum of the list with head $a$ and tail $as$. It is
computed from the head: it equals $a$ when $as$ is empty, and when $as$ has head $b$ and tail $bs$
it equals the left-fold minimum of $\min(a, b)$ and $bs$.
