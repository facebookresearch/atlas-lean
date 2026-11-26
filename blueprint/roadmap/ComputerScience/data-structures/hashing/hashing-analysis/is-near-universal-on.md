# Indexed near-universal hash family on a key set

Let $S$ be a finite set of keys in an arbitrary key type. A finite indexed family into $m>0$
slots is near-universal on $S$ if its index set is nonempty and, for each pair of distinct
keys in $S$, at most a $2/m$ fraction of its indices give a collision. No bound is required for
pairs involving keys outside $S$. Each index has equal weight even if several indices induce
the same function. Equivalently, the number of colliding indices for each such pair, multiplied
by $m$, is at most twice the number of indices.

An [indexed universal family](../universal-hashing/is-universal-on.md), such as the
[mod-prime family](../universal-hashing/mod-prime-is-universal-on.md), satisfies this condition
on every finite set of its keys: its $1/m$ bound on all distinct keys implies the $2/m$ bound.
