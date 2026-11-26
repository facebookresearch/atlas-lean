# Kd-tree construction from two presorted rank lists

Given the same $n$ even rank
points sorted on the current and opposite axes, split the first list at $\lfloor n/2\rfloor$.
The separator is one less than the first right coordinate. Stably partition the other order
at this separator, then swap the roles of the two lists in each recursive call. Charge one per
call and, at each split, the requested prefix size $\lfloor n/2\rfloor$ plus one per partition
test. For well-formed orders the requested size is the actual prefix length; a shorter first
list still incurs the full requested charge. The size parameter determines the recursion; on
malformed orders an absent singleton gives an empty tree and an absent right head uses the
default coordinate zero.
