# Band check from a starting offset

For a band width $w$, a starting offset $(i, j)$ of natural numbers and an [alignment](../pairwise-sequence-alignment/alignment.md) $A$, the band check passes if for every prefix of $A$ (the empty prefix and $A$ itself included), with $i'$ and $j'$ the starting offsets increased by the numbers of letters of the first and second rows in the prefix, $|i' - j'| \le w$.
