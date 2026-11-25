# Group of a representative

For a grouped y-fast trie $t$ and a key $r$, the group of $r$
is the first group of $t$, in the order of the groups, whose last element is $r$, or the empty
list if no group of $t$ ends with $r$.

In a valid trie every group is strictly increasing, so its last element is its maximum.
