# In-place slot rearrangement by cycle following

Let $n$ slots hold items, a subset $A$ of them active and the others free (their contents may be overwritten), and let $\tau : A \to [n]$ be injective. Then the items can be moved so that the item of slot $s \in A$ ends in slot $\tau(s)$, using one extra bit per slot (an *active* marker), $O(1)$ registers and $O(n)$ steps, by following the cycles and paths of the partial permutation $\tau$: from each still-active slot, repeatedly move the displaced item to its target and clear markers along the way.

## Proof sketch

The partial injection decomposes into disjoint cycles and paths; following each from its start moves every item exactly once, holding one item in a register, and clearing the marker of each moved item prevents revisiting. A walk started in the middle of a path stops at a free slot, and the earlier part of the path is moved later into the slot it vacated. A fixed loop of $n$ iterations visits every possible start.

## Depends on

- [Bit-packed array on the Word RAM](../word-ram-hash-families/bit-packed-array.md)

## Sources

- D. E. Knuth, "The Art of Computer Programming, Volume 1: Fundamental Algorithms", 3rd edition, Addison-Wesley, 1997 (Section 1.3.3, permutations in place).
