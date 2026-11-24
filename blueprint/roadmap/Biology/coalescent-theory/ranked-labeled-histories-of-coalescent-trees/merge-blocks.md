# Merging two lineage blocks

For a list $(B_0, \dots, B_{r-1})$ of blocks of sampled genes and natural numbers $a$ and $b$, merging the blocks at positions $a$ and $b$ replaces the block at position $a$ by $B_a \cup B_b$ and then removes the entry at position $b$, where a position outside the list contributes the empty set and removes nothing. For $a < b < r$ this merges the lineages at positions $a$ and $b$ into one lineage at position $a$.
