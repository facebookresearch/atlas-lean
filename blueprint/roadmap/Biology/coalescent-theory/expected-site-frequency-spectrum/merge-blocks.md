# Merging two blocks of a block-size list

For a finite list $b = (b_0, \dots, b_{r-1})$ of natural numbers and natural numbers $i$ and $j$, the merged list is obtained by deleting the entry at position $j$ of $b$, then deleting the entry at position $i$ of the resulting list (a position outside a list deletes nothing), and appending one entry $b_i + b_j$ at the end, where an entry at a position outside $b$ counts as $0$. For $i < j < r$ this removes the blocks $b_i$ and $b_j$, keeps the order of the other blocks and appends the merged block $b_i + b_j$.
