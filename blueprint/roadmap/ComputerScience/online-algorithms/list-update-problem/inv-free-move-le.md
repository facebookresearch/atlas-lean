# Free moves never add inversions against a list headed by the moved item

Let $L$ be a list
without duplicates, $x$ an item of $L$, and $N$ a list that is empty or starts with $x$, all of
whose items occur in $L$. For every $j \in \mathbb{N}$, let $L'$ be the list obtained from $L$ by
moving $x$ forward for free so that exactly $j$ items precede it, where $L' = L$ if at most $j$
items already precede $x$ in $L$. Then the number of inversions of $L'$ against $N$ is at most the
number of inversions of $L$ against $N$.

This applies to move-to-front's list right after accessing $x$.
